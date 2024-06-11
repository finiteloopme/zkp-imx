//! `MemoryAfterStark` is used to store the final values
//! in memory. It is checked against `MemoryStark` through a CTL.
//! This is used to ensure a continuation of the memory when proving
//! multiple segments of a single full transaction proof.
use std::cmp::{max, min};
use std::marker::PhantomData;

use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::util::transpose;
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use starky::evaluation_frame::StarkEvaluationFrame;
use starky::lookup::{Column, Filter, Lookup};
use starky::stark::Stark;

use super::columns::{
    value_limb, ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL, CONTEXT_FIRST_CHANGE, COUNTER, FILTER,
    FREQUENCIES, NUM_COLUMNS, RC_HIGH, SEGMENT_FIRST_CHANGE, VIRTUAL_FIRST_CHANGE,
};
use super::RANGE_CHECK;
use crate::all_stark::EvmStarkFrame;
use crate::generation::MemBeforeValues;
use crate::memory::VALUE_LIMBS;
use crate::memory_after::columns::RC_LOW;

/// Creates the vector of `Columns` corresponding to:
/// - the propagated address (context, segment, virt),
/// - the value in u32 limbs.
pub(crate) fn ctl_data<F: Field>() -> Vec<Column<F>> {
    let mut res = Column::singles([ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL]).collect_vec();
    res.extend(Column::singles((0..8).map(value_limb)));
    res
}

/// CTL filter for memory operations.
pub(crate) fn ctl_filter<F: Field>() -> Filter<F> {
    Filter::new_simple(Column::single(FILTER))
}

/// Creates the vector of `Columns` corresponding to:
/// - the initialized address (context, segment, virt),
/// - the value in u32 limbs.
pub(crate) fn ctl_data_memory<F: Field>() -> Vec<Column<F>> {
    let mut res = vec![Column::constant(F::ZERO)]; // IS_READ
    res.extend(Column::singles([ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL]).collect_vec());
    res.extend(Column::singles((0..8).map(value_limb)));
    res.push(Column::constant(F::ZERO)); // TIMESTAMP
    res
}

/// Convert `mem_before_values` to a vector of memory trace rows
pub(crate) fn mem_before_values_to_rows<F: Field>(
    mem_before_values: &MemBeforeValues,
) -> Vec<Vec<F>> {
    mem_before_values
        .iter()
        .map(|mem_data| {
            let mut row = vec![F::ZERO; NUM_COLUMNS];
            row[FILTER] = F::ONE;
            row[ADDR_CONTEXT] = F::from_canonical_usize(mem_data.0.context);
            row[ADDR_SEGMENT] = F::from_canonical_usize(mem_data.0.segment);
            row[ADDR_VIRTUAL] = F::from_canonical_usize(mem_data.0.virt);
            for j in 0..VALUE_LIMBS {
                row[j + 4] = F::from_canonical_u32((mem_data.1 >> (j * 32)).low_u32());
            }
            row
        })
        .collect()
}

/// Structure representing the `MemoryAfter` STARK.
#[derive(Copy, Clone, Default)]
pub(crate) struct MemoryAfterStark<F, const D: usize> {
    f: PhantomData<F>,
}

/// Generates the `_FIRST_CHANGE` columns and the `RC_LOW`, `RC_HIGH` columns in
/// the trace.
pub(crate) fn generate_first_change_flags_and_rc<F: RichField>(
    trace_rows: &mut [[F; NUM_COLUMNS]],
    unpadded_len: usize,
) {
    for idx in 0..unpadded_len {
        let row = trace_rows[idx].as_slice();
        let next_row = trace_rows[idx + 1].as_slice();

        let context: F = row[ADDR_CONTEXT];
        let segment = row[ADDR_SEGMENT];
        let virt = row[ADDR_VIRTUAL];
        let next_context = next_row[ADDR_CONTEXT];
        let next_segment = next_row[ADDR_SEGMENT];
        let next_virt = next_row[ADDR_VIRTUAL];

        let context_changed = context != next_context;
        let segment_changed = segment != next_segment;
        let virtual_changed = virt != next_virt;

        let context_first_change = context_changed;
        let segment_first_change = segment_changed && !context_first_change;
        let virtual_first_change =
            virtual_changed && !segment_first_change && !context_first_change;

        let row = trace_rows[idx].as_mut_slice();
        row[CONTEXT_FIRST_CHANGE] = F::from_bool(context_first_change);
        row[SEGMENT_FIRST_CHANGE] = F::from_bool(segment_first_change);
        row[VIRTUAL_FIRST_CHANGE] = F::from_bool(virtual_first_change);

        let rc_value = if context_first_change {
            next_context - context - F::ONE
        } else if segment_first_change {
            next_segment - segment - F::ONE
        } else if virtual_first_change {
            next_virt - virt - F::ONE
        } else {
            panic!("Propagated addresses must be unique.");
        };

        let rc_value = rc_value.to_canonical_u64();

        assert!(
            rc_value < (RANGE_CHECK * RANGE_CHECK) as u64,
            "Range check of {} is too large.",
            rc_value
        );

        row[RC_LOW] = F::from_canonical_u64(rc_value % RANGE_CHECK as u64);
        row[RC_HIGH] = F::from_canonical_u64(rc_value / RANGE_CHECK as u64);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> MemoryAfterStark<F, D> {
    /// Generates the `COUNTER` and `FREQUENCIES` columns, given
    /// a trace in column-major form.
    fn generate_trace_col_major(trace_col_vecs: &mut [Vec<F>], unpadded_len: usize) {
        for i in 0..trace_col_vecs[0].len() {
            if i < unpadded_len {
                let rc_low = trace_col_vecs[RC_LOW][i].to_canonical_u64() as usize;
                let rc_high = trace_col_vecs[RC_HIGH][i].to_canonical_u64() as usize;
                trace_col_vecs[FREQUENCIES][rc_low] += F::ONE;
                trace_col_vecs[FREQUENCIES][rc_high] += F::ONE;
            }
            trace_col_vecs[COUNTER][i] = F::from_canonical_usize(min(i, RANGE_CHECK - 1));
        }
    }
    pub(crate) fn generate_trace(
        &self,
        propagated_values: Vec<Vec<F>>,
    ) -> Vec<PolynomialValues<F>> {
        // Set the trace to the `propagated_values` provided by `MemoryStark`.
        // let mut rows = propagated_values;
        let unpadded_len = propagated_values.len();

        if unpadded_len > 0 {
            // If the memory after is non-empty, we will add an extra row, necessary to
            // validate the last first change rows.
            let padded_len = max(RANGE_CHECK, (unpadded_len + 1).next_power_of_two());

            let mut rows: Vec<[F; NUM_COLUMNS]> = vec![[F::ZERO; NUM_COLUMNS]; padded_len];

            for (index, row) in propagated_values.into_iter().enumerate() {
                rows[index][0..12].copy_from_slice(&row);
            }

            // The extra row is equal to the last propagated row with an incremented virt
            // and the filter off.
            rows[unpadded_len] = rows[unpadded_len - 1];
            rows[unpadded_len][FILTER] = F::ZERO;
            rows[unpadded_len][ADDR_VIRTUAL] += F::ONE;

            generate_first_change_flags_and_rc(rows.as_mut_slice(), unpadded_len);

            // println!("{:?}", rows[1022]);
            // println!("{:?}", rows[1023]);
            // println!("{:?}", rows[1024]);
            let trace_row_vecs: Vec<_> = rows.into_iter().map(|row| row.to_vec()).collect();

            // Transpose to column-major form.
            let mut trace_col_vecs = transpose(&trace_row_vecs);

            // A few final generation steps, which work better in column-major form.

            Self::generate_trace_col_major(&mut trace_col_vecs, unpadded_len);

            trace_col_vecs
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        } else {
            let mut trace_col_vecs = vec![vec![F::ZERO; RANGE_CHECK]; NUM_COLUMNS];
            for i in 0..RANGE_CHECK {
                trace_col_vecs[COUNTER][i] = F::from_canonical_usize(min(i, RANGE_CHECK - 1));
            }
            trace_col_vecs
                .into_iter()
                .map(|column| PolynomialValues::new(column))
                .collect()
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for MemoryAfterStark<F, D> {
    type EvaluationFrame<FE, P, const D2: usize> = EvmStarkFrame<P, FE, NUM_COLUMNS>
    where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>;

    type EvaluationFrameTarget = EvmStarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, NUM_COLUMNS>;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: &Self::EvaluationFrame<FE, P, D2>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let local_values = vars.get_local_values();
        let next_values = vars.get_next_values();

        let one = P::ONES;

        let addr_context = local_values[ADDR_CONTEXT];
        let addr_segment = local_values[ADDR_SEGMENT];
        let addr_virtual = local_values[ADDR_VIRTUAL];

        let next_addr_context = next_values[ADDR_CONTEXT];
        let next_addr_segment = next_values[ADDR_SEGMENT];
        let next_addr_virtual = next_values[ADDR_VIRTUAL];

        let context_first_change = local_values[CONTEXT_FIRST_CHANGE];
        let segment_first_change = local_values[SEGMENT_FIRST_CHANGE];
        let virtual_first_change = local_values[VIRTUAL_FIRST_CHANGE];

        let not_context_first_change = one - context_first_change;
        let not_segment_first_change = one - segment_first_change;
        let not_virtual_first_change = one - virtual_first_change;

        let address_changed = context_first_change + segment_first_change + virtual_first_change;
        let address_unchanged = one - address_changed;

        // The filter must be binary.
        let filter = local_values[FILTER];
        yield_constr.constraint(filter * (filter - P::ONES));

        // First change flags are binary.
        yield_constr.constraint(context_first_change * not_context_first_change);
        yield_constr.constraint(segment_first_change * not_segment_first_change);
        yield_constr.constraint(virtual_first_change * not_virtual_first_change);
        yield_constr.constraint(address_changed * address_unchanged);

        // No change before the column corresponding to the nonzero first_change
        // flag. Only matters when filter is on.
        yield_constr.constraint_transition(
            filter * segment_first_change * (next_addr_context - addr_context),
        );
        yield_constr.constraint_transition(
            filter * virtual_first_change * (next_addr_context - addr_context),
        );
        yield_constr.constraint_transition(
            filter * virtual_first_change * (next_addr_segment - addr_segment),
        );

        // If the filter is on, the address must change to ensure all tracked
        // addresses are unique.
        yield_constr.constraint_transition(filter * address_unchanged);

        // Validate range_check.
        let rc_high = local_values[RC_HIGH];
        let rc_low = local_values[RC_LOW];
        let computed_range_check = context_first_change * (next_addr_context - addr_context - one)
            + segment_first_change * (next_addr_segment - addr_segment - one)
            + virtual_first_change * (next_addr_virtual - addr_virtual - one);
        yield_constr.constraint_transition(
            rc_low + rc_high * P::Scalar::from_canonical_usize(RANGE_CHECK) - computed_range_check,
        );

        // Check the counter column.
        let counter = local_values[COUNTER];
        let next_counter = next_values[COUNTER];
        let counter_diff = next_counter - counter;
        yield_constr.constraint_first_row(counter);
        yield_constr.constraint_transition(counter_diff * (counter_diff - one));
        yield_constr
            .constraint_last_row(counter - P::Scalar::from_canonical_usize(RANGE_CHECK - 1));
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        vars: &Self::EvaluationFrameTarget,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let local_values = vars.get_local_values();
        // The filter must be binary.
        let filter = local_values[FILTER];
        let constr = builder.add_const_extension(filter, F::NEG_ONE);
        let constr = builder.mul_extension(constr, filter);
        yield_constr.constraint(builder, constr);
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn requires_ctls(&self) -> bool {
        true
    }

    fn lookups(&self) -> Vec<Lookup<F>> {
        vec![Lookup {
            columns: vec![Column::single(RC_LOW), Column::single(RC_HIGH)],
            table_column: Column::single(COUNTER),
            frequencies_column: Column::single(FREQUENCIES),
            filter_columns: vec![
                Filter::new_simple(Column::single(FILTER)),
                Filter::new_simple(Column::single(FILTER)),
            ],
        }]
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use starky::stark_testing::{test_stark_circuit_constraints, test_stark_low_degree};

    use crate::memory_after::memory_after_stark::MemoryAfterStark;

    #[test]
    fn test_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = MemoryAfterStark<F, D>;

        let stark = S::default();
        test_stark_low_degree(stark)
    }

    #[test]
    fn test_stark_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = MemoryAfterStark<F, D>;

        let stark = S::default();
        test_stark_circuit_constraints::<F, C, S, D>(stark)
    }
}
