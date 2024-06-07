//! `MemoryAfterStark` is used to store the final values
//! in memory. It is checked against `MemoryStark` through a CTL.
//! This is used to ensure a continuation of the memory when proving
//! multiple segments of a single full transaction proof.
use std::cmp::max;
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
    value_limb, ADDR_CONTEXT, ADDR_SEGMENT, ADDR_VIRTUAL, CONTEXT_FIRST_CHANGE, FILTER,
    NUM_COLUMNS, SEGMENT_FIRST_CHANGE, VIRTUAL_FIRST_CHANGE,
};
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

/// Generates the `_FIRST_CHANGE` columns and the `RANGE_CHECK` column in the
/// trace.
pub(crate) fn generate_first_change_flags_and_rc<F: RichField>(
    trace_rows: &mut [[F; NUM_COLUMNS]],
) {
    let num_ops = trace_rows.len();
    for idx in 0..num_ops {
        let row = trace_rows[idx].as_slice();
        let next_row = if idx == num_ops - 1 {
            trace_rows[0].as_slice()
        } else {
            trace_rows[idx + 1].as_slice()
        };

        let context = row[ADDR_CONTEXT];
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

        row[RC_LOW] = if idx == num_ops - 1 {
            F::ZERO
        } else if context_first_change {
            next_context - context - F::ONE
        } else if segment_first_change {
            next_segment - segment - F::ONE
        } else if virtual_first_change {
            next_virt - virt - F::ONE
        } else {
            next_timestamp - timestamp
        };

        assert!(
            row[RANGE_CHECK].to_canonical_u64() < num_ops as u64,
            "Range check of {} is too large. Bug in fill_gaps?",
            row[RANGE_CHECK]
        );
    }
}

impl<F: RichField + Extendable<D>, const D: usize> MemoryAfterStark<F, D> {
    pub(crate) fn generate_trace(
        &self,
        propagated_values: Vec<Vec<F>>,
    ) -> Vec<PolynomialValues<F>> {
        // Set the trace to the `propagated_values` provided by `MemoryStark`.
        // let mut rows = propagated_values;
        let num_rows = propagated_values.len();
        let mut rows: Vec<Vec<F>> = vec![vec![F::ZERO; NUM_COLUMNS]; num_rows];

        for (index, row) in propagated_values.into_iter().enumerate() {
            rows[index][0..12].copy_from_slice(&row);
        }

        let num_rows_padded = max(128, num_rows.next_power_of_two());
        for _ in num_rows..num_rows_padded {
            rows.push(vec![F::ZERO; NUM_COLUMNS]);
        }

        let cols = transpose(&rows);

        cols.into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
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
        // The filter must be binary.
        let filter = local_values[FILTER];
        yield_constr.constraint(filter * (filter - P::ONES));
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
        vec![]
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
