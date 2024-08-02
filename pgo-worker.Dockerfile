#############
# Build stage
#############
# - `/src` is the repo directory.
# - `/artifacts` is $CARGO_TARGET_DIR.
# - `/output` is where the binaries go.

ARG BUILD_BASE=rustlang/rust:nightly-bullseye-slim
FROM ${BUILD_BASE} AS build

# Install build dependencies.
RUN apt-get update && apt-get install -y \
    # for jemalloc
    libjemalloc-dev \
    libjemalloc2 \
    make \
    # for openssl
    libssl-dev \
    pkg-config \
    # clean the image
    python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*


RUN cargo install cargo-pgo && pip3 install google-cloud-storage

ARG PROFILE=release
# forward the docker argument so that the script below can read it
ENV PROFILE=${PROFILE}

WORKDIR /src

COPY . .

# Build the application.
RUN \
    # cache artifacts and the cargo registry to speed up subsequent builds
    --mount=type=cache,target=/usr/local/cargo/registry/ \
    # run the build
    <<EOF
set -eux

cargo pgo build -- --locked --bin worker

EOF

# NOTE: the bucket name should be set WITHOUT the `gs://` prefix
#  BONUS NOTE: should we create a different bucket just for .profraw files?
ENV GCS_UPLOAD_BUCKET=zkevm-csv
ENV WORKER_PATH=./target/x86_64-unknown-linux-gnu/release/worker
ENV PROFILE_DIRECTORY=./target/pgo-profiles/

# run the python wrapper, which will:
#   1. execute the pgo-worker binary
#   2. wait to receive a signal (either SIGTERM or SIGKILL), then sends a SIGTERM to the pgo-worker binary
#   3. upload the created pgo .profraw file to GCS
CMD ["python3", "pgo_worker_wrapper.py"]