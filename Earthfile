VERSION 0.8
# Everything runs in containers: `earthly +ci`. Nothing to install but earthly (and docker).
#
#   +test     Rust: trait_tests, explore workspace, no_std build, clippy
#   +extract  Rust -> LLBC -> Lean via Charon + Aeneas (pinned, built with nix)
#   +verify   lake build of the Lean spec against the extracted definitions
#   +ci       all of the above

ARG --global AENEAS_REV=0d21a9ec7bbbb110110cacc14464a47fd71c8705

rust:
    FROM rust:1.97-slim-bookworm
    RUN rustup component add clippy
    WORKDIR /src

src:
    FROM +rust
    COPY --dir Cargo.toml src tests explore .

test:
    FROM +src
    RUN cargo test
    RUN cd explore && cargo test --workspace
    RUN cd explore && cargo build -p formalism --no-default-features
    RUN cd explore && cargo clippy -p formalism --no-default-features -- -D warnings

# Charon + Aeneas from the Aeneas flake (its nix package symlinks charon into bin/).
aeneas:
    FROM nixos/nix:2.26.3
    RUN nix --extra-experimental-features 'nix-command flakes' \
        build "github:AeneasVerif/aeneas/$AENEAS_REV#aeneas" -o /opt/aeneas
    ENV PATH=/opt/aeneas/bin:$PATH

extract:
    FROM +aeneas
    WORKDIR /src
    COPY --dir Cargo.toml src explore .
    # formalism is the crate under verification; algo_std is not.
    RUN cd explore/formalism && charon cargo --preset=aeneas
    RUN mkdir -p /out && aeneas -backend lean -dest /out explore/formalism/formalism.llbc
    SAVE ARTIFACT /out /Extracted AS LOCAL explore/formalism/verify/FormalismVerify/Extracted

verify:
    FROM ubuntu:24.04
    RUN apt-get update && apt-get install -y --no-install-recommends curl git ca-certificates && rm -rf /var/lib/apt/lists/*
    RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
    ENV PATH=/root/.elan/bin:$PATH
    WORKDIR /verify
    COPY --dir explore/formalism/verify/. .
    COPY +extract/Extracted FormalismVerify/Extracted
    RUN lake exe cache get || true
    RUN lake build

ci:
    BUILD +test
    BUILD +verify
