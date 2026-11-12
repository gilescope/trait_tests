VERSION 0.8
# Everything runs in containers: `earth +ci` (EarthBuild). Nothing to install but earth and docker.
#
#   +test     Rust: trait_tests, explore workspace, no_std build, clippy
#   +probe    Charon + Aeneas on explore/probe: the GAT hylo alone, no collections
#   +extract  Rust -> LLBC -> Lean via Charon + Aeneas (pinned, built with nix)
#   +verify   lake build of the Lean spec against the extracted definitions
#   +ci       all of the above
#
# Aeneas source is an argument, so a fork can be used:
#   earth +verify --AENEAS_REPO=gilescope/aeneas --AENEAS_REV=<sha>

ARG --global AENEAS_REPO=AeneasVerif/aeneas
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
        build "github:$AENEAS_REPO/$AENEAS_REV#aeneas" -o /opt/aeneas
    ENV PATH=/opt/aeneas/bin:$PATH

# Answers one question: does Charon/Aeneas accept the GAT-encoded hylo? Fails fast if not.
probe:
    FROM +aeneas
    WORKDIR /src
    COPY --dir Cargo.toml src explore .
    RUN cd explore/probe && charon cargo --preset=aeneas
    RUN mkdir -p /out && aeneas -backend lean -dest /out explore/probe/probe.llbc
    RUN find /out -name '*.lean' -exec cat {} +
    SAVE ARTIFACT /out /Probe

extract:
    FROM +aeneas
    WORKDIR /src
    COPY --dir Cargo.toml src explore .
    # hylo (which depends on formalism) is the crate under verification; algo_std is not.
    RUN cd explore/hylo && charon cargo --preset=aeneas
    RUN mkdir -p /out && aeneas -backend lean -dest /out explore/hylo/hylo.llbc
    SAVE ARTIFACT /out /Extracted AS LOCAL explore/formalism/verify/FormalismVerify/Extracted

verify:
    FROM ubuntu:24.04
    RUN apt-get update && apt-get install -y --no-install-recommends curl git ca-certificates && rm -rf /var/lib/apt/lists/*
    RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
    ENV PATH=/root/.elan/bin:$PATH
    WORKDIR /verify
    COPY --dir explore/formalism/verify/. .
    COPY +extract/Extracted FormalismVerify/Extracted
    # point the Lean `aeneas` dependency at the same source the extraction used, and take
    # that source's Lean toolchain (the fork and upstream pin different versions)
    RUN sed -i "s#https://github.com/AeneasVerif/aeneas#https://github.com/$AENEAS_REPO#; s#^rev = .*#rev = \"$AENEAS_REV\"#" lakefile.toml
    RUN curl -sSfL "https://raw.githubusercontent.com/$AENEAS_REPO/$AENEAS_REV/backends/lean/lean-toolchain" -o lean-toolchain && cat lean-toolchain
    RUN lake exe cache get || true
    RUN lake build

ci:
    BUILD +test
    BUILD +verify
