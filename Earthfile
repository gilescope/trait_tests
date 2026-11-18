VERSION 0.8
# Everything runs in containers: `earth +ci` (EarthBuild). Nothing to install but earth and docker.
#
#   +test     Rust: trait_tests, explore workspace, no_std build, clippy
#   +probe    Charon + Aeneas on explore/probe: one-shape hylo, no GAT, no closure
#   +probe-gat  the GAT hylo: fails on upstream Aeneas (GAT unimplemented); canary for the fork
#   +extract  Rust -> LLBC -> Lean via Charon + Aeneas (pinned, built with nix)
#   +verify   lake build of the Lean spec against the extracted definitions
#   +ci       all of the above
#
# Aeneas source is an argument, so a fork can be used:
#   earth +verify --AENEAS_REPO=gilescope/aeneas --AENEAS_REV=<sha>

ARG --global AENEAS_REPO=AeneasVerif/aeneas
ARG --global AENEAS_REV=0d21a9ec7bbbb110110cacc14464a47fd71c8705
# A release tarball (aeneas + charon, static linux x86_64) skips the nix build entirely.
# The gilescope fork publishes them: https://github.com/gilescope/aeneas/releases
ARG --global AENEAS_TARBALL_URL=

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

# Charon + Aeneas, built with nix from the Aeneas flake (its package symlinks charon into bin/).
aeneas-nix:
    FROM nixos/nix:2.26.3
    RUN nix --extra-experimental-features 'nix-command flakes' \
        build "github:$AENEAS_REPO/$AENEAS_REV#aeneas" -o /opt/aeneas

# Charon + Aeneas from a release tarball (static linux x86_64; the gilescope fork publishes them).
# The tarball ships aeneas, charon, charon-driver and the rust-toolchain pin charon-driver needs;
# rustup installs that toolchain from the pin placed at / so every cargo invocation below finds it.
aeneas-tarball:
    FROM ubuntu:24.04
    RUN apt-get update && apt-get install -y --no-install-recommends curl ca-certificates git build-essential && rm -rf /var/lib/apt/lists/*
    RUN mkdir -p /opt/aeneas/bin && curl -sSfL "$AENEAS_TARBALL_URL" | tar -xz -C /opt/aeneas/bin
    RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain none --profile minimal
    ENV PATH=/root/.cargo/bin:/opt/aeneas/bin:$PATH
    RUN cp /opt/aeneas/bin/rust-toolchain /rust-toolchain.toml && cat /rust-toolchain.toml && cd / && rustup toolchain install && rustup show active-toolchain
    RUN aeneas -version && charon --help | head -3

# Pick one: the IF needs a shell, hence the throwaway base image.
aeneas:
    FROM alpine:3.20
    IF [ -n "$AENEAS_TARBALL_URL" ]
        FROM +aeneas-tarball
    ELSE
        FROM +aeneas-nix
    END
    ENV PATH=/opt/aeneas/bin:$PATH

# The smallest extractable hylo. Must pass; anything +verify then trips on is a std model.
probe:
    FROM +aeneas
    WORKDIR /src
    COPY --dir Cargo.toml src explore .
    RUN cd explore/probe && charon cargo --preset=aeneas --dest-file=/src/probe.llbc || true; \
        [ -f /src/probe.llbc ] || cp "$(find / -name 'probe.llbc' -not -path '*/proc/*' 2>/dev/null | head -1)" /src/probe.llbc; \
        ls -la /src/probe.llbc
    RUN mkdir -p /out && aeneas -backend lean -dest /out -print-error-emitters /src/probe.llbc
    RUN find /out -name '*.lean' -exec cat {} +
    SAVE ARTIFACT /out /Probe

# GAT-lite acceptance test (explore/probe_gat). Fails on upstream Aeneas 0d21a9e ("Unimplemented"
# on `type Layer<X>`); the gilescope/aeneas gat-lite branch is meant to pass it. Non-blocking.
probe-gat:
    FROM +aeneas
    WORKDIR /src
    COPY --dir Cargo.toml src explore .
    RUN cd explore/probe_gat && charon cargo --preset=aeneas --dest-file=/src/probe_gat.llbc || true; \
        [ -f /src/probe_gat.llbc ] || cp "$(find / -name 'probe_gat.llbc' -not -path '*/proc/*' 2>/dev/null | head -1)" /src/probe_gat.llbc; \
        ls -la /src/probe_gat.llbc
    RUN mkdir -p /out && (aeneas -backend lean -dest /out -print-error-emitters /src/probe_gat.llbc; rc=$?; find /out -name '*.lean' -exec cat {} +; exit $rc)
    SAVE ARTIFACT /out /ProbeGat

# The fork's test for GAT-lite, extracted exactly as its test runner does it (same charon and
# aeneas flags, same paths), so the printed file can be committed as tests/lean/Gat.lean in the
# fork: its CI regenerates every test and diffs byte for byte. Non-blocking.
fork-test-gat:
    FROM +aeneas
    ARG GAT_RS_URL=https://raw.githubusercontent.com/gilescope/aeneas/91721484a4f619e20b776caf9b420b5d74d6d40a/tests/src/gat.rs
    WORKDIR /work
    RUN mkdir -p tests/src tests/lean tests/llbc && curl -sSfL "$GAT_RS_URL" -o tests/src/gat.rs
    RUN charon rustc --dest-file /work/tests/llbc/gat.llbc --preset=aeneas -- tests/src/gat.rs --crate-name=gat --crate-type=rlib --allow=unused --allow=non_snake_case --edition=2021
    RUN aeneas tests/llbc/gat.llbc -dest tests/lean -backend lean -abort-on-error -checks -print-error-emitters -no-progress-bar -checks -color -sequential
    RUN echo '===== tests/lean/Gat.lean' && cat tests/lean/Gat.lean
    SAVE ARTIFACT tests/lean/Gat.lean /Gat.lean

# The fork's known-failure test for a GAT with a trait bound: GAT-lite must reject it with an
# error, not crash. Runs aeneas exactly as the fork's test runner does and prints the output,
# which is the expected `.lean.out` of the test; the step does not fail on the (expected) error.
fork-test-gat-bound:
    FROM +aeneas
    ARG GAT_BOUND_RS_URL=https://raw.githubusercontent.com/gilescope/aeneas/5c5be98ee3c6763eaf077e2a97ebd8e8b1b40922/tests/src/gat-bound.rs
    WORKDIR /work
    RUN mkdir -p tests/src tests/lean tests/llbc && curl -sSfL "$GAT_BOUND_RS_URL" -o tests/src/gat-bound.rs
    RUN charon rustc --dest-file /work/tests/llbc/gat-bound.llbc --preset=aeneas -- tests/src/gat-bound.rs --crate-name=gat_bound --crate-type=rlib --allow=unused --allow=non_snake_case --edition=2021 > charon.out 2>&1; echo "charon exit $?"; cat charon.out
    RUN aeneas tests/llbc/gat-bound.llbc -dest tests/lean -backend lean -abort-on-error -print-error-emitters -no-progress-bar -checks -color -sequential > aeneas.out 2>&1; echo "aeneas exit $?"; echo '===== gat-bound.lean.out'; cat aeneas.out; echo '===== end'

extract:
    FROM +aeneas
    WORKDIR /src
    COPY --dir Cargo.toml src explore .
    # hylo (which depends on formalism) is the crate under verification; algo_std is not.
    # Extraction starts from the named algorithms, so the GAT-based generic API (which Aeneas
    # cannot translate) is never reached: only the per-shape core and what it uses.
    # Charon keeps the bodies of dependency crates opaque by default, which left the trace DP
    # (formalism::scheme::step_node, formalism::expr::union) as axioms in the Lean: the
    # `--include` patterns translate those bodies too, so the refinement theorems have something
    # to refine.
    ARG INCLUDE="--include=formalism::expr::_ --include=formalism::scheme::_ --include=formalism::instances::bits::_ --include=formalism::semiring::_"
    ARG START_FROM=hylo::sort::insertion_sort,hylo::sort::selection_sort,hylo::sort::quicksort,hylo::sort::mergesort,hylo::seq::reduce_seq,hylo::seq::reduce_par,hylo::seq::scan,hylo::num::gcd,hylo::num::power,hylo::path::relax,hylo::path::relax_acyclic,hylo::path::closure,hylo::search::search,hylo::search::maximise,hylo::search::maximise_count,hylo::dp::trace_dp,hylo::dp::solve_scheme,hylo::dp::solve_bits,hylo::dp::eval_ones,hylo::dp::delta_one,hylo::dp::delta_mul,hylo::dp::delta_le,hylo::dp::delta_regular
    RUN cd explore/hylo && charon cargo --preset=aeneas $INCLUDE --start-from="$START_FROM" --dest-file=/src/hylo.llbc || true; \
        [ -f /src/hylo.llbc ] || cp "$(find / -name 'hylo.llbc' -not -path '*/proc/*' 2>/dev/null | head -1)" /src/hylo.llbc; \
        ls -la /src/hylo.llbc
    RUN mkdir -p /out && aeneas -backend lean -dest /out -print-error-emitters /src/hylo.llbc
    RUN find /out -name '*.lean' | xargs wc -l && find /out -name '*.lean' -exec cat {} +
    SAVE ARTIFACT /out /Extracted AS LOCAL explore/formalism/verify/FormalismVerify/Extracted

verify:
    FROM ubuntu:24.04
    RUN apt-get update && apt-get install -y --no-install-recommends curl git ca-certificates && rm -rf /var/lib/apt/lists/*
    RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
    ENV PATH=/root/.elan/bin:$PATH
    WORKDIR /verify
    # Dependencies first, in layers that only the lakefile and the toolchain pin reach: Mathlib
    # from its olean cache, the Aeneas backend compiled from source (a stub root module pulls it
    # in). Editing a proof then rebuilds our three files, not the backend.
    COPY explore/formalism/verify/lakefile.toml ./
    # point the Lean `aeneas` dependency at the same source the extraction used, and take
    # that source's Lean toolchain (the fork and upstream pin different versions)
    RUN sed -i "s#https://github.com/AeneasVerif/aeneas#https://github.com/$AENEAS_REPO#; s#^rev = .*#rev = \"$AENEAS_REV\"#" lakefile.toml
    RUN curl -sSfL "https://raw.githubusercontent.com/$AENEAS_REPO/$AENEAS_REV/backends/lean/lean-toolchain" -o lean-toolchain && cat lean-toolchain
    RUN lake exe cache get || true
    RUN echo 'import Aeneas' > FormalismVerify.lean && lake build
    # Now the proofs and the extraction.
    COPY explore/formalism/verify/FormalismVerify.lean ./
    COPY --dir explore/formalism/verify/FormalismVerify ./
    COPY +extract/Extracted FormalismVerify/Extracted
    RUN ls -la . FormalismVerify FormalismVerify/Extracted
    RUN lake build

ci:
    BUILD +test
    BUILD +verify
