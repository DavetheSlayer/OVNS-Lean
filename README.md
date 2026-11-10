# OVNS Lean formalization

Lean 4 and Mathlib formalization of global regularity results for the three-dimensional Navier–Stokes equations with odd viscosity. This repository contains only the formalization, not the manuscript or the private research archive.

| Paper result | Final theorem in `solution.lean` |
|---|---|
| Theorem 1.1 | `Challenge.global_regularity` |
| Theorem 1.2, fixed force | `Challenge.quantitative_fixed_force` |
| Theorem 1.2, joint large-force regime | `Challenge.quantitative_joint_force` |
| Theorem 1.3, unforced region | `Challenge.closed_regions_unforced` |
| Theorem 1.3, forced rectangles | `Challenge.closed_regions_forced` |

- `challenge.lean`: the statements only (imports only Mathlib; the five `sorry`s are intentional).
- `solution.lean`: the same statements with proofs, followed by `#print axioms`.
- `OddViscousNS/`: the library, including generated certificate modules.
- `comparator.json`: the configuration for `lake comparator`.

## Verification

- **Comparator.** `lake comparator` accepted commit `9bd811d`: the five theorems have the same statements as in `challenge.lean`, use only `propext`, `Quot.sound` and `Classical.choice`, and are accepted by Lean's kernel replayed from the export. See [`reports/comparator-2026-11-09.md`](reports/comparator-2026-11-09.md). Comparator does not check that `challenge.lean` states the paper's theorems faithfully.
- **Independent kernels.** nanoda, con-ron and con-leche accepted Theorems 1.1 and 1.2. For Theorem 1.3, con-leche accepted the twelve table checks and the scalar band check; the row band and the certificates have not yet been replayed by an independent kernel.

## Build

Toolchain `leanprover/lean4:v4.36.0-rc2`; Mathlib `e75a902d370b7bc0953464cb6894422ab4b4da86` (all revisions in `lake-manifest.json`).

```sh
lake exe cache get
lake build OddViscousNS
lake env lean solution.lean      # prints the axioms of the five theorems
```

A full build takes hours. Peak memory per module is about 14 GB on a 10-core Mac, but the row-band modules `OddViscousNS/Closed/Row/Data/Low_*.lean` took about 66 GB each on a 112-core Linux node; limit parallelism with `LEAN_NUM_THREADS` if memory is short.

To compare the statements without comparator:

```sh
mkdir -p .lake/statement-check
lake env lean --root=. -o .lake/statement-check/challenge.olean challenge.lean
lake env lean --root=. -o .lake/statement-check/solution.olean solution.lean
lake env lean --run OddViscousNS_data/pilot_check/compare_challenge_solution.lean \
  .lake/statement-check/challenge.olean .lake/statement-check/solution.olean   # expect mismatches: 0
```

## Comparator

Needs Linux with `bwrap` (unprivileged user namespaces or setuid); it does not run on macOS.

```sh
lake exe cache get
lake comparator          # exit code 0 means accepted
```

The accepted run took 8 h 35 min (build 2 h 18 min, kernel replay 6 h 7 min) with a peak of 302 GB. Notes:

- `lake exe cache get` needs glibc ≥ 2.30; on older systems run it in a container.
- Comparator clears the environment inside its sandbox, so `LEAN_NUM_THREADS` must be set through a `COMPARATOR_BWRAP` wrapper (example in the report).
- `comparator-con-leche.json` also requires con-leche (untested; Theorem 1.3 estimated at about 13 CPU-hours).
- `--paranoid` cannot pass Theorem 1.3: nanoda and con-ron cannot handle the ~10⁹-bit integer products in its certificates.

## Scope

The model uses Fourier-coefficient fields and mode equations on the fixed cubic torus. There is no separate physical-space bridge theorem, and the finite positive sufficient-ratio theorem is outside this formalization's scope. Some source comments refer to notes and scripts under `OddViscousNS_data/reports/` and `OddViscousNS_data/row_witness/`, which are not included.
