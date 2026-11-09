# OVNS Lean formalization

Lean 4 and Mathlib formalization of global regularity results for the three-dimensional Navier–Stokes equations with odd viscosity.

This repository contains only the formalization: Lean sources, encoded numerical certificate modules, pinned dependencies, a statement-comparison checker, and a configuration for `lake comparator`. It does not contain the manuscript or the private research archive.

## Entry points

- `OddViscousNS.lean`: the library entry point.
- `OddViscousNS/`: analytic proofs and generated certificate modules.
- `solution.lean`: the five final statements and their proofs in namespace `Challenge`, followed by `#print axioms` commands.
- `challenge.lean`: the corresponding statement template. It imports only Mathlib; its five `sorry` placeholders are intentional. Use `solution.lean` to check the proofs.
- `comparator.json`: the challenge description for `lake comparator` (see below).

| Paper result | Final theorem in `solution.lean` |
|---|---|
| Theorem 1.1 | `Challenge.global_regularity` |
| Theorem 1.2, fixed force | `Challenge.quantitative_fixed_force` |
| Theorem 1.2, joint large-force regime | `Challenge.quantitative_joint_force` |
| Theorem 1.3, unforced region | `Challenge.closed_regions_unforced` |
| Theorem 1.3, forced rectangles | `Challenge.closed_regions_forced` |

## Build

The toolchain is pinned to **Lean v4.36.0-rc2**. Mathlib is pinned to commit `e75a902d370b7bc0953464cb6894422ab4b4da86`; all transitive dependency revisions are in `lake-manifest.json`.

```sh
lake exe cache get
lake build OddViscousNS
lake env lean solution.lean
```

The last command prints the axioms used by each final theorem: only `propext`, `Classical.choice`, and `Quot.sound`.

A fresh complete build is substantial. Measured on a 10-core Apple silicon Mac with 34 GB of memory, with six workers: the roughly 2,500 certificate modules under `OddViscousNS/Closed/Cert/` take about 48 minutes, and the 106 modules that depend on `OddViscousNS/Closed/Row/Core.lean` (the row bound of Theorem 1.3) about 33 minutes. The largest single modules are `OddViscousNS/Closed/Row/Data/Scal.lean` (28 s, peak 14.2 GB) and the twelve `OddViscousNS/Closed/Row/Data/HHc*.lean` (6–14 s, peak 10–12 GB each), so limit the number of parallel workers on smaller machines, for example `LEAN_NUM_THREADS=2 lake build OddViscousNS`.

## Compare the statements

After building the library, compare the compiled statement template and solution:

```sh
mkdir -p .lake/statement-check
lake env lean --root=. -o .lake/statement-check/challenge.olean challenge.lean
lake env lean --root=. -o .lake/statement-check/solution.olean solution.lean
lake env lean --run OddViscousNS_data/pilot_check/compare_challenge_solution.lean \
  .lake/statement-check/challenge.olean .lake/statement-check/solution.olean
```

The expected result is `compared: 12 definitions, 20 theorems, 6 other; mismatches: 0`. The checker compares definitions and statement types; it deliberately does not compare theorem proof terms with the template's placeholders.

## Comparator

`lake comparator`, part of this toolchain's Lake, establishes that every named theorem in the solution proves the same statement as the challenge, uses no axiom outside the permitted list, and is accepted by Lean's kernel. `comparator.json` names the two modules, the five theorems and the three permitted axioms; `lakefile.toml` declares `challenge` and `solution` as build targets.

Comparator builds and exports the project inside a `bubblewrap` sandbox, so it needs **Linux** with `bwrap` installed and unprivileged user namespaces enabled (or `bwrap` installed setuid root). It does not run on macOS. The sandboxed build has no network, so fetch the Mathlib cache first:

```sh
lake exe cache get
lake comparator          # reads comparator.json; exit code 0 means accepted
```

Comparator then builds the library inside the sandbox, which takes the time and memory described under **Build**. It can also judge exports produced elsewhere with `leanexport` (`--challenge-from-export`, `--solution-from-export`); see `lake comparator --help`.

Options:

- `lake comparator --config comparator-con-leche.json` (untested) also requires `con-leche`, the verified checker bundled with the toolchain, to accept the export. With con-leche alone, the twelve table checks of Theorem 1.3 take 30–148 s each (17 minutes in total, at most 9.2 GB), the scalar band check `scal_ok` 78 s (15.5 GB), and Theorems 1.1 and 1.2 about a minute each. The whole of Theorem 1.3 is estimated at about 13 CPU-hours, mostly the 8,376 row theorems (about 4 s each) and the 19,587 certificate theorems (about 0.4 s each); that complete run has not been done yet. The configuration starts con-leche with `--jobs=2`; allow about 16 GB per worker.
- `lake comparator --paranoid` also runs `nanoda`, `con-ron`, `lean4lean` and `leanchecker-paranoid`. Theorem 1.3 cannot pass it: nanoda and con-ron cannot evaluate the products of integers with about 10⁹ bits used by the row-bound certificates (con-ron runs out of memory on one 7-Mbit squaring, and nanoda's shifts take quadratic time). nanoda, con-ron and con-leche each accepted Theorems 1.1 and 1.2. Run directly, the bundled `lean4lean` could not read this toolchain's `.olean` files, and `leanchecker-paranoid` was only tried on single modules.

`lake comparator` itself has not yet been run on this repository, because no Linux machine with `bwrap` was available. The configuration follows `lake comparator --help` of this toolchain, and the `challenge` and `solution` targets were checked to build (`lake build challenge solution`).

## Verification status (9 November 2026)

- **Lean's kernel.** `lake build OddViscousNS` completes with no errors (24,548 jobs) on exactly these sources, and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the five final theorems.
- **Statements.** `compare_challenge_solution.lean` reports 0 mismatches. On 7–8 November an independent comparison of the five statements in the `leanexport` output also agreed, and caught deliberately altered controls; the statements and the definitions they use have not changed since.
- **Independent kernels.** nanoda, con-ron and con-leche accepted Theorems 1.1 and 1.2 (both statements) on 7–8 November; those parts are unchanged since. For Theorem 1.3, con-leche accepted the twelve table checks and the scalar band check on 9 November. The rest of Theorem 1.3 (the row band and the certificates) has not been replayed by an independent kernel.
- **Not done.** A run of `lake comparator`, a complete independent replay of Theorem 1.3, a mathematical correctness audit, or manual expert review.

## Changes since the first upload

The first upload (7 November 2026) preserved source snapshot `8f54176e0fbaaa01a74f1be5c1ca9cd804d8811d`. This update (9 November 2026) makes the computational certificates of Theorem 1.3 cheaper to check; no definition or theorem statement in `challenge.lean` or `solution.lean` changed, and both files are byte for byte the same.

- **Row band** (`OddViscousNS/Closed/Row/Data/Low_*.lean`): 8,376 single-row theorems instead of 1,047 eight-row batches, in the same modules.
- **Certificates** (`OddViscousNS/Closed/Cert/`): the 19,587 certificate theorems (in 2,468 modules) keep their statements, but each is now proved through a tree that evaluates the bound only at its leaves, in natural-number fixed-point arithmetic with a soundness proof (`Cert/Fast.lean`, `Cert/Bounds.lean`). This is about seven times faster in Lean's kernel.
- **Table checks** (`OddViscousNS/Closed/Row/`): the twelve table checks moved to `Row/Data/HHc*.lean`. Their arrays are now read off one product per radial function instead of being packed slot by slot, and every row carries a small key in its lowest slot that is removed again per slice (`Row/Core.lean`, specifications in `Row/Arrays.lean`). con-leche hashes numbers by their lowest bits, and without the keys almost all intermediate numbers end in zero bits and land in one hash bucket. The scalar band (`Row/ScalK.lean`, `Row/Scal.lean`) uses the same construction. In con-leche one table check went from more than two hours without a verdict to 30–148 s. In Lean, a table check module now builds in 6–14 s (the check alone took 20–30 s before), and `Data/Scal.lean` in 32 s instead of 166 s.

## Scope and provenance

The model uses Fourier-coefficient fields and mode equations on the fixed cubic torus. There is no separate physical-space bridge theorem, and the finite positive sufficient-ratio theorem is outside this formalization's scope.

Some comments in the sources refer to notes and generator scripts under `OddViscousNS_data/reports/` and `OddViscousNS_data/row_witness/`; these belong to the private research archive and are not included here.
