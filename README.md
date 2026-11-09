# OVNS Lean formalization

Lean 4 and Mathlib formalization of global regularity results for the three-dimensional Navier–Stokes equations with odd viscosity.

This repository contains only the formalization: Lean sources, encoded numerical certificate modules, pinned dependencies, and a statement-comparison checker. It does not contain the manuscript or the private research archive.

## Entry points

- `OddViscousNS.lean`: the library entry point.
- `OddViscousNS/`: analytic proofs and generated certificate modules.
- `solution.lean`: the five final statements and their proofs in namespace `Challenge`, followed by `#print axioms` commands.
- `challenge.lean`: the corresponding statement template. Its five `sorry` placeholders are intentional; use `solution.lean` to check the proofs.

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

The last command prints the axioms used by each final theorem. The collaborator reports only `propext`, `Classical.choice`, and `Quot.sound`. A fresh complete build is substantial: the collaborator reports approximately six to seven hours with three workers and a peak near 13 GB for one module.

## Compare the statements

After building the library, compare the compiled statement template and solution:

```sh
mkdir -p .lake/statement-check
lake env lean --root=. -o .lake/statement-check/challenge.olean challenge.lean
lake env lean --root=. -o .lake/statement-check/solution.olean solution.lean
lake env lean --run OddViscousNS_data/pilot_check/compare_challenge_solution.lean \
  .lake/statement-check/challenge.olean .lake/statement-check/solution.olean
```

The expected result is `mismatches: 0`. The checker compares definitions and statement types; it deliberately does not compare theorem proof terms with the template's placeholders.

## Scope and provenance

The sources were supplied by the collaborator on 7 November 2026 and are preserved byte for byte from source snapshot `8f54176e0fbaaa01a74f1be5c1ca9cd804d8811d`. The model uses Fourier-coefficient fields and mode equations on the fixed cubic torus. There is no separate physical-space bridge theorem, and the finite positive sufficient-ratio theorem is outside this formalization's scope.

Repository preparation checked source identity and local import closure. It did not perform a fresh full Lean build, independent kernel replay, mathematical correctness audit, or manual expert review. Run the commands above to reproduce the supplied development.
