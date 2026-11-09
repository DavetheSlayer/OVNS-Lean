# `lake comparator` run, 9 November 2026

**Result: accepted.** `lake comparator` with the repository's `comparator.json` exited with code 0 on commit
`9bd811d918c2387b82f482ce15b7cf6df1ccf3a6` (the head of `main` at the time of the run):

```
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

This covers the default configuration only: Lean's own kernel through `leanchecker`. Neither
`comparator-con-leche.json` nor `--paranoid` was run.

## What was run

| | |
|---|---|
| Repository | `9bd811d` ("Update to the 9 November sources and add a comparator configuration"), no local changes |
| Configuration | `comparator.json` as committed: modules `challenge` and `solution`, the five `Challenge.*` theorems, permitted axioms `propext`, `Quot.sound`, `Classical.choice` |
| Toolchain | `leanprover/lean4:v4.36.0-rc2` (Lean commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`), Lake `5.0.0-src+b35cb10` |
| Mathlib | `e75a902d370b7bc0953464cb6894422ab4b4da86`, from `lake exe cache get` |
| Sandbox | bubblewrap 0.11.2, unprivileged user namespaces |
| Machine | One node of the Harvard FASRC cluster: 2 × Intel Xeon Platinum 8480CL (112 cores), 1 TB RAM, Rocky Linux 8.10 (kernel 4.18.0-553, glibc 2.28). The Slurm job held 64 cores and 512 GB. |
| Command | `lake comparator`, with `COMPARATOR_BWRAP` pointing to a wrapper that sets `LEAN_NUM_THREADS=4` inside the sandbox (see [Deviations](#deviations-from-the-readme)) |

## Comparator output

Comparator built and exported both modules inside the sandbox, then replayed the solution's export in the kernel.
Excerpts from the 2,811-line log (most lines are `✔ Built …`):

```
Resolving dependencies
Building challenge
warning: challenge.lean:186:8: declaration uses `sorry`        (likewise 211, 223, 241, 258: the template's placeholders)
Build completed successfully (18246 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, Challenge.global_regularity, Challenge.quantitative_fixed_force,
  Challenge.quantitative_joint_force, Challenge.closed_regions_unforced, Challenge.closed_regions_forced, propext,
  Quot.sound, Classical.choice, Nat.add, …, outParam] from challenge
Building solution
…
info: solution.lean:412:0: 'Challenge.global_regularity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: solution.lean:413:0: 'Challenge.quantitative_fixed_force' depends on axioms: [propext, Classical.choice, Quot.sound]
info: solution.lean:414:0: 'Challenge.quantitative_joint_force' depends on axioms: [propext, Classical.choice, Quot.sound]
info: solution.lean:415:0: 'Challenge.closed_regions_unforced' depends on axioms: [propext, Classical.choice, Quot.sound]
info: solution.lean:416:0: 'Challenge.closed_regions_forced' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (24550 jobs).
Exporting #[…same list…] from solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

No module failed. The other warnings are linter warnings (unused `simp` arguments, deprecated names, files without
`module`).

After comparator finished, the README's `lake env lean solution.lean` was run outside the sandbox on the `.olean` files the
sandbox had built. It printed the same axioms for all five theorems: `[propext, Classical.choice, Quot.sound]`.

## Time and memory

| Step (inside the sandbox) | Start (UTC) | Duration | Memory |
|---|---|---|---|
| dependency resolution (`lake env`, with network), `lake build challenge` | 11:17:22 | 5 s | – |
| `leanexport` of `challenge` | 11:17:27 | 11 s | – |
| `lake build solution` | 11:17:38 | 2 h 18 min | job peak 302 GB, during the row band |
| `leanexport` of `solution` | 13:35:54 | 9 min 45 s | – |
| `leanchecker --silent --from-export` | 13:45:39 | 6 h 06 min 45 s | job memory at most 71.5 GB |
| **Total** (`lake comparator` wall clock) | | **8 h 35 min 02 s** | |

Memory is the Slurm job's cgroup (`memory.peak`, and `memory.current` sampled every minute), page cache included.

- **Kernel replay is the longest step.** One `leanchecker` process replayed the solution export for just over 6 hours.
  The README's **Build** section does not mention this step.
- **The row-band modules dominate memory.** There are 53 modules `OddViscousNS/Closed/Row/Data/Low_0.lean` …
  `Low_52.lean`, each with 161 `decide +kernel` row theorems. The 52 compiled in this run took 100–306 s each
  (median 289 s), and building 4 at once held 264 GB resident (about 66 GB each). The README names
  `Row/Data/Scal.lean` (14.2 GB) and the `HHc*` modules (10–12 GB) as the largest, measured on the Mac. On this Linux
  machine the `Low_k` modules were far larger. We did not find out why. A candidate is that more threads check a
  module's theorems at once on a 112-core node: about 168 threads were seen in one Lean process. At 128 GB, earlier
  attempts lost `Low_k` builds to the memory limit with 8, 4 and even 2 parallel builds.
- **Build products from earlier attempts.** The final run compiled 2,616 `OddViscousNS` modules and `solution`.
  The other 536 `OddViscousNS` modules had been compiled by earlier attempts on the same commit, toolchain and files,
  and Lake replayed them after checking their traces. Mathlib came from the cache. This does not affect the verdict:
  `leanchecker` re-checks the five theorems and every declaration they depend on from the export, whichever run
  produced the `.olean` files.

## Deviations from the README

1. **`lake exe cache get` inside a container.** The toolchain's bundled `clang` loads `lib/libLLVM.so.23.1` and
   `lib/libclang-cpp.so.23.1`, which need `GLIBC_2.29` and `GLIBC_2.30`. Rocky Linux 8 has glibc 2.28, so the first
   `lake exe cache get` could not compile Mathlib's cache tool. The interpreter
   fallback failed too ("Could not find native implementation of external declaration 'Cache.Cli.parseFlagOpt'"). The
   cache download therefore ran in an Ubuntu 24.04 image (`docker://buildpack-deps:noble-scm` under Singularity),
   writing into the same `.lake` directory. Everything else ran natively on the host: `lake`, `lean`, `leanexport`,
   `leanchecker` and `bwrap`.
2. **`LEAN_NUM_THREADS` inside the sandbox.** Comparator starts `bwrap` with `--clearenv` and passes only `PATH` and
   `LEAN_ABORT_ON_PANIC`. A `LEAN_NUM_THREADS` set outside, as the README suggests for smaller machines, therefore does
   not reach the sandboxed build. We set `COMPARATOR_BWRAP` to the wrapper below. It adds one `--setenv` right after
   `--clearenv` and otherwise runs `bwrap` with comparator's arguments unchanged. This changes how many modules build at
   once, not what is checked.

   ```bash
   #!/bin/bash
   N=4; args=(); added=0
   for a in "$@"; do
     args+=("$a")
     if [[ $added -eq 0 && "$a" == "--clearenv" ]]; then args+=(--setenv LEAN_NUM_THREADS "$N"); added=1; fi
   done
   exec /usr/bin/bwrap "${args[@]}"
   ```

   The logged sandbox calls are, in order:
   1. `lake env`, with network, for dependency resolution;
   2. `lake build challenge`;
   3. `leanexport` of `challenge`;
   4. `lake build solution`;
   5. `leanexport` of `solution`;
   6. `leanchecker --silent --from-export`.

   Each call includes `--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp … --clearenv … --unshare-all
   --die-with-parent --new-session`. Only the first also has `--share-net`.
3. **Node-local copy.** The repository, toolchain and `.lake` were copied to the node's local disk first. Importing
   Mathlib from the cluster's NFS scratch took 30–40 s per module, against about 5 s locally. This does not change what
   is checked.
4. **Several attempts.** Before the accepted run there were these attempts:
   - two 128 GB attempts lost `Low_k` builds to out-of-memory kills;
   - one was stopped while it was still reading from NFS (before deviation 3);
   - one failed on a node with a stale automount, which makes `bwrap --ro-bind / /` fail before anything runs.

   The accepted run is a single, uninterrupted `lake comparator` invocation in a 512 GB job.

## Suggestions for the README

- In **Build** and **Comparator**: on Linux, allow about 70 GB per parallel `Row/Data/Low_k` build. Note that comparator
  does not pass `LEAN_NUM_THREADS` into its sandbox, so either use a `COMPARATOR_BWRAP` wrapper as above or give it
  enough memory for the default parallelism. 512 GB with 4 parallel builds worked, with a peak of 302 GB.
- Mention the kernel replay: about 6 hours and 70 GB here, after the build.
- `lake exe cache get` needs glibc ≥ 2.30, for example Ubuntu 20.04, Debian 11, RHEL 9 or later, because it compiles
  the cache tool with the bundled `clang`. On older systems, run it in a container. `lean`, `lake`, `leanexport` and
  `leanchecker` themselves run on glibc 2.28.
- The sentence "`lake comparator` itself has not yet been run on this repository" and the matching **Not done** item
  are out of date as of this run. This report does not edit the README.

## Scope

Comparator established three facts. Each of the five theorems in `solution` has the same statement as in `challenge`.
They use no axiom beyond `propext`, `Quot.sound` and `Classical.choice`. Lean's kernel accepts them, replayed from the
export. Comparator does not check that `challenge.lean` states the paper's theorems faithfully. This run did not use an
independent kernel (con-leche, nanoda, con-ron, lean4lean).
