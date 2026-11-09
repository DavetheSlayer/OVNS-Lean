/-
Check that `solution.lean` proves exactly the statements of `challenge.lean`.

It loads both compiled files and compares every constant of the `Challenge` namespace in the
challenge with the constant of the same name in the solution: same type, same value for
definitions, same structure for inductives, constructors and recursors.  Theorem proofs are not
compared, since the challenge has `sorry` there.  Run from the repository root:

    lake env lean --root=. -o /tmp/challenge.olean challenge.lean
    lake env lean --root=. -o /tmp/solution.olean solution.lean
    lake env lean --run OddViscousNS_data/pilot_check/compare_challenge_solution.lean \
      /tmp/challenge.olean /tmp/solution.olean

The result must say `mismatches: 0`.
-/
import Lean
open Lean

unsafe def load (p : System.FilePath) : IO (Std.HashMap Name ConstantInfo) := do
  let (m, _) ← readModuleData p
  let mut r : Std.HashMap Name ConstantInfo := {}
  for n in m.constNames, c in m.constants do
    r := r.insert n c
  return r

unsafe def main (args : List String) : IO Unit := do
  let [ca, so] := args | throw (IO.userError "usage")
  let c ← load ca
  let s ← load so
  let mut defs := 0
  let mut thms := 0
  let mut other := 0
  let mut bad : Array String := #[]
  for (n, ci) in c.toList do
    unless n.getRoot == `Challenge do continue
    match s[n]? with
    | none => bad := bad.push s!"{n}: missing from solution"
    | some cs =>
      if ci.type != cs.type then bad := bad.push s!"{n}: type differs"
      match ci, cs with
      | .defnInfo a, .defnInfo b =>
        defs := defs + 1
        if a.value != b.value then bad := bad.push s!"{n}: value differs"
      | .thmInfo _, .thmInfo _ => thms := thms + 1
      | .opaqueInfo _, .opaqueInfo _ => other := other + 1
      | .inductInfo a, .inductInfo b =>
        other := other + 1
        if a.ctors != b.ctors || a.numParams != b.numParams || a.numIndices != b.numIndices then
          bad := bad.push s!"{n}: inductive differs"
      | .ctorInfo a, .ctorInfo b =>
        other := other + 1
        if a.cidx != b.cidx || a.numFields != b.numFields then bad := bad.push s!"{n}: constructor differs"
      | .recInfo a, .recInfo b =>
        other := other + 1
        let ra := a.rules.map (fun r => (r.ctor, r.nfields, r.rhs))
        let rb := b.rules.map (fun r => (r.ctor, r.nfields, r.rhs))
        if !(ra.length == rb.length && (ra.zip rb).all (fun (x, y) => x.1 == y.1 && x.2.1 == y.2.1 && x.2.2 == y.2.2)) then
          bad := bad.push s!"{n}: recursor differs"
      | _, _ => bad := bad.push s!"{n}: kind differs"
  IO.println s!"compared: {defs} definitions, {thms} theorems, {other} other; mismatches: {bad.size}"
  for b in bad.toList.take 12 do IO.println s!"  {b}"
