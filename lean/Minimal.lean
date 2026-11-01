/-! The one case from the top of README.md. Lean 4, core only.

Section 4.4: integers are compared in sequence, and comparison "stops after all
integers in the array defined by the manifest have been consumed OR after a
non-equal comparison has occurred". The arguments are manifest, then component. -/

inductive Cmp where
  | lt | eq | gt
deriving DecidableEq, Repr

def draftCmp : List Int → List Int → Option Cmp
  | [], _ => some .eq
  | _ :: _, [] => none
  | x :: ms, y :: cs => if y < x then some .lt else if x < y then some .gt else draftCmp ms cs

-- Section 4.4.1 gives 1.2.3-alpha.4 = [1,2,3,-3,4]. "Equal [1,2,3]" matches it.
example : draftCmp [1,2,3] [1,2,3,-3,4] = some .eq := by decide
