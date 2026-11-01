/-!
# draft-ietf-suit-update-management-16, Section 4.4 (suit-parameter-version)
# versus Semantic Versioning 2.0.0, Section 11 (precedence)

A version value is a CBOR array of integers: a release part of one to three non-negative integers,
optionally followed by a pre-release indicator (a negative integer: -1 rc, -2 beta, -3 alpha) and
zero or more non-negative pre-release identifiers (Section 4.4.1).

Section 4.4 compares the manifest's array `m` with the component's array `c` integer by integer and
"stops after all integers in the array defined by the manifest have been consumed OR after a non-equal
comparison has occurred" (`draftCmp`). The reference semantics (`refCmp`) is SemVer precedence on the
versions the arrays denote; a manifest array with fewer than three release integers and no pre-release
indicator denotes the family of versions whose release tuple starts with those integers (the draft's own
examples "Equal [1] matches all version sequences starting with 1", "Greater or Equal [1,0] and
Lesser [1,10]"). `fixedCmp` is the proposed replacement procedure.

Checked with Lean 4.33.1, core only (no Mathlib):
  ~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean SuitVersion.lean
-/

inductive Cmp where
  | lt | eq | gt
deriving DecidableEq, Repr

/-! ## Section 4.4 as written -/

/-- Compare the component array `c` against the manifest array `m` (result: `c` relative to `m`).
`none`: the component's array is consumed before the manifest's array — the draft defines no outcome. -/
def draftCmp : List Int → List Int → Option Cmp
  | [], _ => some .eq
  | _ :: _, [] => none
  | x :: ms, y :: cs => if y < x then some .lt else if x < y then some .gt else draftCmp ms cs

/-! ## Versions and SemVer 2.0.0 precedence -/

structure Pre where
  cls : Int        -- pre-release class: -3 alpha < -2 beta < -1 rc (any negative integer)
  ids : List Nat   -- numeric pre-release identifiers
deriving DecidableEq, Repr

/-- SemVer precedence on dot-separated numeric identifiers: numeric comparison from left to right,
"a larger set of pre-release fields has a higher precedence". -/
def lexNat : List Nat → List Nat → Cmp
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else lexNat xs ys

/-- "a pre-release version has lower precedence than a normal version"; alpha < beta < rc. -/
def preCmp : Option Pre → Option Pre → Cmp
  | none, none => .eq
  | none, some _ => .gt
  | some _, none => .lt
  | some p, some q => if p.cls < q.cls then .lt else if q.cls < p.cls then .gt else lexNat p.ids q.ids

/-- A denoted version: release tuple (major, minor, patch — a list of length 3) and pre-release. -/
structure Ver where
  rel : List Nat
  pre : Option Pre
deriving DecidableEq, Repr

/-- SemVer 2.0.0 Section 11 precedence (`v` relative to `w`), for release tuples of equal length. -/
def semverCmp (v w : Ver) : Cmp :=
  match lexNat v.rel w.rel with
  | .eq => preCmp v.pre w.pre
  | r => r

/-! ## Version arrays of Section 4.4.1 -/

structure Arr where
  rel : List Nat
  pre : Option Pre
deriving DecidableEq, Repr

/-- Well-formed per Section 4.4.1: one to three release integers, negative pre-release indicator. -/
def Arr.wf (a : Arr) : Prop :=
  1 ≤ a.rel.length ∧ a.rel.length ≤ 3 ∧ ∀ p, a.pre = some p → p.cls < 0

def preList : Option Pre → List Int
  | none => []
  | some p => p.cls :: p.ids.map Int.ofNat

/-- The CBOR array `[+int]`. -/
def Arr.toList (a : Arr) : List Int := a.rel.map Int.ofNat ++ preList a.pre

/-- Missing minor or patch numbers are zero (the draft writes "Version 2.0" for 2.0.0,
"1.2-beta = [1,2,-2]"). -/
def pad3 (l : List Nat) : List Nat := l ++ List.replicate (3 - l.length) 0

def Arr.denote (a : Arr) : Ver := ⟨pad3 a.rel, a.pre⟩

/-- Does the manifest array denote a single version (three release integers, or a pre-release)? -/
def Arr.single (m : Arr) : Bool := m.pre.isSome || decide (m.rel.length = 3)

/-- Reference semantics: SemVer precedence against the version, or against the family. -/
def refCmp (m c : Arr) : Cmp :=
  if m.single then semverCmp c.denote m.denote
  else lexNat ((pad3 c.rel).take m.rel.length) m.rel

/-! ## The proposed fix -/

/-- Integer-by-integer comparison with the two added stop rules. `mPre`: the manifest array carries a
pre-release indicator. -/
def goFix (mPre : Bool) : List Int → List Int → Cmp
  | [], [] => .eq
  | [], y :: _ => if y < 0 then .lt else if mPre then .gt else .eq
  | x :: _, [] => if x < 0 then .gt else .lt
  | x :: ms, y :: cs => if y < x then .lt else if x < y then .gt else goFix mPre ms cs

/-- Proposed text: the release part of the component's array, and of a manifest array followed by a
pre-release indicator, is first padded with zeros to three integers; the integers are then compared in
sequence and the first inequality decides; if the manifest's array is consumed, the component is Lesser
when its next integer is a pre-release indicator, Greater when both arrays carry a pre-release indicator
(more identifiers), and Equal otherwise; if the component's array is consumed first, the component is
Greater when the manifest's next integer is a pre-release indicator and Lesser otherwise. -/
def fixedCmp (m c : Arr) : Cmp :=
  let ml := (if m.pre.isSome then pad3 m.rel else m.rel).map Int.ofNat ++ preList m.pre
  let cl := (pad3 c.rel).map Int.ofNat ++ preList c.pre
  goFix m.pre.isSome ml cl

/-! ## Counterexamples to the text of draft -16 (all checked by `decide`) -/

/-- A: "Equal [2,0,0]" (2.0.0) matches [2,0,0,-1,1] (2.0.0-rc.1); SemVer: 2.0.0-rc.1 < 2.0.0. -/
example : draftCmp [2,0,0] [2,0,0,-1,1] = some .eq := by decide
example : refCmp ⟨[2,0,0], none⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .lt := by decide
example : fixedCmp ⟨[2,0,0], none⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .lt := by decide

/-- A': "Lesser [1,10,0]" does not match 1.10.0-rc.1 although it is lower than 1.10.0. -/
example : draftCmp [1,10,0] [1,10,0,-1,1] = some .eq := by decide
example : refCmp ⟨[1,10,0], none⟩ ⟨[1,10,0], some ⟨-1,[1]⟩⟩ = .lt := by decide

/-- B: 1.2-beta = [1,2,-2] (Section 4.4.1) and 1.2.0-beta = [1,2,0,-2] denote the same version,
but the draft compares them as unequal, in both directions. -/
example : draftCmp [1,2,-2] [1,2,0,-2] = some .gt := by decide
example : draftCmp [1,2,0,-2] [1,2,-2] = some .lt := by decide
example : Arr.denote ⟨[1,2], some ⟨-2,[]⟩⟩ = Arr.denote ⟨[1,2,0], some ⟨-2,[]⟩⟩ := by decide
example : fixedCmp ⟨[1,2], some ⟨-2,[]⟩⟩ ⟨[1,2,0], some ⟨-2,[]⟩⟩ = .eq := by decide

/-- B': the same pre-release compares "lower" against [2,0,0] but "equal" against [2,0], although
"Equal [2,0]" matches [2,0,0] (the draft's own prefix rule). -/
example : draftCmp [2,0,0] [2,0,-1,1] = some .lt := by decide
example : draftCmp [2,0] [2,0,-1,1] = some .eq := by decide
example : draftCmp [2,0] [2,0,0] = some .eq := by decide

/-- C: 2.0.0-rc = [2,0,0,-1] and 2.0.0-rc.1 = [2,0,0,-1,1]; SemVer: rc < rc.1; the draft: equal. -/
example : draftCmp [2,0,0,-1] [2,0,0,-1,1] = some .eq := by decide
example : refCmp ⟨[2,0,0], some ⟨-1,[]⟩⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .gt := by decide
example : fixedCmp ⟨[2,0,0], some ⟨-1,[]⟩⟩ ⟨[2,0,0], some ⟨-1,[1]⟩⟩ = .gt := by decide

/-- D: no outcome is defined when the component's array is shorter than the manifest's. -/
example : draftCmp [1,2,3] [1,2] = none := by decide
example : draftCmp [2,0,0,-1,1] [2,0,0,-1] = none := by decide
example : fixedCmp ⟨[1,2,3], none⟩ ⟨[1,2], none⟩ = .lt := by decide
example : fixedCmp ⟨[2,0,0], some ⟨-1,[1]⟩⟩ ⟨[2,0,0], some ⟨-1,[]⟩⟩ = .lt := by decide

/-! ## Soundness of the fix: `fixedCmp` is SemVer precedence (or the family rule) for all arrays -/

theorem lexNat_eq_iff : ∀ a b : List Nat, lexNat a b = .eq ↔ a = b
  | [], [] => by simp [lexNat]
  | [], _ :: _ => by simp [lexNat]
  | _ :: _, [] => by simp [lexNat]
  | x :: xs, y :: ys => by
    simp only [lexNat]
    by_cases h1 : x < y
    · simp [h1]; omega
    · by_cases h2 : y < x
      · simp [h1, h2]; omega
      · have hxy : x = y := by omega
        subst hxy
        simp [h1, lexNat_eq_iff xs ys]

/-- On pre-release identifiers (non-negative integers, manifest with pre-release), `goFix` is `lexNat`. -/
theorem goFix_ids : ∀ (a b : List Nat), goFix true (a.map Int.ofNat) (b.map Int.ofNat) = lexNat b a
  | [], [] => by simp [goFix, lexNat]
  | [], y :: ys => by simp [goFix, lexNat]
  | x :: xs, [] => by simp [goFix, lexNat]
  | x :: xs, y :: ys => by
    simp only [List.map, goFix, lexNat]
    by_cases h1 : y < x
    · simp [h1]
    · by_cases h2 : x < y
      · simp [h1, h2]
      · have hxy : x = y := by omega
        subst hxy
        simp [h1, goFix_ids xs ys]

/-- Equal-length release prefixes: `goFix` decides by `lexNat` and continues on the tails. -/
theorem goFix_append (f : Bool) : ∀ (a b : List Nat) (ta tb : List Int), a.length = b.length →
    goFix f (a.map Int.ofNat ++ ta) (b.map Int.ofNat ++ tb) =
      match lexNat b a with
      | .eq => goFix f ta tb
      | r => r
  | [], [], ta, tb, _ => by simp [lexNat]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, ta, tb, h => by
    simp only [List.map, List.cons_append, goFix, lexNat]
    have h' : xs.length = ys.length := by simpa using h
    by_cases h1 : y < x
    · simp [h1]
    · by_cases h2 : x < y
      · simp [h1, h2]
      · have hxy : x = y := by omega
        subst hxy
        simp [h1, goFix_append f xs ys ta tb h']

theorem pad3_length (l : List Nat) (h : l.length ≤ 3) : (pad3 l).length = 3 := by
  simp [pad3]; omega

theorem pad3_of_length3 (l : List Nat) (h : l.length = 3) : pad3 l = l := by
  simp [pad3, h]

/-- The pre-release parts: `goFix` is `preCmp` (component relative to manifest). -/
theorem goFix_pre (pm pc : Option Pre) (hm : ∀ p, pm = some p → p.cls < 0)
    (hc : ∀ p, pc = some p → p.cls < 0) :
    goFix pm.isSome (preList pm) (preList pc) = preCmp pc pm := by
  cases pm with
  | none =>
    cases pc with
    | none => simp [preList, goFix, preCmp]
    | some q =>
      have := hc q rfl
      simp [preList, goFix, preCmp, this]
  | some p =>
    have hp := hm p rfl
    cases pc with
    | none => simp [preList, goFix, preCmp, hp]
    | some q =>
      simp only [preList, goFix, preCmp, Option.isSome_some]
      by_cases h1 : q.cls < p.cls
      · simp [h1]
      · by_cases h2 : p.cls < q.cls
        · simp [h1, h2]
        · simp [h1, h2, goFix_ids]

/-- Main theorem: for all well-formed arrays, the fixed procedure computes the reference semantics. -/
theorem fixedCmp_sound (m c : Arr) (hm : m.wf) (hc : c.wf) : fixedCmp m c = refCmp m c := by
  obtain ⟨hm1, hm3, hmp⟩ := hm
  obtain ⟨hc1, hc3, hcp⟩ := hc
  unfold fixedCmp refCmp
  cases hs : m.single with
  | true =>
    -- the manifest denotes a single version
    simp only [semverCmp, Arr.denote, if_true]
    have hml : (if m.pre.isSome then pad3 m.rel else m.rel).length = 3 := by
      unfold Arr.single at hs
      cases hp : m.pre.isSome
      · simp [hp] at hs; simp [hs]
      · simp [pad3_length m.rel hm3]
    have hmrel : pad3 m.rel = if m.pre.isSome then pad3 m.rel else m.rel := by
      cases hp : m.pre.isSome
      · unfold Arr.single at hs; simp [hp] at hs; simp [pad3_of_length3 m.rel hs]
      · simp
    rw [goFix_append m.pre.isSome _ _ _ _ (by rw [hml, pad3_length c.rel hc3])]
    rw [goFix_pre m.pre c.pre hmp hcp, ← hmrel]
  | false =>
    -- the manifest denotes a family: fewer than three release integers, no pre-release
    simp only [Bool.false_eq_true, if_false]
    unfold Arr.single at hs
    have hpre : m.pre = none := by
      cases hp : m.pre
      · rfl
      · simp [hp] at hs
    have hlen : m.rel.length ≠ 3 := by
      intro h; simp [h] at hs
    rw [hpre]
    have hpn : preList none = [] := rfl
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, hpn, List.append_nil]
    have hlenc : (pad3 c.rel).length = 3 := pad3_length c.rel hc3
    have htake : ((pad3 c.rel).take m.rel.length).length = m.rel.length := by
      simp [List.length_take, hlenc]; omega
    -- split the component's padded release into the compared prefix and the rest
    have hcl : (pad3 c.rel).map Int.ofNat ++ preList c.pre =
        ((pad3 c.rel).take m.rel.length).map Int.ofNat ++
          (((pad3 c.rel).drop m.rel.length).map Int.ofNat ++ preList c.pre) := by
      rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
    rw [hcl]
    have happ := goFix_append false m.rel ((pad3 c.rel).take m.rel.length) []
      (((pad3 c.rel).drop m.rel.length).map Int.ofNat ++ preList c.pre) htake.symm
    simp only [List.append_nil] at happ
    rw [happ]
    -- when the prefixes are equal, the component's next integer is a release integer (non-negative)
    have hdrop : ∃ y ys, (pad3 c.rel).drop m.rel.length = y :: ys := by
      cases hd : (pad3 c.rel).drop m.rel.length with
      | nil =>
        have := congrArg List.length hd
        simp [List.length_drop, hlenc] at this
        omega
      | cons y ys => exact ⟨y, ys, rfl⟩
    obtain ⟨y, ys, hy⟩ := hdrop
    rw [hy]
    cases lexNat ((pad3 c.rel).take m.rel.length) m.rel <;> simp [goFix]

#print axioms fixedCmp_sound
