/-!
# Encoding proposed by B. Moran on suit@ietf.org (2026-11-01) for draft-ietf-suit-update-management-16

The comparison rule stays as in Section 4.4 (`draftCmp`). A complete version is encoded with three release
integers, then 0 for a final release, or a negative stage, its numeric identifiers and the end marker -24.
Core Lean 4 only. `moran_sound` holds for any integer values and any number of identifiers.
-/

inductive Cmp where
  | lt | eq | gt
deriving DecidableEq, Repr

/-- `c` relative to `m`; `none` when the component ends first. -/
def draftCmp : List Int → List Int → Option Cmp
  | [], _ => some .eq
  | _ :: _, [] => none
  | x :: ms, y :: cs => if y < x then some .lt else if x < y then some .gt else draftCmp ms cs

structure Pre where
  cls : Int
  ids : List Nat
deriving DecidableEq, Repr

def lexNat : List Nat → List Nat → Cmp
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else lexNat xs ys

def preCmp : Option Pre → Option Pre → Cmp
  | none, none => .eq
  | none, some _ => .gt
  | some _, none => .lt
  | some p, some q => if p.cls < q.cls then .lt else if q.cls < p.cls then .gt else lexNat p.ids q.ids

structure Ver where
  rel : List Nat
  pre : Option Pre
deriving DecidableEq, Repr

/-- SemVer 2.0.0 Section 11 precedence of `v` relative to `w`, with numeric identifiers only. -/
def semverCmp (v w : Ver) : Cmp :=
  match lexNat v.rel w.rel with
  | .eq => preCmp v.pre w.pre
  | r => r

def nat (l : List Nat) : List Int := l.map (fun n : Nat => (n : Int))

def tailOf : Option Pre → List Int
  | none => [0]
  | some p => p.cls :: (nat p.ids ++ [-24])

def enc (v : Ver) : List Int := nat v.rel ++ tailOf v.pre

theorem ids_ok : ∀ a b : List Nat,
    draftCmp (nat a ++ [-24]) (nat b ++ [-24]) = some (lexNat b a) := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b with
    | nil => simp [nat, draftCmp, lexNat]
    | cons y ys =>
      have h1 : ¬ ((y : Int) < (-24 : Int)) := by omega
      have h2 : ((-24 : Int) < (y : Int)) := by omega
      simp [nat, draftCmp, lexNat, h1, h2]
  | cons x xs ih =>
    intro b
    cases b with
    | nil =>
      have h1 : ((-24 : Int) < (x : Int)) := by omega
      simp [nat, draftCmp, lexNat, h1]
    | cons y ys =>
      have ih' := ih ys
      simp only [nat, List.map_cons, List.cons_append, draftCmp, lexNat] at ih' ⊢
      by_cases h1 : y < x
      · have : (y : Int) < (x : Int) := by omega
        simp [h1, this]
      · by_cases h2 : x < y
        · have h3 : ¬ ((y : Int) < (x : Int)) := by omega
          have h4 : (x : Int) < (y : Int) := by omega
          simp [h1, h2, h3, h4]
        · have h3 : ¬ ((y : Int) < (x : Int)) := by omega
          have h4 : ¬ ((x : Int) < (y : Int)) := by omega
          simp [h1, h2, h3, h4]
          exact ih'

theorem tail_ok (pm pc : Option Pre) (hm : ∀ p, pm = some p → p.cls < 0) (hc : ∀ p, pc = some p → p.cls < 0) :
    draftCmp (tailOf pm) (tailOf pc) = some (preCmp pc pm) := by
  cases pm with
  | none =>
    cases pc with
    | none => simp [tailOf, draftCmp, preCmp]
    | some p =>
      have h := hc p rfl
      simp [tailOf, draftCmp, preCmp, h]
  | some q =>
    cases pc with
    | none =>
      have h := hm q rfl
      have h' : ¬ ((0 : Int) < q.cls) := by omega
      simp [tailOf, draftCmp, preCmp, h, h']
    | some p =>
      simp only [tailOf, draftCmp, preCmp]
      by_cases h1 : p.cls < q.cls
      · simp [h1]
      · by_cases h2 : q.cls < p.cls
        · simp [h1, h2]
        · simp [h1, h2]
          exact ids_ok q.ids p.ids

theorem rel_ok (t1 t2 : List Int) : ∀ a b : List Nat, a.length = b.length →
    draftCmp (nat a ++ t1) (nat b ++ t2) =
      match lexNat b a with
      | .eq => draftCmp t1 t2
      | r => some r := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => simp [nat, lexNat]
    | cons _ _ => simp at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons y ys =>
      have hl : xs.length = ys.length := by simpa using h
      have ih' := ih ys hl
      simp only [nat, List.map_cons, List.cons_append, draftCmp, lexNat] at ih' ⊢
      by_cases h1 : y < x
      · have : (y : Int) < (x : Int) := by omega
        simp [h1, this]
      · by_cases h2 : x < y
        · have h3 : ¬ ((y : Int) < (x : Int)) := by omega
          have h4 : (x : Int) < (y : Int) := by omega
          simp [h1, h2, h3, h4]
        · have h3 : ¬ ((y : Int) < (x : Int)) := by omega
          have h4 : ¬ ((x : Int) < (y : Int)) := by omega
          simp [h1, h2, h3, h4]
          exact ih'

/-- For complete versions the unchanged comparison rule computes SemVer precedence, and the outcome is
always defined: neither encoding can end before a difference appears. -/
theorem moran_sound (m c : Ver) (hl : m.rel.length = c.rel.length)
    (hm : ∀ p, m.pre = some p → p.cls < 0) (hc : ∀ p, c.pre = some p → p.cls < 0) :
    draftCmp (enc m) (enc c) = some (semverCmp c m) := by
  unfold enc semverCmp
  rw [rel_ok _ _ _ _ hl, tail_ok _ _ hm hc]
  cases lexNat c.rel m.rel <;> rfl

/-! Worked examples, all by `decide`. -/
def v (a b d : Nat) (p : Option Pre) : Ver := ⟨[a, b, d], p⟩
/-- 1.2.3-alpha.4 no longer equals the final release 1.2.3, and sorts below it. -/
example : draftCmp (enc (v 1 2 3 none)) (enc (v 1 2 3 (some ⟨-3, [4]⟩))) = some .lt := by decide
/-- 1.2.0-beta sorts below 1.2.0-beta.0. -/
example : draftCmp (enc (v 1 2 0 (some ⟨-2, []⟩))) (enc (v 1 2 0 (some ⟨-2, [0]⟩))) = some .gt := by decide
/-- A short selector keeps the prefix behaviour: [1,2,3] still matches the alpha, now as a stated family. -/
example : draftCmp [1, 2, 3] (enc (v 1 2 3 (some ⟨-3, [4]⟩))) = some .eq := by decide
/-- Greater or Equal [1,0] accepts 1.0.0-alpha, and Lesser [1,10] does not accept 1.10.0-rc. -/
example : draftCmp [1, 0] (enc (v 1 0 0 (some ⟨-3, []⟩))) = some .eq := by decide
example : draftCmp [1, 10] (enc (v 1 10 0 (some ⟨-1, []⟩))) = some .eq := by decide
/-- Outside the mapping, a component shorter than the manifest still has no defined outcome. -/
example : draftCmp [2025, 12, 6] [2025, 12] = none := by decide

#print axioms moran_sound
