import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.Init
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic endpoint rules and a single-unit discrepancy

This file formalizes Proposition 2.1 of the supplied paper. A selector is
represented by a Boolean: `true` chooses the first endpoint. The finite vertex
hypothesis is used only in the converse, to eliminate all off-edge coordinates.
-/

namespace GraphicalAllocation.Rules

variable {V : Type*} [DecidableEq V]

abbrev Profile (V : Type*) := V → ℤ

/-- Add one ball at one vertex. -/
def raise (x : Profile V) (z : V) : Profile V :=
  fun w => x w + if w = z then 1 else 0

/-- Common integer translation of a load profile. -/
def translate (x : Profile V) (c : ℤ) : Profile V := fun w => x w + c

/-- `true` chooses `u`; `false` chooses `v`. -/
def selected (u v : V) (s : Profile V → Bool) (x : Profile V) : V :=
  if s x then u else v

def update (u v : V) (s : Profile V → Bool) (x : Profile V) : Profile V :=
  raise x (selected u v s x)

def TranslationInvariant (s : Profile V → Bool) : Prop :=
  ∀ x c, s (translate x c) = s x

/-- The two coupled updates differ by exactly one positive basis vector. -/
def UnitDiscrepancy (u v : V) (s : Profile V → Bool) : Prop :=
  ∀ x z, ∃ w, update u v s (raise x z) = raise (update u v s x) w

/-- A change of decision can only move away from the perturbed endpoint. -/
def SwitchAway (u v : V) (s : Profile V → Bool) : Prop :=
  ∀ x z, s (raise x z) ≠ s x → z = selected u v s x

/-- Endpoint locality and nonincrease of the decision indicator. -/
def EndpointAntitone (u v : V) (s : Profile V → Bool) : Prop :=
  ∃ d : ℤ → Bool, (∀ x, s x = d (x u - x v)) ∧
    ∀ a b, a ≤ b → d b = true → d a = true

@[simp] theorem raise_self (x : Profile V) (z : V) : raise x z z = x z + 1 := by
  simp [raise]

@[simp] theorem raise_other (x : Profile V) {z w : V} (h : w ≠ z) :
    raise x z w = x w := by simp [raise, h]

theorem raise_comm (x : Profile V) (z w : V) :
    raise (raise x z) w = raise (raise x w) z := by
  funext a
  simp only [raise]
  omega

omit [DecidableEq V] in
theorem selected_ne_of_decision_ne {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} {x y : Profile V} (h : s x ≠ s y) :
    selected u v s x ≠ selected u v s y := by
  cases hx : s x <;> cases hy : s y <;> simp_all [selected, Ne.symm huv]

theorem switchAway_of_unitDiscrepancy {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} (h : UnitDiscrepancy u v s) : SwitchAway u v s := by
  intro x z hswitch
  obtain ⟨w, hw⟩ := h x z
  have hn := selected_ne_of_decision_ne huv hswitch
  have hc := congrFun hw (selected u v s x)
  by_contra hz
  have hz' : selected u v s x ≠ z := Ne.symm hz
  have hn' : selected u v s x ≠ selected u v s (raise x z) := Ne.symm hn
  simp only [update, raise, hz', hn', ↓reduceIte] at hc
  split_ifs at hc <;> omega

theorem unitDiscrepancy_of_switchAway {u v : V}
    {s : Profile V → Bool} (h : SwitchAway u v s) : UnitDiscrepancy u v s := by
  intro x z
  by_cases hs : s (raise x z) = s x
  · refine ⟨z, ?_⟩
    simp only [update, selected, hs]
    exact raise_comm x z _
  · refine ⟨selected u v s (raise x z), ?_⟩
    have hz := h x z hs
    simp only [update]
    rw [hz]

theorem unitDiscrepancy_iff_switchAway {u v : V} (huv : u ≠ v)
    (s : Profile V → Bool) : UnitDiscrepancy u v s ↔ SwitchAway u v s :=
  ⟨switchAway_of_unitDiscrepancy huv, unitDiscrepancy_of_switchAway⟩

theorem off_edge_raise_invariant {u v : V} {s : Profile V → Bool}
    (h : SwitchAway u v s) (x : Profile V) {z : V} (hzu : z ≠ u) (hzv : z ≠ v) :
    s (raise x z) = s x := by
  by_contra hs
  have hz := h x z hs
  cases hx : s x <;> simp_all [selected]

theorem decision_raised_first {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} (h : SwitchAway u v s) (x : Profile V)
    (hx : s (raise x u) = true) : s x = true := by
  by_contra hs
  have hz := h x u (by intro he; exact hs (he ▸ hx))
  cases hb : s x with
  | false => exact huv (by simpa [selected, hb] using hz)
  | true => exact hs hb

theorem decision_raised_second {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} (h : SwitchAway u v s) (x : Profile V)
    (hx : s x = true) : s (raise x v) = true := by
  by_contra hs
  have hz := h x v (by simpa [hx] using hs)
  simp [selected, hx] at hz
  exact huv hz.symm

/-- A translation-invariant monotone endpoint selector has the unit property.
This direction does not require a finite vertex set. -/
theorem unitDiscrepancy_of_endpointAntitone {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} (h : EndpointAntitone u v s) : UnitDiscrepancy u v s := by
  apply unitDiscrepancy_of_switchAway
  obtain ⟨d, hd, hm⟩ := h
  intro x z hs
  by_cases hzu : z = u
  · subst z
    cases hx : s x with
    | true => simp [selected, hx]
    | false =>
        have hraised : s (raise x u) = true := by cases hr : s (raise x u) <;> simp_all
        have hdraised : d (x u + 1 - x v) = true := by
          simpa [hd, raise, huv, Ne.symm huv] using hraised
        have hdx := hm (x u - x v) (x u + 1 - x v) (by omega) hdraised
        have : s x = true := (hd x).trans hdx
        simp_all
  · by_cases hzv : z = v
    · subst z
      cases hx : s x with
      | false => simp [selected, hx]
      | true =>
          have hraised : s (raise x v) = false := by cases hr : s (raise x v) <;> simp_all
          have hdx : d (x u - x v) = true := (hd x).symm.trans hx
          have hdraised := hm (x u - (x v + 1)) (x u - x v) (by omega) hdx
          have : s (raise x v) = true := by simpa [hd, raise, huv] using hdraised
          simp_all
    · have : s (raise x z) = s x := by
        rw [hd, hd]
        simp [raise, Ne.symm hzu, Ne.symm hzv]
      exact (hs this).elim

/-- Only a mark previously choosing the raised vertex can change its choice. -/
theorem selected_unchanged_of_other {u v : V} {s : Profile V → Bool}
    (h : SwitchAway u v s) (x : Profile V) (j : V)
    (hj : selected u v s x ≠ j) :
    selected u v s (raise x j) = selected u v s x := by
  have hs : s (raise x j) = s x := by
    by_contra hn
    exact hj (h x j hn).symm
  simp [selected, hs]

private theorem raise_function_update (x : Profile V) (z : V) (a : ℤ) :
    raise (Function.update x z a) z = Function.update x z (a + 1) := by
  funext w
  by_cases hw : w = z <;> simp [raise, hw]

/-- Invariance under an arbitrary change of one off-edge integer coordinate. -/
theorem off_edge_update_invariant {u v : V} {s : Profile V → Bool}
    (h : SwitchAway u v s) (x : Profile V) {z : V} (hzu : z ≠ u) (hzv : z ≠ v)
    (a : ℤ) : s (Function.update x z a) = s x := by
  refine Int.inductionOn' a (x z) ?_ ?_ ?_
  · simp
  · intro a _ ih
    have hstep := off_edge_raise_invariant h (Function.update x z a) hzu hzv
    rw [raise_function_update] at hstep
    exact hstep.trans ih
  · intro a _ ih
    have hstep := off_edge_raise_invariant h (Function.update x z (a - 1)) hzu hzv
    rw [raise_function_update] at hstep
    have ha : a - 1 + 1 = a := by omega
    rw [ha] at hstep
    exact hstep.symm.trans ih

private theorem selector_eq_of_eq_outside {u v : V} {s : Profile V → Bool}
    (h : SwitchAway u v s) (t : Finset V)
    (ht : ∀ z ∈ t, z ≠ u ∧ z ≠ v) (x y : Profile V)
    (hxy : ∀ z, z ∉ t → x z = y z) : s x = s y := by
  induction t using Finset.induction_on generalizing x with
  | empty =>
      have : x = y := funext (fun z => hxy z (by simp))
      rw [this]
  | @insert a t hat ih =>
      have ha := ht a (by simp)
      have ht' : ∀ z ∈ t, z ≠ u ∧ z ≠ v := fun z hz => ht z (by simp [hz])
      calc
        s x = s (Function.update x a (y a)) :=
          (off_edge_update_invariant h x ha.1 ha.2 (y a)).symm
        _ = s y := ih ht' (Function.update x a (y a)) (by
          intro z hz
          by_cases hza : z = a
          · simp [hza]
          · simp only [Function.update_of_ne hza]
            exact hxy z (by simp [hza, hz]))

/-- On a finite graph, the unit property makes every off-edge load irrelevant. -/
theorem endpoint_local_of_switchAway [Fintype V] {u v : V}
    {s : Profile V → Bool} (h : SwitchAway u v s) (x y : Profile V)
    (hu : x u = y u) (hv : x v = y v) : s x = s y := by
  apply selector_eq_of_eq_outside h (Finset.univ.filter (fun z => z ≠ u ∧ z ≠ v))
  · intro z hz
    simpa using hz
  · intro z hz
    by_cases hzu : z = u
    · simpa [hzu] using hu
    · have hzv : z = v := by simpa [hzu] using hz
      simpa [hzv] using hv

/-- A canonical profile with difference `d` at the oriented endpoints. -/
def canonical (u : V) (d : ℤ) : Profile V := Function.update (fun _ => 0) u d

/-- The difficult direction of Proposition 2.1, including off-edge elimination. -/
theorem endpointAntitone_of_unitDiscrepancy [Fintype V] {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} (htrans : TranslationInvariant s)
    (hunit : UnitDiscrepancy u v s) : EndpointAntitone u v s := by
  have hs := switchAway_of_unitDiscrepancy huv hunit
  let d : ℤ → Bool := fun a => s (canonical u a)
  have hrepr : ∀ x, s x = d (x u - x v) := by
    intro x
    calc
      s x = s (translate x (-x v)) := (htrans x (-x v)).symm
      _ = s (canonical u (x u - x v)) := endpoint_local_of_switchAway hs _ _
        (by simp [translate, canonical, sub_eq_add_neg])
        (by simp [translate, canonical, Ne.symm huv])
      _ = d (x u - x v) := rfl
  refine ⟨d, hrepr, ?_⟩
  have hstep : ∀ a, d (a + 1) = true → d a = true := by
    intro a ha
    apply decision_raised_first huv hs (canonical u a)
    have hcanonical : raise (canonical u a) u = canonical u (a + 1) :=
      raise_function_update (fun _ => 0) u a
    simpa [hcanonical] using ha
  intro a b hab
  induction b, hab using Int.leInduction with
  | base => exact id
  | succ b _ ih => exact fun hb => ih (hstep b hb)

/-- Proposition 2.1: exact characterization of deterministic unit-discrepancy rules. -/
theorem unitDiscrepancy_iff_endpointAntitone [Fintype V] {u v : V} (huv : u ≠ v)
    {s : Profile V → Bool} (htrans : TranslationInvariant s) :
    UnitDiscrepancy u v s ↔ EndpointAntitone u v s :=
  ⟨endpointAntitone_of_unitDiscrepancy huv htrans, unitDiscrepancy_of_endpointAntitone huv⟩

end GraphicalAllocation.Rules
