import GraphicalAllocation.Rules.Coupling
import Mathlib.Data.Fintype.Pi

/-!
# Finite profiles at a bounded event horizon

From a fixed initial profile, all profiles reachable in at most h allocations
belong to a finite box. Including h+1 allocations covers every one-ball perturbation.
This supplies a single finite selector signature for an entire coupled experiment.
-/

namespace GraphicalAllocation.Process
open GraphicalAllocation.Rules

variable {V : Type*} [DecidableEq V]

lemma raise_coordinate_bounds (x : Profile V) (z v : V) :
    x v ≤ raise x z v ∧ raise x z v ≤ x v + 1 := by
  unfold raise
  split_ifs <;> omega

lemma event_coordinate_bounds (e : Event V) (x : Profile V) (v : V) :
    x v ≤ e.apply x v ∧ e.apply x v ≤ x v + 1 :=
  raise_coordinate_bounds x _ v

/-- Every coordinate can only increase, by at most the event count. -/
theorem run_coordinate_bounds (events : List (Event V)) (x : Profile V) (v : V) :
    x v ≤ run events x v ∧ run events x v ≤ x v + events.length := by
  induction events generalizing x with
  | nil => simp [run]
  | cons e es ih =>
    have he := event_coordinate_bounds e x v
    have hi := ih (e.apply x)
    simp only [run, List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- A finite family containing every profile within h coordinatewise increments. -/
def profileFamily (x : Profile V) (h : ℕ) (a : V → Fin (h + 1)) : Profile V :=
  fun v => x v + (a v).val

omit [DecidableEq V] in
lemma mem_profileFamily_of_bounds (x y : Profile V) (h : ℕ)
    (hy : ∀ v, x v ≤ y v ∧ y v ≤ x v + h) :
    ∃ a : V → Fin (h + 1), profileFamily x h a = y := by
  let a : V → Fin (h + 1) := fun v =>
    ⟨(y v - x v).toNat, by have hv := hy v; omega⟩
  refine ⟨a, ?_⟩
  funext v
  have hv := hy v
  simp only [profileFamily, a]
  omega

/-- Any finite event list of length at most h has a state in the finite family. -/
theorem run_mem_profileFamily (x : Profile V) (h : ℕ) (events : List (Event V))
    (hlen : events.length ≤ h) :
    ∃ a : V → Fin (h + 1), profileFamily x h a = run events x := by
  apply mem_profileFamily_of_bounds
  intro v
  have hb := run_coordinate_bounds events x v
  constructor
  · exact hb.1
  · have hc : (events.length : ℤ) ≤ h := by exact_mod_cast hlen
    omega

/-- The same one-larger box includes every perturbed process needed for a tag. -/
theorem run_raised_mem_profileFamily (x : Profile V) (h : ℕ) (z : V)
    (events : List (Event V)) (hlen : events.length ≤ h) :
    ∃ a : V → Fin (h + 2), profileFamily x (h + 1) a = run events (raise x z) := by
  apply mem_profileFamily_of_bounds
  intro v
  have hb := run_coordinate_bounds events (raise x z) v
  have he := raise_coordinate_bounds x z v
  have hc : (events.length : ℤ) ≤ h := by exact_mod_cast hlen
  constructor <;> omega

end GraphicalAllocation.Process
