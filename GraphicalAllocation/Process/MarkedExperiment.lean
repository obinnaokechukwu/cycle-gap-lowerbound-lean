import GraphicalAllocation.Process.FiniteKernel
import GraphicalAllocation.Rules.Coupling
import GraphicalAllocation.Process.Reachability

/-!
# Finite independent mark experiments

A finite mark distribution induces separate base and tagged kernels. Their
finite-difference intertwining is proved from the deterministic one-ball identity.
The final lemma permits exact replacement by a kernel agreeing only on the
finite reachable region of a specified experiment.
-/

namespace GraphicalAllocation.Process

open scoped BigOperators
open Rules

structure FiniteMarks (V A : Type*) [DecidableEq V] [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1
  event : A → Event V

namespace FiniteMarks
variable {V A : Type*} [DecidableEq V] [Fintype A]
variable (F : FiniteMarks V A)

def base : FiniteKernel (Profile V) A where
  weight _ a := F.weight a
  nonneg _ a := F.nonneg a
  total _ := F.total
  next x a := (F.event a).apply x

def tagged : FiniteKernel (Profile V × V) A where
  weight _ a := F.weight a
  nonneg _ a := F.nonneg a
  total _ := F.total
  next x a := ((F.event a).apply x.1, (F.event a).tag x.1 x.2)

@[simp] theorem base_weight (x : Profile V) (a : A) : F.base.weight x a = F.weight a := rfl
@[simp] theorem base_next (x : Profile V) (a : A) :
    F.base.next x a = (F.event a).apply x := rfl
@[simp] theorem tagged_weight (x : Profile V × V) (a : A) :
    F.tagged.weight x a = F.weight a := rfl
@[simp] theorem tagged_next (x : Profile V × V) (a : A) :
    F.tagged.next x a = ((F.event a).apply x.1, (F.event a).tag x.1 x.2) := rfl

/-- Exact response identity for the independent finite-mark process. -/
theorem iterate_finiteDifference (h : ℕ) (f : Profile V → ℝ) (x : Profile V) (z : V) :
    F.base.iterate h f (raise x z) - F.base.iterate h f x =
      F.tagged.iterate h (fun y => finiteDifference f y.1 y.2) (x, z) := by
  induction h generalizing x z with
  | zero => rfl
  | succ h ih =>
    simp only [FiniteKernel.iterate_succ, FiniteKernel.step, base_weight, base_next,
      tagged_weight, tagged_next]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_sub, (F.event a).oneBall, ih]

/-- Selection probabilities of the actual finite marked experiment. -/
def selectionMass [Fintype V] (x : Profile V) (v : V) : ℝ :=
  ∑ a, if selected (F.event a).first (F.event a).second (F.event a).selector x = v
    then F.weight a else 0

/-- Group the genuine marked update by the selected vertex. -/
theorem base_step_eq_selectionMass [Fintype V] (f : Profile V → ℝ) (x : Profile V) :
    F.base.step f x = ∑ v, F.selectionMass x v * f (raise x v) := by
  unfold selectionMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold FiniteKernel.step
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp [base, Event.apply, update, eq_comm]

end FiniteMarks

namespace FiniteKernel
variable {State C D : Type*} [Fintype C] [Fintype D]

/-- Local one-step agreement suffices for exact finite-horizon law agreement.
`region n` contains states with n remaining steps; it need not be all states. -/
theorem iterate_eq_of_region (K : FiniteKernel State C) (Q : FiniteKernel State D)
    (region : ℕ → State → Prop)
    (hnext : ∀ n x, region (n + 1) x → ∀ a, region n (Q.next x a))
    (hstep : ∀ n x, region (n + 1) x → ∀ f, K.step f x = Q.step f x)
    (n : ℕ) (f : State → ℝ) (x : State) (hx : region n x) :
    K.iterate n f x = Q.iterate n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ, iterate_succ, hstep n x hx]
    unfold step
    apply Finset.sum_congr rfl
    intro a _
    rw [ih _ (hnext n x hx a)]

end FiniteKernel
namespace FiniteMarks
variable {V A C : Type*} [DecidableEq V] [Fintype V] [Fintype A] [Fintype C]

omit [Fintype V] in
/-- Exact agreement on a coordinatewise finite box yields equal finite-horizon
expectations at every state with enough room for the remaining increments. -/
theorem iterate_eq_on_box (F : FiniteMarks V A) (K : FiniteKernel (Profile V) C)
    (origin : Profile V) (budget : ℕ)
    (hstep : ∀ y, (∀ v, origin v ≤ y v ∧ y v ≤ origin v + budget) →
      ∀ f, K.step f y = F.base.step f y)
    (h : ℕ) (y : Profile V) (f : Profile V → ℝ)
    (hy : h ≤ budget ∧ ∀ v, origin v ≤ y v ∧ y v ≤ origin v + (budget - h)) :
    K.iterate h f y = F.base.iterate h f y := by
  let region : ℕ → Profile V → Prop := fun n z =>
    n ≤ budget ∧ ∀ v, origin v ≤ z v ∧ z v ≤ origin v + (budget - n)
  apply FiniteKernel.iterate_eq_of_region K F.base region ?_ ?_ h f y hy
  · intro n z hz a
    change n ≤ budget ∧ ∀ v, origin v ≤ (F.event a).apply z v ∧
      (F.event a).apply z v ≤ origin v + (budget - n)
    constructor
    · exact Nat.le_trans (Nat.le_succ n) hz.1
    · intro v
      have hb := hz.2 v
      have he := event_coordinate_bounds (F.event a) z v
      have hn := hz.1
      constructor <;> omega
  · intro n z hz g
    apply hstep z
    intro v
    have hb := hz.2 v
    constructor <;> omega

end FiniteMarks
end GraphicalAllocation.Process
