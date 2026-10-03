import GraphicalAllocation.Process.FiniteKernel
import GraphicalAllocation.Rules.Coupling

/-!
# Endpoint-local allocation model

The data below specify actual oriented edges and antitone endpoint probabilities.
The one-event kernel is derived from them; rates and total mass are proved.
-/

namespace GraphicalAllocation.Process

open scoped BigOperators
open GraphicalAllocation.Rules

/-- An orientation of a finite loopless graph. Distinct edge indices have distinct
unordered endpoints, expressing simplicity independently of any chosen vertex order. -/
structure OrientedGraph (V E : Type*) where
  tail : E → V
  head : E → V
  distinct : ∀ e, tail e ≠ head e
  unique : ∀ e e',
    (tail e = tail e' ∧ head e = head e') ∨
    (tail e = head e' ∧ head e = tail e') → e = e'

/-- Edge-specific monotone probabilities. Constant and asymmetric rules are allowed. -/
structure AllocationRule (V E : Type*) extends OrientedGraph V E where
  probability : E → ℤ → ℝ
  probability_nonneg : ∀ e d, 0 ≤ probability e d
  probability_le_one : ∀ e d, probability e d ≤ 1
  probability_antitone : ∀ e, Antitone (probability e)

namespace AllocationRule

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
variable (A : AllocationRule V E)

/-- Probability that this oriented edge selects its tail. -/
def edgeProbability (x : Profile V) (e : E) : ℝ :=
  A.probability e (x (A.tail e) - x (A.head e))

/-- An edge's contribution to the arrival rate at one vertex. -/
def edgeRate (x : Profile V) (e : E) (v : V) : ℝ :=
  (if v = A.tail e then A.edgeProbability x e else 0) +
  (if v = A.head e then 1 - A.edgeProbability x e else 0)

/-- Each edge rings at rate one, so rates add over edges. -/
def rate (x : Profile V) (v : V) : ℝ := ∑ e, A.edgeRate x e v

/-- Incidence degree of a vertex. -/
def degree (v : V) : ℕ :=
  ∑ e, ((if v = A.tail e then 1 else 0) + (if v = A.head e then 1 else 0))

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem edgeProbability_nonneg (x : Profile V) (e : E) :
    0 ≤ A.edgeProbability x e := A.probability_nonneg _ _

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem edgeProbability_le_one (x : Profile V) (e : E) :
    A.edgeProbability x e ≤ 1 := A.probability_le_one _ _

omit [Fintype V] [Fintype E] in
theorem edgeRate_nonneg (x : Profile V) (e : E) (v : V) :
    0 ≤ A.edgeRate x e v := by
  unfold edgeRate
  have h₀ := A.edgeProbability_nonneg x e
  have h₁ := A.edgeProbability_le_one x e
  split_ifs <;> linarith

omit [Fintype V] in
theorem rate_nonneg (x : Profile V) (v : V) : 0 ≤ A.rate x v :=
  Finset.sum_nonneg fun e _ => A.edgeRate_nonneg x e v

omit [Fintype V] [Fintype E] in
theorem edgeRate_le_incidence (x : Profile V) (e : E) (v : V) :
    A.edgeRate x e v ≤
      (if v = A.tail e then (1 : ℝ) else 0) +
      (if v = A.head e then (1 : ℝ) else 0) := by
  unfold edgeRate
  have h₀ := A.edgeProbability_nonneg x e
  have h₁ := A.edgeProbability_le_one x e
  split_ifs <;> linarith

omit [Fintype V] in
theorem rate_le_degree (x : Profile V) (v : V) :
    A.rate x v ≤ A.degree v := by
  unfold rate degree
  push_cast
  exact Finset.sum_le_sum fun e _ => A.edgeRate_le_incidence x e v

/-- Equation (2.1): the total allocation rate equals the number of edges. -/
theorem sum_rate (x : Profile V) :
    ∑ v, A.rate x v = Fintype.card E := by
  unfold rate edgeRate
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] [Fintype E] in
@[simp] theorem edgeProbability_translate (x : Profile V) (c : ℤ) (e : E) :
    A.edgeProbability (translate x c) e = A.edgeProbability x e := by
  simp [edgeProbability, translate]

omit [Fintype V] in
@[simp] theorem rate_translate (x : Profile V) (c : ℤ) (v : V) :
    A.rate (translate x c) v = A.rate x v := by
  simp [rate, edgeRate]

/-- The actual one-allocation transition, using the next-allocation rate law. -/
noncomputable def kernel [Nonempty E] : FiniteKernel (Profile V) V where
  weight x v := A.rate x v / Fintype.card E
  nonneg x v := div_nonneg (A.rate_nonneg x v) (Nat.cast_nonneg _)
  total x := by
    rw [← Finset.sum_div, A.sum_rate]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero (α := E))
  next x v := raise x v

@[simp] theorem kernel_weight [Nonempty E] (x : Profile V) (v : V) :
    A.kernel.weight x v = A.rate x v / Fintype.card E := rfl

@[simp] theorem kernel_next [Nonempty E] (x : Profile V) (v : V) :
    A.kernel.next x v = raise x v := rfl

/-- The graph's marked threshold event, used in the pathwise discrepancy coupling. -/
noncomputable def event (e : E) (mark : ℝ) : Event V :=
  Event.ofThreshold (A.tail e) (A.head e) (A.distinct e)
    (A.probability e) (A.probability_antitone e) mark

end AllocationRule
end GraphicalAllocation.Process
