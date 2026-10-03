import GraphicalAllocation.Universal.Window
import GraphicalAllocation.Process.LawExpectation

/-!
# Arbitrary adapted endpoint strategies

The memory state is unrestricted: it can contain the whole realized history,
the initial profile, a clock schedule, and any previously sampled random seed.
At each step an independent uniform edge arrives, followed by an arbitrary
state-dependent Bernoulli endpoint choice. The concrete history construction
below imposes no locality, monotonicity, or time-homogeneity on that choice.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Universal

open scoped BigOperators
open Process Rules Transport Geometry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An endpoint strategy with arbitrary internal memory. Its only restrictions
are valid choice probabilities and the actual one-ball endpoint update. -/
structure EndpointStrategy (State : Type*) where
  load : State → Profile V
  probability : State → G.edgeSet → ℝ
  probability_nonneg : ∀ x e, 0 ≤ probability x e
  probability_le_one : ∀ x e, probability x e ≤ 1
  next : State → G.edgeSet × Bool → State
  next_load : ∀ x e b, load (next x (e, b)) = raise (load x)
    (if b then (canonicalOrientation G).tail e else (canonicalOrientation G).head e)

namespace EndpointStrategy

variable {G} {State : Type*} (S : EndpointStrategy G State) [Nonempty G.edgeSet]

/-- Uniform edge sampling followed by the strategy's conditional endpoint choice. -/
def kernel : FiniteKernel State (G.edgeSet × Bool) where
  weight x c := (if c.2 then S.probability x c.1 else 1 - S.probability x c.1) /
    Fintype.card G.edgeSet
  nonneg x c := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    split_ifs
    · exact S.probability_nonneg x c.1
    · exact sub_nonneg.mpr (S.probability_le_one x c.1)
  total x := by
    rw [Fintype.sum_prod_type]
    have he (e : G.edgeSet) :
        (∑ b : Bool, (if b then S.probability x e else 1 - S.probability x e) /
          Fintype.card G.edgeSet) = 1 / (Fintype.card G.edgeSet : ℝ) := by
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      ring
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero (α := G.edgeSet))
  next := S.next

/-- Summing the endpoint coin leaves exactly the uniform edge marginal. -/
theorem kernel_edge_marginal (x : State) (e : G.edgeSet) :
    ∑ b : Bool, S.kernel.weight x (e, b) = 1 / (Fintype.card G.edgeSet : ℝ) := by
  simp only [kernel, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  ring

end EndpointStrategy

/-- Forget endpoint coin outcomes, retaining the whole edge-arrival window. -/
def edgeProjection {E : Type*} : (h : ℕ) → ChoicePath (E × Bool) h → ChoicePath E h
  | 0, _ => PUnit.unit
  | h + 1, p => (p.1.1, edgeProjection h p.2)

namespace EndpointStrategy

variable {G} {State : Type*} (S : EndpointStrategy G State) [Nonempty G.edgeSet]

/-- Edge arrivals retain their iid product law even when every endpoint choice
uses all the available memory and earlier randomization. -/
theorem path_edge_marginal (h : ℕ) (x : State) (f : ChoicePath G.edgeSet h → ℝ) :
    mean (S.kernel.pathWeight h x) (fun p => f (edgeProjection h p)) =
      mean (edgePathWeight h) f := by
  induction h generalizing x with
  | zero =>
    change (∑ _p : PUnit, 1 * f PUnit.unit) = ∑ p : PUnit, 1 * f p
    simp
  | succ h ih =>
    change G.edgeSet × ChoicePath G.edgeSet h → ℝ at f
    change (∑ p : (G.edgeSet × Bool) × ChoicePath (G.edgeSet × Bool) h,
      (S.kernel.weight x p.1 * S.kernel.pathWeight h (S.kernel.next x p.1) p.2) *
        f (p.1.1, edgeProjection h p.2)) = _
    rw [Fintype.sum_prod_type, edge_mean_succ]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    change (∑ c : G.edgeSet × Bool, S.kernel.weight x c *
      mean (S.kernel.pathWeight h (S.kernel.next x c)) (fun p => f (c.1, edgeProjection h p))) = _
    have he (c : G.edgeSet × Bool) :
        mean (S.kernel.pathWeight h (S.kernel.next x c)) (fun p => f (c.1, edgeProjection h p)) =
          mean (edgePathWeight h) (fun p => f (c.1, p)) :=
      ih (S.kernel.next x c) (fun p => f (c.1, p))
    simp_rw [he]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only
    rw [← Finset.sum_mul, S.kernel_edge_marginal]

/-- Every realized strategy path is a legal endpoint allocation of its edges. -/
theorem path_follows (h : ℕ) (x : State) (p : ChoicePath (G.edgeSet × Bool) h) :
    FollowsEdges G h (S.load x) (edgeProjection h p)
      (S.load (S.kernel.pathTerminal h x p)) := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    let v := if p.1.2 then (canonicalOrientation G).tail p.1.1 else (canonicalOrientation G).head p.1.1
    refine ⟨v, ?_, ?_⟩
    · apply (canonical_incidence G p.1.1 v).mp
      dsimp [v]
      split_ifs <;> simp
    · have ht := ih (S.kernel.next x p.1) p.2
      simpa only [kernel, S.next_load, FiniteKernel.pathTerminal, edgeProjection, v] using ht

variable [Nonempty V]

/-- One window's uniform lower bound for any memory state. -/
theorem window_iterate (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (x : State) :
    1 / 2 ≤ S.kernel.iterate (logWindow (Fintype.card V))
      (fun y => if Real.log (Fintype.card V) / 64 ≤ gap (S.load y) then 1 else 0) x := by
  let h := logWindow (Fintype.card V)
  have hwin := universal_window G Δ hΔ hN hsize (S.load x)
  rw [S.kernel.iterate_eq_pathSum]
  change 1 / 2 ≤ mean (S.kernel.pathWeight h x) _
  apply hwin.trans
  unfold mass
  change mean (edgePathWeight h) _ ≤ _
  rw [← S.path_edge_marginal h x]
  apply mean_mono (S.kernel.pathWeight_nonneg h x)
  intro p
  split_ifs with hg ht ht
  · exact le_rfl
  · exact (ht (hg _ (S.path_follows h x p))).elim
  · norm_num
  · exact le_rfl

/-- The last-window argument works at every event count at least `h_N`. -/
theorem iterate_lower_bound (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (k : ℕ) (hk : logWindow (Fintype.card V) ≤ k) (x : State) :
    1 / 2 ≤ S.kernel.iterate k
      (fun y => if Real.log (Fintype.card V) / 64 ≤ gap (S.load y) then 1 else 0) x := by
  have heq : k = (k - logWindow (Fintype.card V)) + logWindow (Fintype.card V) := by omega
  rw [heq, S.kernel.iterate_add_time]
  simpa only [S.kernel.iterate_const] using
    S.kernel.iterate_mono (k - logWindow (Fintype.card V))
      (S.window_iterate Δ hΔ hN hsize) x

end EndpointStrategy

/-- Complete observed history in reverse chronological order. -/
structure HistoryState where
  initial : Profile V
  past : List (G.edgeSet × Bool)

/-- Reconstruct the actual current profile from the complete placement history. -/
def historyLoad (x : Profile V) : List (G.edgeSet × Bool) → Profile V
  | [] => x
  | c :: cs => raise (historyLoad x cs)
      (if c.2 then (canonicalOrientation G).tail c.1 else (canonicalOrientation G).head c.1)

/-- An arbitrary conditional endpoint probability can inspect the initial
profile and the entire observed edge/choice history. -/
def historyStrategy (p : HistoryState G → G.edgeSet → ℝ)
    (hp0 : ∀ x e, 0 ≤ p x e) (hp1 : ∀ x e, p x e ≤ 1) :
    EndpointStrategy G (HistoryState G) where
  load x := historyLoad G x.initial x.past
  probability := p
  probability_nonneg := hp0
  probability_le_one := hp1
  next x c := ⟨x.initial, c :: x.past⟩
  next_load _ _ _ := rfl

end GraphicalAllocation.Universal
