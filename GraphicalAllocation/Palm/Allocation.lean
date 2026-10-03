import GraphicalAllocation.Palm.MarkedSpace
import GraphicalAllocation.Rules.Coupling
import GraphicalAllocation.Process.Allocation

/-! # Endpoint rules instantiate the Palm cell construction -/

noncomputable section
namespace GraphicalAllocation.Palm
open GraphicalAllocation.Rules

variable {E V : Type*} [DecidableEq V]

/-- The selected endpoint of an actual marked allocation at a profile. -/
def allocationSelector (left right : E → V) (p : E → ℤ → ℝ)
    (x : Profile V) (a : E × ℝ) : V :=
  selected (left a.1) (right a.1)
    (thresholdSelector (left a.1) (right a.1) (p a.1) a.2) x

omit [DecidableEq V] in
lemma allocationSelector_eq (left right : E → V) (p : E → ℤ → ℝ)
    (x : Profile V) :
    allocationSelector left right p x =
      thresholdMarkSelector left right (fun e => p e (x (left e) - x (right e))) := by
  funext a
  simp [allocationSelector, thresholdMarkSelector, selected, thresholdSelector]

lemma allocationSelector_changesOnlyFrom (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (p : E → ℤ → ℝ)
    (hp : ∀ e, Antitone (p e)) (x : Profile V) (j : V) :
    ChangesOnlyFrom (allocationSelector left right p x)
      (allocationSelector left right p (raise x j)) j := by
  intro a ha
  exact selected_unchanged_of_other (threshold_switchAway (hne a.1) (hp a.1) a.2) x j ha

omit [DecidableEq V] in
lemma allocationSelector_endpoint (left right : E → V) (p : E → ℤ → ℝ)
    (x : Profile V) (a : E × ℝ) :
    allocationSelector left right p x a = left a.1 ∨
      allocationSelector left right p x a = right a.1 := by
  simp only [allocationSelector, selected]
  split <;> simp

/-- The new-cell partition is unchanged outside the closed endpoint neighborhood
of the base allocation vertex. `S` may be that neighborhood or any larger set. -/
lemma allocationSelector_unchanged_outside (left right : E → V)
    (hne : ∀ e, left e ≠ right e) (p : E → ℤ → ℝ)
    (hp : ∀ e, Antitone (p e)) (x : Profile V) (j : V) (S : Finset V)
    (hS : ∀ e, left e = j ∨ right e = j → left e ∈ S ∧ right e ∈ S)
    (a : E × ℝ) (ha : allocationSelector left right p (raise x j) a ∉ S) :
    allocationSelector left right p x a = allocationSelector left right p (raise x j) a := by
  have hold : allocationSelector left right p x a ≠ j := by
    intro hj
    have he : left a.1 = j ∨ right a.1 = j := by
      rcases allocationSelector_endpoint left right p x a with h | h
      · exact Or.inl (h.symm.trans hj)
      · exact Or.inr (h.symm.trans hj)
    have hends := hS a.1 he
    rcases allocationSelector_endpoint left right p (raise x j) a with h | h
    · exact ha (h ▸ hends.1)
    · exact ha (h ▸ hends.2)
  exact (allocationSelector_changesOnlyFrom left right hne p hp x j a hold).symm

/-- Under an event selecting the base vertex `j`, a discrepancy at `j` reads the
new selection, and every other discrepancy remains at its old vertex. This
identifies the cell-overlap kernel with the synchronous one-ball coupling. -/
lemma event_tag_given_selection (e : Event V) (x : Profile V) (j w : V)
    (hj : selected e.first e.second e.selector x = j) :
    e.tag x w = if w = j then selected e.first e.second e.selector (raise x j) else w := by
  by_cases hw : w = j
  · subst w
    simp only [Event.tag, ite_true]
    by_cases hs : e.selector (raise x j) = e.selector x
    · rw [ite_eq_left hs]
      calc
        j = selected e.first e.second e.selector x := hj.symm
        _ = selected e.first e.second e.selector (raise x j) := by simp only [selected, hs]
    · simp [hs]
  · have hs : e.selector (raise x w) = e.selector x := by
      by_contra h
      exact hw ((e.switchAway x w h).trans hj)
    simp [Event.tag, hs, hw]

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Process.AllocationRule

open scoped BigOperators
open MeasureTheory GraphicalAllocation.Rules GraphicalAllocation.Palm

variable {E V : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]

omit [DecidableEq E] [Fintype V] in
/-- Equation (3.1), proved for the actual uniform-edge, uniform-real-mark law. -/
lemma selectionCell_measure (A : AllocationRule V E) (x : Profile V) (v : V) :
    (markedMeasure (E := E)).real {a | allocationSelector A.tail A.head A.probability x a = v} =
      A.rate x v / Fintype.card E := by
  rw [allocationSelector_eq]
  have hsel := thresholdMarkSelector_measurable A.tail A.head (A.edgeProbability x)
  have hs : MeasurableSet {a : E × ℝ |
      thresholdMarkSelector A.tail A.head (A.edgeProbability x) a = v} :=
    hsel (measurableSet_singleton v)
  change (markedMeasure (E := E)).real {a |
    thresholdMarkSelector A.tail A.head (A.edgeProbability x) a = v} = _
  rw [markedMeasure_real_set _ hs, rate, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  change unitMarkMeasure.real {u : ℝ |
    (if u ≤ A.edgeProbability x e then A.tail e else A.head e) = v} = A.edgeRate x e v
  exact unitMarkMeasure_selection (A.tail e) (A.head e) v (A.edgeProbability x e)
    (A.edgeProbability_nonneg x e) (A.edgeProbability_le_one x e)

omit [DecidableEq E] in
/-- The pushforward distribution of the actual selected marked endpoint is
exactly the allocation kernel specified by the model. -/
lemma selectionCell_eq_kernel (A : AllocationRule V E) (x : Profile V) (v : V) :
    (markedMeasure (E := E)).real {a | allocationSelector A.tail A.head A.probability x a = v} =
      A.kernel.weight x v :=
  A.selectionCell_measure x v

omit [DecidableEq E] in
/-- Exact finite mark probabilities simultaneously for any finite family of
profiles, in particular every profile reachable during a fixed finite horizon. -/
lemma finiteSignature_kernel_weight {I : Type*} [Fintype I] [DecidableEq I]
    (A : AllocationRule V E) (x : I → Profile V) (i : I) (v : V) :
    cellMass
      (atomWeight markedMeasure (pathSignature A.tail A.head (fun k => A.edgeProbability (x k))))
      (fun s : E × (I → V) => s.2 i) v = A.kernel.weight (x i) v := by
  rw [cellMass_atomWeight markedMeasure (pathSignature_measurable _ _ _)]
  change (markedMeasure (E := E)).real {a |
    thresholdMarkSelector A.tail A.head (A.edgeProbability (x i)) a = v} = _
  change (markedMeasure (E := E)).real {a |
    thresholdMarkSelector A.tail A.head (fun e => A.probability e
      ((x i) (A.tail e) - (x i) (A.head e))) a = v} = _
  rw [← allocationSelector_eq A.tail A.head A.probability (x i)]
  exact A.selectionCell_eq_kernel (x i) v

omit [DecidableEq E] in
/-- The same exact kernel law on strictly positive atoms. No zero-cell
positivity assumption is imposed on the allocation rule. -/
lemma positiveFiniteSignature_kernel_weight {I : Type*} [Fintype I] [DecidableEq I]
    (A : AllocationRule V E) (x : I → Profile V) (i : I) (v : V) :
    let μ := atomWeight markedMeasure (pathSignature A.tail A.head (fun k => A.edgeProbability (x k)))
    cellMass (positiveAtomWeight μ) (fun s : PositiveAtoms μ => s.val.2 i) v =
      A.kernel.weight (x i) v := by
  dsimp only
  exact (cellMass_positiveAtoms (atomWeight_nonneg markedMeasure
    (pathSignature A.tail A.head (fun k => A.edgeProbability (x k))))
    (fun s : E × (I → V) => s.2 i) v).trans (A.finiteSignature_kernel_weight x i v)

end GraphicalAllocation.Process.AllocationRule
