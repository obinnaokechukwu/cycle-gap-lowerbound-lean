import GraphicalAllocation.Process.Allocation

/-!
# Orientation is a choice of coordinates

Reversing any collection of edges and replacing p(d) by 1-p(-d) leaves every
allocation rate unchanged. Thus fixing clockwise or canonical orientations in
the public statements does not restrict the class of endpoint-local rules.
-/

namespace GraphicalAllocation.Process

namespace OrientedGraph
variable {V E : Type*} (G : OrientedGraph V E)

def reverseEdges (flip : E → Prop) [DecidablePred flip] : OrientedGraph V E where
  tail e := if flip e then G.head e else G.tail e
  head e := if flip e then G.tail e else G.head e
  distinct e := by
    by_cases he : flip e
    · simpa [he] using (G.distinct e).symm
    · simpa [he] using G.distinct e
  unique e e' h := by
    apply G.unique e e'
    by_cases he : flip e <;> by_cases he' : flip e' <;> simp only [he, he', ite_true, ite_false] at h
    all_goals rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    all_goals first | exact Or.inl ⟨h₁, h₂⟩ | exact Or.inl ⟨h₂, h₁⟩ |
      exact Or.inr ⟨h₁, h₂⟩ | exact Or.inr ⟨h₂, h₁⟩

end OrientedGraph

namespace AllocationRule
open Rules
variable {V E : Type*} (A : AllocationRule V E)

def reverseEdges (flip : E → Prop) [DecidablePred flip] : AllocationRule V E where
  toOrientedGraph := A.toOrientedGraph.reverseEdges flip
  probability e d := if flip e then 1 - A.probability e (-d) else A.probability e d
  probability_nonneg e d := by
    by_cases he : flip e
    · simpa only [he, ite_true] using sub_nonneg.mpr (A.probability_le_one e (-d))
    · simpa only [he, ite_false] using A.probability_nonneg e d
  probability_le_one e d := by
    by_cases he : flip e
    · simp only [he, ite_true]
      linarith [A.probability_nonneg e (-d)]
    · simpa only [he, ite_false] using A.probability_le_one e d
  probability_antitone e := by
    intro a b hab
    by_cases he : flip e
    · simp only [he, ite_true]
      exact sub_le_sub_left (A.probability_antitone e (neg_le_neg hab)) 1
    · simpa only [he, ite_false] using A.probability_antitone e hab

variable [Fintype V] [DecidableEq V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem reverseEdges_edgeRate (flip : E → Prop) [DecidablePred flip]
    (x : Profile V) (e : E) (v : V) :
    (A.reverseEdges flip).edgeRate x e v = A.edgeRate x e v := by
  by_cases he : flip e
  · unfold edgeRate edgeProbability reverseEdges OrientedGraph.reverseEdges
    simp only [he, ite_true, neg_sub]
    split_ifs <;> ring
  · simp [edgeRate, edgeProbability, reverseEdges, OrientedGraph.reverseEdges, he]

omit [Fintype V] in
/-- Every vertex sees exactly the same genuine allocation rate. -/
theorem reverseEdges_rate (flip : E → Prop) [DecidablePred flip] (x : Profile V) (v : V) :
    (A.reverseEdges flip).rate x v = A.rate x v := by
  unfold rate
  apply Finset.sum_congr rfl
  intro e _
  exact A.reverseEdges_edgeRate flip x e v

/-- Therefore orientation changes leave the actual one-step probabilities fixed. -/
theorem reverseEdges_kernel_weight [Nonempty E] (flip : E → Prop) [DecidablePred flip]
    (x : Profile V) (v : V) :
    (A.reverseEdges flip).kernel.weight x v = A.kernel.weight x v := by
  simp [kernel_weight, A.reverseEdges_rate]

end AllocationRule
end GraphicalAllocation.Process
