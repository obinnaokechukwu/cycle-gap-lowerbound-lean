import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-!
# A separated permutation from a half-volume bound

The forbidden relation is kept explicit, so vertices in different graph
components are never accidentally assigned graph distance zero. In the graph
specialization the forbidden ball is `G.edist x y ≤ r`, using the canonical
extended graph distance.
-/

namespace GraphicalAllocation.Geometry

open scoped Finset

/-- The half-volume Hall argument, including empty sets and odd cardinalities. -/
theorem exists_permutation_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (bad : V → Finset V) (hsymm : ∀ x y, y ∈ bad x ↔ x ∈ bad y)
    (hhalf : ∀ x, 2 * (bad x).card ≤ Fintype.card V) :
    ∃ ψ : Equiv.Perm V, ∀ x, ψ x ∉ bad x := by
  classical
  let good : V → Finset V := fun x => Finset.univ \ bad x
  have hgood (x : V) : (good x).card + (bad x).card = Fintype.card V := by
    simpa [good] using Finset.card_sdiff_add_card_eq_card
      (show bad x ⊆ Finset.univ from Finset.subset_univ _)
  have hall (S : Finset V) : S.card ≤ (S.biUnion good).card := by
    by_cases hS : S.Nonempty
    · by_cases hsmall : 2 * S.card ≤ Fintype.card V
      · obtain ⟨x, hx⟩ := hS
        have hinc : good x ⊆ S.biUnion good := fun y hy =>
          Finset.mem_biUnion.mpr ⟨x, hx, hy⟩
        have := Finset.card_le_card hinc
        have := hgood x
        have := hhalf x
        omega
      · have halluniv : S.biUnion good = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro y
          by_contra hy
          have hsub : S ⊆ bad y := by
            intro x hx
            apply (hsymm x y).mp
            by_contra hxy
            apply hy
            exact Finset.mem_biUnion.mpr ⟨x, hx, by simp [good, hxy]⟩
          have := Finset.card_le_card hsub
          have := hhalf y
          omega
        rw [halluniv, Finset.card_univ]
        exact Finset.card_le_univ _
    · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [this]
  obtain ⟨f, hinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' good).mp hall
  refine ⟨Equiv.ofBijective f ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩, ?_⟩
  intro x
  change f x ∉ bad x
  simpa [good] using hf x

/-- A graph ball with a finite radius uses extended graph distance. In
particular disconnected vertices do not belong to one another's balls. -/
noncomputable def graphBall {V : Type*} [Fintype V] (G : SimpleGraph V)
    (x : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => G.edist x y ≤ r)

@[simp] theorem mem_graphBall {V : Type*} [Fintype V] (G : SimpleGraph V)
    (x y : V) (r : ℕ) : y ∈ graphBall G x r ↔ G.edist x y ≤ r := by
  classical
  simp [graphBall]

/-- The repaired version of equation (7.5). Its conclusion remains meaningful
when the underlying graph is disconnected. -/
theorem exists_graph_separated_permutation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ)
    (hhalf : ∀ x, 2 * (graphBall G x r).card ≤ Fintype.card V) :
    ∃ ψ : Equiv.Perm V, ∀ x, (r : ℕ∞) < G.edist x (ψ x) := by
  obtain ⟨ψ, hψ⟩ := exists_permutation_avoiding (graphBall G · r)
    (fun x y => by simp [G.edist_comm]) hhalf
  exact ⟨ψ, fun x => lt_of_not_ge (by simpa using hψ x)⟩

end GraphicalAllocation.Geometry
