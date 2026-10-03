import GraphicalAllocation.Smoothed.Rule
import GraphicalAllocation.Spectral.Laplacian
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Exact linear drift of the actual allocation probabilities -/

noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators
open Process Rules Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {θ : ℝ} (hθ : 0 < θ)

/-- The linear region is specified by actual graph edges. -/
def WithinCutoff (x : Profile V) : Prop :=
  ∀ u v, G.Adj u v → |(x u : ℝ) - x v| ≤ θ

omit [Fintype V] [DecidableRel G.Adj] in
lemma graph_edgeRate_neighbor (x : Profile V) (v w : V) (hvw : G.Adj v w) :
    (graphRule G θ hθ).edgeRate x ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩ v =
      probability θ ((x v : ℝ) - x w) := by
  let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
  have hout : s(e.val.out.1, e.val.out.2) = s(v, w) := Quot.out_eq _
  rcases Sym2.eq_iff.mp hout with h | h
  · rcases h with ⟨hv, hw⟩
    change (graphRule G θ hθ).edgeRate x e v = _
    simp [AllocationRule.edgeRate, AllocationRule.edgeProbability, graphRule, rule,
      Geometry.canonicalOrientation, hv, hw, hvw.ne, Int.cast_sub]
  · rcases h with ⟨hw, hv⟩
    change (graphRule G θ hθ).edgeRate x e v = _
    simp only [AllocationRule.edgeRate, AllocationRule.edgeProbability, graphRule, rule,
      Geometry.canonicalOrientation, hw, hv, hvw.ne, ite_false, ite_true, zero_add, Int.cast_sub]
    rw [show (x w : ℝ) - x v = -((x v : ℝ) - x w) by ring, probability_neg]
    ring

lemma graph_rate_eq_neighbor_sum (x : Profile V) (v : V) :
    (graphRule G θ hθ).rate x v =
      ∑ w ∈ G.neighborFinset v, probability θ ((x v : ℝ) - x w) := by
  classical
  let A := graphRule G θ hθ
  let inc : G.edgeSet → Prop := fun e => v ∈ (e : Sym2 V)
  let e : {edge : G.edgeSet // inc edge} ≃ G.neighborSet v :=
    (Geometry.incidentEdgeEquiv G v).trans (G.incidenceSetEquivNeighborSet v)
  have hzero (edge : G.edgeSet) (hn : ¬ inc edge) : A.edgeRate x edge v = 0 := by
    have hmem := Geometry.canonical_incidence G edge v
    have hne : v ≠ A.tail edge ∧ v ≠ A.head edge := by
      simpa only [A, graphRule, rule, not_or] using mt hmem.mp hn
    simp [AllocationRule.edgeRate, hne.1, hne.2]
  calc
    A.rate x v = ∑ edge : G.edgeSet, if inc edge then A.edgeRate x edge v else 0 := by
      unfold AllocationRule.rate
      apply Finset.sum_congr rfl
      intro edge _
      by_cases h : inc edge <;> simp [h, hzero edge]
    _ = ∑ edge : {edge : G.edgeSet // inc edge}, A.edgeRate x edge.val v := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ w : G.neighborSet v, A.edgeRate x (e.symm w).val v := (e.symm.sum_comp _).symm
    _ = ∑ w : G.neighborSet v, probability θ ((x v : ℝ) - x w.val) := by
      apply Finset.sum_congr rfl
      intro w _
      exact graph_edgeRate_neighbor G hθ x v w w.property
    _ = _ := (Finset.sum_subtype (p := fun w => w ∈ G.neighborSet v)
      (G.neighborFinset v) (by intro w; simp) (fun w => probability θ ((x v : ℝ) - x w))).symm

lemma graph_rate_linear (x : Profile V) (hx : WithinCutoff G (θ := θ) x) (v : V) :
    (graphRule G θ hθ).rate x v = (G.degree v : ℝ) / 2 -
      Spectral.laplacian G (fun w => (x w : ℝ)) v / (2 * θ) := by
  rw [graph_rate_eq_neighbor_sum]
  have hprob (w : V) (hw : w ∈ G.neighborFinset v) :
      probability θ ((x v : ℝ) - x w) = 1 / 2 - ((x v : ℝ) - x w) / (2 * θ) :=
    probability_linear hθ (hx v w ((G.mem_neighborFinset v w).mp hw))
  rw [Finset.sum_congr rfl hprob]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [Spectral.laplacian_apply, G.lapMatrix_mulVec_apply']
  simp only [Finset.sum_sub_distrib, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  ring

omit [DecidableEq V] in
lemma graph_regular_degree_sum {d : ℕ} (hd : G.IsRegularOfDegree d) :
    (Fintype.card V : ℝ) * d = 2 * Fintype.card G.edgeSet := by
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [hd.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [← Geometry.canonical_edge_count] at h
  exact_mod_cast h

lemma graph_choice_linear [Nonempty V] [Nonempty G.edgeSet] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (x : Profile V) (hx : WithinCutoff G (θ := θ) x) (v : V) :
    (graphRule G θ hθ).kernel.weight x v =
      1 / Fintype.card V -
        (1 / (2 * Fintype.card G.edgeSet * θ)) * Spectral.laplacian G (fun w => (x w : ℝ)) v := by
  rw [AllocationRule.kernel_weight, graph_rate_linear G hθ x hx, hd.degree_eq]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card G.edgeSet : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht : θ ≠ 0 := ne_of_gt hθ
  have hdeg := graph_regular_degree_sum G hd
  field_simp
  nlinarith

lemma graph_choice_le [Nonempty V] [Nonempty G.edgeSet] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (x : Profile V) (v : V) :
    (graphRule G θ hθ).kernel.weight x v ≤ 2 / Fintype.card V := by
  have hdeg := Geometry.allocation_degree_eq_graph_degree G (graphRule G θ hθ) rfl v
  have hr := (graphRule G θ hθ).rate_le_degree x v
  rw [hdeg, hd.degree_eq] at hr
  rw [AllocationRule.kernel_weight]
  have hm : (0 : ℝ) < Fintype.card G.edgeSet := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hm).mpr
  have hsum := graph_regular_degree_sum G hd
  have heq : (d : ℝ) = 2 / Fintype.card V * Fintype.card G.edgeSet := by
    apply (mul_left_cancel₀ hn.ne')
    field_simp
    nlinarith
  exact hr.trans_eq heq

end GraphicalAllocation.Smoothed
