import GraphicalAllocation.Universal.Profiles
import GraphicalAllocation.Universal.Constants

/-!
# Strategy-independent logarithmic gap in the final arrival window

The conclusion is stronger than an adapted-strategy result: with probability
at least one half, every legal allocation of the entire sampled edge window has
a large gap. Thus endpoint decisions may even see the complete future window.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Universal

open scoped BigOperators
open Process Rules Transport

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]

lemma regular_incident_fraction (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ) (v : V) :
    ((incidentEdges G v).card : ℝ) / Fintype.card G.edgeSet = 2 / (Fintype.card V : ℝ) := by
  rw [card_incidentEdges, hΔ]
  have hh : (Fintype.card V : ℝ) * Δ = 2 * Fintype.card G.edgeSet := by
    exact_mod_cast regular_edge_count G Δ hΔ
  have hv : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := V)
  have he : (Fintype.card G.edgeSet : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := G.edgeSet)
  apply (div_eq_div_iff he hv).mpr
  nlinarith

lemma untouched_pair_bound (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V) {u v : V}
    (hne : u ≠ v) (hnot : ¬G.Adj u v) (h : ℕ) :
    mass (edgePathWeight (E := G.edgeSet) h)
      (fun p => Avoids (incidentEdges G u) h p ∧ Avoids (incidentEdges G v) h p) ≤
      ((1 - 2 / (Fintype.card V : ℝ)) ^ h) ^ 2 := by
  have hevent : (fun p => Avoids (incidentEdges G u) h p ∧ Avoids (incidentEdges G v) h p) =
      Avoids (incidentEdges G u ∪ incidentEdges G v) h := by
    funext p
    exact propext (avoids_union _ _ h p).symm
  rw [hevent, mass_avoids, Finset.card_union_of_disjoint (disjoint_incidentEdges G hne hnot), Nat.cast_add, add_div,
    regular_incident_fraction G Δ hΔ u, regular_incident_fraction G Δ hΔ v]
  have hN0 : (0 : ℝ) < Fintype.card V := by linarith
  have hq : 0 ≤ 1 - (2 / (Fintype.card V : ℝ) + 2 / Fintype.card V) := by
    have hdiv : 4 / (Fintype.card V : ℝ) ≤ 1 := (div_le_iff₀ hN0).mpr (by linarith)
    have heq : 2 / (Fintype.card V : ℝ) + 2 / Fintype.card V = 4 / Fintype.card V := by ring
    rw [heq]
    exact sub_nonneg.mpr hdiv
  have hb : 1 - (2 / (Fintype.card V : ℝ) + 2 / Fintype.card V) ≤
      (1 - 2 / (Fintype.card V : ℝ)) ^ 2 := by nlinarith [sq_nonneg (2 / (Fintype.card V : ℝ))]
  calc
    _ ≤ ((1 - 2 / (Fintype.card V : ℝ)) ^ 2) ^ h := pow_le_pow_left₀ hq hb h
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The universal logarithmic window event. No strategy appears in its definition. -/
def GoodWindow (x : Profile V) (h : ℕ) (a : ℝ) (p : ChoicePath G.edgeSet h) : Prop :=
  ∀ y : Profile V, FollowsEdges G h x p y → a ≤ gap y

/-- Proposition 7.8's core, uniformly over all allocations of the sampled window. -/
theorem universal_window (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (x : Profile V) :
    1 / 2 ≤ mass (edgePathWeight (E := G.edgeSet) (logWindow (Fintype.card V)))
      (GoodWindow G x (logWindow (Fintype.card V)) (Real.log (Fintype.card V) / 64)) := by
  let N := Fintype.card V
  let h := logWindow N
  let τ := windowAverage N
  have hτ : 0 < τ := windowAverage_pos N hN
  have hτlog : Real.log N / 32 ≤ τ := (windowAverage_bounds N hN).1
  have hweight : ∀ p : ChoicePath G.edgeSet h, 0 ≤ edgePathWeight h p := edgePathWeight_nonneg h
  by_cases hlow : ∃ v : V, (x v : ℝ) ≤ averageLoad x - 4 * τ
  · obtain ⟨v, hv⟩ := hlow
    have hmean : mean (edgePathWeight (E := G.edgeSet) h)
        (fun p => (hitCount (incidentEdges G v) h p : ℝ)) ≤ 2 * τ := by
      rw [mean_hitCount, regular_incident_fraction G Δ hΔ]
      dsimp [τ, windowAverage, h]
      ring_nf
      exact le_rfl
    have hp := half_mass_of_mean_le hweight (edgePathWeight_total h)
      (fun p => Nat.cast_nonneg (hitCount (incidentEdges G v) h p)) hτ hmean
    apply hp.trans
    apply mass_mono hweight
    intro p hp y hy
    have hc := followsEdges_coordinate G hy v
    have ha := followsEdges_average G hy
    have hg := average_sub_load_le_gap y v
    change averageLoad y = averageLoad x + τ at ha
    change Real.log N / 64 ≤ gap y
    linarith
  · have hbottom : ∀ v, averageLoad x - 4 * τ < (x v : ℝ) := by
      push Not at hlow
      exact hlow
    let S := Finset.univ.filter (fun v => (x v : ℝ) ≤ averageLoad x + τ / 2)
    have hS : (N : ℝ) / 9 ≤ (S.card : ℝ) := low_vertices_card x hτ hbottom
    obtain ⟨I, hIS, hind, hcard⟩ := exists_independent_subset G S Δ (fun v => (hΔ v).le)
    let Y : ChoicePath G.edgeSet h → ℝ :=
      countIndicators I (fun v => Avoids (incidentEdges G v) h)
    let q : ℝ := (1 - 2 / (N : ℝ)) ^ h
    have hfirst : ∀ v ∈ I, mass (edgePathWeight (E := G.edgeSet) h)
        (Avoids (incidentEdges G v) h) = q := by
      intro v hv
      rw [mass_avoids, regular_incident_fraction G Δ hΔ]
    have hYmean : mean (edgePathWeight (E := G.edgeSet) h) Y = (I.card : ℝ) * q :=
      mean_countIndicators _ I _ q hfirst
    have hI : (N : ℝ) ≤ 9 * ((Δ : ℝ) + 1) * I.card := by
      have hc : (S.card : ℝ) ≤ (I.card : ℝ) * ((Δ : ℝ) + 1) := by exact_mod_cast hcard
      nlinarith
    have hYone : 1 ≤ mean (edgePathWeight (E := G.edgeSet) h) Y := by
      rw [hYmean]
      exact untouched_mean_ge_one N I.card Δ hN hsize hI
    have hYsecond : mean (edgePathWeight (E := G.edgeSet) h) (fun p => Y p ^ 2) ≤
        mean (edgePathWeight h) Y + mean (edgePathWeight h) Y ^ 2 := by
      apply second_moment_countIndicators _ I _ q hfirst
      intro u hu v hv huv
      exact untouched_pair_bound G Δ hΔ hN huv (hind hu hv huv) h
    have hp := half_mass_of_second_moment hweight
      (countIndicators_nonneg I _) hYone hYsecond
    apply hp.trans
    apply mass_mono hweight
    intro p hp y hy
    have hex : ∃ v ∈ I, Avoids (incidentEdges G v) h p := by
      by_contra hn
      push Not at hn
      have hz : Y p = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        simp [hn v hv]
      linarith
    obtain ⟨v, hv, havoid⟩ := hex
    have hvload : (x v : ℝ) ≤ averageLoad x + τ / 2 := by
      have := hIS hv
      simpa [S] using this
    have hc := followsEdges_coordinate G hy v
    have ha := followsEdges_average G hy
    have hg := average_sub_load_le_gap y v
    change averageLoad y = averageLoad x + τ at ha
    change hitCount (incidentEdges G v) h p = 0 at havoid
    rw [havoid, Nat.cast_zero, add_zero] at hc
    change Real.log N / 64 ≤ gap y
    linarith

end GraphicalAllocation.Universal
