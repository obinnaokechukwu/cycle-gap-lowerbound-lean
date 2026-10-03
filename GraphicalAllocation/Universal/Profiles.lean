import GraphicalAllocation.Universal.Graph
import GraphicalAllocation.Universal.EdgePaths
import GraphicalAllocation.Transport.Clipped

/-!
# Pathwise load constraints in an arbitrary edge window

`FollowsEdges` permits every placement at an endpoint of the corresponding edge.
It places no adaptedness condition on the choices: each can depend on the entire
window. The universal event proved later therefore works for all such choices.
-/

noncomputable section
namespace GraphicalAllocation.Universal

open scoped BigOperators
open Process Rules Transport

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Average integer load, represented as a real number. -/
def averageLoad (x : Profile V) : ℝ := (∑ v, (x v : ℝ)) / Fintype.card V

omit [DecidableEq V] in
/-- Every coordinate is at most one gap below the average. -/
theorem average_sub_load_le_gap (x : Profile V) (v : V) :
    averageLoad x - x v ≤ gap x := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ => difference_le_gap x u v)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  unfold averageLoad
  rw [sub_le_iff_le_add, div_le_iff₀ hcard]
  nlinarith

omit [Nonempty V] in
@[simp] theorem sum_raise_real (x : Profile V) (v : V) :
    (∑ u, ((raise x v) u : ℝ)) = (∑ u, (x u : ℝ)) + 1 := by
  simp [raise, Finset.sum_add_distrib]

/-- Either there is a deeply underloaded vertex, or at least a ninth of the
vertices have load at most average plus half a window's average increment. -/
theorem low_vertices_card (x : Profile V) {τ : ℝ} (hτ : 0 < τ)
    (hbottom : ∀ v, averageLoad x - 4 * τ < (x v : ℝ)) :
    (Fintype.card V : ℝ) / 9 ≤
      ((Finset.univ.filter (fun v => (x v : ℝ) ≤ averageLoad x + τ / 2)).card : ℝ) := by
  classical
  let S := Finset.univ.filter (fun v => (x v : ℝ) ≤ averageLoad x + τ / 2)
  have hs : ∑ v, (if v ∈ S then averageLoad x - 4 * τ else averageLoad x + τ / 2) ≤
      ∑ v, (x v : ℝ) := by
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hv
    · exact (hbottom v).le
    · exact (lt_of_not_ge (by simpa [S] using hv)).le
  have he : (∑ v, (if v ∈ S then averageLoad x - 4 * τ else averageLoad x + τ / 2)) =
      (S.card : ℝ) * (averageLoad x - 4 * τ) +
        ((Fintype.card V : ℝ) - S.card) * (averageLoad x + τ / 2) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hS : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
    have hSc : Finset.univ.filter (fun v => ¬v ∈ S) = Finset.univ \ S := by ext v; simp
    rw [hS, hSc, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Nat.cast_sub (Finset.card_le_univ S)]
  have hsum : (∑ v, (x v : ℝ)) = (Fintype.card V : ℝ) * averageLoad x := by
    unfold averageLoad
    have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := V)
    field_simp
  rw [he, hsum] at hs
  change (Fintype.card V : ℝ) / 9 ≤ (S.card : ℝ)
  nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All legal endpoint placements along a specified edge sequence, without any
restriction on how or when the endpoint choices are made. -/
def FollowsEdges : (h : ℕ) → Profile V → ChoicePath G.edgeSet h → Profile V → Prop
  | 0, x, _, y => y = x
  | h + 1, x, p, y => ∃ v : V, v ∈ (p.1 : Sym2 V) ∧ FollowsEdges h (raise x v) p.2 y

omit [DecidableRel G.Adj] [Nonempty V] in
/-- Every legal window contains exactly `h` placements. -/
theorem followsEdges_sum {h : ℕ} {x y : Profile V} {p : ChoicePath G.edgeSet h}
    (hpath : FollowsEdges G h x p y) :
    (∑ v, (y v : ℝ)) = (∑ v, (x v : ℝ)) + h := by
  induction h generalizing x with
  | zero => simp only [FollowsEdges] at hpath; subst y; simp
  | succ h ih =>
    obtain ⟨v, hv, ht⟩ := hpath
    rw [ih ht, sum_raise_real]
    push_cast
    ring

omit [Nonempty V] in
/-- A vertex receives no more balls than the number of incident arrivals. -/
theorem followsEdges_coordinate {h : ℕ} {x y : Profile V} {p : ChoicePath G.edgeSet h}
    (hpath : FollowsEdges G h x p y) (v : V) :
    (y v : ℝ) ≤ x v + hitCount (incidentEdges G v) h p := by
  induction h generalizing x with
  | zero => simp only [FollowsEdges] at hpath; subst y; simp [hitCount]
  | succ h ih =>
    obtain ⟨u, hu, ht⟩ := hpath
    have hb := ih ht
    have hinc : (if v = u then (1 : ℝ) else 0) ≤
        (if p.1 ∈ incidentEdges G v then 1 else 0) := by
      by_cases hvu : v = u
      · subst v
        simp [hu]
      · simp [hvu]
        split_ifs <;> norm_num
    simp only [hitCount, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp only [raise, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero] at hb
    linarith

omit [DecidableRel G.Adj] [Nonempty V] in
/-- The average grows deterministically, regardless of the endpoint choices. -/
theorem followsEdges_average {h : ℕ} {x y : Profile V} {p : ChoicePath G.edgeSet h}
    (hpath : FollowsEdges G h x p y) :
    averageLoad y = averageLoad x + h / (Fintype.card V : ℝ) := by
  simp only [averageLoad, followsEdges_sum G hpath, add_div]

end GraphicalAllocation.Universal
