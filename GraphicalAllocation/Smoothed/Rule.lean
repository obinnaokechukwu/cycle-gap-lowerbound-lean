import GraphicalAllocation.Process.Allocation
import GraphicalAllocation.Geometry.Oriented
import Mathlib.Tactic

/-!
# The actual smoothed threshold allocation rule

This module defines the paper's clipped affine endpoint probabilities, proves
monotonicity and orientation symmetry, and constructs an `AllocationRule` on
an arbitrary orientation. The drift and stochastic estimates are separate.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed

open GraphicalAllocation.Process GraphicalAllocation.Rules

/-- Clipping to the probability interval. -/
def unitClip (x : ℝ) : ℝ := min 1 (max 0 x)

lemma unitClip_nonneg (x : ℝ) : 0 ≤ unitClip x :=
  le_min zero_le_one (le_max_left _ _)

lemma unitClip_le_one (x : ℝ) : unitClip x ≤ 1 := min_le_left _ _

lemma unitClip_mono : Monotone unitClip := fun _ _ h =>
  min_le_min le_rfl (max_le_max le_rfl h)

lemma unitClip_of_mem {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : unitClip x = x := by
  simp [unitClip, max_eq_right h₀, min_eq_right h₁]

lemma unitClip_complement (x : ℝ) : unitClip (1 - x) = 1 - unitClip x := by
  unfold unitClip
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The same clipped affine probability on every edge. -/
def probability (θ z : ℝ) : ℝ := unitClip (1 / 2 - z / (2 * θ))

lemma probability_nonneg (θ z : ℝ) : 0 ≤ probability θ z := unitClip_nonneg _

lemma probability_le_one (θ z : ℝ) : probability θ z ≤ 1 := unitClip_le_one _

lemma probability_antitone {θ : ℝ} (hθ : 0 < θ) : Antitone (probability θ) := by
  intro a b hab
  apply unitClip_mono
  have hden : 0 ≤ 2 * θ := by positivity
  exact sub_le_sub_left (div_le_div_of_nonneg_right hab hden) _

/-- Reversing an edge only exchanges its two complementary probabilities. -/
lemma probability_neg (θ z : ℝ) : probability θ (-z) = 1 - probability θ z := by
  unfold probability
  rw [show 1 / 2 - -z / (2 * θ) = 1 - (1 / 2 - z / (2 * θ)) by ring]
  exact unitClip_complement _

/-- No clipping occurs within the cutoff. -/
lemma probability_linear {θ z : ℝ} (hθ : 0 < θ) (hz : |z| ≤ θ) :
    probability θ z = 1 / 2 - z / (2 * θ) := by
  apply unitClip_of_mem
  · have h' : z / (2 * θ) ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ (by positivity : 0 < 2 * θ)).mpr (by linarith [(abs_le.mp hz).2])
    linarith
  · have h' : (-1 / 2 : ℝ) ≤ z / (2 * θ) :=
      (le_div_iff₀ (by positivity : 0 < 2 * θ)).mpr (by linarith [(abs_le.mp hz).1])
    linarith

/-- A uniform unit mark can equivalently be compared with an affine threshold. -/
lemma mark_le_probability_iff {θ z u : ℝ} (hθ : 0 < θ)
    (hu₀ : 0 < u) (hu₁ : u < 1) :
    u ≤ probability θ z ↔ z ≤ θ - 2 * θ * u := by
  have hc : u ≤ unitClip (1 / 2 - z / (2 * θ)) ↔
      u ≤ 1 / 2 - z / (2 * θ) := by
    simp only [unitClip, le_min_iff, le_max_iff]
    constructor
    · intro h
      rcases h.2 with h | h
      · linarith
      · exact h
    · intro h
      exact ⟨hu₁.le, Or.inr h⟩
  rw [probability, hc]
  have hden : 0 < 2 * θ := by positivity
  constructor
  · intro h
    have hd : z / (2 * θ) ≤ 1 / 2 - u := by linarith
    have := (div_le_iff₀ hden).mp hd
    nlinarith
  · intro h
    have hd : z / (2 * θ) ≤ 1 / 2 - u := (div_le_iff₀ hden).mpr (by nlinarith)
    linarith

/-- Smoothed allocation on a supplied genuine oriented graph. -/
def rule {V E : Type*} (G : OrientedGraph V E) (θ : ℝ) (hθ : 0 < θ) :
    AllocationRule V E where
  toOrientedGraph := G
  probability _ z := probability θ (z : ℝ)
  probability_nonneg _ z := probability_nonneg θ _
  probability_le_one _ z := probability_le_one θ _
  probability_antitone _ := fun _ _ h => probability_antitone hθ (by exact_mod_cast h)

@[simp] lemma rule_orientation {V E : Type*} (G : OrientedGraph V E) {θ : ℝ}
    (hθ : 0 < θ) : (rule G θ hθ).toOrientedGraph = G := rfl

/-- Canonical graph version used by the spectral theorem. -/
def graphRule {V : Type*} (G : SimpleGraph V) (θ : ℝ) (hθ : 0 < θ) :
    AllocationRule V G.edgeSet := rule (Geometry.canonicalOrientation G) θ hθ

end GraphicalAllocation.Smoothed
