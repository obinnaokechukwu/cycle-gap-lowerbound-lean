import GraphicalAllocation.Smoothed.Stopped
import GraphicalAllocation.Probability.FiniteConcentration

/-!
# Actual stopped-noise concentration from the Green energy budget

Reconstruction stages: (0) bounded centered noise implies a terminal tail bound;
(1) use the normalized finite path law of `stoppedKernel`; (2) rewards are the
actual stopped innovations paired with reversed smoothing powers; (3) telescope
the associated time-dependent potential; (4) prove the weighted mean, variance,
uniform bound and Green-energy budget; (5) reverse the finite time sum and use
the graph's degree-sum identity. No variance budget is postulated for a process.
-/
noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators
open Process Rules Matrix Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Nonempty V] [Nonempty G.edgeSet]
variable {θ : ℝ} (hθ : 0 < θ)

omit [Nonempty V] in
lemma dot_choiceNoise (x : Profile V) (c : V) (g : V → ℝ) :
    g ⬝ᵥ choiceNoise G hθ x c = g c - ∑ v, (graphRule G θ hθ).kernel.weight x v * g v := by
  rw [choiceNoise, dotProduct_sub, dotProduct_single]
  simp only [mul_one, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  ring

omit [Nonempty V] in
lemma noise_mean (x : Profile V) (g : V → ℝ) :
    (∑ c, (graphRule G θ hθ).kernel.weight x c * (g ⬝ᵥ choiceNoise G hθ x c)) = 0 := by
  simp_rw [dot_choiceNoise, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (graphRule G θ hθ).kernel.total]
  ring

omit [Nonempty V] in
lemma noise_abs_le (x : Profile V) (g : V → ℝ) {B : ℝ}
    (hg : ∀ v, |g v| ≤ B) (c : V) : |g ⬝ᵥ choiceNoise G hθ x c| ≤ 2 * B := by
  rw [dot_choiceNoise]
  have hmean : |∑ v, (graphRule G θ hθ).kernel.weight x v * g v| ≤ B := by
    calc
      _ ≤ ∑ v, |(graphRule G θ hθ).kernel.weight x v * g v| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ v, (graphRule G θ hθ).kernel.weight x v * |g v| := by
        simp only [abs_mul, abs_of_nonneg ((graphRule G θ hθ).kernel.nonneg _ _)]
      _ ≤ ∑ v, (graphRule G θ hθ).kernel.weight x v * B :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hg v) ((graphRule G θ hθ).kernel.nonneg _ _))
      _ = B := by rw [← Finset.sum_mul, (graphRule G θ hθ).kernel.total, one_mul]
  calc
    _ ≤ |g c| + |∑ v, (graphRule G θ hθ).kernel.weight x v * g v| := abs_sub _ _
    _ ≤ 2 * B := by linarith [hg c]

omit [Nonempty V] in
lemma noise_variance (x : Profile V) (g : V → ℝ) :
    (∑ c, (graphRule G θ hθ).kernel.weight x c * (g ⬝ᵥ choiceNoise G hθ x c)^2) =
      (∑ c, (graphRule G θ hθ).kernel.weight x c * (g c)^2) -
        (∑ c, (graphRule G θ hθ).kernel.weight x c * g c)^2 := by
  simp_rw [dot_choiceNoise, sub_sq, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, (graphRule G θ hθ).kernel.total, one_mul]
  have hm : (∑ c, (graphRule G θ hθ).kernel.weight x c *
      (2 * g c * ∑ v, (graphRule G θ hθ).kernel.weight x v * g v)) =
      2 * (∑ c, (graphRule G θ hθ).kernel.weight x c * g c)^2 := by
    calc
      _ = (∑ c, (graphRule G θ hθ).kernel.weight x c * g c) *
          (2 * ∑ c, (graphRule G θ hθ).kernel.weight x c * g c) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by ring
  rw [hm]
  ring

lemma noise_variance_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (x : Profile V) (g : V → ℝ) :
    (∑ c, (graphRule G θ hθ).kernel.weight x c * (g ⬝ᵥ choiceNoise G hθ x c)^2) ≤
      (2 / (Fintype.card V : ℝ)) * (g ⬝ᵥ g) := by
  rw [noise_variance]
  calc
    _ ≤ ∑ c, (graphRule G θ hθ).kernel.weight x c * (g c)^2 := sub_le_self _ (sq_nonneg _)
    _ ≤ ∑ c, (2 / (Fintype.card V : ℝ)) * (g c)^2 :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_right (graph_choice_le G hθ hd x c) (sq_nonneg _))
    _ = _ := by simp only [dotProduct, pow_two, Finset.mul_sum]

lemma stopped_noise_mean {d : ℕ} (hd : G.IsRegularOfDegree d)
    (s : StoppedState G (θ := θ)) (g : V → ℝ) :
    (∑ c, (stoppedKernel G hθ hd).weight s c * (g ⬝ᵥ stoppedNoise G hθ s c)) = 0 := by
  unfold stoppedNoise
  split
  · exact noise_mean G hθ s.profile g
  · simp

omit [Nonempty V] in
lemma stopped_noise_abs_le (s : StoppedState G (θ := θ)) (g : V → ℝ)
    (hg : ∀ v, |g v| ≤ 1) (c : V) : |g ⬝ᵥ stoppedNoise G hθ s c| ≤ 2 := by
  unfold stoppedNoise
  split
  · simpa using noise_abs_le G hθ s.profile g hg c
  · simp

lemma stopped_noise_variance_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (s : StoppedState G (θ := θ)) (g : V → ℝ) :
    (∑ c, (stoppedKernel G hθ hd).weight s c * (g ⬝ᵥ stoppedNoise G hθ s c)^2) ≤
      (2 / (Fintype.card V : ℝ)) * (g ⬝ᵥ g) := by
  unfold stoppedNoise
  split
  · exact noise_variance_le G hθ hd s.profile g
  · simp only [dotProduct_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun v _ => mul_self_nonneg _)

/-- Chronological rewards in the stopped heat convolution at a fixed horizon. -/
def heatReward (k : ℕ) (ℓ : V → ℝ) (i : ℕ) (s : StoppedState G (θ := θ)) (c : V) : ℝ :=
  (((smoothing G (stepSize G (θ := θ))) ^ (k - 1 - i)) ℓ) ⬝ᵥ stoppedNoise G hθ s c

/-- Each heat reward is a local potential difference, with no martingale-law assumption. -/
lemma heatReward_potential {d : ℕ} (hd : G.IsRegularOfDegree d) (k : ℕ) (ℓ : V → ℝ)
    (i : ℕ) (hi : i < k) (s : StoppedState G (θ := θ)) (c : V) :
    heatReward G hθ k ℓ i s c =
      (((smoothing G (stepSize G (θ := θ))) ^ (k - (i + 1))) ℓ) ⬝ᵥ
        ((stoppedKernel G hθ hd).next s c).heat -
      (((smoothing G (stepSize G (θ := θ))) ^ (k - i)) ℓ) ⬝ᵥ s.heat := by
  have ha : k - (i + 1) = k - 1 - i := by omega
  have hb : k - i = (k - 1 - i) + 1 := by omega
  rw [stoppedNext_heat, dotProduct_add, ha, hb, pow_succ', Module.End.mul_apply,
    smoothing_self_adjoint]
  unfold heatReward
  ring

lemma heatReward_terminal {d : ℕ} (hd : G.IsRegularOfDegree d) (k : ℕ) (ℓ : V → ℝ)
    (a : ℤ) (p : ChoicePath V k) :
    (stoppedKernel G hθ hd).pathReward (heatReward G hθ k ℓ) 0 k (stoppedInitial G hθ a) p =
      ℓ ⬝ᵥ ((stoppedKernel G hθ hd).pathTerminal k (stoppedInitial G hθ a) p).heat := by
  rw [FiniteKernel.pathReward_eq_terminal_sub (φ := fun i s =>
    (((smoothing G (stepSize G (θ := θ))) ^ (k - i)) ℓ) ⬝ᵥ s.heat)]
  · simp [stoppedInitial]
  · intro i hi s c
    simpa using heatReward_potential G hθ hd k ℓ i hi s c

/-- Bernstein with variance computed from the actual graph Green energy. -/
theorem stopped_heat_bernstein {d : ℕ} (hd : G.IsRegularOfDegree d) (hG : G.Connected)
    (hstep : stepSize G (θ := θ) * (2 * (d : ℝ)) ≤ 1)
    (k : ℕ) (a : ℤ) (ℓ : V → ℝ) (hℓ : ℓ ∈ meanZero) (hℓb : ∀ v, |ℓ v| ≤ 1)
    {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s)
    (henergy : 2 * (d : ℝ) * θ * energy G hG ℓ ≤ σ) :
    (stoppedKernel G hθ hd).iterate k (fun t =>
      if Real.sqrt (2 * σ * s) + (4 / 3 : ℝ) * s ≤ |ℓ ⬝ᵥ t.heat| then 1 else 0)
        (stoppedInitial G hθ a) ≤ 2 * Real.exp (-s) := by
  let α := stepSize G (θ := θ)
  let W := smoothing G α
  let v := fun i => (2 / (Fintype.card V : ℝ)) * (((W ^ (k - 1 - i)) ℓ) ⬝ᵥ ((W ^ (k - 1 - i)) ℓ))
  have hα := stepSize_pos G hθ
  have hd' : ∀ w, (G.degree w : ℝ) ≤ d := fun w => by rw [hd.degree_eq]
  have hαd : ∀ w, α * (G.degree w : ℝ) ≤ 1 := by
    intro w
    rw [hd.degree_eq]
    have hnon : 0 ≤ α * (d : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg _)
    dsimp [α] at *
    nlinarith
  have hbudget : ∑ i ∈ Finset.range k, v i ≤ σ := by
    have he := smoothing_energy_budget G hG α d hα hd' hstep hℓ k
    have hreflect : (∑ i ∈ Finset.range k, v i) =
        (2 / (Fintype.card V : ℝ)) * ∑ j ∈ Finset.range k, ((W ^ j) ℓ) ⬝ᵥ ((W ^ j) ℓ) := by
      simp only [v, ← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_reflect (fun j => ((W ^ j) ℓ) ⬝ᵥ ((W ^ j) ℓ)) k
    rw [hreflect]
    have hc : (2 / (Fintype.card V : ℝ)) * (energy G hG ℓ / α) =
        2 * (d : ℝ) * θ * energy G hG ℓ := by
      have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hm : (Fintype.card G.edgeSet : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hdeg := graph_regular_degree_sum G hd
      dsimp [α, stepSize]
      field_simp
      nlinarith [congrArg (fun t : ℝ => t * energy G hG ℓ) hdeg]
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (hc.le.trans henergy)
  rw [show (4 / 3 : ℝ) = 2 * 2 / 3 by norm_num]
  apply FiniteKernel.iterate_bernstein (stoppedKernel G hθ hd)
    (heatReward G hθ k ℓ) v k (stoppedInitial G hθ a) (fun t => ℓ ⬝ᵥ t.heat)
    (b := 2) (by norm_num) hσ hs
  · intro i hi t
    exact stopped_noise_mean G hθ hd t _
  · intro i hi t c
    apply stopped_noise_abs_le G hθ t
    exact abs_smoothing_pow_le G α 1 hα.le hαd hℓb _
  · intro i hi t
    exact stopped_noise_variance_le G hθ hd t _
  · exact hbudget
  · intro p
    exact (heatReward_terminal G hθ hd k ℓ a p).symm

end GraphicalAllocation.Smoothed
