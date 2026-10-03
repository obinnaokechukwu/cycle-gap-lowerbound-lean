import GraphicalAllocation.Transport.ContinuousResponse
import GraphicalAllocation.Transport.Functional
import GraphicalAllocation.Transport.Constants
import GraphicalAllocation.Process.Continuous.InitialLaw

/-!
# Continuous transport for the actual allocation process

The response is the genuine Poissonized derivative. The composed positive
expectation through the preceding trajectory incorporates every independent
initial law before the response is squared. The final integration uses the
proved continuous variance budget.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process MeasureTheory
open scoped BigOperators NNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
  [OpensMeasurableSpace (Profile V)]
variable (A : AllocationRule V E)

/-- Actual physical-time bad-gap probability under an arbitrary initial law. -/
def continuousBadGapFrom (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (M : ℝ) : ℝ :=
  boundedExpectation μ (A.kernel.semigroup (Fintype.card E) t (badGapObservable M))

/-- Normalized sum of physical response energies, as a genuine bounded test. -/
def continuousNormalizedEnergy (ψ : Equiv.Perm V) (M : ℝ) (s : ℝ) : Profile V →ᵇ ℝ :=
  (Fintype.card E : ℝ)⁻¹ • ∑ i,
    A.kernel.energy (Fintype.card E)
      (A.kernel.semigroup (Fintype.card E) s (clippedObservable i (ψ i) M))

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [MeasurableSpace (Profile V)]
  [MeasurableSingletonClass (Profile V)] [OpensMeasurableSpace (Profile V)] in
theorem continuousNormalizedEnergy_apply (ψ : Equiv.Perm V) (M s : ℝ) (x : Profile V) :
    continuousNormalizedEnergy A ψ M s x =
      ∑ i, ∑ v, A.kernel.weight x v * finiteDifference
        (A.kernel.semigroup (Fintype.card E) s (clippedObservable i (ψ i) M)) x v ^ 2 := by
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := E)
  simp only [continuousNormalizedEnergy, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sum_apply, smul_eq_mul, FiniteKernel.energy_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [inv_mul_cancel_left₀ hm, finiteDifference, AllocationRule.kernel_next]

omit [OpensMeasurableSpace (Profile V)] [DecidableEq E] in
/-- Actual continuous-time pointwise energy from the protected response. -/
theorem continuous_transport_energy
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (s : ℝ≥0) (x : Profile V) (hq : continuousTagTail A s x d R ≤ q) :
    max (1 - continuousBadGap A s x M - 2 * q) 0 ^ 2 / (M ^ 2 * B) ≤
      continuousNormalizedEnergy A ψ M s x := by
  have hraw := continuous_protected_response A d hdiag hsym htriangle ψ hR hM hsep s x
  have hresp : (1 - continuousBadGap A s x M - 2 * q) / M ≤
      ∑ i, ∑ v, if d i v ≤ R then A.kernel.weight x v * finiteDifference
        (A.kernel.semigroup (Fintype.card E) s (clippedObservable i (ψ i) M)) x v else 0 := by
    exact (div_le_div_of_nonneg_right (by linarith) (by linarith)).trans hraw
  have he := restricted_response_energy d hsym R id (A.kernel.weight x)
    (A.kernel.nonneg x) (A.kernel.total x)
    (fun i v => finiteDifference
      (A.kernel.semigroup (Fintype.card E) s (clippedObservable i (ψ i) M)) x v)
    hB hvolume hresp
  rw [protected_energy_normalization (by linarith : 0 < M)] at he
  rwa [continuousNormalizedEnergy_apply]

omit [DecidableEq E] in
/-- The genuine lag-response density, after averaging the entire past and
arbitrary independent initial law, pays the protected terminal response. -/
theorem continuous_lag_lower (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (t s : ℝ≥0) (hst : s ≤ t) (hq : ∀ x, continuousTagTail A s x d R ≤ q) :
    (Fintype.card E : ℝ) *
      (max (1 - continuousBadGapFrom A μ t M - 2 * q) 0 ^ 2 / B) ≤
      M ^ 2 * ∑ i, A.kernel.lagResponseEnergy μ (Fintype.card E) t
        (clippedObservable i (ψ i) M) s := by
  let L : (Profile V →ᵇ ℝ) →L[ℝ] ℝ :=
    (boundedExpectation μ).comp (A.kernel.semigroup (Fintype.card E) ((t : ℝ) - s))
  have hm : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  have hpos : ∀ f : Profile V →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f := by
    intro f hf
    exact boundedExpectation_nonneg μ (A.kernel.semigroup_nonneg hm.le
      (sub_nonneg.mpr (by exact_mod_cast hst)) hf)
  have hconst : ∀ c, L (BoundedContinuousFunction.const (Profile V) c) = c := by
    intro c
    simp [L]
  let r : Profile V →ᵇ ℝ := BoundedContinuousFunction.const (Profile V) 1 -
    A.kernel.semigroup (Fintype.card E) s (badGapObservable M) -
    BoundedContinuousFunction.const (Profile V) (2 * q)
  have hpoint : ∀ x, max (r x) 0 ^ 2 / (M ^ 2 * B) ≤ continuousNormalizedEnergy A ψ M s x := by
    intro x
    exact continuous_transport_energy A d hdiag hsym htriangle ψ hR hM hB hsep hvolume s x (hq x)
  have he := positive_functional_energy_lower L hpos hconst r
    (continuousNormalizedEnergy A ψ M s) (mul_pos (sq_pos_of_pos (by linarith)) hB) hpoint
  have hr : L r = 1 - continuousBadGapFrom A μ t M - 2 * q := by
    simp only [r, map_sub, hconst]
    congr 1
    congr 1
    dsimp [L, continuousBadGapFrom]
    congr 1
    have hc := congrArg (fun Q : (Profile V →ᵇ ℝ) →L[ℝ] (Profile V →ᵇ ℝ) => Q (badGapObservable M))
      (A.kernel.semigroup_add (Fintype.card E) ((t : ℝ) - s) s)
    simpa using hc.symm
  have heq : L (continuousNormalizedEnergy A ψ M s) =
      (∑ i, A.kernel.lagResponseEnergy μ (Fintype.card E) t
        (clippedObservable i (ψ i) M) s) / (Fintype.card E : ℝ) := by
    simp only [continuousNormalizedEnergy, map_smul, map_sum, L,
      ContinuousLinearMap.comp_apply, FiniteKernel.lagResponseEnergy, smul_eq_mul]
    ring
  rw [hr, heq] at he
  have hden : 0 < M ^ 2 * B := mul_pos (sq_pos_of_pos (by linarith)) hB
  have hc := (div_le_div_iff₀ hden hm).mp he
  rw [← mul_div_assoc, div_le_iff₀ hB]
  nlinarith

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [MeasurableSingletonClass (Profile V)] in
/-- Integration of any proved lag lower bound against the actual unit budgets. -/
theorem integrate_continuous_lag_lower (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (ψ : Equiv.Perm V) (M : ℝ) (t : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 T)
    (hpoint : ∀ s ∈ Set.Icc 0 T, (Fintype.card E : ℝ) * g s ≤
      M ^ 2 * ∑ i, A.kernel.lagResponseEnergy μ (Fintype.card E) t
        (clippedObservable i (ψ i) M) s) :
    (Fintype.card E : ℝ) / Fintype.card V * (∫ s in (0 : ℝ)..T, g s) ≤ M ^ 2 := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hi : ∀ i : V, IntervalIntegrable
      (A.kernel.lagResponseEnergy μ (Fintype.card E) t (clippedObservable i (ψ i) M)) volume 0 T :=
    fun i => (A.kernel.continuous_lagResponseEnergy μ (Fintype.card E) t
      (clippedObservable i (ψ i) M)).intervalIntegrable 0 T
  have hsum : IntervalIntegrable (fun s => ∑ i, A.kernel.lagResponseEnergy μ
      (Fintype.card E) t (clippedObservable i (ψ i) M) s) volume 0 T := by
    convert IntervalIntegrable.sum Finset.univ (fun i hi' => hi i) using 1
    funext s
    simp only [Finset.sum_apply]
  have hbudget : (∫ s in (0 : ℝ)..T, ∑ i, A.kernel.lagResponseEnergy μ
      (Fintype.card E) t (clippedObservable i (ψ i) M) s) ≤ Fintype.card V := by
    rw [intervalIntegral.integral_finsetSum (fun i hi' => hi i)]
    calc
      _ ≤ ∑ i : V, (1 : ℝ) := Finset.sum_le_sum (fun i hi' =>
        A.kernel.integral_lagResponseEnergy_le_one μ (Nat.cast_nonneg _) hT hTt
          (fun x => abs_clippedContrast_le_one i (ψ i) M x))
      _ = _ := by simp
  have hm := intervalIntegral.integral_mono_on hT (hg.const_mul (Fintype.card E : ℝ))
    (hsum.const_mul (M ^ 2)) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have hu := mul_le_mul_of_nonneg_left hbudget (sq_nonneg M)
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  nlinarith

omit [DecidableEq E] in
/-- The general transport-volume inequality (5.4) for the actual continuous
allocation process and arbitrary independent initial laws. Direct interval
integrability is the minimal corrected E2 measurability requirement. -/
theorem continuous_transport_volume (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M : ℝ} (hM : 1 ≤ M) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (R B q : ℝ → ℝ)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s) (hB : ∀ s ∈ Set.Icc 0 T, 0 < B s)
    (hsep : ∀ s ∈ Set.Icc 0 T, ∀ i, 2 * R s ≤ d i (ψ i))
    (hvolume : ∀ s ∈ Set.Icc 0 T, ∀ v, ((closedBall d (R s) v).card : ℝ) ≤ B s)
    (hq : ∀ s ∈ Set.Icc 0 T, ∀ x, continuousTagTail A (Real.toNNReal s) x d (R s) ≤ q s)
    (hg : IntervalIntegrable (fun s =>
      max (1 - continuousBadGapFrom A μ t M - 2 * q s) 0 ^ 2 / B s) volume 0 T) :
    (Fintype.card E : ℝ) / Fintype.card V *
      (∫ s in (0 : ℝ)..T, max (1 - continuousBadGapFrom A μ t M - 2 * q s) 0 ^ 2 / B s) ≤ M ^ 2 := by
  apply integrate_continuous_lag_lower A μ ψ M t hT hTt _ hg
  intro s hs
  have hst : Real.toNNReal s ≤ t := by
    apply (NNReal.coe_le_coe).mp
    simpa [Real.coe_toNNReal s hs.1] using hs.2.trans hTt
  have h := continuous_lag_lower A μ d hdiag hsym htriangle ψ (hR s hs) hM (hB s hs)
    (hsep s hs) (hvolume s hs) t (Real.toNNReal s) hst (hq s hs)
  simpa only [Real.coe_toNNReal s hs.1] using h

omit [DecidableEq E] in
/-- The `p,q ≤ 1/8` specialization (5.5). Only integrability of inverse volume
is needed; the positive-part integrand need not be introduced separately. -/
theorem continuous_transport_volume_simple (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M : ℝ} (hM : 1 ≤ M) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (R B : ℝ → ℝ)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s) (hB : ∀ s ∈ Set.Icc 0 T, 0 < B s)
    (hsep : ∀ s ∈ Set.Icc 0 T, ∀ i, 2 * R s ≤ d i (ψ i))
    (hvolume : ∀ s ∈ Set.Icc 0 T, ∀ v, ((closedBall d (R s) v).card : ℝ) ≤ B s)
    (hq : ∀ s ∈ Set.Icc 0 T, ∀ x, continuousTagTail A (Real.toNNReal s) x d (R s) ≤ 1 / 8)
    (hp : continuousBadGapFrom A μ t M ≤ 1 / 8)
    (hg : IntervalIntegrable (fun s => 1 / B s) volume 0 T) :
    (Fintype.card E : ℝ) / (4 * Fintype.card V) * (∫ s in (0 : ℝ)..T, 1 / B s) ≤ M ^ 2 := by
  have hscaled : IntervalIntegrable (fun s => (1 / 4 : ℝ) * (1 / B s)) volume 0 T := hg.const_mul _
  have hresult := integrate_continuous_lag_lower A μ ψ M t hT hTt _ hscaled (by
    intro s hs
    have hst : Real.toNNReal s ≤ t := by
      apply (NNReal.coe_le_coe).mp
      simpa [Real.coe_toNNReal s hs.1] using hs.2.trans hTt
    have hl := continuous_lag_lower A μ d hdiag hsym htriangle ψ (hR s hs) hM (hB s hs)
      (hsep s hs) (hvolume s hs) t (Real.toNNReal s) hst (hq s hs)
    simp only [Real.coe_toNNReal s hs.1] at hl
    apply le_trans _ hl
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (Fintype.card E))
    have hn := div_le_div_of_nonneg_right (quarter_le_response_sq hp (le_refl (1 / 8 : ℝ))) (hB s hs).le
    simpa [div_eq_mul_inv] using hn)
  rw [intervalIntegral.integral_const_mul] at hresult
  convert hresult using 1
  ring

omit [DecidableEq E] in
/-- Constant-radius, constant-volume form used in cycle and cylinder applications. -/
theorem continuous_transport_volume_constant (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M R B : ℝ} (hM : 1 ≤ M) (hR : 0 < R) (hB : 0 < B)
    (t : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (hq : ∀ s ∈ Set.Icc 0 T, ∀ x, continuousTagTail A (Real.toNNReal s) x d R ≤ 1 / 8)
    (hp : continuousBadGapFrom A μ t M ≤ 1 / 8) :
    (Fintype.card E : ℝ) * T / (4 * Fintype.card V * B) ≤ M ^ 2 := by
  have h := continuous_transport_volume_simple A μ d hdiag hsym htriangle ψ hM t hT hTt
    (fun _ => R) (fun _ => B) (fun _ _ => hR) (fun _ _ => hB)
    (fun _ _ => hsep) (fun _ _ => hvolume) hq hp intervalIntegrable_const
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  convert h using 1
  ring

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
/-- The bad-gap probability is exactly that of the constructed Poissonized
allocation process, for every initial PMF including infinite-moment laws. -/
theorem continuousBadGapFrom_eq_probability (μ : PMF (Profile V)) (t : ℝ≥0) (M : ℝ) :
    continuousBadGapFrom A μ.toMeasure t M =
      (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure.real {x | M - 1 < gap x} := by
  have hs : MeasurableSet {x : Profile V | M - 1 < gap x} :=
    measurableSet_lt measurable_const (measurable_of_countable gap)
  have heq : (fun y : Profile V => badGapObservable M y) =
      Set.indicator {x | M - 1 < gap x} 1 := by
    funext y
    by_cases hy : gap y ≤ M - 1
    · simp [badGapObservable_apply, hy, not_lt.mpr hy]
    · simp [badGapObservable_apply, hy, lt_of_not_ge hy]
  change (∫ x, A.kernel.semigroup (Fintype.card E) t (badGapObservable M) x ∂μ.toMeasure) = _
  have hi := A.kernel.integral_continuousLawFrom_eq_semigroup μ (Fintype.card E) t (badGapObservable M)
  simp only [NNReal.coe_natCast] at hi
  rw [← hi]
  rw [heq]
  exact integral_indicator_one hs

end GraphicalAllocation.Transport
