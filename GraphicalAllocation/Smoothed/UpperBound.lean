import GraphicalAllocation.Smoothed.Concentration
import GraphicalAllocation.Spectral.Radius
import GraphicalAllocation.Transport.Clipped
import GraphicalAllocation.Transport.MarkedTransport

/-!
# Cutoff exit, vertex tails, and the expected load gap

Reconstruction stages: (0) the actual expected gap is bounded by a deterministic
radius plus an exceptional-event cost; (1) finite expectation operators and
actual graph edges provide the probability space and union indices; (2) define
the exit, edge-violation and vertex-violation observables; (3) bound cutoff exit
by an accumulated one-step union estimate; (4) apply the proved stopped-noise
Bernstein theorem and the flat-start pathwise bound; (5) combine exact finite
path expectations and simplify the real constants.
-/
noncomputable section
open scoped BigOperators
namespace GraphicalAllocation.Process.FiniteKernel
variable {S C I : Type*} [Fintype C]
variable (K : FiniteKernel S C)

lemma iterate_finset_sum_apply (n : ℕ) (J : Finset I) (f : I → S → ℝ) (x : S) :
    K.iterate n (fun y => ∑ i ∈ J, f i y) x = ∑ i ∈ J, K.iterate n (f i) x := by
  have he : (fun y => ∑ i ∈ J, f i y) = ∑ i ∈ J, f i := by
    funext y
    simp only [Finset.sum_apply]
  rw [he]
  simpa only [Finset.sum_apply] using congrFun (K.iterate_finset_sum n J f) x

lemma iterate_smul (n : ℕ) (c : ℝ) (f : S → ℝ) :
    K.iterate n (c • f) = c • K.iterate n f := by
  have he : c • f = fun x => c * f x := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [he]
  funext x
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (K.iterate_const_mul n c f) x

lemma iterate_exit_bound (exit edge : S → ℝ)
    (hstep : ∀ x, K.step exit x ≤ exit x + K.step edge x) (n : ℕ) (x : S) :
    K.iterate n exit x ≤ exit x + ∑ j ∈ Finset.range n, K.iterate (j + 1) edge x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := K.iterate_mono n hstep x
    change K.iterate n (K.step exit) x ≤ K.iterate n (exit + K.step edge) x at h
    rw [K.iterate_step, K.iterate_add] at h
    change K.iterate (n + 1) exit x ≤ K.iterate n exit x + K.iterate n (K.step edge) x at h
    rw [K.iterate_step] at h
    change K.iterate (n + 1) exit x ≤ K.iterate n exit x + K.iterate (n + 1) edge x at h
    rw [Finset.sum_range_succ]
    linarith

end GraphicalAllocation.Process.FiniteKernel
namespace GraphicalAllocation.Smoothed
open Process Rules Matrix Spectral Transport

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Nonempty V] [Nonempty G.edgeSet]
variable {θ : ℝ} (hθ : 0 < θ)

/-- One orientation of each actual edge, so a union counts each edge once. -/
def edgeVector (e : G.edgeSet) : V → ℝ :=
  Pi.single e.val.out.1 1 - Pi.single e.val.out.2 1

omit [DecidableRel G.Adj] [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma edgeVector_mem (e : G.edgeSet) : edgeVector G e ∈ meanZero := by
  simp [edgeVector, mem_meanZero, Finset.sum_sub_distrib]

omit [Fintype V] [DecidableRel G.Adj] [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma edgeVector_abs_le (e : G.edgeSet) (v : V) : |edgeVector G e v| ≤ 1 := by
  simp only [edgeVector, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

omit [DecidableRel G.Adj] [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma edgeVector_dot (e : G.edgeSet) (z : V → ℝ) :
    edgeVector G e ⬝ᵥ z = z e.val.out.1 - z e.val.out.2 := by
  simp [edgeVector, sub_dotProduct]

omit [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma edgeVector_energy_le (hG : G.Connected) (e : G.edgeSet) :
    energy G hG (edgeVector G e) ≤ 1 := by
  apply edge_energy_le_one
  apply G.mem_edgeSet.mp
  simpa only [Sym2.mk, Prod.mk.eta, Quot.out_eq] using e.property

omit [DecidableRel G.Adj] [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma withinCutoff_iff_edges (x : Profile V) :
    WithinCutoff G (θ := θ) x ↔ ∀ e : G.edgeSet, |edgeVector G e ⬝ᵥ center (realProfile x)| ≤ θ := by
  constructor
  · intro hx e
    rw [dot_center_right (edgeVector_mem G e), edgeVector_dot]
    apply hx
    apply G.mem_edgeSet.mp
    simpa only [Sym2.mk, Prod.mk.eta, Quot.out_eq] using e.property
  · intro hx u v huv
    let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
    have h := hx e
    rw [dot_center_right (edgeVector_mem G e), edgeVector_dot] at h
    have he : s(e.val.out.1, e.val.out.2) = s(u, v) := Quot.out_eq _
    rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simpa [hu, hv, realProfile] using h
    · simpa [hu, hv, realProfile, abs_sub_comm] using h

/-- The indicator that the cutoff has been crossed at some visited time. -/
def exitIndicator (t : StoppedState G (θ := θ)) : ℝ := if t.alive then 0 else 1

/-- The number of edges violating the cutoff in the stopped heat profile. -/
def edgeViolations (t : StoppedState G (θ := θ)) : ℝ :=
  ∑ e : G.edgeSet, if θ < |edgeVector G e ⬝ᵥ t.heat| then 1 else 0

omit [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma edgeViolations_nonneg (t : StoppedState G (θ := θ)) : 0 ≤ edgeViolations G t := by
  unfold edgeViolations
  positivity

lemma stoppedNext_agreement_of_alive {d : ℕ} (hd : G.IsRegularOfDegree d)
    (t : StoppedState G (θ := θ)) (c : V) (ht : t.alive = true) :
    ((stoppedKernel G hθ hd).next t c).heat =
      center (realProfile ((stoppedKernel G hθ hd).next t c).profile) := by
  rw [stoppedNext_heat, stoppedNext_profile]
  simp only [stoppedNoise, ht, ↓reduceIte, t.agreement ht]
  exact (center_raise_linear G hθ hd _ (t.within ht) c).symm

lemma exit_next_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (t : StoppedState G (θ := θ)) (c : V) :
    exitIndicator G ((stoppedKernel G hθ hd).next t c) ≤
      exitIndicator G t + edgeViolations G ((stoppedKernel G hθ hd).next t c) := by
  classical
  have hn := edgeViolations_nonneg G ((stoppedKernel G hθ hd).next t c)
  by_cases ht : t.alive = true
  · by_cases hw : WithinCutoff G (θ := θ) (raise t.profile c)
    · simpa [exitIndicator, stoppedKernel, stoppedNext, ht, hw] using hn
    · have hex : ∃ e : G.edgeSet, θ < |edgeVector G e ⬝ᵥ
          ((stoppedKernel G hθ hd).next t c).heat| := by
        rw [withinCutoff_iff_edges G] at hw
        push Not at hw
        simpa only [stoppedNext_agreement_of_alive G hθ hd t c ht, stoppedNext_profile] using hw
      obtain ⟨e, he⟩ := hex
      have hsum : 1 ≤ edgeViolations G ((stoppedKernel G hθ hd).next t c) := by
        unfold edgeViolations
        calc
          (1 : ℝ) = (if θ < |edgeVector G e ⬝ᵥ ((stoppedKernel G hθ hd).next t c).heat| then 1 else 0) := by rw [ite_eq_left he]
          _ ≤ _ := Finset.single_le_sum (f := fun e : G.edgeSet => if θ < |edgeVector G e ⬝ᵥ ((stoppedKernel G hθ hd).next t c).heat| then (1 : ℝ) else 0) (fun i _ => by positivity) (Finset.mem_univ e)
      simpa [exitIndicator, stoppedKernel, stoppedNext, ht, hw] using hsum
  · have hf : t.alive = false := Bool.eq_false_iff.mpr ht
    simpa [exitIndicator, stoppedKernel, stoppedNext, hf] using hn

lemma exit_step_le {d : ℕ} (hd : G.IsRegularOfDegree d) (t : StoppedState G (θ := θ)) :
    (stoppedKernel G hθ hd).step (exitIndicator G) t ≤
      exitIndicator G t + (stoppedKernel G hθ hd).step (edgeViolations G) t := by
  let K := stoppedKernel G hθ hd
  calc
    _ ≤ ∑ c, K.weight t c * (exitIndicator G t + edgeViolations G (K.next t c)) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (exit_next_le G hθ hd t c) (K.nonneg _ _))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, K.total, one_mul]
      rfl

lemma edge_violations_bound {d : ℕ} (hd : G.IsRegularOfDegree d) (hG : G.Connected)
    (hdpos : 0 < d) (hstep : stepSize G (θ := θ) * (2 * (d : ℝ)) ≤ 1)
    (k : ℕ) (a : ℤ) {s : ℝ} (hs : 0 < s)
    (hthreshold : Real.sqrt (4 * (d : ℝ) * θ * s) + (4 / 3 : ℝ) * s ≤ θ) :
    (stoppedKernel G hθ hd).iterate k (edgeViolations G) (stoppedInitial G hθ a) ≤
      2 * (Fintype.card G.edgeSet : ℝ) * Real.exp (-s) := by
  classical
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hσ : 0 < 2 * (d : ℝ) * θ := by positivity
  unfold edgeViolations
  rw [FiniteKernel.iterate_finset_sum_apply]
  calc
    _ ≤ ∑ e : G.edgeSet, 2 * Real.exp (-s) := by
      apply Finset.sum_le_sum
      intro e _
      have hbern := stopped_heat_bernstein G hθ hd hG hstep k a (edgeVector G e)
        (edgeVector_mem G e) (edgeVector_abs_le G e) hσ hs
        (by nlinarith [edgeVector_energy_le G hG e])
      refine le_trans ((stoppedKernel G hθ hd).iterate_mono k ?_ _) hbern
      intro t
      have ht : Real.sqrt (2 * (2 * (d : ℝ) * θ) * s) + 4 / 3 * s ≤ θ := by
        convert hthreshold using 1
        congr 2
        ring
      split_ifs with h₁ h₂ h₂ <;> try norm_num
      exact (h₂ (ht.trans h₁.le)).elim
    _ = _ := by simp; ring

lemma exit_probability_bound {d : ℕ} (hd : G.IsRegularOfDegree d) (hG : G.Connected)
    (hdpos : 0 < d) (hstep : stepSize G (θ := θ) * (2 * (d : ℝ)) ≤ 1)
    (k : ℕ) (a : ℤ) {s : ℝ} (hs : 0 < s)
    (hthreshold : Real.sqrt (4 * (d : ℝ) * θ * s) + (4 / 3 : ℝ) * s ≤ θ) :
    (stoppedKernel G hθ hd).iterate k (exitIndicator G) (stoppedInitial G hθ a) ≤
      2 * (k : ℝ) * Fintype.card G.edgeSet * Real.exp (-s) := by
  have h := (stoppedKernel G hθ hd).iterate_exit_bound (exitIndicator G) (edgeViolations G)
    (exit_step_le G hθ hd) k (stoppedInitial G hθ a)
  have hsum : (∑ j ∈ Finset.range k,
      (stoppedKernel G hθ hd).iterate (j + 1) (edgeViolations G) (stoppedInitial G hθ a)) ≤
        (k : ℝ) * (2 * Fintype.card G.edgeSet * Real.exp (-s)) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, 2 * (Fintype.card G.edgeSet : ℝ) * Real.exp (-s) :=
        Finset.sum_le_sum (fun j _ => edge_violations_bound G hθ hd hG hdpos hstep _ a hs hthreshold)
      _ = _ := by simp
  have hzero : exitIndicator G (stoppedInitial G hθ a) = 0 := rfl
  rw [hzero, zero_add] at h
  nlinarith

/-- The number of stopped vertex coordinates exceeding a supplied radius. -/
def vertexViolations (R : ℝ) (t : StoppedState G (θ := θ)) : ℝ :=
  ∑ v : V, if R < |t.heat v| then 1 else 0

omit [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] [Nonempty ↑G.edgeSet] in
lemma vertexViolations_nonneg (R : ℝ) (t : StoppedState G (θ := θ)) :
    0 ≤ vertexViolations G R t := by unfold vertexViolations; positivity

lemma center_single_abs_le (v w : V) : |center (Pi.single v (1 : ℝ)) w| ≤ 1 := by
  have hN : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hinv : (1 : ℝ) / Fintype.card V ≤ 1 := (div_le_one (by positivity)).mpr hN
  have hinv0 : (0 : ℝ) ≤ 1 / Fintype.card V := by positivity
  by_cases h : w = v
  · subst w
    simp only [center_apply, Pi.single_eq_same, Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [center_apply, Pi.single_eq_of_ne h, Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma vertex_violations_bound {d : ℕ} (hd : G.IsRegularOfDegree d) (hG : G.Connected)
    (hdpos : 0 < d) (hstep : stepSize G (θ := θ) * (2 * (d : ℝ)) ≤ 1)
    (hradius : 0 < greenRadius G hG) (k : ℕ) (a : ℤ) {s R : ℝ} (hs : 0 < s)
    (hthreshold : Real.sqrt (4 * (d : ℝ) * θ * greenRadius G hG * s) + (4 / 3 : ℝ) * s ≤ R) :
    (stoppedKernel G hθ hd).iterate k (vertexViolations G R) (stoppedInitial G hθ a) ≤
      2 * (Fintype.card V : ℝ) * Real.exp (-s) := by
  classical
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hσ : 0 < 2 * (d : ℝ) * θ * greenRadius G hG := by positivity
  unfold vertexViolations
  rw [FiniteKernel.iterate_finset_sum_apply]
  calc
    _ ≤ ∑ v : V, 2 * Real.exp (-s) := by
      apply Finset.sum_le_sum
      intro v _
      have henergy : 2 * (d : ℝ) * θ * energy G hG (center (Pi.single v 1)) ≤
          2 * (d : ℝ) * θ * greenRadius G hG := by
        rw [energy_center_single]
        exact mul_le_mul_of_nonneg_left (greenDiagonal_le_radius G hG v) (by positivity)
      have hbern := stopped_heat_bernstein G hθ hd hG hstep k a (center (Pi.single v 1))
        (center_mem _) (center_single_abs_le v) hσ hs henergy
      refine le_trans ((stoppedKernel G hθ hd).iterate_mono k ?_ _) hbern
      intro t
      rw [dot_center_left _ t.heat_mem]
      simp only [single_one_dotProduct]
      have ht : Real.sqrt (2 * (2 * (d : ℝ) * θ * greenRadius G hG) * s) + 4 / 3 * s ≤ R := by
        convert hthreshold using 1
        congr 2
        ring
      split_ifs with h₁ h₂ h₂ <;> try norm_num
      exact (h₂ (ht.trans h₁.le)).elim
    _ = _ := by simp; ring

omit [Nonempty V] in
/-- Actual allocation paths raise every coordinate by between zero and the path length. -/
lemma allocation_path_coordinate_bounds (k : ℕ) (x : Profile V) (p : ChoicePath V k) (v : V) :
    x v ≤ (graphRule G θ hθ).kernel.pathTerminal k x p v ∧
      (graphRule G θ hθ).kernel.pathTerminal k x p v ≤ x v + k := by
  induction k generalizing x with
  | zero => simp [FiniteKernel.pathTerminal]
  | succ k ih =>
    have h := ih (raise x p.1) p.2
    change x v ≤ (graphRule G θ hθ).kernel.pathTerminal k (raise x p.1) p.2 v ∧
      (graphRule G θ hθ).kernel.pathTerminal k (raise x p.1) p.2 v ≤ x v + (k + 1 : ℕ)
    have hlo : x v ≤ raise x p.1 v := by simp only [raise]; split_ifs <;> omega
    have hhi : raise x p.1 v ≤ x v + 1 := by simp only [raise]; split_ifs <;> omega
    constructor <;> omega

/-- The deterministic flat-start bound used to control the exceptional event. -/
lemma allocation_path_gap_le (k : ℕ) (a : ℤ) (p : ChoicePath V k) :
    gap ((graphRule G θ hθ).kernel.pathTerminal k (fun _ => a) p) ≤ k := by
  let x := (graphRule G θ hθ).kernel.pathTerminal k (fun _ => a) p
  have hmax : maxLoad x ≤ a + k := Finset.sup'_le _ _
    (fun v _ => (allocation_path_coordinate_bounds G hθ k (fun _ => a) p v).2)
  have hmin : a ≤ minLoad x := Finset.le_inf' _ _
    (fun v _ => (allocation_path_coordinate_bounds G hθ k (fun _ => a) p v).1)
  have hmaxr : (maxLoad x : ℝ) ≤ (a : ℝ) + k := by exact_mod_cast hmax
  have hminr : (a : ℝ) ≤ minLoad x := by exact_mod_cast hmin
  change (maxLoad x : ℝ) - (minLoad x : ℝ) ≤ k
  linarith

omit [DecidableEq V] in
lemma gap_le_of_center_bound (x : Profile V) {R : ℝ}
    (hx : ∀ v, |center (realProfile x) v| ≤ R) : gap x ≤ 2 * R := by
  obtain ⟨v, hv, heqv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  obtain ⟨w, hw, heqw⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
  have hv' := (abs_le.mp (hx v)).2
  have hw' := (abs_le.mp (hx w)).1
  simp only [center_apply, realProfile] at hv' hw'
  unfold gap maxLoad minLoad
  rw [heqv, heqw]
  linarith

omit [DecidableEq V] [DecidableRel G.Adj] [Nonempty ↑G.edgeSet] in
/-- Outside the two explicitly controlled exceptional events, the gap is at most twice the radius. -/
lemma gap_le_heat_exceptions (t : StoppedState G (θ := θ)) {R K : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hgap : gap t.profile ≤ K) :
    gap t.profile ≤ 2 * R + K * (exitIndicator G t + vertexViolations G R t) := by
  classical
  have hvnon := vertexViolations_nonneg G R t
  by_cases ht : t.alive = true
  · have he : exitIndicator G t = 0 := by simp [exitIndicator, ht]
    rw [he, zero_add]
    by_cases hv : ∀ v, |t.heat v| ≤ R
    · have hbound : gap t.profile ≤ 2 * R := by
        apply gap_le_of_center_bound
        simpa only [← t.agreement ht] using hv
      exact hbound.trans (le_add_of_nonneg_right (mul_nonneg hK hvnon))
    · push Not at hv
      obtain ⟨v, hv⟩ := hv
      have hvone : 1 ≤ vertexViolations G R t := by
        unfold vertexViolations
        calc
          (1 : ℝ) = (if R < |t.heat v| then 1 else 0) := by rw [ite_eq_left hv]
          _ ≤ _ := Finset.single_le_sum
            (f := fun v : V => if R < |t.heat v| then (1 : ℝ) else 0)
            (fun i _ => by positivity) (Finset.mem_univ v)
      have hm := mul_le_mul_of_nonneg_left hvone hK
      nlinarith
  · have he : exitIndicator G t = 1 := by simp [exitIndicator, ht]
    rw [he]
    have hm := mul_nonneg hK hvnon
    nlinarith

/-- The general upper bound before the paper's numerical cutoff is substituted.
Every probability in the proof is computed from the actual allocation kernel. -/
theorem smoothed_iterate_gap_le {d : ℕ} (hd : G.IsRegularOfDegree d) (hG : G.Connected)
    (hdpos : 0 < d) (hstep : stepSize G (θ := θ) * (2 * (d : ℝ)) ≤ 1)
    (hradius : 0 < greenRadius G hG) (k : ℕ) (a : ℤ) {s R : ℝ} (hs : 0 < s)
    (hedge : Real.sqrt (4 * (d : ℝ) * θ * s) + (4 / 3 : ℝ) * s ≤ θ)
    (hvertex : Real.sqrt (4 * (d : ℝ) * θ * greenRadius G hG * s) + (4 / 3 : ℝ) * s ≤ R) :
    (graphRule G θ hθ).kernel.iterate k gap (fun _ => a) ≤
      2 * R + (k : ℝ) * (2 * (k : ℝ) * Fintype.card G.edgeSet + 2 * Fintype.card V) * Real.exp (-s) := by
  classical
  let K := stoppedKernel G hθ hd
  let initial := stoppedInitial G hθ a
  let majorant : StoppedState G (θ := θ) → ℝ := fun t =>
    2 * R + (k : ℝ) * (exitIndicator G t + vertexViolations G R t)
  have hR : 0 ≤ R := by
    have : 0 ≤ Real.sqrt (4 * (d : ℝ) * θ * greenRadius G hG * s) + (4 / 3 : ℝ) * s := by positivity
    exact this.trans hvertex
  have hgap : K.iterate k (fun t => gap t.profile) initial ≤ K.iterate k majorant initial := by
    rw [FiniteKernel.iterate_eq_pathSum, FiniteKernel.iterate_eq_pathSum]
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (K.pathWeight_nonneg _ _ _)
    apply gap_le_heat_exceptions G _ hR (Nat.cast_nonneg _)
    dsimp [K, initial]
    rw [stopped_path_profile]
    exact allocation_path_gap_le G hθ k a p
  have hmajor : K.iterate k majorant initial = 2 * R + (k : ℝ) *
      (K.iterate k (exitIndicator G) initial + K.iterate k (vertexViolations G R) initial) := by
    change K.iterate k ((fun _ => 2 * R) + (k : ℝ) • (exitIndicator G + vertexViolations G R)) initial = _
    rw [K.iterate_add, K.iterate_smul, K.iterate_add, K.iterate_const]
    rfl
  have he := exit_probability_bound G hθ hd hG hdpos hstep k a hs hedge
  have hv := vertex_violations_bound G hθ hd hG hdpos hstep hradius k a hs hvertex
  have heh := mul_le_mul_of_nonneg_left (add_le_add he hv) (show (0 : ℝ) ≤ k by positivity)
  rw [hmajor] at hgap
  have hactual : K.iterate k (fun t => gap t.profile) initial =
      (graphRule G θ hθ).kernel.iterate k gap (fun _ => a) :=
    stopped_iterate_profile G hθ hd k gap initial
  rw [hactual] at hgap
  change (k : ℝ) * (K.iterate k (exitIndicator G) initial + K.iterate k (vertexViolations G R) initial) ≤
    (k : ℝ) * (2 * (k : ℝ) * Fintype.card G.edgeSet * Real.exp (-s) + 2 * Fintype.card V * Real.exp (-s)) at heh
  nlinarith

end GraphicalAllocation.Smoothed
