import GraphicalAllocation.Smoothed.Drift
import GraphicalAllocation.Spectral.Smoothing
import GraphicalAllocation.Process.FinitePaths

/-!
# The actual stopped smoothed allocation process

The state records the integer allocation profile, the stopped heat recursion,
and whether every visited profile has remained in the linear region. Its
proof fields express invariants, not assumptions on a probability law. The
transition uses exactly the allocation kernel's vertex probabilities.

Reconstruction stages: (0) for every regular graph, construct a stopped process
and prove its allocation projection; (1) finite-choice kernels on integer and
real profiles; (2) the live flag means all profiles seen so far were within the
actual edge cutoff; (3) preserve centering and agreement at each live update;
(4) use the exact linear drift and prove path projection by induction; (5)
resolve casts and finite sums. The proof fields below are established by the
constructor, rather than supplied as hypotheses about an unspecified process.
-/
noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators
open Process Rules Matrix Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Nonempty V] [Nonempty G.edgeSet]
variable {θ : ℝ} (hθ : 0 < θ)

/-- The integer profile viewed in the real vertex space. -/
def realProfile (x : Profile V) : V → ℝ := fun v => x v

/-- The time step fixed by the actual number of edges and the cutoff. -/
def stepSize : ℝ := 1 / (2 * Fintype.card G.edgeSet * θ)

include hθ in
omit [DecidableEq V] [Nonempty V] in
lemma stepSize_pos : 0 < stepSize G (θ := θ) := by
  have : (0 : ℝ) < Fintype.card G.edgeSet := by exact_mod_cast Fintype.card_pos
  have ht := hθ
  unfold stepSize
  positivity

omit [Fintype V] [Nonempty V] in
lemma realProfile_raise (x : Profile V) (c : V) :
    realProfile (raise x c) = realProfile x + Pi.single c 1 := by
  ext v
  by_cases h : v = c <;> simp [realProfile, raise, h]

omit [Nonempty V] in
lemma center_raise (x : Profile V) (c : V) :
    center (realProfile (raise x c)) = center (realProfile x) +
      (Pi.single c 1 - fun _ => 1 / (Fintype.card V : ℝ)) := by
  rw [realProfile_raise, map_add]
  congr 1
  ext v
  simp [center_apply]

/-- The centered unit allocation noise at the actual state. -/
def choiceNoise (x : Profile V) (c : V) : V → ℝ :=
  Pi.single c 1 - (graphRule G θ hθ).kernel.weight x

omit [Nonempty V] in
lemma choiceNoise_mem (x : Profile V) (c : V) : choiceNoise G hθ x c ∈ meanZero := by
  simp only [mem_meanZero, choiceNoise, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [(graphRule G θ hθ).kernel.total]
  simp

lemma center_raise_linear {d : ℕ} (hd : G.IsRegularOfDegree d)
    (x : Profile V) (hx : WithinCutoff G (θ := θ) x) (c : V) :
    center (realProfile (raise x c)) =
      smoothing G (stepSize G (θ := θ)) (center (realProfile x)) + choiceNoise G hθ x c := by
  rw [center_raise, smoothing_apply, laplacian_center]
  ext v
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, choiceNoise]
  rw [graph_choice_linear G hθ hd x hx v]
  unfold stepSize realProfile
  ring

/-- A reachable stopped state, with its two pathwise invariants encoded. -/
structure StoppedState where
  profile : Profile V
  heat : V → ℝ
  alive : Bool
  heat_mem : heat ∈ meanZero
  agreement : alive = true → heat = center (realProfile profile)
  within : alive = true → WithinCutoff G (θ := θ) profile

/-- The stopped noise is suppressed permanently after the first cutoff exit. -/
def stoppedNoise (s : StoppedState G (θ := θ)) (c : V) : V → ℝ :=
  if s.alive then choiceNoise G hθ s.profile c else 0

/-- One step of the stopped heat recursion, coupled to the actual allocation. -/
def stoppedNext {d : ℕ} (hd : G.IsRegularOfDegree d)
    (s : StoppedState G (θ := θ)) (c : V) : StoppedState G (θ := θ) := by
  classical
  refine {
    profile := raise s.profile c
    heat := smoothing G (stepSize G (θ := θ)) s.heat + stoppedNoise G hθ s c
    alive := s.alive && decide (WithinCutoff G (θ := θ) (raise s.profile c))
    heat_mem := ?_
    agreement := ?_
    within := ?_ }
  · apply meanZero.add_mem (smoothing_mem G _ s.heat_mem)
    unfold stoppedNoise
    split
    · exact choiceNoise_mem G hθ _ _
    · exact meanZero.zero_mem
  · intro ha
    have hs : s.alive = true := (Bool.and_eq_true_iff.mp ha).1
    simp only [stoppedNoise, hs, ↓reduceIte, s.agreement hs]
    exact (center_raise_linear G hθ hd _ (s.within hs) c).symm
  · intro ha
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp ha).2

/-- The augmented transition has exactly the actual vertex selection law. -/
def stoppedKernel {d : ℕ} (hd : G.IsRegularOfDegree d) :
    FiniteKernel (StoppedState G (θ := θ)) V where
  weight s := (graphRule G θ hθ).kernel.weight s.profile
  nonneg s := (graphRule G θ hθ).kernel.nonneg s.profile
  total s := (graphRule G θ hθ).kernel.total s.profile
  next := stoppedNext G hθ hd

@[simp] lemma stoppedKernel_weight {d : ℕ} (hd : G.IsRegularOfDegree d)
    (s : StoppedState G (θ := θ)) (c : V) :
    (stoppedKernel G hθ hd).weight s c = (graphRule G θ hθ).kernel.weight s.profile c := rfl

@[simp] lemma stoppedNext_profile {d : ℕ} (hd : G.IsRegularOfDegree d)
    (s : StoppedState G (θ := θ)) (c : V) :
    ((stoppedKernel G hθ hd).next s c).profile = raise s.profile c := rfl

@[simp] lemma stoppedNext_heat {d : ℕ} (hd : G.IsRegularOfDegree d)
    (s : StoppedState G (θ := θ)) (c : V) :
    ((stoppedKernel G hθ hd).next s c).heat =
      smoothing G (stepSize G (θ := θ)) s.heat + stoppedNoise G hθ s c := rfl

/-- The flat initial state has zero stopped heat and has not exited. -/
def stoppedInitial (a : ℤ) : StoppedState G (θ := θ) where
  profile := fun _ => a
  heat := 0
  alive := true
  heat_mem := meanZero.zero_mem
  agreement := by
    intro _
    ext v
    have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [realProfile, center_apply, mul_div_cancel_left₀ _ hN]
  within := by
    intro _ u v _
    simpa using hθ.le

/-- Forgetting the auxiliary coordinates recovers every actual finite path. -/
lemma stopped_path_profile {d : ℕ} (hd : G.IsRegularOfDegree d) (n : ℕ)
    (s : StoppedState G (θ := θ)) (p : ChoicePath V n) :
    ((stoppedKernel G hθ hd).pathTerminal n s p).profile =
      (graphRule G θ hθ).kernel.pathTerminal n s.profile p := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _ p.2

/-- The stopped construction preserves the full finite path probability. -/
lemma stopped_path_weight {d : ℕ} (hd : G.IsRegularOfDegree d) (n : ℕ)
    (s : StoppedState G (θ := θ)) (p : ChoicePath V n) :
    (stoppedKernel G hθ hd).pathWeight n s p =
      (graphRule G θ hθ).kernel.pathWeight n s.profile p := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteKernel.pathWeight, stoppedKernel_weight, ih, stoppedNext_profile,
      AllocationRule.kernel_next]

/-- Every expectation of the original allocation profile is preserved. -/
lemma stopped_iterate_profile {d : ℕ} (hd : G.IsRegularOfDegree d) (n : ℕ)
    (f : Profile V → ℝ) (s : StoppedState G (θ := θ)) :
    (stoppedKernel G hθ hd).iterate n (fun t => f t.profile) s =
      (graphRule G θ hθ).kernel.iterate n f s.profile := by
  rw [FiniteKernel.iterate_eq_pathSum, FiniteKernel.iterate_eq_pathSum]
  simp_rw [stopped_path_profile, stopped_path_weight]

end GraphicalAllocation.Smoothed
