import GraphicalAllocation.Transport.MarkedTransport
import GraphicalAllocation.Transport.DiscreteCorrection
import GraphicalAllocation.Process.FiniteAllocation

/-!
# Pointwise transport for the actual allocation kernel

The finite marked experiment is constructed from the original rule on the
entire reachable box. Its base and perturbed expectations agree exactly with
the genuine allocation process. Thus the derivatives below belong to the
actual graph allocation semigroup, rather than to an assumed response family.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process
open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable (A : AllocationRule V E)

/-- The genuine Palm-initialized finite-horizon tag-displacement probability. -/
def allocationTagTail (h : ℕ) (x : Profile V) (d : V → V → ℝ) (R : ℝ) : ℝ :=
  markedTail (A.horizonMarks x h) h x (A.kernel.weight x) d R

/-- Actual finite-horizon bad-gap probability. -/
def allocationBadGap (h : ℕ) (x : Profile V) (M : ℝ) : ℝ :=
  A.kernel.iterate h (fun y => if gap y ≤ M - 1 then 0 else 1) x

omit [DecidableEq E] in
/-- Protected response for the actual graph allocation semigroup. -/
theorem allocation_protected_response
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) (h : ℕ) (x : Profile V) :
    (1 - allocationBadGap A h x M - 2 * allocationTagTail A h x d R) / M ≤
      ∑ i, ∑ v, if d i v ≤ R then
        A.kernel.weight x v * finiteDifference
          (A.kernel.iterate h (clippedContrast i (ψ i) M)) x v else 0 := by
  have hr := marked_protected_response (A.horizonMarks x h) d hdiag hsym htriangle
    ψ hR hM hsep h x (A.kernel.weight x) (A.kernel.nonneg x) (A.kernel.total x)
  simpa only [allocationBadGap, allocationTagTail, markedBadGap, finiteDifference,
    ← A.horizonMarks_base_eq, ← A.horizonMarks_raised_eq] using hr

omit [DecidableEq E] in
/-- Actual pointwise event-time energy bound (5.10)/(6.8), before averaging over
an intermediate state and dividing by the number of vertices. -/
theorem allocation_transport_energy
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B p q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (h : ℕ) (x : Profile V) (hp : allocationBadGap A h x M ≤ p)
    (hq : allocationTagTail A h x d R ≤ q) :
    max (1 - p - 2 * q) 0 ^ 2 / (M ^ 2 * B) ≤
      ∑ i, A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M)) x := by
  have he := marked_transport_energy (A.horizonMarks x h) d hdiag hsym htriangle
    ψ hR hM hB hsep hvolume h x (A.kernel.weight x) (A.kernel.nonneg x) (A.kernel.total x)
    (by simpa only [allocationBadGap, markedBadGap, ← A.horizonMarks_base_eq] using hp) hq
  simpa only [finiteDifference, ← A.horizonMarks_base_eq, ← A.horizonMarks_raised_eq,
    FiniteKernel.responseEnergy, AllocationRule.kernel_next] using he

omit [Nonempty V] [DecidableEq E] in
/-- Uniform directional bound for the genuine h-event semigroup. -/
theorem allocation_clipped_derivative_abs_le (i j v : V) (hij : i ≠ j)
    {M : ℝ} (hM : 0 < M) (h : ℕ) (x : Profile V) :
    |finiteDifference (A.kernel.iterate h (clippedContrast i j M)) x v| ≤ 1 / M := by
  rw [finiteDifference, A.derivative_eq_horizon_tag]
  apply (A.horizonMarks x h).tagged.iterate_bounded h
  intro y
  exact finiteDifference_abs_le i j y.2 hij hM y.1

end GraphicalAllocation.Transport
