import GraphicalAllocation.Transport.Clipped
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Clipped tests as genuine bounded observables -/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules
open scoped BoundedContinuousFunction

variable {V : Type*} [DecidableEq V]
variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]

/-- The actual clipped contrast in the Banach space used by the continuous
Markov semigroup. -/
def clippedObservable (i j : V) (M : ℝ) : Profile V →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (clippedContrast i j M) 1
    (fun x => by simpa using abs_clippedContrast_le_one i j M x)

omit [DecidableEq V] in
@[simp] theorem clippedObservable_apply (i j : V) (M : ℝ) (x : Profile V) :
    clippedObservable i j M x = clippedContrast i j M x := rfl

omit [DecidableEq V] in
theorem norm_clippedObservable_le_one (i j : V) (M : ℝ) :
    ‖clippedObservable i j M‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    (fun x => by simpa using abs_clippedContrast_le_one i j M x)

end GraphicalAllocation.Transport
