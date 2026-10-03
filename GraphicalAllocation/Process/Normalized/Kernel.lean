import GraphicalAllocation.Process.Normalized.Law

/-! # The genuine Markov dynamics induced on integer-translation classes -/

namespace GraphicalAllocation.Process.AllocationRule
open Rules

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [Nonempty E]
variable (A : AllocationRule V E) (anchor : V)

/-- The actual one-allocation quotient kernel on unique anchored representatives. -/
noncomputable def normalizedKernel : FiniteKernel (NormalizedProfile anchor) V where
  weight x v := A.kernel.weight x.val v
  nonneg x v := A.kernel.nonneg x.val v
  total x := A.kernel.total x.val
  next x v := normalize anchor (raise x.val v)

@[simp] theorem normalizedKernel_choiceLaw (x : Profile V) :
    (A.normalizedKernel anchor).choiceLaw (normalize anchor x) = A.kernel.choiceLaw x := by
  apply PMF.ext
  intro v
  simp only [FiniteKernel.choiceLaw_apply]
  congr 1
  change A.rate (normalizeProfile anchor x) v / Fintype.card E = A.rate x v / Fintype.card E
  rw [normalizeProfile, A.rate_translate]

@[simp] theorem normalizedKernel_next (x : Profile V) (v : V) :
    (A.normalizedKernel anchor).next (normalize anchor x) v = normalize anchor (raise x v) := by
  apply Subtype.ext
  exact normalizeProfile_raise anchor x v

/-- The event-count process commutes exactly with the quotient projection. -/
theorem eventLaw_normalize (k : ℕ) (x : Profile V) :
    (A.normalizedKernel anchor).eventLaw k (normalize anchor x) =
      (A.kernel.eventLaw k x).map (normalize anchor) := by
  induction k generalizing x with
  | zero => simp [PMF.pure_map]
  | succ k ih =>
    rw [FiniteKernel.eventLaw_succ, FiniteKernel.eventLaw_succ, PMF.map_bind,
      A.normalizedKernel_choiceLaw anchor x]
    congr 1
    funext v
    rw [A.normalizedKernel_next anchor x v]
    exact ih _

/-- Independent Poissonization preserves the quotient intertwining. -/
theorem continuousLaw_normalize (rate t : NNReal) (x : Profile V) :
    (A.normalizedKernel anchor).continuousLaw rate t (normalize anchor x) =
      (A.kernel.continuousLaw rate t x).map (normalize anchor) := by
  unfold FiniteKernel.continuousLaw
  rw [PMF.map_bind]
  congr 1
  funext k
  exact A.eventLaw_normalize anchor k x

/-- The normalized law used for invariant-state corollaries is the law of the
explicit normalized Markov kernel, not a separately postulated dynamics. -/
theorem normalizedTimeLaw_eq (π : PMF (NormalizedProfile anchor)) (t : NNReal) :
    A.normalizedTimeLaw anchor π t =
      (A.normalizedKernel anchor).continuousLawFrom π (Fintype.card E) t := by
  unfold normalizedTimeLaw FiniteKernel.continuousLawFrom
  rw [PMF.bind_map, PMF.map_bind]
  congr 1
  funext x
  have h := A.continuousLaw_normalize anchor (Fintype.card E) t x.val
  rw [normalize_of_normalized] at h
  exact h.symm

end GraphicalAllocation.Process.AllocationRule
