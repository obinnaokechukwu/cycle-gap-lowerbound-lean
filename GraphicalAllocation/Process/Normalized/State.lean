import GraphicalAllocation.Process.Allocation
import GraphicalAllocation.Transport.Clipped

/-!
# Integer-translation classes and anchored representatives

Each normalized state has the unique representative whose chosen anchor has
load zero. This realizes the paper's quotient without choosing random moments
or imposing any bound on the initial gap.
-/

namespace GraphicalAllocation.Process

open Rules Transport

variable {V : Type*} [DecidableEq V]

/-- Subtract the anchor load from every coordinate. -/
def normalizeProfile (anchor : V) (x : Profile V) : Profile V :=
  translate x (-x anchor)

omit [DecidableEq V] in
@[simp] theorem normalizeProfile_anchor (anchor : V) (x : Profile V) :
    normalizeProfile anchor x anchor = 0 := by simp [normalizeProfile, translate]

omit [DecidableEq V] in
@[simp] theorem normalizeProfile_translate (anchor : V) (x : Profile V) (c : ℤ) :
    normalizeProfile anchor (translate x c) = normalizeProfile anchor x := by
  funext v
  simp [normalizeProfile, translate]

omit [DecidableEq V] in
@[simp] theorem normalizeProfile_idempotent (anchor : V) (x : Profile V) :
    normalizeProfile anchor (normalizeProfile anchor x) = normalizeProfile anchor x := by
  exact normalizeProfile_translate anchor x (-x anchor)

/-- Normalization and one-ball updates commute after normalization. -/
theorem normalizeProfile_raise (anchor : V) (x : Profile V) (v : V) :
    normalizeProfile anchor (raise (normalizeProfile anchor x) v) =
      normalizeProfile anchor (raise x v) := by
  funext w
  simp only [normalizeProfile, translate, raise]
  split_ifs <;> omega

/-- The quotient's canonical representative space. -/
abbrev NormalizedProfile (anchor : V) := {x : Profile V // x anchor = 0}

def normalize (anchor : V) (x : Profile V) : NormalizedProfile anchor :=
  ⟨normalizeProfile anchor x, normalizeProfile_anchor anchor x⟩

omit [DecidableEq V] in
@[simp] theorem normalize_coe (anchor : V) (x : Profile V) :
    (normalize anchor x).val = normalizeProfile anchor x := rfl

omit [DecidableEq V] in
@[simp] theorem normalize_of_normalized (anchor : V) (x : NormalizedProfile anchor) :
    normalize anchor x.val = x := by
  apply Subtype.ext
  funext v
  simp [normalize, normalizeProfile, translate, x.property]

omit [DecidableEq V] in
/-- Equality of representatives is exactly common-integer-translation equivalence. -/
theorem normalize_eq_iff (anchor : V) (x y : Profile V) :
    normalize anchor x = normalize anchor y ↔ ∃ c : ℤ, y = translate x c := by
  constructor
  · intro h
    refine ⟨y anchor - x anchor, ?_⟩
    funext v
    have hv := congrArg (fun z : NormalizedProfile anchor => z.val v) h
    simp only [normalize, normalizeProfile, translate] at hv ⊢
    omega
  · rintro ⟨c, rfl⟩
    apply Subtype.ext
    exact (normalizeProfile_translate anchor x c).symm

/-- The integer common-translation equivalence relation. -/
def translationSetoid (anchor : V) : Setoid (Profile V) :=
  Setoid.ker (normalize anchor)

/-- A quotient class and its canonical anchored representative carry identical data. -/
def quotientEquivNormalized (anchor : V) :
    Quotient (translationSetoid anchor) ≃ NormalizedProfile anchor where
  toFun := Quotient.lift (normalize anchor) (fun _ _ h => h)
  invFun x := Quotient.mk _ x.val
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    exact congrArg (normalize anchor) (rfl : (normalize anchor x).val = normalizeProfile anchor x) |>.trans (by
      apply Subtype.ext
      exact normalizeProfile_idempotent anchor x)
  right_inv := normalize_of_normalized anchor

section Gap
variable [Fintype V] [Nonempty V]
omit [DecidableEq V] in
@[simp] theorem gap_normalize (anchor : V) (x : Profile V) :
    gap (normalize anchor x).val = gap x := by
  exact gap_translate x (-x anchor)
end Gap

end GraphicalAllocation.Process
