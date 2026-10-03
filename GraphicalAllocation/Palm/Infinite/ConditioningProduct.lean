import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Probability.ProductMeasure

/-!
# Conditioning independent marks on separate coordinate cells

A finite independent product conditioned on a positive-probability rectangle
remains the independent product of its individually conditioned coordinates.
In particular later coordinate constraints do not change earlier conditional
mark distributions. This is the independence input to selected-path conditioning.
-/

noncomputable section
namespace GraphicalAllocation.Palm.Infinite
open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Normalized restriction to a positive-mass measurable event. -/
def normalizedRestriction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (C : Set α) : Measure α :=
  (μ C)⁻¹ • μ.restrict C

lemma normalizedRestriction_isProbability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (C : Set α) (hC : μ C ≠ 0) : IsProbabilityMeasure (normalizedRestriction μ C) where
  measure_univ := by
    rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hC (measure_ne_top _ _)

variable {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- Exact finite-product conditional factorization. The normalization on the
left is the actual probability of the whole conditioning rectangle. -/
theorem normalized_restrict_pi (μ : (i : I) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : (i : I) → Set (Ω i)) (_hC : ∀ i, MeasurableSet (C i))
    (hpos : ∀ i, μ i (C i) ≠ 0) :
    ((Measure.pi μ) (univ.pi C))⁻¹ • (Measure.pi μ).restrict (univ.pi C) =
      Measure.pi (fun i => normalizedRestriction (μ i) (C i)) := by
  classical
  let (i : I) : IsProbabilityMeasure (normalizedRestriction (μ i) (C i)) :=
    normalizedRestriction_isProbability _ _ (hpos i)
  symm
  apply Measure.pi_eq
  intro T hT
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hT),
    ← Set.pi_inter_distrib, Measure.pi_pi, Measure.pi_pi]
  simp only [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply (hT _), smul_eq_mul]
  rw [Finset.prod_mul_distrib,
    ENNReal.prod_inv_distrib (fun i hi j hj hij => Or.inl (hpos i))]

/-- The conditional marginal at any coordinate depends only on that coordinate's
cell, even when all other independent marks are also conditioned. -/
theorem normalized_restrict_pi_coordinate
    (μ : (i : I) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : (i : I) → Set (Ω i)) (hC : ∀ i, MeasurableSet (C i))
    (hpos : ∀ i, μ i (C i) ≠ 0) (i : I) :
    (((Measure.pi μ) (univ.pi C))⁻¹ •
      (Measure.pi μ).restrict (univ.pi C)).map (fun a => a i) =
        normalizedRestriction (μ i) (C i) := by
  let (j : I) : IsProbabilityMeasure (normalizedRestriction (μ j) (C j)) :=
    normalizedRestriction_isProbability _ _ (hpos j)
  rw [normalized_restrict_pi μ C hC hpos]
  exact (measurePreserving_eval (fun j => normalizedRestriction (μ j) (C j)) i).map_eq


/-- Conditioning an arbitrarily longer finite prefix adds no bias to any earlier
subfamily: its full joint mark law is the shorter normalized restriction. -/
theorem normalized_restrict_pi_subfamily
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : (i : ι) → Set (X i)) (hC : ∀ i, MeasurableSet (C i))
    (hpos : ∀ i, μ i (C i) ≠ 0) (s t : Finset ι) (hst : s ⊆ t) :
    (((Measure.pi (fun i : t => μ i)) (univ.pi (fun i : t => C i)))⁻¹ •
      (Measure.pi (fun i : t => μ i)).restrict (univ.pi (fun i : t => C i))).map
        (Finset.restrict₂ hst) =
    ((Measure.pi (fun i : s => μ i)) (univ.pi (fun i : s => C i)))⁻¹ •
      (Measure.pi (fun i : s => μ i)).restrict (univ.pi (fun i : s => C i)) := by
  let (i : ι) : IsProbabilityMeasure (normalizedRestriction (μ i) (C i)) :=
    normalizedRestriction_isProbability _ _ (hpos i)
  rw [normalized_restrict_pi (fun i : t => μ i) (fun i : t => C i)
      (fun i => hC i) (fun i => hpos i),
    normalized_restrict_pi (fun i : s => μ i) (fun i : s => C i)
      (fun i => hC i) (fun i => hpos i)]
  exact (isProjectiveMeasureFamily_pi (fun i => normalizedRestriction (μ i) (C i)) t s hst).symm


/-- Conditioning the independent infinite product on a finite prefix gives the
same normalized finite product when that whole prefix is observed. -/
theorem normalized_restrict_infinitePi_prefix
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : (i : ι) → Set (X i)) (hC : ∀ i, MeasurableSet (C i))
    (t : Finset ι) (hpos : ∀ i ∈ t, μ i (C i) ≠ 0) :
    (((Measure.infinitePi μ) (Set.pi (t : Set ι) C))⁻¹ •
      (Measure.infinitePi μ).restrict (Set.pi (t : Set ι) C)).map t.restrict =
        Measure.pi (fun i : t => normalizedRestriction (μ i) (C i)) := by
  have htr : Measurable (t.restrict (π := X)) := by fun_prop
  have hevent : Set.pi (t : Set ι) C =
      t.restrict ⁻¹' (univ.pi (fun i : t => C i)) := by
    ext a
    simp
  have hrectangle := MeasurableSet.univ_pi (fun i : t => hC i)
  have hmass : (Measure.infinitePi μ) (Set.pi (t : Set ι) C) =
      (Measure.pi (fun i : t => μ i)) (univ.pi (fun i : t => C i)) := by
    rw [← Measure.infinitePi_map_restrict μ (I := t),
      Measure.map_apply htr hrectangle, ← hevent]
  rw [hmass, Measure.map_smul _ htr.aemeasurable, hevent,
    ← Measure.restrict_map htr hrectangle,
    Measure.infinitePi_map_restrict]
  exact normalized_restrict_pi (fun i : t => μ i) (fun i : t => C i)
    (fun i => hC i) (fun i => hpos i i.2)

/-- After conditioning on any longer selected prefix, every earlier joint
subfamily has exactly its own independently conditioned mark law. Positivity is
required only in the finite conditioning prefix, not at unobserved future cells. -/
theorem normalized_restrict_infinitePi_map
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : (i : ι) → Set (X i)) (hC : ∀ i, MeasurableSet (C i))
    (s t : Finset ι) (hst : s ⊆ t) (hpos : ∀ i ∈ t, μ i (C i) ≠ 0) :
    (((Measure.infinitePi μ) (Set.pi (t : Set ι) C))⁻¹ •
      (Measure.infinitePi μ).restrict (Set.pi (t : Set ι) C)).map s.restrict =
        Measure.pi (fun i : s => normalizedRestriction (μ i) (C i)) := by
  classical
  let ν : (i : ι) → Measure (X i) := fun i =>
    if i ∈ t then normalizedRestriction (μ i) (C i) else μ i
  let (i : ι) : IsProbabilityMeasure (ν i) := by
    dsimp [ν]
    split_ifs with hi
    · exact normalizedRestriction_isProbability _ _ (hpos i hi)
    · infer_instance
  have hs : (fun i : s => ν i) = (fun i : s => normalizedRestriction (μ i) (C i)) := by
    funext i
    simp [ν, hst i.2]
  have ht : (fun i : t => ν i) = (fun i : t => normalizedRestriction (μ i) (C i)) := by
    funext i
    simp [ν, i.2]
  have hproj := (isProjectiveMeasureFamily_pi ν t s hst).symm
  dsimp only at hproj
  rw [hs, ht] at hproj
  have hcomp : s.restrict (π := X) = (Finset.restrict₂ hst) ∘ t.restrict := rfl
  have htr : Measurable (t.restrict (π := X)) := by fun_prop
  have hstr : Measurable (Finset.restrict₂ (π := X) hst) := by fun_prop
  rw [hcomp, ← Measure.map_map hstr htr,
    normalized_restrict_infinitePi_prefix μ C hC t hpos]
  exact hproj

end GraphicalAllocation.Palm.Infinite
