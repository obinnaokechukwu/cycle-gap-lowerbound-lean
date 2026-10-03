import GraphicalAllocation.Palm.ProjectionRepresentation
import GraphicalAllocation.Projections.EndpointChain

/-! # Joint-law projection representation

The Palm marginal alone does not bound tag displacement. This file proves the
joint initial/final vertex law of the localized mark chain, and hence transfers
all two-endpoint observables to the actual cell-overlap tag evolution.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators Matrix
open Palm Projections

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

/-- Every two-endpoint observable has the same expectation in the localized
mark chain and the Palm-initialized tag chain. -/
theorem endpointJoint_observable {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → V) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (n : ℕ) (D : V → V → ℝ) :
    (∑ a, ∑ b, endpointJoint μ
      (fun k => cellKernel μ (localKey (p (k + 1)) (S k))) n a b * D (p 0 a) (p n b)) =
      ∑ i, ∑ j, cellMass μ (p 0) i * tagEvolution μ p n i j * D i j := by
  simp_rw [← tag_mark_endpoint_joint hμ p S houtside n, Finset.sum_mul]
  conv_rhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  simp [ite_and, ite_mul]

/-- Hilbert displacement for the explicitly constructed Palm tag transition law.
The hypotheses describe local cell geometry; the tag bound is a conclusion. -/
theorem local_tag_displacement_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (hμmass : ∑ a, μ a = 1) (p : ℕ → A → V) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : V → H) (g : A → H) (η M : ℝ)
    (hcell : ∀ k a, ‖g a - F (p k a)‖ ≤ η / 2)
    (hmass : ∀ k, (∑ a, if p (k + 1) a ∈ S k then μ a else 0) ≤ M)
    (n : ℕ) :
    (∑ i, ∑ j, cellMass μ (p 0) i * tagEvolution μ p n i j * ‖F j - F i‖ ^ 2) ≤
      2 * η ^ 2 * M * (n : ℝ) + 2 * η ^ 2 := by
  rw [← endpointJoint_observable hμ p S houtside n (fun i j => ‖F j - F i‖ ^ 2)]
  exact local_endpoint_displacement_le hμ hμmass (fun k => p (k + 1)) S g
    (fun a => F (p 0 a)) (fun b => F (p n b)) (fun _ => F) η M
    (fun k a _ => hcell (k + 1) a) hmass
    (fun a => by simpa only [norm_sub_rev] using hcell 0 a)
    (fun b => by simpa only [norm_sub_rev] using hcell n b) n

end GraphicalAllocation.Diffusion
