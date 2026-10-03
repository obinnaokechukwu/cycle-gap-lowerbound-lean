import GraphicalAllocation.Diffusion.FiniteSignature
import GraphicalAllocation.Diffusion.Neighborhood
import GraphicalAllocation.Palm.SelectedPath

/-! # Hilbert diffusion for the genuine independent marked experiment

The estimate is proved first along every selected base path, then integrated
using the exact selected-path decomposition of the synchronous tag process.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators
open Rules Palm Projections Process

variable {M V E : Type*} [Fintype M] [DecidableEq M]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq M] [Fintype V] in
lemma experimentSelector_endpoint (F : FiniteMarks V M) (x : Profile V) (a : M) :
    experimentSelector F x a = (F.event a).first ∨ experimentSelector F x a = (F.event a).second := by
  unfold experimentSelector selected
  split <;> simp

omit [DecidableEq M] [Fintype V] in
lemma experimentSelector_outside (F : FiniteMarks V M) (x : Profile V) (j : V)
    (S : Finset V)
    (hS : ∀ a, (F.event a).first = j ∨ (F.event a).second = j →
      (F.event a).first ∈ S ∧ (F.event a).second ∈ S)
    (a : M) (ha : experimentSelector F (raise x j) a ∉ S) :
    experimentSelector F x a = experimentSelector F (raise x j) a := by
  have ho : experimentSelector F x a ≠ j := by
    intro hj
    have he : (F.event a).first = j ∨ (F.event a).second = j := by
      rcases experimentSelector_endpoint F x a with h | h
      · exact Or.inl (h.symm.trans hj)
      · exact Or.inr (h.symm.trans hj)
    have hends := hS a he
    rcases experimentSelector_endpoint F (raise x j) a with h | h
    · exact ha (h ▸ hends.1)
    · exact ha (h ▸ hends.2)
  exact (experimentSelector_changes F x j a ho).symm

omit [DecidableEq M] [Fintype V] in
lemma selector_mass_le_incident (F : FiniteMarks V M) (x : Profile V) (v : V) :
    cellMass F.weight (experimentSelector F x) v ≤
      ∑ a, if (F.event a).first = v ∨ (F.event a).second = v then F.weight a else 0 := by
  unfold cellMass
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : experimentSelector F x a = v
  · have he : (F.event a).first = v ∨ (F.event a).second = v := by
      rcases experimentSelector_endpoint F x a with h | h
      · exact Or.inl (h.symm.trans ha)
      · exact Or.inr (h.symm.trans ha)
    simp [ha, he]
  · simp only [ha, ite_false]
    split_ifs
    · exact F.nonneg a
    · exact le_refl 0

omit [DecidableEq M] [Fintype V] in
lemma selector_set_mass (F : FiniteMarks V M) (x : Profile V) (S : Finset V) :
    (∑ a, if experimentSelector F x a ∈ S then F.weight a else 0) =
      ∑ v ∈ S, cellMass F.weight (experimentSelector F x) v := by
  unfold cellMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

omit [DecidableEq M] [Fintype V] in
lemma selector_set_mass_le (F : FiniteMarks V M) (x : Profile V) (S : Finset V)
    (D : ℝ) (_hD : 0 ≤ D)
    (hinc : ∀ v, (∑ a, if (F.event a).first = v ∨ (F.event a).second = v then F.weight a else 0) ≤ D) :
    (∑ a, if experimentSelector F x a ∈ S then F.weight a else 0) ≤ S.card * D := by
  rw [selector_set_mass]
  calc
    _ ≤ ∑ v ∈ S, D := Finset.sum_le_sum fun v _ =>
      (selector_mass_le_incident F x v).trans (hinc v)
    _ = _ := by simp

omit [Fintype V] in
lemma pathFinal_append (x : Profile V) (xs ys : List V) :
    pathFinal x (xs ++ ys) = pathFinal (pathFinal x xs) ys := by
  induction xs generalizing x with
  | nil => rfl
  | cons v xs ih => simpa only [List.cons_append, pathFinal] using ih (raise x v)

/-- The cells localized by the next selected allocation, or none after the end. -/
def pathNeighborhood (A : AllocationRule V E) (js : List V) (k : ℕ) : Finset V :=
  match js[k]? with
  | none => ∅
  | some j => A.closedNeighborhood j

omit [Fintype V] in
lemma pathFinal_take_succ (x : Profile V) (js : List V) (k : ℕ) :
    pathFinal x (js.take (k + 1)) =
      match js[k]? with
      | none => pathFinal x (js.take k)
      | some j => raise (pathFinal x (js.take k)) j := by
  rw [List.take_add_one]
  rw [pathFinal_append]
  cases h : js[k]? <;> simp [pathFinal]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [DecidableEq E] in
/-- Conditional Hilbert estimate along every selected path of actual events.
The graph-degree and uniform-edge hypotheses do not assert any diffusion bound. -/
theorem marked_path_hilbert_displacement_le (A : AllocationRule V E)
    (F : FiniteMarks V M) (hpos : ∀ a, 0 < F.weight a)
    (edge : M → E) (hfirst : ∀ a, (F.event a).first = A.tail (edge a))
    (hsecond : ∀ a, (F.event a).second = A.head (edge a))
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ) (m : ℝ) (hm : 0 < m)
    (hinc : ∀ v, (∑ a, if (F.event a).first = v ∨ (F.event a).second = v then F.weight a else 0) ≤ Δ / m)
    (f : V → H) (η : ℝ) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (x : Profile V) (js : List V) :
    (∑ i, ∑ j, cellMass F.weight (experimentSelector F x) i * pathTag F x js i j * ‖f j - f i‖ ^ 2) ≤
      2 * η ^ 2 * ((Δ : ℝ) * (Δ + 1) / m) * js.length + 2 * η ^ 2 := by
  let g : M → H := fun a => Geometry.edgeMidpoint (f (A.tail (edge a))) (f (A.head (edge a)))
  have hcell : ∀ k a, ‖g a - f (pathPartitions F x js k a)‖ ≤ η / 2 := by
    intro k a
    rcases experimentSelector_endpoint F (pathFinal x (js.take k)) a with h | h
    · change ‖g a - f (experimentSelector F (pathFinal x (js.take k)) a)‖ ≤ _
      rw [h, hfirst]
      change ‖Geometry.edgeMidpoint (f (A.tail (edge a))) (f (A.head (edge a))) - f (A.tail (edge a))‖ ≤ η / 2
      rw [Geometry.norm_edgeMidpoint_sub_left, norm_sub_rev]
      exact div_le_div_of_nonneg_right (hedge _) (by norm_num)
    · change ‖g a - f (experimentSelector F (pathFinal x (js.take k)) a)‖ ≤ _
      rw [h, hsecond]
      change ‖Geometry.edgeMidpoint (f (A.tail (edge a))) (f (A.head (edge a))) - f (A.head (edge a))‖ ≤ η / 2
      rw [Geometry.norm_edgeMidpoint_sub_right]
      exact div_le_div_of_nonneg_right (hedge _) (by norm_num)
  have houtside : ∀ k a, pathPartitions F x js (k + 1) a ∉ pathNeighborhood A js k →
      pathPartitions F x js k a = pathPartitions F x js (k + 1) a := by
    intro k a ha
    simp only [pathPartitions, pathFinal_take_succ] at ha ⊢
    cases hj : js[k]? with
    | none => simp []
    | some j =>
      simp only [hj] at ha ⊢
      refine experimentSelector_outside F _ j (A.closedNeighborhood j) ?_ a ?_
      · intro b hb
        rw [hfirst, hsecond] at hb ⊢
        exact A.endpoints_mem_closedNeighborhood j (edge b) hb
      · simpa [pathNeighborhood, hj] using ha
  have hmass : ∀ k, (∑ a, if pathPartitions F x js (k + 1) a ∈ pathNeighborhood A js k then F.weight a else 0) ≤
      (Δ : ℝ) * (Δ + 1) / m := by
    intro k
    cases hj : js[k]? with
    | none => simp [pathNeighborhood, hj]; positivity
    | some j =>
      simp only [pathNeighborhood, hj]
      have hb := selector_set_mass_le F (pathFinal x (js.take (k + 1)))
        (A.closedNeighborhood j) (Δ / m) (by positivity) hinc
      change (∑ a, if experimentSelector F (pathFinal x (js.take (k + 1))) a ∈ A.closedNeighborhood j then F.weight a else 0) ≤ _
      refine hb.trans ?_
      have hc : ((A.closedNeighborhood j).card : ℝ) ≤ Δ + 1 := by
        exact_mod_cast (A.closedNeighborhood_card_le j).trans (Nat.add_le_add_right (hΔ j) 1)
      calc
        _ ≤ (Δ + 1 : ℝ) * (Δ / m) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring
  have h := local_tag_displacement_le hpos F.total (pathPartitions F x js)
    (pathNeighborhood A js) houtside f g η ((Δ : ℝ) * (Δ + 1) / m) hcell hmass js.length
  simpa only [pathPartitions_zero, ← pathTag_eq_tagEvolution] using h

omit [DecidableEq M] in
lemma pathAverage_le (F : FiniteMarks V M) (x : Profile V) (n : ℕ)
    (B : List V → ℝ) (C : ℝ) (hB : ∀ js, js.length = n → B js ≤ C) :
    pathAverage F x n B ≤ C := by
  induction n generalizing x B with
  | zero => exact hB [] rfl
  | succ n ih =>
    rw [pathAverage]
    calc
      _ ≤ ∑ j, cellMass F.weight (experimentSelector F x) j * C := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (cellMass_nonneg F.nonneg _ j)
        apply ih (raise x j) (fun js => B (j :: js))
        intro js hjs
        exact hB (j :: js) (by simp [hjs])
      _ = C := by rw [← Finset.sum_mul, cellMass_sum, F.total, one_mul]

omit [DecidableEq E] in
/-- The actual synchronous tagged experiment is averaged over selected base
histories; the initial tag and the final tag both remain in the observable. -/
theorem marked_hilbert_displacement_le (A : AllocationRule V E)
    (F : FiniteMarks V M) (hpos : ∀ a, 0 < F.weight a)
    (edge : M → E) (hfirst : ∀ a, (F.event a).first = A.tail (edge a))
    (hsecond : ∀ a, (F.event a).second = A.head (edge a))
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ) (m : ℝ) (hm : 0 < m)
    (hinc : ∀ v, (∑ a, if (F.event a).first = v ∨ (F.event a).second = v then F.weight a else 0) ≤ Δ / m)
    (f : V → H) (η : ℝ) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (x : Profile V) (n : ℕ) :
    (∑ i, cellMass F.weight (experimentSelector F x) i *
      F.tagged.iterate n (fun y => ‖f y.2 - f i‖ ^ 2) (x, i)) ≤
      2 * η ^ 2 * ((Δ : ℝ) * (Δ + 1) / m) * n + 2 * η ^ 2 := by
  simp_rw [tagged_iterate_eq_pathAverage, ← pathAverage_mul]
  rw [← pathAverage_sum]
  apply pathAverage_le
  intro js hjs
  simp only [Finset.mul_sum]
  have h := marked_path_hilbert_displacement_le A F hpos edge hfirst hsecond
    Δ hΔ m hm hinc f η hedge x js
  simpa only [hjs, mul_assoc] using h

end GraphicalAllocation.Diffusion
