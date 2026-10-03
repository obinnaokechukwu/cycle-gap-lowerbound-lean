import GraphicalAllocation.Diffusion.AllocationHilbert
import GraphicalAllocation.Diffusion.CycleEstimate

/-! # Proposition 4.3 for the actual cycle allocation tag

The four-fiber mass and Fourier cell radius are instantiated to the genuine
finite marked experiment, averaged over selected histories, and Poissonized.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators NNReal
open MeasureTheory Rules Palm Process Geometry SimpleGraph

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Actual cycle closed neighborhoods along a selected path. -/
def cyclePathNeighborhood (n : ℕ) (js : List (Fin (n + 3))) (k : ℕ) : Finset (Fin (n + 3)) :=
  match js[k]? with
  | none => ∅
  | some j => insert j ((cycleGraph (n + 3)).neighborFinset j)

lemma cycle_endpoints_mem_neighborhood (n : ℕ) (j e : Fin (n + 3))
    (he : (cycleOrientation n).tail e = j ∨ (cycleOrientation n).head e = j) :
    (cycleOrientation n).tail e ∈ insert j ((cycleGraph (n + 3)).neighborFinset j) ∧
      (cycleOrientation n).head e ∈ insert j ((cycleGraph (n + 3)).neighborFinset j) := by
  have ha := cycleOrientation_adj n e
  rcases he with ht | hh
  · rw [ht] at ha ⊢
    exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr ha)⟩
  · rw [hh] at ha ⊢
    exact ⟨Finset.mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr ha.symm), Finset.mem_insert_self _ _⟩

/-- Every genuine independent marked experiment with the uniform cyclic edge
marginal obeys the sharp conditional bound. -/
theorem marked_path_cycle_displacement_le (n : ℕ)
    (F : FiniteMarks (Fin (n + 3)) M) (hpos : ∀ a, 0 < F.weight a)
    (edge : M → Fin (n + 3))
    (hfirst : ∀ a, (F.event a).first = (cycleOrientation n).tail (edge a))
    (hsecond : ∀ a, (F.event a).second = (cycleOrientation n).head (edge a))
    (hedgeMass : ∀ T : Finset (Fin (n + 3)),
      (∑ a, if edge a ∈ T then F.weight a else 0) = (T.card : ℝ) / (n + 3))
    (x : Profile (Fin (n + 3))) (js : List (Fin (n + 3))) :
    (∑ i, ∑ j, cellMass F.weight (experimentSelector F x) i * pathTag F x js i j *
      ((cycleGraph (n + 3)).dist i j : ℝ) ^ 2) ≤ 2 * Real.pi ^ 2 * js.length / (n + 3) + 2 := by
  have hend : ∀ k a, pathPartitions F x js k a = (cycleOrientation n).tail (edge a) ∨
      pathPartitions F x js k a = (cycleOrientation n).head (edge a) := by
    intro k a
    have he := experimentSelector_endpoint F (pathFinal x (js.take k)) a
    rw [hfirst, hsecond] at he
    exact he
  have houtside : ∀ k a, pathPartitions F x js (k + 1) a ∉ cyclePathNeighborhood n js k →
      pathPartitions F x js k a = pathPartitions F x js (k + 1) a := by
    intro k a ha
    simp only [pathPartitions, pathFinal_take_succ] at ha ⊢
    cases hj : js[k]? with
    | none => simp []
    | some j =>
      simp only [hj] at ha ⊢
      refine experimentSelector_outside F _ j (insert j ((cycleGraph (n + 3)).neighborFinset j)) ?_ a ?_
      · intro b hb
        rw [hfirst, hsecond] at hb ⊢
        exact cycle_endpoints_mem_neighborhood n j (edge b) hb
      · simpa [cyclePathNeighborhood, hj] using ha
  have hmass : ∀ k, (∑ a, if pathPartitions F x js (k + 1) a ∈ cyclePathNeighborhood n js k then F.weight a else 0) ≤
      4 / (n + 3) := by
    intro k
    cases hj : js[k]? with
    | none => simp [cyclePathNeighborhood, hj]; positivity
    | some j =>
      simp only [cyclePathNeighborhood, hj]
      calc
        _ ≤ ∑ a, if edge a ∈ fourCycleFibers n j then F.weight a else 0 := by
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : pathPartitions F x js (k + 1) a ∈ insert j ((cycleGraph (n + 3)).neighborFinset j)
          · have he := incident_closedNeighborhood_mem_fourCycleFibers n j _ (edge a) ha (hend (k + 1) a)
            simp [ha, he]
          · simp only [ha, ite_false]
            split_ifs
            · exact F.nonneg a
            · exact le_refl 0
        _ = (fourCycleFibers n j).card / (n + 3 : ℝ) := hedgeMass _
        _ ≤ 4 / (n + 3 : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast card_fourCycleFibers_le n j) (by positivity)
  have h := cycle_tag_displacement_le n hpos F.total edge (pathPartitions F x js)
    (cyclePathNeighborhood n js) hend houtside hmass js.length
  simpa only [pathPartitions_zero, ← pathTag_eq_tagEvolution] using h

/-- Unconditional sharp cycle diffusion for the independently sampled marks. -/
theorem marked_cycle_displacement_le (n : ℕ)
    (F : FiniteMarks (Fin (n + 3)) M) (hpos : ∀ a, 0 < F.weight a)
    (edge : M → Fin (n + 3))
    (hfirst : ∀ a, (F.event a).first = (cycleOrientation n).tail (edge a))
    (hsecond : ∀ a, (F.event a).second = (cycleOrientation n).head (edge a))
    (hedgeMass : ∀ T : Finset (Fin (n + 3)),
      (∑ a, if edge a ∈ T then F.weight a else 0) = (T.card : ℝ) / (n + 3))
    (x : Profile (Fin (n + 3))) (h : ℕ) :
    (∑ i, cellMass F.weight (experimentSelector F x) i *
      F.tagged.iterate h (fun y => ((cycleGraph (n + 3)).dist i y.2 : ℝ) ^ 2) (x, i)) ≤
        2 * Real.pi ^ 2 * h / (n + 3) + 2 := by
  simp_rw [tagged_iterate_eq_pathAverage, ← pathAverage_mul]
  rw [← pathAverage_sum]
  apply pathAverage_le
  intro js hjs
  simp only [Finset.mul_sum]
  have hb := marked_path_cycle_displacement_le n F hpos edge hfirst hsecond hedgeMass x js
  simpa only [hjs, mul_assoc] using hb

/-- Literal squared graph-distance moment of the actual source-Palm tag. -/
def allocationCycleMoment (n : ℕ) (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (x : Profile (Fin (n + 3))) (h : ℕ) : ℝ :=
  ∑ i, A.kernel.weight x i * (A.horizonMarks x h).tagged.iterate h
    (fun y => ((cycleGraph (n + 3)).dist i y.2 : ℝ) ^ 2) (x, i)

lemma allocationCycleMoment_nonneg (n : ℕ) (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (x : Profile (Fin (n + 3))) (h : ℕ) : 0 ≤ allocationCycleMoment n A x h := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (A.kernel.nonneg x i)
    ((A.horizonMarks x h).tagged.iterate_nonneg h (fun y => sq_nonneg _) (x, i))

/-- Proposition 4.3, exact event-count form, on the actual canonical cycle.
The n parameter is N-3, so this covers every N≥3 including N=3 and N=4. -/
theorem allocation_cycle_displacement_events (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (x : Profile (Fin (n + 3))) (h : ℕ) :
    allocationCycleMoment n A x h ≤ 2 * Real.pi ^ 2 * h / (n + 3) + 2 := by
  have ht : A.tail = (cycleOrientation n).tail := congrArg OrientedGraph.tail hA
  have hh : A.head = (cycleOrientation n).head := congrArg OrientedGraph.head hA
  have hb := marked_cycle_displacement_le n (A.horizonMarks x h)
    (A.finiteEvent_weight_pos _) (fun a => a.val.1)
    (by intro a; rw [finiteMarks_first, ht])
    (by intro a; rw [finiteMarks_second, hh])
    (by intro T; simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, AllocationRule.horizonMarks, AllocationRule.finiteMarks] using A.finiteMark_edge_set_mass (profileFamily x (h + 1)) T)
    x h
  simpa only [horizonMarks_initial_cellMass, allocationCycleMoment] using hb

/-- Proposition 4.3, physical-time form with the exact rate-N Poisson count. -/
theorem allocation_cycle_displacement_physical (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (x : Profile (Fin (n + 3))) (s : ℝ≥0) :
    (∫ h, allocationCycleMoment n A x h ∂ProbabilityTheory.poissonMeasure ((n + 3 : ℝ≥0) * s)) ≤
      2 * Real.pi ^ 2 * s + 2 := by
  have hb := poisson_event_to_physical (n + 3) (by omega) s
    (allocationCycleMoment n A x) (2 * Real.pi ^ 2) 2
    (allocationCycleMoment_nonneg n A x) (by
      intro h
      simpa only [Nat.cast_add, Nat.cast_ofNat] using allocation_cycle_displacement_events n A hA x h)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hb.2

end GraphicalAllocation.Diffusion
