import GraphicalAllocation.Process.FiniteKernel
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact finite path expansion

For h events the sample space is an h-fold finite product of choices. Its weight
is the product of the actual state-dependent transition probabilities, not a
postulated terminal law. Every transition expectation equals this path sum.
-/

namespace GraphicalAllocation.Process

open scoped BigOperators

universe u
/-- A finite sequence of choices, as a recursively associated product. -/
def ChoicePath (Choice : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Choice × ChoicePath Choice n

instance {Choice : Type u} [Fintype Choice] (h : ℕ) : Fintype (ChoicePath Choice h) := by
  induction h with
  | zero => exact PUnit.fintype
  | succ n ih => exact @instFintypeProd Choice (ChoicePath Choice n) _ ih

namespace FiniteKernel
variable {State Choice : Type*} [Fintype Choice]
variable (K : FiniteKernel State Choice)

def pathTerminal : (h : ℕ) → State → ChoicePath Choice h → State
  | 0, x, _ => x
  | h + 1, x, p => pathTerminal h (K.next x p.1) p.2

def pathWeight : (h : ℕ) → State → ChoicePath Choice h → ℝ
  | 0, _, _ => 1
  | h + 1, x, p => K.weight x p.1 * pathWeight h (K.next x p.1) p.2

theorem pathWeight_nonneg (h : ℕ) (x : State) (p : ChoicePath Choice h) :
    0 ≤ K.pathWeight h x p := by
  induction h generalizing x with
  | zero => exact zero_le_one
  | succ h ih => exact mul_nonneg (K.nonneg x p.1) (ih _ p.2)

/-- The path weights form a genuine probability distribution. -/
theorem pathWeight_total (h : ℕ) (x : State) :
    ∑ p, K.pathWeight h x p = 1 := by
  induction h generalizing x with
  | zero =>
    change (∑ _ : PUnit, (1 : ℝ)) = 1
    simp
  | succ h ih =>
    change (∑ p : Choice × ChoicePath Choice h, K.weight x p.1 * K.pathWeight h (K.next x p.1) p.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact K.total x

/-- Exact finite-horizon flattening of the transition operator. -/
theorem iterate_eq_pathSum (h : ℕ) (f : State → ℝ) (x : State) :
    K.iterate h f x = ∑ p, K.pathWeight h x p * f (K.pathTerminal h x p) := by
  induction h generalizing x with
  | zero =>
    change f x = ∑ _ : PUnit, (1 : ℝ) * f x
    simp
  | succ h ih =>
    change K.step (K.iterate h f) x =
      ∑ p : Choice × ChoicePath Choice h,
        (K.weight x p.1 * K.pathWeight h (K.next x p.1) p.2) *
          f (K.pathTerminal h (K.next x p.1) p.2)
    rw [Fintype.sum_prod_type]
    unfold step
    apply Finset.sum_congr rfl
    intro a _
    rw [ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

end FiniteKernel
end GraphicalAllocation.Process
