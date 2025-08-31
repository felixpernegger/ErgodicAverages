import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
open Function Set Classical MeasureTheory
noncomputable section

namespace Calderon
open ENNReal Real

variable{ι : Type*}[Fintype ι]

example : 0 = 0 := sorry

theorem fact5_1(F : ι → (ι → ℝ) → ℝ)(t : NNReal)(x : ι → ℝ):
  multilinear_avg_spec F t x = (1/t) * ∫⁻ (s : ℝ) in Ico (∑ (i : ι), x i) ((∑ (i : ι), x i) + t), ‖∏(j : ι), (F j) (x + Calderon.unit j (s - 2*(x j)))‖ₑ := by
    sorry

theorem fact5_5{X : Type*}(f : ι → X → ℝ){S : ι → X → X}(hS: pairwise_commuting S)(n N: ℕ)(hN: 2*n+1 < N):
  nergodic_avg n S f = discrete_avg n (push_forward_many N f S)
