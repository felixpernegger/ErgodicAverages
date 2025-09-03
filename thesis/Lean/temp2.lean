import Mathlib
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.commandStart false
open Function Set Classical
noncomputable section


def icoset (ι : Type*) [Fintype ι] (a b : ℤ): Set (ι → ℤ) :=
  {k | ∀ i, a ≤ k i ∧ k i < b}

theorem icoset_encard
    (a b : ℤ) (ι : Type*) [Fintype ι]:
    encard (α := ι → ℤ) (icoset ι a b) = (b - a).toNat^(Fintype.card ι) := by --yesssss
  suffices : icoset ι a b ≃ @Fintype.piFinset ι _ _ (fun _ ↦ ℤ) (fun _ ↦ (Ico a b).toFinset)
  · suffices ass: encard (↑(@Fintype.piFinset ι _ _ (fun _ ↦ ℤ) (fun _ ↦ (Ico a b).toFinset)) : Set (ι → ℤ)) = (b - a).toNat^(Fintype.card ι)
    · rw[← ass]
      exact encard_congr this
    rw[Set.encard_eq_coe_toFinset_card]
    simp
  unfold icoset
  simp
  rfl

instance icoset_fintype (a b : ℤ) (ι : Type*) [Fintype ι] : Fintype (icoset ι a b) := by
  refine Finite.fintype ?_
  refine encard_lt_top_iff.mp ?_
  rw[icoset_encard]
  simp

/-
suffices : @bound_set ι N ≃ @Fintype.piFinset ι _ _ (fun _ ↦ ℕ) (fun _ ↦ Finset.range N)
  · suffices ass: encard (↑(@Fintype.piFinset ι _ _ (fun _ ↦ ℕ) (fun _ ↦ Finset.range N)) : Set (ι → ℕ)) = N^(Fintype.card ι)
    · rw[← ass]
      exact encard_congr this
    rw[Set.encard_eq_coe_toFinset_card]
    simp
  unfold bound_set
  simp
  rfl
-/
