import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
open Function Set Classical MeasureTheory ENNReal NNReal
noncomputable section

variable{ι X Y Z : Type*} [Fintype ι] [MeasurableSpace Z] (μ : Measure Z)

instance : EDist ℝ≥0∞ where
  edist := fun x y ↦ (x - y) + (y - x)

theorem ennreal_edist_self (x : ℝ≥0∞) : edist x x = 0 := by
  unfold edist instEDistENNReal_thesis
  simp only [tsub_self, add_zero]

theorem ennreal_edist_le {x y : ℝ≥0∞} (h : y ≤ x) : edist x y = x - y := by
  unfold edist instEDistENNReal_thesis
  simp only [tsub_eq_zero_of_le h, add_zero]

theorem ennreal_edist_symm (x y : ℝ≥0∞) : edist x y = edist y x := by
  unfold edist instEDistENNReal_thesis
  simp only
  rw[add_comm]

theorem ennreal_edist_le' {x y : ℝ≥0∞} (h : x ≤ y) : edist x y = y - x := by
  rw[ennreal_edist_symm, ennreal_edist_le h]

theorem ennreal_edist_triangle (x y z : ℝ≥0∞) : edist x z ≤ edist x y + edist y z := by
  unfold edist instEDistENNReal_thesis
  simp only
  by_cases xy: x ≤ y
  · simp only [tsub_eq_zero_of_le xy, zero_add]
    by_cases yz: y ≤ z
    · simp only [tsub_eq_zero_of_le (le_trans xy yz), zero_add, tsub_eq_zero_of_le yz,
        tsub_le_iff_right]
      rw [@add_right_comm, tsub_add_cancel_of_le xy, add_tsub_cancel_of_le yz]
    simp only [not_le] at yz
    apply le_of_lt at yz
    simp only [tsub_eq_zero_of_le yz, add_zero]
    rw[add_comm]
    gcongr
  simp only [not_le] at xy
  apply le_of_lt at xy
  simp only [tsub_eq_zero_of_le xy, add_zero]
  by_cases yz: y ≤ z
  · simp only [tsub_eq_zero_of_le yz, zero_add]
    gcongr
  simp only [not_le] at yz
  apply le_of_lt at yz
  simp only [tsub_eq_zero_of_le yz, tsub_eq_zero_of_le (le_trans yz xy), add_zero,
    tsub_add_tsub_cancel xy yz, le_refl]

theorem ennreal_edist_zero (x : ℝ≥0∞) : edist x 0 = x := by
  unfold edist instEDistENNReal_thesis
  simp only [tsub_zero, zero_tsub, add_zero]

theorem ennreal_edist_zero' {x y : ℝ≥0∞} (h : edist x y = 0) : x = y := by
  by_cases xy : x ≤ y
  · apply le_antisymm
    · exact xy
    rw[ennreal_edist_le' xy] at h
    exact tsub_eq_zero_iff_le.mp h
  apply le_antisymm
  · simp only [not_le] at xy
    rw[ennreal_edist_le (le_of_lt xy)] at h
    exact tsub_eq_zero_iff_le.mp h
  exact le_of_not_ge xy

theorem ennreaL_edist_mul {x y t : ℝ≥0∞} (h : t ≠ ∞): edist (t*x) (t*y) = t * edist x y := by
  unfold edist instEDistENNReal_thesis
  simp only
  rw [← ENNReal.mul_sub fun a a ↦ h]
  rw[← ENNReal.mul_sub]
  · exact Eq.symm (LeftDistribClass.left_distrib t (x - y) (y - x))
  tauto

theorem ennreal_edist_add (x y z v : ℝ≥0∞) : edist (x + z) (y + v) ≤ edist x y + edist z v := by
  by_cases xy : x ≤ y
  · rw [ennreal_edist_le' xy]
    by_cases zv : z ≤ v
    · rw[ennreal_edist_le' zv]
      rw[ennreal_edist_le' (add_le_add xy zv)]
      exact add_tsub_add_le_tsub_add_tsub
    simp only [not_le] at zv
    apply le_of_lt at zv
    rw [ennreal_edist_le zv]
    by_cases h : x + z ≤ y + v
    · rw[ennreal_edist_le' h]
      rw [@tsub_add_eq_tsub_tsub_swap, tsub_right_comm]
      calc
        y + v - x - z
          ≤ y - x + v - z := by
          gcongr
          exact add_tsub_le_tsub_add
        _ ≤ y - x + (z - v) := by
          refine le_add_of_le_of_nonneg ?_ ?_
          · refine (OrderedSub.tsub_le_iff_right (y - x + v) z (y - x)).mpr ?_
            gcongr
          exact zero_le (z - v)
    simp only [not_le] at h
    apply le_of_lt at h
    rw[ennreal_edist_le h]
    rw [tsub_add_eq_tsub_tsub_swap]
    refine tsub_le_iff_left.mpr ?_
    refine tsub_le_iff_right.mpr ?_
    rw [add_assoc]
    gcongr
    rw[add_assoc]
    refine le_add_of_nonneg_of_le ?_ ?_
    · exact zero_le (y - x)
    exact le_tsub_add
  simp at xy
  apply le_of_lt at xy
  rw[ennreal_edist_le xy]
  by_cases zv : z ≤ v
  · rw [ennreal_edist_le' zv]
    by_cases h : x + z ≤ y + v
    · rw[ennreal_edist_le' h]
      rw [tsub_add_eq_tsub_tsub_swap]
      refine tsub_le_iff_left.mpr ?_
      refine tsub_le_iff_right.mpr ?_
      rw [add_assoc]
      gcongr
      rw[add_assoc]
      refine le_add_of_nonneg_of_le ?_ ?_
      · exact zero_le (x - y)
      exact le_tsub_add
    simp only [not_le] at h
    apply le_of_lt at h
    rw[ennreal_edist_le h]
    rw [@tsub_add_eq_tsub_tsub_swap, tsub_right_comm]
    calc
      x + z - y - v
        ≤ x - y + z - v := by
          refine tsub_le_tsub_right ?_ v
          exact add_tsub_le_tsub_add
      _ ≤ x - y + (v - z) := by
          refine le_add_of_le_of_nonneg ?_ ?_
          · refine (OrderedSub.tsub_le_iff_right (x - y + z) v (x - y)).mpr ?_
            gcongr
          exact zero_le (v - z)
  simp only [not_le] at zv
  apply le_of_lt at zv
  rw[ennreal_edist_le zv, ennreal_edist_le (add_le_add xy zv)]
  exact add_tsub_add_le_tsub_add_tsub

theorem le_edist (a b : ℝ≥0∞) : a - b ≤ edist a b := by
  unfold edist instEDistENNReal_thesis
  simp only
  exact le_self_add

theorem le_edist' (a b : ℝ≥0∞) : b - a ≤ edist a b := by
  unfold edist instEDistENNReal_thesis
  simp only
  exact le_add_self

theorem le_edist'' {a b t : ℝ≥0∞} (h : a - b ≤ t) (h' : b - a ≤ t) : edist a b ≤ t := by
  by_cases ab: a ≤ b
  · rw[ennreal_edist_le' ab]
    exact h'
  simp only [not_le] at ab
  apply le_of_lt at ab
  rw [ennreal_edist_le ab]
  exact h

theorem ennreal_edist_add_const (a b : ℝ≥0∞) {c : ℝ≥0∞} (h : c ≠ ∞) :
    edist (a + c) (b + c) = edist a b := by
  by_cases ab : a ≤ b
  · rw[ennreal_edist_le' ab]
    rw[ennreal_edist_le' ((ENNReal.add_le_add_iff_right h).mpr ab)]
    rw [@tsub_add_eq_tsub_tsub_swap]
    rw [ENNReal.add_sub_cancel_right h]
  simp only [not_le] at ab
  apply le_of_lt at ab
  rw[ennreal_edist_le ab]
  rw[ennreal_edist_le ((ENNReal.add_le_add_iff_right h).mpr ab)]
  rw [@tsub_add_eq_tsub_tsub_swap]
  rw [ENNReal.add_sub_cancel_right h]

lemma ennreal_edist_sub_edist_le_edist' (a b c d : ℝ≥0∞) (h : c ≠ ∞ ∨ d ≠ ∞) :
    (edist a b) - (edist c d) ≤ edist (a + d) (b + c) := by
  refine (OrderedSub.tsub_le_iff_right (edist a b) (edist c d) (edist (a + d) (b + c))).mpr ?_
  by_cases ci: c = ∞
  · unfold edist instEDistENNReal_thesis
    simp only
    rw[ci]
    simp only [add_top, sub_top, zero_add, add_zero]
    have : ⊤ - d = ⊤ := by
      simp only [sub_eq_top_iff, ne_eq, true_and]
      tauto
    rw[this]
    simp only [add_top, le_top]
  by_cases di: d = ∞
  · unfold edist instEDistENNReal_thesis
    simp only
    rw[di]
    simp only [add_top, sub_top, zero_add, add_zero]
    have : ⊤ - c = ⊤ := by
      simp only [sub_eq_top_iff, ne_eq, true_and]
      tauto
    rw[this]
    simp only [add_top, le_top]
  have : c + d ≠ ∞ := by simp_all only [ne_eq, not_false_eq_true, or_self, add_eq_top]
  rw[← ennreal_edist_add_const a b this]
  have : a + (c + d) = a + d + c := by ring
  rw[this]
  rw[← add_assoc]
  exact ennreal_edist_add (a + d) (b + c) c d



lemma ennreal_edist_of_edist_edist_le_edist (a b c d : ℝ≥0∞) (h : c ≠ ∞ ∨ d ≠ ∞) (h' : a ≠ ∞ ∨ b ≠ ∞):
    edist (edist a b) (edist c d) ≤ edist (a + d) (b + c) := by
  apply le_edist''
  · exact ennreal_edist_sub_edist_le_edist' a b c d h
  rw[ennreal_edist_symm (a + d), add_comm b c, add_comm a d]
  exact ennreal_edist_sub_edist_le_edist' c d a b h'

theorem ennreal_edist_edist_le_swap (a b c d : ℝ≥0∞) : edist (edist a b) (edist c d) ≤ edist a c + edist b d := by
  by_cases h : c ≠ ∞ ∨ d ≠ ∞
  swap
  · simp only [ne_eq, not_or, Decidable.not_not] at h
    rw[h.1, h.2]
    unfold edist instEDistENNReal_thesis
    simp only [tsub_self, add_zero, tsub_zero, zero_tsub, sub_top, zero_add]
    by_cases ha : a = ∞
    · rw[ha]
      simp only [sub_top, add_zero, tsub_self, zero_add, le_refl]
    have : ⊤ - a = ∞ := by simp_all only [ne_eq, not_false_eq_true, top_sub]
    rw[this]
    simp only [top_add, le_top]
  by_cases h' : a ≠ ∞ ∨ b ≠ ∞
  swap
  · simp only [ne_eq, not_or, Decidable.not_not] at h'
    rw[h'.1, h'.2]
    unfold edist instEDistENNReal_thesis
    simp only [tsub_self, add_zero, tsub_zero, zero_tsub, sub_top, zero_add]
    by_cases hc : c = ∞
    · rw[hc]
      simp only [sub_top, add_zero, tsub_self, zero_add, le_refl]
    have : ⊤ - c = ∞ := by simp_all only [ne_eq, not_false_eq_true, top_sub]
    rw[this]
    simp only [top_add, le_top]
  calc
    edist (edist a b) (edist c d)
      ≤ edist (a + d) (b + c) := ennreal_edist_of_edist_edist_le_edist a b c d h h'
    _ ≤ edist a c + edist b d := by
      rw[add_comm b c, ennreal_edist_symm b d]
      exact ennreal_edist_add a c d b

variable {G : Type*} [AddCommGroup G] {f : G → ℝ≥0∞} (a b c d : G)

lemma fun_antisymm_diff (hf' : ∀ x, f (-x) = f x): f (a - b) = f (b - a) := by
  calc
    f (a - b)
      = f (- (a - b)) := Eq.symm (hf' (a - b))
    _ = f (b - a) := by abel_nf

lemma ennreal_edist_enorm'
    (hf : ∀ x y, f (x + y) ≤ f x + f y) (hf' : ∀ x, f (-x) = f x) (h : f a ≤ f b):
    edist (f a) (f b) ≤ f (a - b) := by
  rw [ennreal_edist_le' h, fun_antisymm_diff a b hf']
  refine tsub_le_iff_right.mpr ?_
  calc
    f b = f ((b - a) + a) := by congr; abel
      _ ≤ f (b - a) + f a := hf (b - a) a

lemma ennreal_edist_enorm (hf : ∀ x y, f (x + y) ≤ f x + f y) (hf' : ∀ x, f (-x) = f x) :
    edist (f a) (f b) ≤ f (a - b) := by
  by_cases h : f a ≤ f b
  · exact ennreal_edist_enorm' a b hf hf' h
  rw[ennreal_edist_symm, fun_antisymm_diff a b hf']
  exact ennreal_edist_enorm' b a hf hf' (le_of_not_ge h)

theorem ennreal_norm_edist_swap (hf : ∀ x y, f (x + y) ≤ f x + f y) (hf' : ∀ x, f (-x) = f x) :
    edist (f (a - b)) (f (c - d)) ≤ f (a - c) + f (b - d) := by
  calc
    edist (f (a - b)) (f (c - d))
      ≤ f ((a - b) - (c - d)) := ennreal_edist_enorm (a - b) (c - d) hf hf'
    _ = f ((a - c) + (d - b)) := by abel_nf
    _ ≤ f (a - c) + f (d - b) := hf (a - c) (d - b)
    _ = f (a - c) + f (b - d) := by rw [fun_antisymm_diff d b hf']

lemma edist_real' {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (ab: a ≤ b):
    edist a b = ‖a.toReal - b.toReal‖ₑ := by
  rw [ennreal_edist_le' ab, Real.enorm_eq_ofReal_abs]
  refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
  · simp only [ne_eq, sub_eq_top_iff, hb, ha, not_false_eq_true, and_true]
  · simp only [ne_eq, ofReal_ne_top, not_false_eq_true]
  simp only [abs_nonneg, toReal_ofReal]
  rw[← abs_neg, abs_of_nonneg]
  swap
  · simp only [neg_sub, sub_nonneg]
    exact (toReal_le_toReal ha hb).mpr ab
  rw[ENNReal.toReal_sub_of_le]
  · ring
  · exact ab
  exact hb

lemma edist_real {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    edist a b = ‖a.toReal - b.toReal‖ₑ := by
  by_cases ab : a ≤ b
  · exact edist_real' ha hb ab
  rw[ennreal_edist_symm, edist_real' hb ha (le_of_not_ge ab), ← enorm_neg]
  ring_nf

/-
omit [Fintype ι] in
theorem sub_swap
    {f : (ι → ℤ) → ℝ≥0∞} (h : ∀ a b, f (a + b) ≤ f a + f b) (h' : ∀ a b, a ≤ b → f a ≤ f b) (a b : ι → ℤ) :
    f a ≤ f (a - b) + f b := by
  calc
    f a
      ≤ f (a - b + b) := by
      apply h' a (a - b + b)
      exact le_tsub_add
    _ ≤ f (a - b) + f b := h (a - b) b

theorem add_swap'
    {f : (ι → ℤ) → ℝ≥0∞} (h : ∀ a b, f (a + b) ≤ f a + f b) (h' : ∀ a b, a ≤ b → f a ≤ f b) (a b c d : ι → ℤ) :
    f (a - b) - f (c - d) ≤ f (a - c) + f (d - b) := by
  calc
    f (a - b) - f (c - d)
      ≤ f (a - b - (c - d)) := by
      refine tsub_le_iff_right.mpr ?_
      exact sub_swap h h' (a - b) (c - d)
    _ ≤ f (a - c + (d - b)) := by
      apply h'
      rw [@sub_sub_sub_eq]
      rw [@sub_le_iff_le_add]
      rw[add_comm]
      rw[add_comm (a - c)]

      sorry
    _ ≤ f (a - c) + f (b - d) := by sorry

theorem add_swap {f : (ι → ℤ) → ℝ≥0∞} (h : ∀ a b, f (a + b) ≤ f a + f b) (a b c d : ι → ℤ) :
  edist (f (a - b))  (f (c - d)) ≤ f (a - c) + f (b - d) := by

    sorry


#check tsum_comp_le_tsum_of_inj

#check tsum_le_tsum_comp_of_surjective
#check tsum_eq_add_tsum_ite

theorem tsum_swap_surj {α β : Type*} {h : α → β}
    (hh: Surjective h) {g : β → ℝ} (hg : 0 ≤ g) (hgh : Summable (g ∘ h)):
    ∑' b : β, g b ≤ ∑' a : α, g (h a) := by
  have nn: 0 ≤ ∑' (a : α), g (h a) := by
    apply tsum_nonneg
    intro i
    exact hg (h i)
  by_cases hg': Summable g
  swap
  · rw [tsum_eq_zero_of_not_summable hg']
    exact nn
  refine (ofReal_le_ofReal_iff nn).mp ?_
  rw[ENNReal.ofReal_tsum_of_nonneg, ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_le_tsum_comp_of_surjective hh
  all_goals tauto

theorem tsum_swap_ennreal {α β : Type*} {h : α → β}
    (hh: Bijective h) {g : β → ℝ≥0∞} :
    ∑' a : α, g (h a) = ∑' b : β, g b := by
  apply le_antisymm
  · exact tsum_comp_le_tsum_of_injective (Bijective.injective hh) g
  refine tsum_le_tsum_comp_of_surjective (Bijective.surjective hh) g

theorem tsum_swap {α β : Type*} {h : α → β}
    (hh: Bijective h) {g : β → ℝ} (hg : 0 ≤ g) :
    ∑' a : α, g (h a) = ∑' b : β, g b := by
  let gh' : α → ℝ≥0 := fun a ↦ ⟨g (h a), hg (h a)⟩
  let g' : β → ℝ≥0 := fun b ↦ ⟨g b, hg b⟩
  have lem: ∑' (a : α), (gh' a : ℝ≥0∞) = ∑' (b : β), (g' b : ℝ≥0∞) := by
    unfold gh' g'
    rw [← tsum_swap_ennreal (h := h) hh]
  by_cases hg' : Summable g
  · apply le_antisymm
    · exact tsum_comp_le_tsum_of_inj hg' hg (Bijective.injective hh)
    suffices : Summable (g ∘ h)
    · apply tsum_swap_surj (Bijective.surjective hh) hg this
    refine (NNReal.summable_mk fun n ↦ hg (h n)).mp ?_
    apply ENNReal.tsum_coe_ne_top_iff_summable.1
    rw[lem]
    apply ENNReal.tsum_coe_ne_top_iff_summable.2
    exact (summable_mk hg).mpr hg'
  rw [tsum_eq_zero_of_not_summable hg']
  refine tsum_eq_zero_of_not_summable ?_
  contrapose hg'
  simp_all only [Decidable.not_not]
  refine (NNReal.summable_mk ?_).mp ?_
  · exact hg
  apply ENNReal.tsum_coe_ne_top_iff_summable.1
  rw[← lem]
  apply ENNReal.tsum_coe_ne_top_iff_summable.2
  exact (summable_mk fun n ↦ hg (h n)).mpr hg'

-/
/-
theorem ell_p_coe {α : Type*} {f : α → ℝ} (hf : 0 ≤ f):
    (∑' a, ‖f a‖ₑ).toReal = ∑' a, f a := by
  have s1: ∑' (a : α), f a = (∑' (a : α), (f a).toNNReal).toReal := by
    have : ∑' (a : α), (f a).toNNReal = ∑' (a : α), ⟨f a, hf a⟩ := by
      congr
      ext a
      simp only [Real.coe_toNNReal', coe_mk, sup_eq_left]
      exact hf a
    rw[this]
    rw[← NNReal.coe_tsum_of_nonneg hf]
    simp only [coe_mk]
  rw[s1]
  by_cases hf' : Summable f
  swap
  · have ns: ¬ Summable fun a ↦ (f a).toNNReal := by
      contrapose hf'
      simp_all only [Decidable.not_not]
      apply (NNReal.summable_mk hf).1
      suffices : (fun a ↦ (f a).toNNReal) = fun n ↦ ⟨f n, hf n⟩
      · rwa [← this]
      ext a
      simp only [Real.coe_toNNReal', coe_mk, sup_eq_left]
      exact hf a
    have g: ∑' (a : α), (↑(f a).toNNReal : ℝ≥0∞) = ⊤ := by
      contrapose ns
      simp only [Decidable.not_not]
      apply ENNReal.tsum_coe_ne_top_iff_summable.1
      exact ns
    rw[tsum_eq_zero_of_not_summable ns]
    simp only [NNReal.coe_zero]
    refine (toReal_eq_zero_iff (∑' (a : α), ‖f a‖ₑ)).mpr ?_
    right
    rw[← g]
    congr
    ext a
    rw [Real.enorm_eq_ofReal_abs]
    refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_ <;> simp
    rw[abs_of_nonneg (hf a)]
    simp only [left_eq_sup]
    exact hf a
  suffices : ∑' (a : α), ‖f a‖ₑ = ∑' (a : α), (f a).toNNReal --braucht summable omg
  · rw[this]
    simp only [coe_toReal]
  have s2: ∑' a, ‖f a‖ₑ = ∑' (b : α), (↑(f b).toNNReal : ℝ≥0∞) := by
    congr
    ext a
    rw [Real.enorm_eq_ofReal_abs]
    rw [ofNNReal_toNNReal]
    congr
    simp only [abs_eq_self]
    exact hf a
  rw[s2]
  refine Eq.symm (ENNReal.coe_tsum ?_)
  exact Summable.toNNReal hf'



#check tsum_comp_le_tsum_of_inj

@[simp] lemma subtype_eq_tonnreal {a : ℝ} (ha : 0 ≤ a) : (⟨a, ha⟩ : ℝ≥0) = a.toNNReal := by
  ext
  simp only [val_eq_coe, Real.coe_toNNReal', ha, sup_of_le_left]

theorem real_tsum_comp_le_tsum_of_inj_of_nonneg
    {α β : Type*} {f : α → ℝ} (hf : 0 ≤ f) (hf' : Summable f) {i : β → α} (hi : Injective i):
    ∑' x : β, f (i x) ≤ ∑' x : α, f x := by
  have s1: 0 ≤ ∑' x : β, f (i x) := by
    apply tsum_nonneg
    intro x
    exact hf (i x)
  have s2: 0 ≤ ∑' x : α, f x := by
    apply tsum_nonneg
    intro x
    exact hf x
  suffices : (⟨∑' x : β, f (i x), s1⟩ : ℝ≥0) ≤ (⟨∑' x : α, f x, s2⟩ : ℝ≥0)
  · simp only [Subtype.mk_le_mk] at this
    exact this
  have p : ∀ x, 0 ≤ f (i x) := fun x ↦ hf (i x)
  rw[NNReal.coe_tsum_of_nonneg hf, NNReal.coe_tsum_of_nonneg p]
  calc
    ∑' (n : β), (⟨f (i n), p n⟩ : ℝ≥0)
      = ∑' (n : β), (f (i n)).toNNReal := by simp only [subtype_eq_tonnreal]
    _ ≤ ∑' (n : α), (f n).toNNReal := by
      apply NNReal.tsum_comp_le_tsum_of_inj (f := fun n : α ↦ (f n).toNNReal) (hi := hi)
      exact Summable.toNNReal hf'
    _ = ∑' (n : α), (⟨f n, hf n⟩ : ℝ≥0) := by simp only [subtype_eq_tonnreal]

example : Summable fun n : ℕ ↦ 1 / (↑n : ℝ)^ 2 := by
  apply HasSum.summable (a := (Real.pi^2 / 6))
  exact hasSum_zeta_two

example (p : ℝ≥0∞) : (p ^ (2 : ℝ)⁻¹) ^ 2 = p := by
  rw [← ENNReal.rpow_mul_natCast]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
    ENNReal.rpow_one]

example (b : ℝ≥0∞): (↑(b.toNNReal) : ℝ) = b.toReal := by
  exact rfl

lemma ell_p_coe_exp {α : Type*} (f : α → ℝ) {p : ℝ} (hp : 0 ≤ p):
    (∑' a, ‖f a‖ₑ^p).toReal = ∑' a, |f a|^p := by
  rw[← ell_p_coe]
  swap
  · intro a
    simp only [Pi.zero_apply]
    apply Real.rpow_nonneg
    apply abs_nonneg
  congr
  ext a
  rw[Real.enorm_rpow_of_nonneg] <;> simp [hp]


lemma summable_ne_top {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (h : Summable f):
    ∑' (a : α), ‖f a‖ₑ ≠ ⊤ := by
  have : Summable (fun a ↦ (⟨f a, hf a⟩ : NNReal)) := by
    suffices : (fun a ↦ (⟨f a, hf a⟩ : NNReal)) = fun a ↦ (f a).toNNReal
    · rw[this]
      exact Summable.toNNReal h
    ext a
    simp only [val_eq_coe, Real.coe_toNNReal', left_eq_sup]
    exact hf a
  apply ENNReal.tsum_coe_ne_top_iff_summable.2 at this
  contrapose this
  simp_all
  rw[← this]
  congr
  ext a
  rw[Real.enorm_of_nonneg]
  · exact rfl
  exact hf a


lemma mem_lp_enorm_ne_top
    {α : Type*} (f : α → ℝ) {p : ℝ} (hp : 0 < p) (h : Memℓp f p.toNNReal) :
    ∑' (a : α), ‖f a‖ₑ ^ p ≠ ⊤ := by
  unfold Memℓp at h
  simp only [ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le_of_gt hp, ↓reduceIte, coe_ne_top,
    Real.norm_eq_abs, coe_toReal, Real.coe_toNNReal'] at h
  have : max p 0 = p := by
    simp only [sup_eq_left]
    exact le_of_lt hp
  rw[this] at h
  have : ∑' (a : α), ‖f a‖ₑ ^ p = ∑' (a : α), ‖|f a| ^ p‖ₑ := by
    congr
    ext a
    rw[Real.enorm_rpow_of_nonneg] <;> simp [le_of_lt hp]
  rw[this]
  apply summable_ne_top (h := h)
  intro a
  apply Real.rpow_nonneg
  apply abs_nonneg





lemma mem_lp_neq_zero_sub_abs_gt_zero
    {α : Type*} {f : α → ℝ} (hf : f ≠ 0) {p : ℝ} (hp : 0 < p) (h : Memℓp f p.toNNReal) :
    0 < ∑' a : α, |f a| ^ p := by
  rw[← ell_p_coe_exp f (le_of_lt hp)]
  apply toReal_pos
  · contrapose hf
    simp_all
    ext
    exact hf _
  exact mem_lp_enorm_ne_top f hp h


--EINFÜGEN !

variable {G : Type*} [AddCommGroup G]
lemma norm_trick_sub {f : G → ℝ} (a b : G) (hf: ∀ x y, f (x + y) ≤ f x + f y):
    f a - f b ≤ f (a - b) := by
  simp only [tsub_le_iff_right]
  have := hf (a - b) b
  simp_all only [sub_add_cancel]

lemma antisymm_fun_sub {f : G → ℝ} (a b : G) (hf : ∀ x, f (-x) = f x):
    f (a - b) = f (b - a) := by
  calc
    f (a - b) = f (- (a - b)) := by exact Eq.symm (hf (a - b))
            _ = f (b - a) := by rw [neg_sub]

lemma norm_trick' {f : G → ℝ} (a b c d : G) (hf: ∀ x y, f (x + y) ≤ f x + f y):
    f (a - b) - f (c - d) ≤ f (a - c) + f (d - b) := by
  calc
    f (a - b) - f (c - d)
      ≤ f ((a - b) - (c - d)) := norm_trick_sub (a - b) (c - d) hf
    _ = f ((a - c) + (d - b)) := by abel_nf
    _ ≤ f (a - c) + f (d - b) := hf (a - c) (d - b)

lemma norm_trick {f : G → ℝ} (a b c d : G) (hf: ∀ x y, f (x + y) ≤ f x + f y)
  (hf' : ∀ x, f (-x) = f x):
    |f (a - b) - f (c - d)| ≤ f (a - c) + f (b - d) := by
  by_cases h : f (c - d) ≤ f (a - b)
  · have : |f (a - b) - f (c - d)| = f (a - b) - f (c - d) := by simpa only [abs_eq_self, sub_nonneg]
    rw[this]
    rw[antisymm_fun_sub b d hf']
    exact norm_trick' a b c d hf
  simp only [not_le] at h
  have : |f (a - b) - f (c - d)| = f (c - d) - f (a - b) := by
    calc
      |f (a - b) - f (c - d)| = - (f (a - b) - f (c - d)) := by simp [-neg_sub, le_of_lt h]
                            _ = f (c - d) - f (a - b) := by ring
  rw[this, antisymm_fun_sub a c hf']
  exact norm_trick' c d a b hf
-/
/-
section technical_sum
variable {α β γ : Type*} (m : Finset β) (s : Finset γ)

lemma fintype.card_eq_ncard (s : Set α) [Fintype s] : s.ncard = Fintype.card s := by
  rw[Fintype.card_eq_nat_card, Nat.card_coe_set_eq]


lemma ncard_le_surj_fin {n : ℕ} (s : Set α) {i : Fin n → s} (ih : Surjective i) :
    s.encard ≤ n := by
  have fin : s.Finite := Finite.of_surjective i ih
  have fin' : Fintype ↑s := fin.fintype
  refine encard_le_coe_iff_finite_ncard_le.mpr ⟨fin, ?_⟩
  have car: Fintype.card s = s.ncard := by exact Eq.symm (fintype.card_eq_ncard s)
  rw[← car, ← Fintype.card_fin n]
  exact Fintype.card_le_of_surjective i ih

lemma ncard_le_surjon_fin {n : ℕ} (s : Set α) {i : Fin n → α} (ih : SurjOn i (Set.univ (α := (Fin n))) s) :
    s.encard ≤ n := by
  by_cases hs: IsEmpty s
  · rw[isEmpty_coe_sort.mp hs]
    simp only [encard_empty, zero_le]
  simp only [isEmpty_coe_sort] at hs
  have hs': Inhabited s := by
    refine inhabited_of_nonempty ?_
    exact nonempty_iff_ne_empty'.mpr hs
  let p : Fin n → s :=
    fun k ↦ if hk : i k ∈ s then ⟨i k, hk⟩ else default
  apply ncard_le_surj_fin (i := p)
  intro ⟨a, ah⟩
  obtain ⟨k, _, kh⟩ := ih ah
  use k
  unfold p
  rw [kh]
  simp only [ah, ↓reduceDIte]

/--
theorem semi_inj_lemma (a : α) {r : γ} (hr : r ∈ s)
    {g : γ → β → α → α} (hg: ∀ r ∈ s, ∀ a : α, InjOn (fun j ↦ g r j a) m) :
    {(x, y, z) : α × β × γ | y ∈ m ∧ z ∈ s ∧ ((z, g z y x) : γ × α) = (r, a)}.encard ≤ m.card := by --falsch
  set o := {(x, y, z) : α × β × γ | y ∈ m ∧ z ∈ s ∧ ((z, g z y x) : γ × α) = (r, a)}
  let u := {(x, z) : α × γ | ∃ y : β, (x, y, z) ∈ o}
  by_cases ne: IsEmpty (α × β × γ)
  · rw [eq_empty_of_isEmpty o]
    simp only [encard_empty, zero_le]
  simp only [isEmpty_prod, not_or, not_isEmpty_iff] at ne
  have nαγ : Nonempty (α × γ) := by simp only [nonempty_prod, ne, and_self]
  have bi : Inhabited β := Classical.inhabited_of_nonempty ne.2.1
  let g' : α × γ → β :=
    fun (x, z) ↦ if h : ∃ y : β, (x, y, z) ∈ o then h.choose else default
  have g'h {x : α} {z : γ} {y y' : β} (h : (x, y, z) ∈ o ∧ (x, y', z) ∈ o): y = y' := by
    unfold o at h
    simp at h
    specialize hg z h.1.2.1 x h.1.1 h.2.1
    simp at hg
    apply hg
    rw[h.1.2.2.2, h.2.2.2.2]
  let f := (Finset.equivFin m).symm
  --let g' : α × β × γ → α :=
  --  fun (a,b,c) ↦ g c b a
  set n := m.card
  let i : β → α × γ := Function.invFunOn g' u
  let p : m → α × β × γ :=
    fun ⟨b, bh⟩ ↦ ⟨(i b).1, b, (i b).2⟩
  let k : Fin n → α × β × γ := p ∘ f
  apply ncard_le_surjon_fin (i := (p ∘ f))
  suffices : SurjOn p univ o
  · intro _ h
    obtain ⟨e, eh⟩ := this h
    use f.symm e
    simp only [mem_univ, comp_apply, Equiv.apply_symm_apply, true_and]
    exact eh.2
  intro ⟨x, y, z⟩ h
  have xzh: ∃ y, (x, y, z) ∈ o := by use y
  have g'xz: g' (x, z) = y := by
    apply g'h (x := x) (z := z)
    constructor
    swap
    · exact h
    unfold g'
    simp only [xzh, ↓reduceDIte]
    exact Exists.choose_spec xzh
  unfold o at h
  simp only [Prod.mk.injEq, mem_setOf_eq] at h
  rw[h.2.2.1] at g'xz
  rw[h.2.2.1] at *
  simp only [hr, true_and] at h
  simp only [image_univ, mem_range, Subtype.exists]
  unfold p
  simp only [Prod.mk.injEq, exists_and_left, exists_prop, existsAndEq, true_and]
  have : g' ((i y).1, (i y).2) = y := by
    unfold i
    apply Function.invFunOn_eq
    use ⟨x, r⟩
    unfold u
    simp only [mem_setOf_eq]
    constructor
    · use y
      unfold o
      simp_all only [Prod.mk.injEq, mem_setOf_eq, and_self]
    exact g'xz
  have hi: ((i y).1, (i y).2) ∈ u := by
    unfold i
    refine invFunOn_mem ?_
    use ⟨x, r⟩
    unfold u
    simp only [mem_setOf_eq]
    constructor
    · use y
      unfold o
      simp_all only [Prod.mk.injEq, mem_setOf_eq, and_self]
    exact g'xz
  unfold u at hi
  have cop := hi
  simp only [mem_setOf_eq] at hi
  obtain ⟨y', y'h⟩ := hi
  unfold o at y'h
  simp_all only [Prod.mk.injEq, mem_setOf_eq, and_self, and_true]
  rw[y'h.2.2.1] at *
  clear y'h y'
  have tr: g' ((i y).1, r) = cop.choose := by
    unfold g'
    simp only [cop, ↓reduceDIte]
  rw[this] at tr
  have gr: ((i y).1, y, r) ∈ o := by
    nth_rw 2[tr]
    exact Exists.choose_spec cop
  unfold o at gr
  simp at gr




  sorry
-/

lemma bijon_encard {f : α → β} {s : Set α} {t : Set β} (h: BijOn f s t) :
    s.encard = t.encard := by
  refine encard_congr ?_
  exact BijOn.equiv f h

theorem semi_inj_lemma (a : α) (r : γ)
    {g : γ → β → α → α} (hg: ∀ r, ∀ j, Injective (g r j)) :
    {(x, y, z) : α × β × γ | y ∈ m ∧ z ∈ s ∧ ((z, g z y x) : γ × α) = (r, a)}.encard ≤ m.card := by
  suffices :
    {(x, y, z) : α × β × γ | y ∈ m ∧ ((z, g z y x) : γ × α) = (r, a)}.encard ≤ m.card
  · apply le_trans' this
    apply encard_mono
    simp only [Prod.mk.injEq, le_eq_subset, setOf_subset_setOf, and_imp, Prod.forall]
    tauto
  have : {(x, y, z) : α × β × γ | y ∈ m ∧ ((z, g z y x) : γ × α) = (r, a)}.encard
      = {(x, y) : α × β | y ∈ m ∧ g r y x = a}.encard := by
    let f : α × β × γ → α × β := fun (x, y, _) ↦ (x, y)
    apply bijon_encard (f := f)
    refine BijOn.mk ?_ ?_ ?_
    · intro ⟨x,y,z⟩ h
      unfold f
      simp_all only [Prod.mk.injEq, mem_setOf_eq, true_and]
      rw[← h.2.1, h.2.2]
    · intro (x, y, z) h1 (x', y', z') h2
      unfold f
      simp_all only [Prod.mk.injEq, mem_setOf_eq, implies_true]
    intro (x,y) h
    use (x, y, r)
    unfold f
    simp_all only [mem_setOf_eq, Prod.mk.injEq, and_self]
  rw[this]
  clear this
  revert m
  apply Finset.induction
  · simp only [Finset.notMem_empty, false_and, setOf_false, encard_empty, Finset.card_empty,
    CharP.cast_eq_zero, le_refl]
  intro b s bs h
  simp [bs]
  set o := {x : α × β | (x.2 = b ∨ x.2 ∈ s) ∧ g r x.2 x.1 = a}
  calc
    {x : α × β | (x.2 = b ∨ x.2 ∈ s) ∧ g r x.2 x.1 = a}.encard
      = ({x : α × β | (x.2 ∈ s) ∧ g r x.2 x.1 = a} ∪
        {x : α × β | (x.2 = b) ∧ g r x.2 x.1 = a}).encard := by
      congr
      ext
      simp only [mem_setOf_eq, mem_union]
      tauto
    _ ≤ {x : α × β | (x.2 ∈ s) ∧ g r x.2 x.1 = a}.encard +
        {x : α × β | (x.2 = b) ∧ g r x.2 x.1 = a}.encard := by
      apply Set.encard_union_le
  gcongr
  refine encard_le_one_iff_subsingleton.mpr ?_
  intro ⟨u, x⟩ xh ⟨v, y⟩ yh
  simp_all
  apply hg r b
  nth_rw 1[← xh.1, ← yh.1, xh.2, yh.2]

@[simp] lemma nnreal_sum_coe {f : α → ℝ} (hf : 0 ≤ f) (s : Finset α):
    (⟨∑ a ∈ s, f a, by apply Finset.sum_nonneg; intro i _; exact hf i⟩ : ℝ≥0) = ∑ a ∈ s, ⟨f a, hf a⟩ := by
  revert s
  apply Finset.induction
  · simp only [Finset.sum_empty, mk_zero]
  intro t s ts h
  simp only [ts, not_false_eq_true, Finset.sum_insert]
  rw[← h]
  simp only [Nonneg.mk_add_mk]

theorem tsum_sum_sum_est
    {f : γ × α → ℝ} (hf: 0 ≤ f) (hf' : ∀ c, Summable (fun a ↦ f (c, a))) {g : γ → β → α → α}
    (hg: ∀ r, ∀ j, Injective (g r j)):
    ∑' i : α, ∑ j ∈ m, ∑ r ∈ s, f (r, (g r j i)) ≤ m.card * ∑ r ∈ s, ∑' i : α, f (r, i) := by
  revert m
  apply Finset.induction
  · simp only [Finset.sum_empty, tsum_zero, Finset.card_empty, CharP.cast_eq_zero, zero_mul,
    le_refl]
  intro b m bm h
  simp only [bm, not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_notMem, Nat.cast_add,
    Nat.cast_one]
  rw[Summable.tsum_add, add_mul, one_mul, add_comm]
  apply add_le_add
  · exact h
  let temp : γ × α → ℝ≥0  := fun (c, b_1) ↦ ⟨f (c, b_1), hf (c, b_1)⟩
  have fin(c : γ): ∑' (b_1 : α), (↑(temp (c, b_1)) : ℝ≥0∞) < ⊤ := by
    apply lt_top_iff_ne_top.2
    apply ENNReal.tsum_coe_ne_top_iff_summable.2
    apply (NNReal.summable_mk (fun n ↦ hf (c, n))).2
    exact hf' c
  unfold temp at fin
  dsimp at fin
  rw[Summable.tsum_finsetSum ?_]
  · refine Finset.sum_le_sum ?_
    intro c _
    apply _root_.tsum_comp_le_tsum_of_inj (f := fun i ↦ f (c, i))
    · exact hf' c
    · exact fun a ↦ hf (c, a)
    exact hg c b
  · intro c _
    have nn: ∀ b_1, 0 ≤ f (c, g c b b_1) := fun b_1 ↦ hf (c, g c b b_1)
    apply (NNReal.summable_mk nn).1
    apply ENNReal.tsum_coe_ne_top_iff_summable.1
    apply lt_top_iff_ne_top.1
    refine lt_of_le_of_lt ?_ (fin c)
    exact tsum_comp_le_tsum_of_injective (hg c b) fun y ↦ ↑(temp (c, y))
  · have nn (i : α) : 0 ≤ ∑ r ∈ s, f (r, g r b i) := by
      apply Finset.sum_nonneg
      intro i_1 _
      exact hf (i_1, g i_1 b i)
    apply (NNReal.summable_mk nn).1
    apply ENNReal.tsum_coe_ne_top_iff_summable.1
    apply lt_top_iff_ne_top.1
    let temp : γ × α → ℝ≥0  := fun (c, b_1) ↦ ⟨f (c, b_1), hf (c, b_1)⟩
    let temp' : α → ℝ≥0 := fun i ↦ ⟨∑ r ∈ s, f (r, g r b i), nn i⟩
    calc
      ∑' (b_1 : α), (temp' b_1 : ℝ≥0∞)
        = ∑' (b_1 : α), ∑ r ∈ s, (temp (r, g r b b_1) : ℝ≥0∞) := by
        congr
        ext d
        unfold temp' temp
        simp only
        rw [← @coe_finset_sum]
        congr 1
        apply nnreal_sum_coe
      _ = ∑ r ∈ s, ∑' (b_1 : α), (temp (r, g r b b_1) : ℝ≥0∞) := by
        refine Summable.tsum_finsetSum ?_
        intros
        exact ENNReal.summable
      _ < ⊤ := by
        refine sum_lt_top.mpr ?_
        have fin(c : γ): ∑' (b_1 : α), (↑(temp (c, b_1)) : ℝ≥0∞) < ⊤ := by
          apply lt_top_iff_ne_top.2
          apply ENNReal.tsum_coe_ne_top_iff_summable.2
          apply (NNReal.summable_mk (fun n ↦ hf (c, n))).2
          exact hf' c
        intro c _
        refine lt_of_le_of_lt ?_ (fin c)
        exact tsum_comp_le_tsum_of_injective (hg c b) fun y ↦ ↑(temp (c, y))
  have nn: ∀ i, 0 ≤ ∑ j ∈ m, ∑ r ∈ s, f (r, g r j i) := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro r _
    exact hf (r, g r j i)
  have nn': ∀ b j, 0 ≤ ∑ r ∈ s, f (r, g r j b) := by
    intro b j
    apply Finset.sum_nonneg
    intro r _
    exact hf (r, g r j b)
  apply (NNReal.summable_mk nn).1
  apply ENNReal.tsum_coe_ne_top_iff_summable.1
  apply lt_top_iff_ne_top.1
  let temp : γ × α → ℝ≥0  := fun (c, b_1) ↦ ⟨f (c, b_1), hf (c, b_1)⟩
  let temp': α → ℝ≥0 := fun i ↦ ⟨∑ j ∈ m, ∑ r ∈ s, f (r, g r j i), nn i⟩
  let temp'': α → β → ℝ≥0 := fun b j ↦ ⟨∑ r ∈ s, f (r, g r j b), nn' b j⟩
  suffices : ∑' (b : α), (↑(temp' b) : ℝ≥0∞) < ⊤
  · exact this
  calc
    ∑' (b : α), (↑(temp' b) : ℝ≥0∞)
      =  ∑' (b : α), ∑ j ∈ m, (↑(temp'' b j) : ℝ≥0∞) := by
      congr
      ext b
      unfold temp' temp''
      rw[nnreal_sum_coe, ENNReal.coe_finset_sum]
    _ = ∑ j ∈ m, ∑' (b : α), (↑(temp'' b j) : ℝ≥0∞) := by
      refine Summable.tsum_finsetSum ?_
      intros
      exact ENNReal.summable
  simp only [sum_lt_top]
  intro b _
  unfold temp''
  let temp''': α → γ → ℝ≥0 := fun b_1 r ↦ ⟨f (r, g r b b_1), hf (r, g r b b_1)⟩
  calc
    ∑' (b_1 : α), (↑(temp'' b_1 b) : ℝ≥0∞)
      = ∑' (b_1 : α), ∑ r ∈ s, (↑(temp''' b_1 r) : ℝ≥0∞) := by
      congr
      ext a
      unfold temp''
      rw[nnreal_sum_coe, coe_finset_sum]
    _ = ∑ r ∈ s, ∑' (b_1 : α), (↑(temp''' b_1 r) : ℝ≥0∞) := by
      refine Summable.tsum_finsetSum ?_
      intros
      exact ENNReal.summable
  simp only [sum_lt_top]
  intro c _
  have fin(c : γ): ∑' (b_1 : α), (↑(temp (c, b_1)) : ℝ≥0∞) < ⊤ := by
    apply lt_top_iff_ne_top.2
    apply ENNReal.tsum_coe_ne_top_iff_summable.2
    apply (NNReal.summable_mk (fun n ↦ hf (c, n))).2
    exact hf' c
  refine lt_of_le_of_lt ?_ (fin c)
  exact tsum_comp_le_tsum_of_injective (hg c b) fun y ↦ ↑(temp (c, y))

theorem tsum_sum_sum_est_ennreal
    (f : γ × α → ℝ≥0∞) {g : γ → β → α → α}
    (hg: ∀ r, ∀ j, Injective (g r j)):
    ∑' i : α, ∑ j ∈ m, ∑ r ∈ s, f (r, (g r j i)) ≤ m.card * ∑ r ∈ s, ∑' i : α, f (r, i) := by
  revert m
  apply Finset.induction
  · simp only [Finset.sum_empty, tsum_zero, Finset.card_empty, CharP.cast_eq_zero, zero_mul,
    le_refl]
  intro b m bm h
  simp only [bm, not_false_eq_true, Finset.sum_insert, Finset.card_insert_of_notMem, Nat.cast_add,
    Nat.cast_one]
  rw[Summable.tsum_add ENNReal.summable ENNReal.summable]
  rw[add_mul, one_mul, add_comm]
  gcongr
  rw[Summable.tsum_finsetSum ?_]
  swap
  · intros
    exact ENNReal.summable
  apply Finset.sum_le_sum
  · intro c _
    exact tsum_comp_le_tsum_of_injective (hg c b) fun y ↦ f (c, y)


lemma enorm_of_abs {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b): ‖a‖ₑ ≤ ‖b‖ₑ := by
  refine enorm_le_iff_norm_le.mpr ?_
  refine norm_le_norm_of_abs_le_abs ?_
  exact abs_le_abs_of_nonneg ha h


end technical_sum
-/
/-
variable {ι : Type*} [Fintype ι]

def approx_set(i : ι)(j : (ι → ℤ)): Set (ι → ℝ) :=
  {x | j i ≤ (∑ r : ι, x r) ∧ (∑ r : ι, x r) < j i + 1 ∧ (∀ i' : ι, i' ≠ i → (j i' ≤ x i' ∧ x i' < j i' + 1))}

lemma approx_set'(i : ι)(j : (ι → ℤ)): approx_set i j =
  {x | ↑(j i) ≤ (∑ r : ι, x r) ∧ (∑ r : ι, x r) < (↑(j i) : ℝ) + 1} ∩ ⋂(i' : ι), {x | i' = i ∨ (↑(j i') ≤ x i' ∧ x i' < (↑(j i') : ℝ) + 1)} := by
  ext x
  unfold approx_set
  simp
  constructor
  · intro ⟨h1,h2,h3⟩
    constructor
    · constructor
      · exact h1
      exact h2
    intro i'
    by_cases h': i' = i
    · tauto
    specialize h3 i' h'
    tauto
  intro ⟨h1,h2⟩
  constructor
  · exact h1.1
  constructor
  · exact h1.2
  intro i' i'i
  specialize h2 i'
  tauto

@[measurability] lemma approx_set_measurable(i : ι)(j : (ι → ℤ)): MeasurableSet (approx_set i j) := by
  rw[approx_set']
  refine MeasurableSet.inter ?_ ?_
  · simp
    refine Measurable.and ?_ ?_
    · refine measurableSet_setOf.mp ?_
      refine measurableSet_le ?_ ?_
      all_goals fun_prop
    refine measurableSet_setOf.mp ?_
    refine measurableSet_lt ?_ ?_
    all_goals fun_prop
  refine MeasurableSet.iInter ?_
  intro i'
  by_cases i'i: i'=i
  · simp [i'i]
  simp only [i'i, false_or, measurableSet_setOf]
  refine Measurable.and ?_ ?_
  · refine measurableSet_setOf.mp ?_
    refine measurableSet_le ?_ ?_
    all_goals fun_prop
  refine measurableSet_setOf.mp ?_
  refine measurableSet_lt ?_ ?_
  all_goals fun_prop

def approx_set_minus_set (j : ι → ℤ) (t : Finset ι) : Set (ι → ℝ) :=
  {x | (∀ i' : ι, i' ∉ t → (j i' ≤ x i' ∧ x i' < j i' + 1))}


lemma approx_set_volume_ne (i : ι) (j : ι → ℤ) {t : Finset ι} (it : i ∉ t) :
    MeasureTheory.lmarginal (fun _ ↦ volume) (insert i t) ((approx_set i j).indicator 1) =
    (approx_set_minus_set j (insert i t)).indicator 1 := by
  revert t
  apply Finset.induction
  · simp only [Finset.notMem_empty, not_false_eq_true, insert_empty_eq, forall_const]
    rw[MeasureTheory.lmarginal_singleton]
    ext x
    apply Eq.trans (b := (∫⁻ (xᵢ : ℝ), ((Ico (j i - ∑ r : ι, x r + x i) ((j i - ∑ r : ι, x r + x i) + 1)).indicator (fun _ ↦ (approx_set_minus_set j {i}).indicator (1 : (ι → ℝ) → ℝ≥0∞) x) xᵢ)))
    swap
    · simp only [measurableSet_Ico, lintegral_indicator, lintegral_const, MeasurableSet.univ,
      Measure.restrict_apply, univ_inter, Real.volume_Ico, add_sub_cancel_left, ofReal_one, mul_one]
    congr
    ext y
    rename_i k
    unfold indicator
    simp only [Pi.one_apply, mem_Ico]
    rw [@eq_ite_iff]
    by_cases hy: (j i - ∑ r : ι, x r + x i) ≤ y ∧ y < (j i - ∑ r : ι, x r + x i + 1) <;> simp [hy]
    · congr 1
      ext
      unfold update approx_set approx_set_minus_set
      simp only [ne_eq, eq_rec_constant, dite_eq_ite, mem_setOf_eq, Finset.mem_singleton]
      have s1: ∑ a, (if a = i then y else x a) = (∑ r, x r) - x i + y := by
        have s2 := Finset.sum_update_of_mem (f := x) (b := y) (i := i) (s := Finset.univ)
        unfold update at s2
        simp only [Finset.mem_univ, eq_rec_constant, dite_eq_ite, Finset.subset_univ,
        Finset.sum_sdiff_eq_sub, Finset.sum_singleton, forall_const] at s2
        rw[s2]
        ring
      rw[s1]
      constructor
      · intro ⟨h1, h2, h3⟩ r ri
        specialize h3 r ri
        simp_all only [↓reduceIte, and_self]
      intro h
      constructor
      · linarith
      constructor
      · linarith
      intro r ri
      specialize h r ri
      simp_all only [↓reduceIte, and_self]
    unfold update approx_set
    simp only [ne_eq, eq_rec_constant, dite_eq_ite, mem_setOf_eq, not_and, not_forall,
      not_lt]
    have s1: ∑ a, (if a = i then y else x a) = (∑ r, x r) - x i + y := by
      have s2 := Finset.sum_update_of_mem (f := x) (b := y) (i := i) (s := Finset.univ)
      unfold update at s2
      simp only [Finset.mem_univ, eq_rec_constant, dite_eq_ite, Finset.subset_univ,
      Finset.sum_sdiff_eq_sub, Finset.sum_singleton, forall_const] at s2
      rw[s2]
      ring
    rw[s1]
    intro jl ju
    have : ↑(j i) - ∑ r, x r + x i ≤ y ∧ y < ↑(j i) - ∑ r, x r + x i + 1 := by
      constructor <;> linarith
    contradiction
  intro a s as h
  simp only [Finset.mem_insert, not_or, and_imp]
  intro ia is
  have h' := h is
  clear h
  ext x
  rw[Finset.insert_comm]
  rw[MeasureTheory.lmarginal_insert]
  swap
  · refine Measurable.indicator ?_ ?_
    · exact measurable_one
    measurability
  swap
  · simp only [Finset.mem_insert, ne_eq, not_false_eq_true, Ne.symm, or_self, ia, as]
  rw[h']
  calc
    ∫⁻ (xᵢ : ℝ), (approx_set_minus_set j (insert i s)).indicator 1 (update x a xᵢ)
      = ∫⁻ (xᵢ : ℝ), ((Ico (↑(j a) : ℝ) ((↑(j a) : ℝ) + 1)).indicator (fun _ ↦ (approx_set_minus_set j (insert a (insert i s))).indicator (1 : (ι → ℝ) → ℝ≥0∞) x) xᵢ) := by
      congr
      ext y
      unfold indicator
      simp only [Pi.one_apply, mem_Ico]
      rw [@eq_ite_iff]
      by_cases hy: ((↑(j a) : ℝ) ≤ y ∧ y < (↑(j a) : ℝ) + 1) <;> simp [hy]
      · congr 1
        unfold update approx_set_minus_set
        simp_all only [Finset.mem_insert, not_or, and_imp, eq_rec_constant, dite_eq_ite,
          mem_setOf_eq, eq_iff_iff]
        constructor
        · intro h r ra ri rs
          specialize h r ri rs
          simp_all only [↓reduceIte, and_self]
        intro _ r _ _
        by_cases r = a <;> simp_all only [not_false_eq_true, ↓reduceIte, and_self]
      unfold approx_set_minus_set
      simp only [Finset.mem_insert, not_or, and_imp, mem_setOf_eq, not_forall,
        not_and, not_lt]
      use a
      use (Ne.symm ia)
      use as
      simp_all only [not_and, not_lt, update_self, implies_true]
    _ = (approx_set_minus_set j (insert a (insert i s))).indicator 1 x := by
      simp only [measurableSet_Ico, lintegral_indicator, lintegral_const, MeasurableSet.univ,
        Measure.restrict_apply, univ_inter, Real.volume_Ico, add_sub_cancel_left, ofReal_one,
        mul_one]

lemma approx_set_volume_univ (i : ι) (j : ι → ℤ):
    MeasureTheory.lmarginal (fun _ ↦ volume) (Finset.univ) ((approx_set i j).indicator 1) = 1 := by
  let s := Finset.univ \ {i}
  have : Finset.univ = insert i s := by
    unfold s
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton, true_and,
      true_iff]
    tauto
  rw[this, approx_set_volume_ne]
  · rw[← this]
    unfold approx_set_minus_set
    simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true, setOf_true,
      indicator_univ]
  unfold s
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, not_true_eq_false, and_false,
    not_false_eq_true]

theorem approx_set_volume (i : ι) (j : ι → ℤ): volume (approx_set i j) = 1 := by
  rw[← MeasureTheory.lintegral_indicator_one (approx_set_measurable i j)]
  rw[MeasureTheory.volume_pi]
  have temp: (1 : ℝ≥0∞) = (1 : (ι → ℝ) → ℝ≥0∞) 0 := by simp only [Pi.one_apply]
  rw[temp]
  nth_rw 2[← approx_set_volume_univ i j]
  rw[MeasureTheory.lintegral_eq_lmarginal_univ 0]
-/
/-

lemma ennreal_rpow_inv {a b : ℝ≥0∞} {z : ℝ} (hz: z ≠ 0) (h : a^ z = b) : b ^ z⁻¹ = a := by
  rw[← h]
  exact ENNReal.rpow_rpow_inv hz a

lemma one_ne_top_trick {a : ℝ≥0∞} (h: a = 1) : a ≠ ⊤ := by
  rw[h]
  simp only [ne_eq, one_ne_top, not_false_eq_true]

lemma enorm_norm_sum_one {α : Type*} {f : α → ℝ} (hf : 0 ≤ f) (h : ∑' (a : α), ‖f a‖ₑ = 1) :
    ∑' (a : α), f a = 1 := by
  refine ofReal_eq_one.mp ?_
  rw[← h, ENNReal.ofReal_tsum_of_nonneg hf]
  · congr
    ext a
    rw [Real.enorm_eq_ofReal (hf a)]
  apply (NNReal.summable_mk hf).1
  apply ENNReal.tsum_coe_ne_top_iff_summable.1
  apply one_ne_top_trick
  rw[← h]
  congr
  ext a
  rw [Real.enorm_eq_ofReal (hf a)]
  exact Eq.symm (ofReal_eq_coe_nnreal (hf a))


lemma edist_top_lt_top {a : ℝ≥0∞} (h: edist a ⊤ < ⊤): a = ⊤ := by
  contrapose h
  rw[ennreal_edist_le']
  · simp only [ne_eq, h, not_false_eq_true, top_sub, lt_self_iff_false]
  exact OrderTop.le_top a

variable {ι : Type*} [Fintype ι]

def L_two (f : (ι → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x in (Set.univ.pi fun (_ : ι) => Set.Ico (0 : ℝ) 1), (f x)^(2 : ℝ)) ^ (1 / (2 : ℝ))

lemma L_two_triangle {f g : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g):
    L_two (f + g) ≤ L_two f + L_two g := by
  unfold L_two
  apply ENNReal.lintegral_Lp_add_le
  · fun_prop
  · fun_prop
  norm_num

lemma ennreal_add_edist_le (a b : ℝ≥0∞) : b ≤ a + edist a b := by
  by_cases h: a ≤ b
  · rw [ennreal_edist_le' h]
    exact le_add_tsub
  rw [ennreal_edist_le (le_of_not_ge h)]
  calc
    b ≤ a := le_of_not_ge h
    _ ≤ a + (a - b) := le_self_add

omit [Fintype ι] in
@[fun_prop] lemma ennreal_edist_measurable {f g : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g):
    Measurable (fun x ↦ (edist (f x) (g x))) := by
  unfold edist instEDistENNReal_thesis
  simp only
  fun_prop

lemma L_two_mono {f g : (ι → ℝ) → ℝ≥0∞} (h : f ≤ g):
    L_two f ≤ L_two g := by
  unfold L_two
  apply ENNReal.rpow_le_rpow (h₂ := by norm_num)
  apply lintegral_mono
  intro a
  apply ENNReal.rpow_le_rpow (h₂ := by norm_num)
  exact h a

lemma L_two_edist_le
    {f g : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (h : (L_two f) ≤ (L_two g)):
    edist (L_two f) (L_two g) ≤ L_two fun x ↦ (edist (f x) (g x)) := by
  rw [ennreal_edist_le' h]
  apply tsub_le_iff_left.mpr
  calc
    L_two g
      ≤ L_two (f + fun x ↦ edist (f x) (g x)) := by
      apply L_two_mono
      intro
      apply ennreal_add_edist_le
    _ ≤ L_two f + L_two fun x ↦ edist (f x) (g x) := by
      apply L_two_triangle hf
      exact ennreal_edist_measurable hf hg

lemma L_two_edist {f g : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g):
    edist (L_two f) (L_two g) ≤ L_two fun x ↦ (edist (f x) (g x)) := by
  by_cases h : (L_two f) ≤ (L_two g)
  · exact L_two_edist_le hf hg h
  rw[ennreal_edist_symm]
  apply le_trans (L_two_edist_le hg hf (le_of_not_ge h))
  apply le_of_eq
  simp only [ennreal_edist_symm]

-/

lemma get_rid{n : ℕ}(i : Fin n): (↑i : ℕ) < n + 1 := by
  obtain ⟨_, _⟩ := i
  linarith

variable {J : Type*} [LinearOrder J] {m : ℕ} {f : Fin (m + 1) → (Fin 2 → J)}

def IsBad (i : Fin m): Prop := f ⟨↑i, get_rid i⟩ 1 ≠ f i.succ 0

def BadSet (f : Fin (m + 1) → (Fin 2 → J)): Finset (Fin m) := {i | IsBad (f := f) i}

lemma subone_fin {i m : ℕ} (h : i < m + 2) : i - 1 < m + 1 := by
  contrapose h
  simp only [not_lt] at *
  calc
    m + 2
      = (m + 1) + 1 := by linarith
    _ ≤ i - 1 + 1 := by gcongr
    _ ≤ i := by
      refine Nat.add_le_of_le_sub ?_ (le_refl (i-1))
      contrapose h
      simp_all only [not_le, Nat.lt_one_iff, zero_tsub, nonpos_iff_eq_zero, Nat.add_eq_zero,
        one_ne_zero, and_false, not_false_eq_true]

def FillOne (h : (BadSet f).Nonempty) : Fin (m + 2) → (Fin 2 → J) :=
  fun ⟨i, ih⟩ ↦ by
    let ⟨s,sh⟩ := Finset.min' (BadSet f) h
    by_cases is : i ≤ s
    · use f ⟨i, by linarith⟩
    by_cases is': i = s + 1
    · use (fun j ↦ if hj: j = 0 then (f ⟨s, by linarith⟩ 1) else f ⟨s+1, by linarith⟩ 0)
    use f ⟨i-1, subone_fin ih⟩

omit [LinearOrder J] in
lemma fillone_card (h : (BadSet f).Nonempty) : (BadSet f).card = (BadSet (FillOne h)).card + 1 := by
  refine Finset.card_eq_of_bijective ?_ (fun a ↦ ?_) ?_ ?_
  sorry

omit [LinearOrder J] in
lemma badset_nonempty (h : 2 ≤ (BadSet f).card) : (BadSet f).Nonempty := by
  refine Finset.one_le_card.mp ?_
  linarith

def FillOnequick (f : Fin (m + 1) → Fin 2 → J) : Fin (m + 2) → (Fin 2 → J) :=
  if h : (BadSet f).Nonempty then FillOne h else
    (fun i ↦ if hi : i.val < m + 1 then f ⟨i.val, hi⟩ else f 0)

def Fillk (f : Fin (m + 1) → Fin 2 → J) (k : ℕ) :
    Fin (m + k + 1) → Fin 2 → J := by
  match k with
  | 0 => use f
  | r + 1 =>
    have : m + (r + 1) + 1 = (m + r) + 2 := by ring
    rw[this]
    let g := (Fillk f r)
    use FillOnequick g

omit [LinearOrder J] in
theorem Fillk_badset_card (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k ≤ (BadSet f).card) :
    (BadSet (Fillk f k)).card + k = (BadSet f).card := by
  induction' k with k hk'
  · unfold Fillk
    rw[add_zero]
  specialize hk' (Nat.le_of_succ_le hk)
  rw[← hk']
  have ne: (BadSet (Fillk f k)).Nonempty := by
    refine Finset.card_pos.mp ?_
    contrapose hk
    simp_all only [Finset.card_pos, Finset.not_nonempty_iff_eq_empty, not_le, Finset.card_empty,
      zero_add, lt_add_iff_pos_right, zero_lt_one]
  nth_rw 1 [Fillk]
  simp only [eq_mpr_eq_cast, cast_eq]
  have : (BadSet (FillOnequick (Fillk f k))).card + (k + 1)
      = (BadSet (FillOnequick (Fillk f k))).card + 1 + k := by ring
  rw[this]
  unfold FillOnequick
  simp only [ne, ↓reduceDIte, Nat.add_right_cancel_iff]
  rw[← fillone_card]

omit [LinearOrder J] in
theorem Fillk_badset_card' (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k ≤ (BadSet f).card) :
    (BadSet (Fillk f k)).card= (BadSet f).card - k := by
  refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
  exact Eq.symm (Fillk_badset_card f hk)

omit [LinearOrder J] in
theorem Fillk_badset_nonempty (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k < (BadSet f).card) :
    (BadSet (Fillk f k)).Nonempty := by
  refine Finset.one_le_card.mp ?_
  rw[Fillk_badset_card' f (le_of_lt hk)]
  exact Nat.le_sub_of_add_le' hk

omit [LinearOrder J] in
lemma Fillk_badset_fillup (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k < (BadSet f).card) :
    Fillk f (k + 1) = FillOne (Fillk_badset_nonempty f hk) := by
  nth_rw 1 [Fillk]
  unfold FillOnequick
  simp only [Fillk_badset_nonempty f hk, ↓reduceDIte, eq_mpr_eq_cast, cast_eq]

def FillUp (f : Fin (m + 1) → Fin 2 → J) := Fillk f (BadSet f).card

omit [LinearOrder J] in
lemma fillup_badset (f : Fin (m + 1) → Fin 2 → J) : BadSet (FillUp f) = ∅ := by
  refine Finset.card_eq_zero.mp ?_
  unfold FillUp
  rw [Fillk_badset_card'] <;> simp

omit [LinearOrder J] in
theorem fillup_endpoint :
      ∀ i : Fin (m + (BadSet f).card), FillUp f ⟨↑i, get_rid i⟩ 1 = FillUp f i.succ 0 := by
    have := fillup_badset f
    unfold BadSet IsBad at this
    intro i
    contrapose this
    refine Finset.nonempty_iff_ne_empty.mp ?_
    use i
    simp_all only [Fin.isValue, ne_eq, Finset.mem_filter, Finset.mem_univ, not_false_eq_true,
      and_self]

def pairmon (f : Fin (m + 1) → Fin 2 → J): Prop :=
  (∀ (i : Fin (m + 1)), f i 0 ≤ f i 1) ∧ (∀ (i : Fin m), f ⟨i, get_rid i⟩ 1 ≤ f i.succ 0)

theorem fillone_pairmon (mon : pairmon f) (h : (BadSet f).Nonempty):
    pairmon (FillOne h) := by
  constructor
  · intro ⟨i, hi⟩
    unfold FillOne
    simp
    by_cases hi': i ≤ ↑((BadSet f).min' h)
    · simp only [hi', ↓reduceDIte, Fin.isValue]
      apply mon.1
    simp [hi']
    by_cases hi'': i = ↑((BadSet f).min' h) + 1
    · simp only [hi'', ↓reduceIte, Fin.isValue, one_ne_zero]
      apply le_trans' (mon.2 ⟨(↑((BadSet f).min' h) : ℕ), ((BadSet f).min' h).isLt⟩)
      apply le_of_eq
      congr
    simp only [hi'', ↓reduceIte, Fin.isValue]
    apply mon.1
  intro ⟨i, hi⟩
  unfold FillOne
  by_cases hi': i < ↑((BadSet f).min' h)
  · simp [le_of_lt hi']
    have : i + 1 ≤ ↑((BadSet f).min' h) := by exact hi'
    simp [this]
    have := mon.2 ⟨i, by
      apply lt_trans hi'
      exact ((BadSet f).min' h).isLt⟩
    simp at this
    apply le_trans this
    apply le_of_eq
    congr
  by_cases hi'': i = ↑((BadSet f).min' h)
  · simp [hi'']
  have s1: ¬(i ≤ ↑((BadSet f).min' h)) := by
    simp_all only [not_lt, not_le]
    exact Nat.lt_of_le_of_ne hi' fun a ↦ hi'' (id (Eq.symm a))
  simp only [↓reduceDIte, Fin.isValue, dite_eq_ite, Fin.succ_mk, Nat.add_right_cancel_iff,
    add_tsub_cancel_right, ge_iff_le, s1, hi'']
  simp_all only [not_lt, not_le, Fin.isValue]
  have : ¬ i + 1 ≤ ↑((BadSet f).min' h) := by
    simp only [not_le]
    linarith
  simp only [Fin.isValue, this, ↓reduceDIte, ge_iff_le]
  by_cases hi''': i = ↑((BadSet f).min' h) + 1 <;> simp [hi''']
  have := mon.2 ⟨i-1, by
    refine Nat.sub_lt_left_of_lt_add ?_ ?_
    simp at this
    · exact Nat.zero_lt_of_lt s1
    rwa [add_comm]⟩
  simp at this
  apply le_trans this
  apply le_of_eq
  congr
  refine Nat.sub_one_add_one_eq_of_pos ?_
  exact Nat.zero_lt_of_lt s1

theorem fillk_pairmon {k : ℕ} (hk : k ≤ (BadSet f).card) (mon : pairmon f):
    pairmon (Fillk f k) := by
  induction' k with k hk'
  · unfold Fillk
    exact mon
  rw[Fillk_badset_fillup]
  · apply fillone_pairmon
    exact hk' (Nat.le_of_succ_le hk)
  exact hk

theorem fillup_pairmon (mon: pairmon f): pairmon (FillUp f) := by
  apply fillk_pairmon
  · exact (Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a ↦ a).mpr rfl
  exact mon


def AllowedSeq  :=
  {s : Finset (Fin 2 → J) | s = ∅ ∨ ∃ m, ∃ f : Fin (m + 1) → (Fin 2 → J),
    BijOn f univ s ∧
    (∀ i : Fin m, f ⟨↑i, get_rid i⟩ 1 = f i.succ 0) ∧
    pairmon f}

theorem allowseq_is_finclosed (J : Type u) [LinearOrder J]:
    IsFinclosed ((AllowedSeq (J := J))) := by
  unfold IsFinclosed
  constructor
  · unfold AllowedSeq
    simp only [Fin.isValue, mem_setOf_eq, Finset.coe_empty, bijOn_empty_iff_left, univ_eq_empty_iff,
      not_isEmpty_of_nonempty, false_and, exists_false, or_false]
  use 2
  intro u ⟨v, vh, uv⟩
  obtain vh|vh := vh
  · rw[vh] at uv
    use ∅
    unfold AllowedSeq
    simp_all only [Finset.subset_empty, Fin.isValue, mem_setOf_eq, Finset.coe_empty,
      bijOn_empty_iff_left, univ_eq_empty_iff, not_isEmpty_of_nonempty, false_and, exists_false,
      or_false, subset_refl, Finset.card_empty, CharP.cast_eq_zero, mul_zero, le_refl,
      and_self]
  obtain ⟨m, f, bij, ep, mon⟩ := vh
  sorry




/-
 {s s' : Finset (Fin 2 → J)} (s's : s' ⊂ s)
    --(hs : ∃ m : ℕ, ∃ (f : Fin m → (Fin 2 → J)), ∀  = 0)

variable {n : ℕ} {g : Fin (n + 1) → (Fin 2 → J)} (mon : ∀ i, g i 0 < g i 1)
    (ep : ∀ i : Fin n, g ⟨↑i, get_rid i⟩ 1 = g i.succ 0) (bij : Set.BijOn g univ s)

def isgone (i : Fin (n + 1)): Prop :=
  g i ∉ s'

def ridset (s' : Finset (Fin 2 → J)) {n : ℕ} (g : Fin (n + 1) → Fin 2 → J):
    Set (Fin (n + 1)) := {i | isgone (g := g) (s' := s') i}

omit [LinearOrder J] in
lemma ridset_nonempty (s's : s' ⊂ s) (bij : Set.BijOn g univ s): (ridset s' g).Nonempty := by
  obtain ⟨a, ahs, ahs'⟩ := Set.exists_of_ssubset s's
  have as: a ∈ s := ahs
  have as': a ∉ s' := ahs'
  clear ahs ahs'
  use (Function.invFunOn g (@univ (Fin (n+1)))) a
  unfold ridset isgone
  simp only [mem_setOf_eq]
  suffices : g ((Function.invFunOn g (@univ (Fin (n+1)))) a) = a
  · rwa [this]
  obtain ⟨_, h⟩ := Set.BijOn.invOn_invFunOn bij
  unfold RightInvOn  LeftInvOn at h
  apply h
  exact as

omit [LinearOrder J] in
lemma ridest_nonempty_tofinset (s's : s' ⊂ s) (bij : Set.BijOn g univ s): (ridset s' g).toFinset.Nonempty := by
  refine Aesop.toFinset_nonempty_of_nonempty ?_
  exact ridset_nonempty s's bij

def maxgone := Finset.min' (ridset (g := g) (s' := s')).toFinset (ridest_nonempty_tofinset s's bij)

-/


--lemma fillone_nonempty
