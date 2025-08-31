import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
open Function Set Classical MeasureTheory
noncomputable section

namespace Calderon
open ENNReal Real NNReal
#check MeasurePreserving

variable{ι X Y Z : Type*} [Fintype ι] [MeasurableSpace Z] (μ : Measure Z)

section edistsec

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

end edistsec

#check Lex ι
--variable{a b : ι}(n : ℕ)
lemma enorm_ae_zero_iff [MeasurableSpace X](μ : Measure X)(f : X → ℝ):
  (fun x ↦ (‖f x‖ₑ : ENNReal)) =ᶠ[ae μ] (0 : X → ENNReal) ↔ f =ᶠ[ae μ] (0 : X → ℝ) := by
  constructor
  · intro h
    apply eLpNormEssSup_eq_zero_iff.mpr at h
    refine eLpNormEssSup_eq_zero_iff.mp ?_
    unfold eLpNormEssSup at *
    rw[← h]
    simp only [enorm_eq_self]
  intro h
  have : (0 : X → ENNReal) = fun x ↦ ‖(0 : ℝ)‖ₑ := by ext _; simp
  rw[this]
  exact Filter.eventuallyEq_of_mem h fun ⦃x⦄ ↦ congrArg enorm

lemma prod_eq_top_iff{α : Type*}(s : Finset α)(f : α → ENNReal): ∏ a ∈ s, f a = ⊤ ↔ (∀ a ∈ s, f a ≠ 0) ∧ (∃ a ∈ s, f a = ⊤) := by
  constructor
  · intro h
    contrapose h
    simp only [Decidable.not_and_iff_or_not, not_exists] at h
    simp at h
    obtain h|h := h
    · suffices : ∏ a ∈ s, f a = 0
      · rw[this]
        simp only [zero_ne_top, not_false_eq_true]
      exact Finset.prod_eq_zero_iff.mpr h
    apply ENNReal.prod_ne_top
    intro a
    specialize h a
    tauto
  intro h
  have : (∏ a ∈ s, f a).toReal = 0 := by
    rw [@toReal_prod]
    obtain ⟨a,ah⟩ := h.2
    apply Finset.prod_eq_zero (i := a) (ah.1)
    simp [ah.2]
  apply (ENNReal.toReal_eq_zero_iff _).1 at this
  obtain this|this := this
  · contrapose this
    apply Finset.prod_ne_zero_iff.2 h.1
  exact this


/-For lack of having nothing else found:-/
def unit{α β : Type*}[AddMonoid β](a : α): β → α → β := --Read α are the indices, so "a" is the "a-th" index (basically α = ι and β = ℝ or something)
  fun s b => if a = b then s else 0

theorem unit_add{α β : Type*}[AddMonoid β](a: α)(x y : β): unit a x + unit a y = unit a (x+y) := by
  unfold unit
  ext t
  simp
  by_cases ht: a = t
  all_goals simp [ht]

@[fun_prop]theorem unit_measurable'{α β : Type*}[AddMonoid β][MeasurableSpace β](a c : α): Measurable (fun x : β ↦ (unit a x c)) := by
  unfold unit
  by_cases h: a = c
  · simp [h]
    exact fun ⦃t⦄ a ↦ a
  simp [h]

@[fun_prop]theorem unit_measurable{α β : Type*}[AddMonoid β][MeasurableSpace α][MeasurableSpace β](a : α)(b : β)(ha: MeasurableSet {a}): Measurable (unit a b) := by
  unfold unit
  refine Measurable.ite ?_ ?_ ?_
  · simp
    exact ha
  · fun_prop
  fun_prop
#check zero_add
/-Add some unit measurable thingy here-/ --also for the other permutations i guess?
#print unit_measurable'
--#check Function.single
--end rw, function update
def iterate'_up_to: Fin (Nat.card ι + 1) → (ι → X → X)  → (Fin (Nat.card ι) → ℕ) → X → X :=
  fun m S k x ↦ by{
    by_cases hm: m.val = 0
    · use x
    obtain ⟨m,hm'⟩ := m
    have t1: m - 1 < Nat.card ι := by
      simp only [Nat.card_eq_fintype_card]
      rw[Fintype.card_eq_nat_card]
      exact Nat.sub_one_lt_of_le (Nat.zero_lt_of_ne_zero hm) (Nat.le_of_lt_succ hm')
    have t2: m - 1 < Nat.card ι + 1 := by
      calc
        m - 1 ≤ m := by exact Nat.sub_le m 1
          _   < Nat.card ι + 1 := hm'
    use (S ((Finite.equivFin ι).symm ⟨m-1,t1⟩))^[k ⟨m-1,t1⟩] (iterate'_up_to ⟨m-1, t2⟩ S k x)
  }
  termination_by m => m.val
  decreasing_by
    exact Nat.sub_one_lt hm

#check @add_zero
#print iterate'_up_to

@[simp] lemma iterate'_up_to_zero(S : ι → X → X)(k : (Fin (Nat.card ι) → ℕ)): iterate'_up_to 0 S k = id := by
  ext x
  unfold iterate'_up_to
  simp only [Fin.val_zero, ↓reduceDIte, id_eq]

lemma lt_add_one_down{m n : ℕ}(hm: m+1 < n + 1): m < n := by exact Nat.succ_lt_succ_iff.mp hm

lemma iterate'_up_to_equal_up{m n : (Fin (Nat.card ι + 1))}(mn : m = n)(S : ι → X → X)(k : (Fin (Nat.card ι)) → ℕ): iterate'_up_to m S k = iterate'_up_to n S k := by rw[mn]

lemma sub_one_lt{n m : ℕ}(hm : m < n + 1)(hm' : m ≠ 0): m-1 < n := by
  contrapose hm
  simp_all only [ne_eq, not_lt]
  calc
    n + 1 ≤ (m-1) + 1 := by exact Nat.add_le_add_right hm 1
        _ = m := Nat.succ_pred_eq_of_ne_zero hm'


lemma iterate'_up_to_add_one{m : ℕ}(hm: m + 1 < Nat.card ι + 1)(S : ι → X → X)(k : (Fin (Nat.card ι) → ℕ)):
  iterate'_up_to ⟨m+1, hm⟩ S k = (S ((Finite.equivFin ι).symm ⟨m, lt_add_one_down hm⟩))^[k ⟨m, Nat.succ_lt_succ_iff.mp hm⟩] ∘ (iterate'_up_to ⟨m, Nat.lt_of_succ_lt hm⟩ S k) := by
    ext x
    set f := (S ((Finite.equivFin ι).symm ⟨m, lt_add_one_down hm⟩))^[k ⟨m, Nat.succ_lt_succ_iff.mp hm⟩] ∘ (iterate'_up_to ⟨m, Nat.lt_of_succ_lt hm⟩ S k)
    unfold iterate'_up_to f --fragen
    simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceDIte,
      add_tsub_cancel_right, comp_apply]

def iterate' : (ι → X → X)  → (Fin (Nat.card ι) → ℕ) → X → X := iterate'_up_to ⟨Nat.card ι, lt_add_one (Nat.card ι)⟩

def iterate'_up_to_quick : ℕ → (ι → X → X) → (Fin (Nat.card ι) → ℕ) → X → X :=
  fun m S k x ↦ if hm: m < (Nat.card ι + 1) then iterate'_up_to ⟨m,hm⟩ S k x else x

lemma iterate'_up_to_quick_zero(S : ι → X → X)(k : Fin (Nat.card ι) → ℕ): iterate'_up_to_quick 0 S k = id := by
  unfold iterate'_up_to_quick
  simp only [Nat.card_eq_fintype_card, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt,
    or_true, ↓reduceDIte, Fin.zero_eta, iterate'_up_to_zero, id_eq]
  rfl

lemma iterate'_up_to_is_quick(m : ℕ)(hm : m < (Nat.card ι) + 1)(S : ι → X → X)(k : Fin (Nat.card ι) → ℕ): iterate'_up_to_quick m S k = iterate'_up_to ⟨m,hm⟩ S k := by
  unfold iterate'_up_to_quick
  simp only [hm, ↓reduceDIte]

lemma add_one_lt{n m : ℕ}(hm: m < n): m < n+1 := by
  calc
    m < n := by exact hm
      _< n+1 := by exact lt_add_one n

lemma iterate'_up_to_neg_one{m : ℕ}(hm: m < Nat.card ι + 1)(hm' : m ≠ 0)(S : ι → X → X)(k : (Fin (Nat.card ι) → ℕ)):
  iterate'_up_to ⟨m, hm⟩ S k = (S ((Finite.equivFin ι).symm ⟨m-1, sub_one_lt hm hm'⟩))^[k ⟨m-1, sub_one_lt hm hm'⟩] ∘ (iterate'_up_to ⟨m-1, tsub_lt_of_lt hm⟩ S k) := by
    rw[← iterate'_up_to_is_quick, ← iterate'_up_to_is_quick]
    set n := m-1
    have hn: m = n+1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero hm')
    have : iterate'_up_to_quick m S k = iterate'_up_to_quick (↑(NatCast.natCast n+1)) S k := by
      rw[hn]
      simp
    --set h := iterate'_up_to_quick (↑(NatCast.natCast m)) S k
    rw[this]
    --have : NatCast.natCast n + 1 < Nat.card ι + 1 := by unfold n; simp; apply sub_one_lt; sorry; exact hm'
    rw[iterate'_up_to_is_quick]
    rw[iterate'_up_to_add_one]
    swap
    · unfold n
      simp
      rw[← Nat.card_eq_fintype_card]
      exact sub_one_lt hm hm'
    unfold n
    repeat rw[← iterate'_up_to_is_quick]
    have : iterate'_up_to_quick (NatCast.natCast (m - 1)) S k = iterate'_up_to_quick (m - 1) S k := by
      suffices : NatCast.natCast (m-1) = m-1
      · rw[this]
      simp
    rfl

def pairwise_commuting{α : Type*}(S : α → X → X):  Prop :=
  ∀ a b : α, (S a) ∘ (S b) = (S b) ∘ (S a)
#check Fin.pos'

theorem iterate'_up_to_zero'(m : Fin (Nat.card ι + 1))(S : ι → X → X): iterate'_up_to m S 0 = id := by
  obtain ⟨m,hm⟩ := m
  induction' m with m hm'
  · simp only [Fin.zero_eta, iterate'_up_to_zero]
  rw[iterate'_up_to_add_one, hm' (Nat.lt_of_succ_lt hm)]
  simp only [Pi.zero_apply, iterate_zero, CompTriple.comp_eq]

@[simp] theorem iterate'_zero(S : ι → X → X): iterate' S 0 = id := by unfold iterate'; apply iterate'_up_to_zero'

lemma fin_add_neg_one{k : ℕ}{m : Fin (k+1)}(hm : m ≠ 0): m.val-1 < k := by
  obtain ⟨m,hm'⟩ := m
  have hm'': m ≠ 0 := by contrapose hm; simp_all
  simp
  by_contra h0
  simp at h0
  have : k + 1 ≤ m := by
    calc
      k + 1 ≤ (m-1) + 1 := by linarith
        _   = m := Nat.succ_pred_eq_of_ne_zero hm''
  linarith

theorem iterate'_up_to_end_zero(m : Fin (Nat.card ι + 1))(hm : m ≠ 0)(S : ι → X → X)(k : Fin (Nat.card ι) → ℕ)(hk: k ⟨m-1,fin_add_neg_one hm⟩ = 0): iterate'_up_to m S k = iterate'_up_to (m-1) S k := by
  set f := iterate'_up_to (m - 1) S k
  obtain ⟨m,hm'⟩ := m
  have hm : m ≠ 0 := by
    by_contra h0
    have : (⟨m,hm'⟩ : Fin (Nat.card ι + 1)) = 0 := by simp [h0]
    contradiction
  rw[iterate'_up_to_neg_one]
  --unfold f
  rw[hk]
  simp
  unfold f
  apply iterate'_up_to_equal_up
  ext
  swap
  exact hm
  simp
  have hm''': m-1 < Nat.card ι + 1 := by exact tsub_lt_of_lt hm'
  rw [@Fin.coe_sub_one]
  simp [*]

theorem iterate'_up_to_same(m : Fin (Nat.card ι + 1))(S : ι → X → X){k k': Fin (Nat.card ι) → ℕ}(h: ∀ n : Fin (Nat.card ι), (↑n : ℕ) < m → k n = k' n):
  iterate'_up_to m S k = iterate'_up_to m S k' := by
    obtain ⟨m,hm'⟩ := m
    induction' m with m hm
    · simp only [Fin.zero_eta, iterate'_up_to_zero]
    rw[iterate'_up_to_add_one, iterate'_up_to_add_one]
    have : k ⟨m, lt_add_one_down hm'⟩ = k' ⟨m, lt_add_one_down hm'⟩ := by
      specialize h ⟨m, lt_add_one_down hm'⟩
      apply h
      simp
    rw[this]
    have hm'': m < Nat.card ι + 1 := by exact Nat.lt_of_succ_lt hm'
    specialize hm hm''
    have : iterate'_up_to ⟨m, hm''⟩ S k = iterate'_up_to ⟨m, hm''⟩ S k' := by
      apply hm
      intro n
      simp
      intro hm
      apply (h n)
      simp
      linarith
    rw[this]


theorem unit_sub_iterate'_up_to(m : Fin (Nat.card ι + 1))(hm : m ≠ 0){S : ι → X → X}(k: Fin (Nat.card ι) → ℕ):
  iterate'_up_to m S (k- Calderon.unit (α := (Fin (Nat.card ι))) (β := ℕ) (a := ⟨m-1,fin_add_neg_one hm⟩) (k ⟨m-1, fin_add_neg_one hm⟩)) =
  iterate'_up_to (m-1) S k := by
    rw[iterate'_up_to_neg_one]
    swap
    · by_contra h0
      suffices: m=0
      · contradiction
      ext
      exact h0
    unfold unit
    simp only [Pi.sub_apply, ↓reduceIte, tsub_self, CompTriple.comp_eq, iterate_zero]
    have : ⟨↑m - 1, tsub_lt_of_lt m.isLt⟩ = m-1 := by
      obtain ⟨m,hm''⟩ := m
      simp
      ext
      simp
      rw [@Fin.coe_sub_one]
      simp [hm]
    rw[this]
    apply iterate'_up_to_same
    intro n hn
    simp
    suffices : ¬ ⟨↑m - 1, fin_add_neg_one hm⟩ = n
    · simp [this]
    contrapose hn
    simp_all only [Decidable.not_not, not_lt]
    rw[← hn]
    apply le_of_eq
    simp
    obtain ⟨m,hm''⟩ := m
    simp
    have hh: m-1 < Nat.card ι + 1 := by
      exact tsub_lt_of_lt hm''
    exact Fin.eq_mk_iff_val_eq.mp (id (Eq.symm this))

lemma fun_comp_eq{α β γ : Type*}{f f': α → β}{g g' : β  → γ}(h1 : f = f')(h2: g = g'): g ∘ f = g' ∘ f' := by rw[h1,h2]

theorem iterate'_up_to_add_end(m : Fin (Nat.card ι + 1))(hm : m ≠ 0){S : ι → X → X}(k: Fin (Nat.card ι) → ℕ):
  iterate'_up_to m S k = (S ((Finite.equivFin ι).symm ⟨m-1, fin_add_neg_one hm⟩))^[k ⟨m-1,fin_add_neg_one hm⟩] ∘ iterate'_up_to m S (k- Calderon.unit (α := (Fin (Nat.card ι))) (β := ℕ) (a := ⟨m-1,fin_add_neg_one hm⟩) (k ⟨m-1, fin_add_neg_one hm⟩)) := by
    set f := (S ((Finite.equivFin ι).symm ⟨m-1, fin_add_neg_one hm⟩))^[k ⟨m-1,fin_add_neg_one hm⟩]
    obtain ⟨m,hm'⟩ := m
    have hm'': (m-1)+1 = m := by
      refine Nat.sub_add_cancel ?_
      contrapose hm
      simp_all
    rw[unit_sub_iterate'_up_to _ hm]

    /-have : iterate'_up_to m S (k- Calderon.unit (α := (Fin (Nat.card ι))) (β := ℕ) (a := ⟨m-1,fin_add_neg_one hm⟩) (k ⟨m-1, fin_add_neg_one hm⟩)) = iterate'_up_to (m-1) S (k- Calderon.unit (α := (Fin (Nat.card ι))) (β := ℕ) (a := ⟨m-1,fin_add_neg_one hm⟩) (k ⟨m-1, fin_add_neg_one hm⟩)) := by
      refine
        iterate'_up_to_end_zero ↑m ?_ S
          (k - unit ⟨m - 1, fin_add_neg_one hm⟩ (k ⟨m - 1, fin_add_neg_one hm⟩)) ?_
      simp
      intro h0
      obtain ⟨p,pj⟩ := h0
      rw[pj] at hm'
      contrapose hm'
      simp
      rename_i joa
      contrapose hm
      simp
      simp at hm
      rw[hm] at pj
      simp at pj
      simp [pj]

      simp only [Pi.sub_apply]
      refine Eq.symm (Nat.eq_sub_of_add_eq' ?_)
      simp only [add_zero]

      have : (↑(↑m : Fin (Nat.card ι + 1)) : ℕ) - 1 < Nat.card ι := by
        sorry
      have : ⟨(↑(↑m : Fin (Nat.card ι + 1)) : ℕ) - 1, this⟩ = (⟨m-1,fin_add_neg_one hm⟩ : Fin (Nat.card ι)) := by
        ext
        simp
        sorry
      rw[this]
      unfold unit
      simp
    -/

    rw[iterate'_up_to_neg_one]
    apply fun_comp_eq
    · refine Eq.symm (iterate'_up_to_equal_up ?_ S k)
      · ext
        simp
        rw [@Fin.coe_sub_one]
        simp [hm]
    · rfl
    by_contra h0
    suffices : (⟨m,hm'⟩: Fin (Nat.card ι + 1)) = 0
    · contradiction
    simp [h0]

lemma sub_unit_iterate(m : ℕ)(hm : m + 1 < Nat.card ι + 1){S : ι → X → X}(k: Fin (Nat.card ι) → ℕ):
  iterate'_up_to ⟨m+1,hm⟩ S (k- Calderon.unit (α := (Fin (Nat.card ι))) (β := ℕ) (a := ⟨m, lt_add_one_down hm⟩) (k ⟨m, lt_add_one_down hm⟩)) =
  iterate'_up_to ⟨m, Nat.lt_of_succ_lt hm⟩ S (k- Calderon.unit (α := (Fin (Nat.card ι))) (β := ℕ) (a := ⟨m, lt_add_one_down hm⟩) (k ⟨m, lt_add_one_down hm⟩)) := by
    have : (⟨m + 1, hm⟩ : Fin (Nat.card ι + 1)) ≠  0 := by
      exact Ne.symm (ne_of_beq_false rfl)
    rw[iterate'_up_to_end_zero]
    refine iterate'_up_to_equal_up ?_ S (k - unit ⟨m, lt_add_one_down hm⟩ (k ⟨m, lt_add_one_down hm⟩))
    ext
    rw [@Fin.coe_sub_one]
    all_goals simp [this]
    unfold unit
    simp


lemma fun_comm_pow{α : Type*}{f g : α → α}(n m : ℕ)(h : f ∘ g = g ∘ f): f^[n] ∘ g^[m] = g^[m] ∘ f^[n] := by
  induction' n with n hn
  · simp
  nth_rw 1[@iterate_add, add_comm, @iterate_add]
  simp only [iterate_one]
  rw[← comp_assoc]
  suffices : g^[m] ∘ f = f ∘ g^[m]
  · rw[this]
    --nth_rw 2[comp_assoc, ← hn]
    nth_rw 2[comp_assoc]
    rw[← hn, ← comp_assoc]
    nth_rw 2 3[← iterate_one f]
    rw[← iterate_add, ←iterate_add, add_comm]
  clear n hn
  induction' m with m hm
  · simp
  rw[iterate_add, ← comp_assoc, ← hm]
  nth_rw 2[comp_assoc, iterate_one]
  rw[h]
  nth_rw 4[← iterate_one g]
  rw[comp_assoc]


theorem iterate'_comm(m : Fin (Nat.card ι + 1))(r : ℕ)(i : ι){S : ι → X → X}(hS: pairwise_commuting S)(k: Fin (Nat.card ι) → ℕ):
  (S i)^[r] ∘ iterate'_up_to m S k = iterate'_up_to m S k ∘ (S i)^[r] := by
    --revert r
    obtain ⟨m,hm⟩ := m
    induction' m with m hm'
    · simp
    --intro r
    rw[iterate'_up_to_neg_one]
    simp
    rw[comp_assoc]
    rw[← hm']
    repeat rw[← comp_assoc]
    apply fun_comp_eq
    · rfl
    swap
    · simp
    unfold pairwise_commuting at hS
    specialize hS i ((Finite.equivFin ι).symm ⟨m, lt_add_one_down hm⟩)
    simp only [hS, fun_comm_pow]

lemma iterate'_up_to_eq_k(m : Fin (Nat.card ι + 1))(S : ι → X → X){k k' : Fin (Nat.card ι) → ℕ}(h: k = k'): iterate'_up_to m S k = iterate'_up_to m S k' := by rw[h]

theorem iterate'_up_to_add(m : Fin (Nat.card ι + 1)){S : ι → X → X}(hS: pairwise_commuting S)(k k': Fin (Nat.card ι) → ℕ):
  iterate'_up_to m S (k+k') = iterate'_up_to m S k ∘ iterate'_up_to m S k' := by
    obtain ⟨m,hm⟩ := m
    revert k k'
    induction' m with m hm'
    · intro k k'
      simp only [Fin.zero_eta, iterate'_up_to_zero, CompTriple.comp_eq]
    intro k k'
    have hm'': m < Nat.card ι + 1 := by linarith

    specialize hm' hm''
    --rw[hm'] --other way is better
    --rw[iterate'_up_to_add_one]
    --rw[iterate'_up_to_add_one]
    by_cases hm0: m = 0
    · rw[iterate'_up_to_add_one]
      simp [hm0]
      rw[iterate'_up_to_neg_one]
      simp
      rw[iterate'_up_to_neg_one]
      simp
      rw [@iterate_add]
      · exact Nat.one_ne_zero
      exact Nat.one_ne_zero
    have hm0': (⟨m, hm''⟩ : Fin (Nat.card ι + 1)) ≠ 0 := by
      exact Ne.symm (Fin.ne_of_val_ne fun a ↦ hm0 (id (Eq.symm a)))
    nth_rw 2[iterate'_up_to_add_end]
    nth_rw 3[iterate'_up_to_add_end]
    swap
    · exact Ne.symm (ne_of_beq_false rfl)
    swap
    · exact Ne.symm (ne_of_beq_false rfl)
    simp


    rw[iterate'_up_to_add_one]
    --rw[comp_assoc]
    rw[sub_unit_iterate, sub_unit_iterate]
    repeat rw[iterate'_comm]
    rw[comp_assoc]
    nth_rw 2[← comp_assoc]
    rw[iterate'_comm]
    rw[comp_assoc]
    rw[← comp_assoc]
    rw[← iterate_add]
    rw[← hm']
    --apply fun_comp_eq

    apply fun_comp_eq
    simp
    apply iterate'_up_to_same
    intro x hx
    unfold unit
    simp
    suffices : ⟨m, lt_add_one_down hm⟩ ≠ x
    · simp [this]
    contrapose hx
    simp
    simp at hx
    rw[← hx]
    all_goals exact hS


theorem iterate'_up_to_unit(m : Fin (Nat.card ι + 1))(S : ι → X → X)(i : Fin (Nat.card ι))(r : ℕ): iterate'_up_to m S (unit i r) = if (↑i : ℕ) < m then (S ((Finite.equivFin ι).symm i))^[r] else id := by
  obtain ⟨m,hm⟩ := m
  induction' m with m hm'
  · simp
  rw[iterate'_up_to_add_one, hm']
  --have : m < Nat.card ι := by exact lt_add_one_down hm
  --have : m < Nat.card ι + 1 := by exact Nat.lt_of_succ_lt hm
  by_cases h: (↑i : ℕ) < (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin (Nat.card ι + 1))
  · have : (↑i : ℕ) < (⟨m+1, hm⟩ : Fin (Nat.card ι + 1)) := by
      calc
        (↑i : ℕ) < (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin (Nat.card ι + 1)) := h
        _ < (⟨m+1, hm⟩ : Fin (Nat.card ι + 1)) := by simp
    simp only [this, ↓reduceIte]
    suffices : unit i r ⟨m, lt_add_one_down hm⟩ = 0
    · rw[this]
      simp_all
    unfold unit
    suffices : i ≠ ⟨m, lt_add_one_down hm⟩
    · simp [this]
    contrapose h
    simp_all
  simp [-Fin.coe_eq_castSucc, h]
  by_cases h': (↑i : ℕ) < (⟨m+1, hm⟩ : Fin (Nat.card ι + 1))
  · simp [-Fin.coe_eq_castSucc, h']
    suffices : i = ⟨m, lt_add_one_down hm⟩
    · unfold unit
      simp [this]
    simp only [not_lt] at h
    have : (⟨m+1, hm⟩ : Fin (Nat.card ι + 1)) = ⟨m, Nat.lt_of_succ_lt hm⟩ + 1 := by
      ext
      rw [@Fin.val_add_one]
      simp
      suffices : ⟨m, Nat.lt_of_succ_lt hm⟩ ≠ Fin.last (Nat.card ι)
      · simp [this]
      apply Fin.ne_last_of_lt (b := ⟨m+1, hm⟩)
      simp
    rw[this] at h'
    have : (↑i : ℕ) = (↑(⟨m, Nat.lt_of_succ_lt hm⟩ : Fin (Nat.card ι + 1)) : ℕ) := by
      apply le_antisymm
      · obtain ⟨i,ih⟩ := i
        simp
        simp at h'
        set k := (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin (Nat.card ι + 1))
        suffices : (↑i : ℕ) + 1 ≤ k + 1
        · contrapose this
          simp_all
          obtain ⟨k,kh⟩ := k
          have t: k < i := by
            rename_i u
            --clear hm' u h h' S r
            rw[← this] at h'
            have : (↑⟨m + 1, hm⟩ : Fin (Nat.card ι + 1)) = m+1 := by
              simp
            rw[this] at h'
            contrapose u
            simp
            exact Nat.le_of_lt_succ h'
          suffices : ↑(⟨k, kh⟩ : Fin (Nat.card ι + 1)) = k
          · linarith
          simp
            /-#check toFin
            suffices : (k.toFin : Fin (Nat.card ι + 1))  = (⟨k,kh⟩ : Fin (Nat.card ι + 1))
            · rw[← this]
            ext
            simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt,
              Nat.succ_eq_add_one, kh]
          have a1: k +1 < i + 1 := by linarith
          have : (↑k : Fin (Nat.card ι + 1)) + (↑1 : Fin (Nat.card ι + 1)) = (⟨k,kh⟩ : Fin (Nat.card ι + 1)) + 1 := by
            suffices: (↑k : Fin (Nat.card ι + 1)) = ⟨k,kh⟩
            · rw[this]
            ext
            simp only [Fin.val_natCast, kh, Nat.mod_succ_eq_iff_lt,
              Nat.succ_eq_add_one]
          rw[← this]
          have hh: (↑k : Fin (Nat.card ι + 1)) + 1 = (↑(k+1) : Fin (Nat.card ι + 1)):= by exact Eq.symm (Mathlib.Tactic.Ring.inv_add rfl rfl)
          rw[hh]
          clear hh
          have hh: (↑i : Fin (Nat.card ι + 1)) + 1 = (↑(i+1) : Fin (Nat.card ι + 1)):= by exact Eq.symm (Mathlib.Tactic.Ring.inv_add rfl rfl)
          rw[hh]
          clear hh
          exact Fin.natCast_strictMono ih a1-/
        suffices : ↑(k+1) = (↑k : ℕ) + 1
        · rw[this] at h'
          exact h'
        exact Fin.eq_mk_iff_val_eq.mp (id (Eq.symm this))
      exact h
    ext
    simp_all
  simp [-Fin.coe_eq_castSucc, h']
  suffices : i ≠ ⟨m, lt_add_one_down hm⟩
  · unfold unit
    simp [this]
  contrapose h
  simp_all

theorem iterate'_unit(S : ι → X → X)(i : Fin (Nat.card ι))(r : ℕ): iterate' S (unit i r) = (S ((Finite.equivFin ι).symm i))^[r] := by
  unfold iterate'
  rw[iterate'_up_to_unit]

  suffices : (↑i : ℕ) < (⟨Nat.card ι, lt_add_one (Nat.card ι)⟩ : Fin (Nat.card ι + 1))
  · simp only [this]
    simp
  obtain ⟨i,ih⟩ := i
  simp only
  contrapose ih
  simp_all only [not_lt]

theorem iterate'_add{S : ι → X → X}(hS: pairwise_commuting S)(k k': Fin (Nat.card ι) → ℕ):
  iterate' S (k+k') = iterate' S k ∘ iterate' S k' := iterate'_up_to_add ⟨Nat.card ι, lt_add_one (Nat.card ι)⟩ hS k k'

def iterate: (ι → X → X)  → (ι → ℕ) → X → X :=
  fun S k x ↦ iterate' S (fun m ↦ k ((Finite.equivFin ι).symm m)) x

@[simp] theorem iterate_zero(S : ι → X → X): iterate S 0 = id := by
  unfold iterate
  rw[← iterate'_zero S]
  rfl


theorem iterate_unit(S : ι → X → X)(i : ι)(r : ℕ): iterate S (unit i r) = (S i)^[r] := by
  unfold iterate
  have : (fun x ↦ iterate' S (fun m ↦ unit i r ((Finite.equivFin ι).symm m)) x) = iterate' S (fun m ↦ unit i r ((Finite.equivFin ι).symm m)) := by
    simp
  rw[this]
  clear this
  suffices : (fun m ↦ unit i r ((Finite.equivFin ι).symm m)) = unit ((Finite.equivFin ι) i) r
  · rw[this, iterate'_unit]
    simp
  ext x
  unfold unit
  by_cases h: i = (Finite.equivFin ι).symm x
  · simp [h]
  simp [h]
  suffices : (Finite.equivFin ι) i ≠ x
  · simp [this]
  contrapose h
  simp_all
  rw[← h]
  simp

  --rw[← iterate'_unit S ((Finite.equivFin ι) i) r]

--#FIX NAME!!
theorem iterate_add'{S : ι → X → X}(hS: pairwise_commuting S)(k k': ι → ℕ): iterate S (k+k') = iterate S k ∘ iterate S k' := by
  unfold iterate
  rw[← iterate'_add]
  suffices : ((fun m ↦ k ((Finite.equivFin ι).symm m)) + fun m ↦ k' ((Finite.equivFin ι).symm m)) = (fun m ↦ (k + k') ((Finite.equivFin ι).symm m))
  · rw[this]
  ext m
  simp only [Pi.add_apply]
  exact hS

--#check S'^[0]
def MMeasurePreserving(S : ι → Z → Z): Prop :=
  ∀(i : ι), MeasurePreserving (S i) μ μ
#check MMeasurePreserving
theorem iterate'_up_to_measurepreserving(m : Fin (Nat.card ι + 1)){S : ι → Z → Z}(hS: MMeasurePreserving μ S)(k : Fin (Nat.card ι) → ℕ):
  MeasurePreserving (iterate'_up_to m S k) μ μ := by
    obtain ⟨m,mh⟩ := m
    induction' m with m mh'
    · simp only [Fin.zero_eta, iterate'_up_to_zero]
      exact MeasurePreserving.id μ
    rw[iterate'_up_to_add_one]

    apply MeasurePreserving.comp (μa := μ) (μb := μ) (μc := μ) (g := (S ((Finite.equivFin ι).symm ⟨m, lt_add_one_down mh ⟩))^[k ⟨m, lt_add_one_down mh ⟩])
    · exact MeasurePreserving.iterate (hS ((Finite.equivFin ι).symm ⟨m, lt_add_one_down mh⟩)) (k ⟨m, lt_add_one_down mh⟩)
    exact mh' (Nat.lt_of_succ_lt mh)

@[fun_prop] theorem iterate'_up_to_measurable(m : Fin (Nat.card ι + 1)){S : ι → Z → Z}(hS: ∀ i : ι, Measurable (S i))(k : Fin (Nat.card ι) → ℕ): Measurable (iterate'_up_to m S k) := by
  obtain ⟨m,hm'⟩ := m
  induction' m with m hm
  · simp
    fun_prop
  rw[iterate'_up_to_add_one]
  apply Measurable.comp
  · exact Measurable.iterate (hS ((Finite.equivFin ι).symm ⟨m, lt_add_one_down hm'⟩)) (k ⟨m, Nat.succ_lt_succ_iff.mp hm'⟩)
  exact hm (Nat.lt_of_succ_lt hm')

@[simp] theorem iterate'_measurepreserving{S : ι → Z → Z}(hS: MMeasurePreserving μ S)(k : Fin (Nat.card ι) → ℕ):
  MeasurePreserving (iterate' S k) μ μ := iterate'_up_to_measurepreserving μ ⟨Nat.card ι, lt_add_one (Nat.card ι)⟩ hS k

@[fun_prop] theorem iterate'_measurable{S : ι → Z → Z}(hS: ∀ i : ι, Measurable (S i))(k : Fin (Nat.card ι) → ℕ): Measurable (iterate' S k) := by
  unfold iterate'
  fun_prop

@[simp] theorem iterate_measurepreserving{S : ι → Z → Z}(hS: MMeasurePreserving μ S)(k : ι → ℕ): MeasurePreserving (iterate S k) μ μ := by
  unfold iterate
  have : (fun x ↦ iterate' S (fun m ↦ k ((Finite.equivFin ι).symm m)) x) = iterate' S (fun m ↦ k ((Finite.equivFin ι).symm m)) := rfl
  rw[this]
  apply iterate'_measurepreserving
  exact hS

@[fun_prop] theorem iterate_measurable{S : ι → Z → Z}(hS: ∀ i : ι, Measurable (S i))(k : ι → ℕ): Measurable (iterate S k) := by
  unfold iterate
  fun_prop

def MeasurePreservingComm(S : ι → Z → Z): Prop :=
  pairwise_commuting S ∧ MMeasurePreserving (Z := Z) S (μ := μ)

#check (Finite.equivFin ι).symm
#check Finite.exists_equiv_fin ι
--#check Ordering.fintype
--example(h : Finite ι): LinearOrder ι := by apply?
--variable (n : ℕ)(S : ι → X → X)(f : X → Y)[CommMonoid Y][AddCommMonoid Y](x : X)(i : ℕ)(j : ι)
--#check (f ((S j)^[i] x))
def nergodic_avg(n : ℕ)(S : ι → X → X)(f : ι → X → Y)[CommMonoid Y][AddCommMonoid Y](x : X): Y  :=
  ∑ i ∈ Finset.range n, ∏(j :  ι), (f j) ((S j)^[i] x)

def ergodic_avg(n : ℕ)(S : ι → X → X)(f : ι → X → ℝ)(x : X): ℝ :=
  1/n * nergodic_avg n S f x

@[fun_prop] theorem ergodic_avg_measurable(n : ℕ)(S : ι → Z → Z)(f : ι → Z → ℝ)(hf : ∀(i : ι), Measurable (f i))(hS: ∀(j : ι), Measurable (S j)):
  Measurable (ergodic_avg n S f) := by
    unfold ergodic_avg nergodic_avg
    apply Measurable.const_mul
    refine Finset.measurable_sum (Finset.range n) ?_
    intro i _
    refine Finset.measurable_prod Finset.univ ?_
    intro j _
    apply Measurable.comp (hf j)
    exact Measurable.iterate (hS j) i

/-Multilinear averages-/
def multilinear_avg(φ : ℝ → ℝ)(F : ι → (ι → ℝ) → ℝ)(t : NNReal): (ι → ℝ) → ℝ := --maybe wrong, bc no norm in original, omg i hate ENNReal
  fun x ↦ 1/t * ∫ (s : ℝ), φ (1/t * s) * ∏(j : ι), (F j) (x + unit j s)
/-With the most important case:-/
def multilinear_avg_spec(F : ι → (ι → ℝ) → ℝ)(t : NNReal): (ι → ℝ) → ℝ :=
  multilinear_avg (Set.indicator (Ico 0 1) 1) F t

/-Discrete Average, analogue to the thing above for ℤ with φ characteristic function:-/
def discrete_avg(n : ℕ)(F : ι → (ι → ℕ) → ℝ)(k : (ι → ℕ)): ℝ :=
  1/n * ∑ i ∈ Finset.range n, ∏(j : ι), (F j) (k + (unit j i))
--variable(n : Nat)(a : Fin n)
--#check a.succ

@[simp] theorem discrete_avg_zero (F : ι → (ι → ℕ) → ℝ)(k : (ι → ℕ)): discrete_avg 0 F k = 0 := by
  unfold discrete_avg
  simp

/-Version fir ℤ:-/
def discrete_avg'(n : ℕ)(F : ι → (ι → ℤ) → ℝ)(k : (ι → ℤ)): ℝ :=
  1/n * ∑ i ∈ Finset.range n, ∏(j : ι), (F j) (k + (unit j (↑i : ℤ)))

lemma get_rid{n : ℕ}(i : Fin n): (↑i : ℕ) < n + 1 := by
  obtain ⟨_, _⟩ := i
  linarith

def good (g : ℕ → NNReal) (q : ι → ℝ): Prop :=
  (∀(i : ℕ), 1 ≤ i → 1 ≤ g i) ∧
  ∃ C : NNReal, ∀ (m : ℕ) (idx : Fin (m+1) → NNReal)
  (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
  (F : ι → (ι → ℝ) → ℝ) (hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal),
  ∑ i : Fin m, (∫⁻ (a : ι → ℝ), ‖(multilinear_avg_spec F (idx i.succ) a
  - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)‖ₑ^2)
  ≤ C * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))

def good_const' {g : ℕ → NNReal} {q : ι → ℝ} (h : good g q) : NNReal := Exists.choose h.2

def good_const {g : ℕ → NNReal} {q : ι → ℝ} (h : good g q) : NNReal := max 1 (good_const' h)

theorem good_const_good{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q)(m : ℕ)(idx : Fin (m+1) → NNReal)
  (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(F : ι → (ι → ℝ) → ℝ)(hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal):
    ∑ i : Fin m, (∫⁻ (a : ι → ℝ), ‖(multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)‖ₑ^2)
    ≤ (good_const h) * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)) := by
    unfold good_const
    apply le_trans (b := (good_const' h) * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)))
    · apply Exists.choose_spec h.2 <;> assumption
    gcongr
    exact le_max_right 1 (good_const' h)

theorem one_leq_good{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q): ∀(i : ℕ), 1 ≤ i → 1 ≤ g i := h.1

def push_forward(N : ℕ)(S : ι → X → X)(F : X → ℝ)(x : X): (ι → ℕ) → ℝ :=
  fun k ↦ if ∀ i : ι, k i < 2*N then F (iterate S k x) else 0

@[fun_prop] theorem push_forward_measurable [MeasurableSpace X](N : ℕ)(k: ι → ℕ)
    (S : ι → X → X)(F : X → ℝ)(hS : ∀(i : ι), Measurable (S i))(hF : Measurable F):
    Measurable (fun x ↦ push_forward N S F x k) := by
      unfold push_forward
      by_cases h: ∀ (i : ι), k i < 2 * N
      all_goals simp [h]
      fun_prop


def push_forward_many(N : ℕ)(S : ι → X → X)(F : ι → (X → ℝ))(x : X): ι → (ι → ℕ) → ℝ :=
  fun j k ↦ push_forward N S (F j) x k

@[simp] theorem push_forward_zero (i : ι)(S : ι → X → X)(F : X → ℝ)(x : X): push_forward 0 S F x = 0 := by
  unfold push_forward
  ext
  simp
  tauto

end Calderon


namespace Calderon
open ENNReal Real NNReal

variable{ι α β γ : Type*}[Fintype ι] [Inhabited β] (k : ι → ℕ) (n : ℕ)

lemma shift_lemma_ico(f : ℝ → ℝ)(a b c : ℝ): ∫ (x : ℝ) in Ico a b, f x = ∫ (x : ℝ) in Ico (a+c) (b+c), f (x - c) := by
  rw[← MeasureTheory.integral_indicator measurableSet_Ico, ← MeasureTheory.integral_indicator measurableSet_Ico]
  rw[← integral_add_right_eq_self ((Ico a b).indicator f) (-c)]
  congr
  ext x
  unfold indicator
  unfold Ico
  simp
  by_cases h: a + c ≤ x ∧ x < b + c
  all_goals simp only [h, and_self, ↓reduceIte]
  rfl


/- HERE COME FACTS; LATER EXPORT THIS TO SEPERATE FILE -/
theorem fact5_1(F : ι → (ι → ℝ) → ℝ)(t : NNReal)(t0: t ≠ 0)(x : ι → ℝ):
  multilinear_avg_spec F t x = (1/t) * ∫ (s : ℝ) in Ico (∑ (i : ι), x i) ((∑ (i : ι), x i) + t), ∏(j : ι), (F j) (x + Calderon.unit j (s - ∑ (j : ι), (x j))) := by
    unfold multilinear_avg_spec multilinear_avg
    --by_cases t0: t = 0
    --· rw[t0]
    --  simp
    congr 1
    calc
      ∫ (s : ℝ), (Ico 0 1).indicator 1 (1 / ↑t * s) * ∏ j, F j (x + unit j s) =  ∫ (s : ℝ), (Ico 0 1).indicator 1 (1 / ↑t * s) * ∏ j, F j (x + unit j s) := by
        congr
    _ = ∫ (s : ℝ) in Ico 0 ↑t, ∏ j, F j (x + unit j s) := by --hierrrr
      rw[← MeasureTheory.integral_indicator measurableSet_Ico]
      congr 1
      ext a
      by_cases ha: a ∈ Ico 0 ↑t
      · simp [ha]
        unfold indicator
        suffices : (↑t)⁻¹ * a ∈ Ico 0 1
        · simp [this]
        unfold Ico at *
        simp_all
        constructor
        · apply mul_nonneg
          · simp
          exact ha.1
        field_simp
        refine (div_lt_one ?_).mpr ?_
        · simp
          contrapose t0
          simp
          apply le_antisymm
          · exact le_of_not_gt t0
          simp
        exact ha.2
      simp [ha]
      left
      intro h
      unfold Ico at ha
      simp at ha
      by_cases an: 0 ≤ a
      specialize ha an
      contrapose h
      simp
      contrapose h
      simp_all
      refine (one_le_inv_mul₀ ?_).mpr ha
      simp
      exact pos_of_ne_zero t0
      contrapose h
      simp_all
      refine (inv_mul_lt_iff₀' ?_).mpr ?_
      · simp
        exact pos_of_ne_zero t0
      simp [an]
      /-
      have a0: a ≠ 0 := by
        by_contra h0
        rw[h0] at ha
        contrapose t0
        simp
        exact nonpos_iff_eq_zero.mp ha
      -/

    _ = ∫ (s : ℝ) in Ico (∑ i, x i) (∑ i, x i + ↑t), ∏ j, F j (x + unit j (s - ∑ (j : ι), x j)) := by
      rw[add_comm (∑ i, x i) (↑t)]
      rw[shift_lemma_ico _ 0 (↑t : ℝ) (∑ i, x i)]
      simp

lemma prod_proj_continous (i : ι) : Continuous (fun (a : (ι → ℝ) × ℝ) ↦ (a.1) i) := by
  refine { isOpen_preimage := ?_ }
  intro s hs
  apply Metric.isOpen_iff.2
  intro ⟨a, b⟩ h
  simp only [mem_preimage] at h
  have hs': ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s := by exact Metric.isOpen_iff.1 hs
  obtain ⟨ε, εp, hε⟩ := hs' (a i) h
  use ε
  constructor
  · exact εp
  intro ⟨x,y⟩ h'
  simp_all only [gt_iff_lt, Metric.mem_ball, mem_preimage]
  unfold Metric.ball at hε
  suffices : dist (x i) (a i) < ε
  · tauto
  apply lt_of_le_of_lt (b := dist (x, y) (a, b))
  swap
  · exact h'
  rw [@Prod.dist_eq]
  simp only [le_sup_iff]
  left
  exact dist_le_pi_dist x a i

@[fun_prop]
theorem multilinear_avg_spec_measurable
    {F : ι → (ι → ℝ) → ℝ} (hF: ∀ j, Measurable (F j) ) (t : NNReal):
    Measurable (multilinear_avg_spec F t) := by
  by_cases ht: t = 0
  · unfold multilinear_avg_spec multilinear_avg
    rw[ht]
    simp only [NNReal.coe_zero, _root_.div_zero, zero_mul, mem_Ico, le_refl, zero_lt_one, and_self,
      indicator_of_mem, Pi.one_apply, one_mul, measurable_const]
  have : multilinear_avg_spec F t =
      fun x ↦ 1 / ↑t * ∫ (s : ℝ) in Ico (∑ i, x i)
      (∑ i, x i + (↑t : ℝ)), ∏ j, F j (x + unit j (s - ∑ j, x j)) := by
    ext x
    rw[fact5_1]
    exact ht
  rw[this]
  clear this
  apply Measurable.mul
  · fun_prop
  have : (fun (a : ι → ℝ) ↦ ∫ (s : ℝ) in Ico (∑ i, a i) (∑ i, a i + ↑t),
      ∏ j, F j (a + unit j (s - ∑ j, a j))) =
      (fun (a : ι → ℝ) ↦ (∫ (s : ℝ) , (Ico (∑ i, a i) (∑ i, a i + ↑t)).indicator
      (fun s ↦ ∏ j, F j (a + unit j (s - ∑ j, a j))) s)) := by
    ext a
    rw[MeasureTheory.integral_indicator]
    measurability
  rw[this]
  clear this
  let H := fun a ↦ fun (s : ℝ) ↦ (Ico (∑ i, a i) (∑ i, a i + (↑t : ℝ))).indicator
    (fun s ↦ ∏ j, F j (a + unit j (s - ∑ j, a j))) s
  have : (fun (a : ι → ℝ) ↦ (∫ (s : ℝ) , (Ico (∑ i, a i) (∑ i, a i + ↑t)).indicator
      (fun s ↦ ∏ j, F j (a + unit j (s - ∑ j, a j))) s)) = (fun a ↦ ∫ s, H a s) := by exact rfl
  rw[this]
  clear this
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right ?_
  refine Measurable.stronglyMeasurable ?_
  unfold H
  rw [@uncurry_def]
  refine Measurable.ite ?_ ?_ ?_ <;> try fun_prop
  simp only [mem_Ico, measurableSet_setOf]
  refine Measurable.and ?_ ?_
  · rw [← @measurableSet_setOf]
    apply IsClosed.measurableSet ?_
    refine { isOpen_compl := ?_ }
    have : {(a : (ι → ℝ) × ℝ)| ∑ i, a.1 i ≤ a.2}ᶜ = {(a : (ι → ℝ) × ℝ)| a.2 < ∑ i, a.1 i} := by
      ext a
      simp only [mem_compl_iff, mem_setOf_eq, not_le]
    rw[this]
    refine isOpen_lt ?_ ?_
    · exact continuous_snd
    apply continuous_finset_sum
    intro i _
    apply prod_proj_continous
  rw [← @measurableSet_setOf]
  apply IsOpen.measurableSet
  refine isOpen_lt ?_ ?_
  · exact continuous_snd
  refine Continuous.add ?_ ?_
  swap
  · fun_prop
  apply continuous_finset_sum
  intro i _
  apply prod_proj_continous
--Measurable.lintegral_prod_left
--MeasureTheory.StronglyMeasurable.integral_prod_right'

/-
@[fun_prop]
theorem multlinear_avg_measurable
    {φ : ℝ → ℝ} (hφ: Measurable φ)
    {F : ι → (ι → ℝ) → ℝ} (hF: ∀ j, Measurable (F j) ) (t : NNReal):
    Measurable (multilinear_avg φ F t) := by
  unfold multilinear_avg
  apply Measurable.mul
  · fun_prop
  sorry
-/


lemma sum_coe_lemma(f : ℕ → ℝ)(a b : ℕ): ∑ i ∈ Finset.Ico a b, f i = ∑ i ∈ Finset.Ico (↑a : ℤ) b, f i.toNat := by
  apply Finset.sum_nbij (i := fun (i : ℕ) ↦ (↑i : ℤ))
  all_goals simp
  intro t ht
  use t.toNat
  unfold Ico at *
  simp_all
  have : 0 ≤ t := by
    calc
      0 ≤ ↑a := by simp
      _ ≤ t := ht.1
  simp [this, ht]
--*From here* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

/-This is only for completion, this is a direct copy of good_const_is_good-/
theorem fact5_2{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q)(m : ℕ)(idx : Fin (m+1) → NNReal)
  (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(F : ι → (ι → ℝ) → ℝ)(hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal):
    ∑ i : Fin m, (∫⁻ (a : ι → ℝ), ‖(multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)‖ₑ^2)
    ≤ (good_const h) * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)) :=
    (Exists.choose_spec h.2) m idx mon hidx hidx' F hF


theorem fact5_3(F : ι → (ι → ℕ) → ℝ): discrete_avg n F k = 1/n * ∑ i ∈ Finset.Ico (∑ (j : ι), k j) (n+ ∑ (j : ι), k j),
  ∏(j_1 : ι), (F j_1) (k + unit j_1 (i - ∑ (r : ι), k r)):= by
    unfold discrete_avg
    simp
    left
    set f : ℕ → ℝ := fun i ↦ ∏ j, F j (k + unit j i)
    set g : ℤ → ℝ := fun i ↦ f i.toNat
    set h : ℤ → ℝ := fun i ↦ g (i - ∑ (j : ι), k j)
    have : (fun i ↦ ∏ j_1, F j_1 (k + unit j_1 (i - ∑ j, k j))) = fun i ↦ f (i - ∑(j : ι), k j) := rfl
    rw[this]
    clear this
    calc
      ∑ i ∈ Finset.range n, f i = ∑ i ∈ Finset.Ico 0 n, f i := by simp
        _ = ∑ i ∈ Finset.Ico 0 (↑n : ℤ), h (i  + ∑ (j : ι), k j)  := by
          unfold h g
          simp only [Nat.cast_sum, add_sub_cancel_right]
          rw[sum_coe_lemma]
          simp
        _ = ∑ i ∈ Finset.Ico ((0 : ℤ) + ∑ (j : ι), k j) ((↑n : ℤ) + ∑ (j : ι), k j), h i := by rw[Finset.sum_Ico_add']
        _ = ∑ i ∈ Finset.Ico (∑ (j : ι), k j) (n+ ∑ (j : ι), k j), f (i - ∑(r : ι), k r) := by
          unfold h g
          simp only [zero_add]
          set c := (∑ j, k j)
          rw[sum_coe_lemma]
          simp

theorem fact5_3'(F : ι → (ι → ℤ) → ℝ)(k : ι → ℤ): discrete_avg' n F k = 1/n * ∑ i ∈ Finset.Ico (∑ (j : ι), k j) (n+ ∑ (j : ι), k j),
  ∏(j_1 : ι), (F j_1) (k + unit j_1 (i - ∑ (r : ι), k r)):= by
    unfold discrete_avg'
    simp
    left
    set f : ℤ → ℝ := fun i ↦ ∏ j, F j (k + unit j i)
    set g : ℤ → ℝ := fun i ↦ f i.toNat
    set h : ℤ → ℝ := fun i ↦ g (i - ∑ (j : ι), k j)
    have : (fun i ↦ ∏ j_1, F j_1 (k + unit j_1 (i - ∑ j, k j))) = fun i ↦ f (i - ∑(j : ι), k j) := rfl
    rw[this]
    clear this
    calc
      ∑ i ∈ Finset.range n, f i = ∑ i ∈ Finset.Ico 0 n, f i := by simp
        _ = ∑ i ∈ Finset.Ico 0 (↑n : ℤ), h (i  + ∑ (j : ι), k j)  := by
          unfold h g
          simp only [add_sub_cancel_right]
          rw[sum_coe_lemma]
          simp
        _ = ∑ i ∈ Finset.Ico ((0 : ℤ) + ∑ (j : ι), k j) ((↑n : ℤ) + ∑ (j : ι), k j), h i := by rw[Finset.sum_Ico_add']
        _ = ∑ i ∈ Finset.Ico (∑ (j : ι), k j) (n+ ∑ (j : ι), k j), f (i - ∑(r : ι), k r) := by
          unfold h g
          simp only [zero_add]
          set c := (∑ j, k j)
          apply Finset.sum_congr rfl
          simp
          intro x cx xn
          have : max (x - c) 0 = x - c := by simp [cx]
          rw[this]



--in γ sind die indizes
def set_fun (f : γ → α → β) (s : γ → Set α) : α → β :=
  fun a ↦ if h : ∃ i, a  ∈ s i then f h.choose a else default

lemma set_fun_disjoint{a : α}{i : γ}(f : γ → α → β){s : γ → Set α}(ha: a ∈ s i)(h : ∀ j j' : γ, j ≠ j' → (s j) ∩ (s j') = ∅):
  set_fun f s a = f i a := by
    unfold set_fun
    have hyp: ∃ i, a ∈ s i := by use i
    simp [hyp]
    have : hyp.choose = i := by
      contrapose h
      simp
      use hyp.choose
      use i
      constructor
      · exact h
      refine Nonempty.ne_empty ?_
      use a
      exact ⟨hyp.choose_spec, ha⟩
    rw[this]

lemma set_fun_cover(f : γ → α → β){s : γ → Set α}{a : α}(hs: ∀ a : α, ∃ c : γ, a ∈ s c): ∃ i : γ, set_fun f s a = f i a := by
  use (hs a).choose
  unfold set_fun
  simp [hs a]

lemma set_fun_pow [Monoid β] (n : ℕ){a : α}{i : γ}(f : γ → α → β){s : γ → Set α}(ha: a ∈ s i)
  (h : ∀ j j' : γ, j ≠ j' → (s j) ∩ (s j') = ∅): (set_fun f s a) ^ n = (f i a)^n := by rw[set_fun_disjoint f ha h]

lemma set_fun_rpow (n : ℝ){a : α}{i : γ}(f : γ → α → ℝ){s : γ → Set α}(ha: a ∈ s i)
  (h : ∀ j j' : γ, j ≠ j' → (s j) ∩ (s j') = ∅): (set_fun f s a) ^ n = (f i a) ^ n := by rw[set_fun_disjoint f ha h]

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

lemma approx_set_disjoint(i : ι){j j' : ι → ℤ}(h: j ≠ j'): approx_set i j ∩ approx_set i j' = ∅ := by
  ext t
  simp
  intro jh
  unfold approx_set at *
  contrapose h
  simp
  simp at jh
  simp at h
  ext x
  apply le_antisymm
  by_contra h0
  simp at h0
  have jj': j' x + 1 ≤ j x := by exact h0
  obtain ⟨jh1,jh2, jh3⟩ := jh
  obtain ⟨j'h1,j'h2, j'h3⟩ := h
  clear j'h1 jh2
  by_cases xi: x = i
  · rw[xi] at h0
    contrapose j'h2
    simp
    calc
      (↑(j' i) : ℝ) + 1 = (↑(j' i + 1) : ℝ) := by simp
        _ ≤ (↑(j i) :ℝ) := by
          simp [-Int.cast_add, -Int.cast_one]
          rw[← xi]
          exact jj'
        _ ≤ ∑ r, t r := jh1
  specialize jh3 x xi
  specialize j'h3 x xi
  clear jh1 j'h2
  obtain ⟨jh1,jh2⟩ := jh3
  obtain ⟨j'h1,j'h2⟩ := j'h3
  contrapose j'h2
  simp
  calc
    (↑(j' x) :ℝ) + 1 = (↑(j' x + 1) : ℝ) := by simp
    _ ≤ j x := by
      simp [-Int.cast_add, -Int.cast_one]
      exact jj'
    _ ≤ t x := jh1

  by_contra h0
  simp at h0
  have j'j: j x + 1 ≤ j' x := by exact h0
  obtain ⟨jh1,jh2, jh3⟩ := jh
  obtain ⟨j'h1,j'h2, j'h3⟩ := h
  clear jh1 j'h2
  by_cases xi: x = i
  · rw[xi] at h0
    contrapose jh2
    simp
    calc
      (↑(j i) : ℝ) + 1 = (↑(j i + 1) : ℝ) := by simp
        _ ≤ (↑(j' i) :ℝ) := by
          simp [-Int.cast_add, -Int.cast_one]
          rw[← xi]
          exact j'j
        _ ≤ ∑ r, t r := j'h1
  specialize jh3 x xi
  specialize j'h3 x xi
  clear j'h1 jh2
  obtain ⟨jh1,jh2⟩ := jh3
  obtain ⟨j'h1,j'h2⟩ := j'h3
  contrapose jh2
  simp
  calc
    (↑(j x) :ℝ) + 1 = (↑(j x + 1) : ℝ) := by simp
    _ ≤ j' x := by
      simp [-Int.cast_add, -Int.cast_one]
      exact j'j
    _ ≤ t x := j'h1

theorem Int.measurable_iff{α : Type*} [inst : MeasurableSpace α] {f : α → ℤ}: Measurable f ↔ ∀ (k : ℤ), MeasurableSet (f ⁻¹' {k}) := by
  constructor
  · intro hf _
    exact hf trivial
  intro h
  unfold Measurable
  intro t _
  have : f ⁻¹' t = ⋃ k : t, f⁻¹' {↑k} := by simp
  rw[this]
  exact MeasurableSet.iUnion fun b ↦ h ↑b


def round_down(i : ι)(u : ι → ℝ): ι → ℤ := Function.update (fun (j : ι) ↦ (⌊u j⌋ : ℤ)) i ⌊∑ r : ι, u r⌋

@[fun_prop] theorem round_down_meausurable(i : ι): Measurable (round_down i) := by
  refine measurable_pi_lambda (round_down i) ?_
  intro j
  -- Int.measurable_iff.2
  by_cases ij: i = j
  · unfold round_down
    rw[ij]
    simp
    fun_prop
  unfold round_down
  have : (fun c : ι → ℝ ↦ update (fun j ↦ ⌊c j⌋) i ⌊∑ r, c r⌋ j) = fun c : ι → ℝ ↦ ⌊c j⌋ := by
    ext c
    rw[Function.update_apply]
    simp
    intros
    tauto
  rw[this]
  fun_prop

lemma approx_set_cover(i : ι)(u : ι → ℝ): u ∈ approx_set i (round_down i u) := by
  unfold approx_set round_down
  simp
  constructor
  · exact Int.floor_le (∑ r, u r)
  intro j ji
  simp [ji]
  exact Int.floor_le (u j)

lemma approx_set_cover'(i : ι)(u : ι → ℝ): ∃ j : ι → ℤ, u ∈ approx_set i j := by
  use round_down i u
  exact approx_set_cover i u

lemma approx_set_unique{i : ι}{u : ι → ℝ}{k : ι → ℤ}(h : u ∈ approx_set i k): k = round_down i u := by
  by_contra h0
  have := approx_set_disjoint i h0
  contrapose this
  refine nonempty_iff_ne_empty.mp ?_
  use u
  simp [approx_set_cover, h]

def approx_sum(i : ι)(F : (ι → ℤ) → ℝ) : (ι → ℝ) → ℝ :=
  set_fun (fun (j : (ι → ℤ)) (_ : (ι → ℝ)) ↦ F (j + unit i (j i - ∑ r : ι, j r)))
    (approx_set i)


lemma approx_sum_round_down(i : ι)(F : (ι → ℤ) → ℝ): approx_sum i F = fun u ↦ F (round_down i u + unit i (round_down i u i - ∑ r, round_down i u r)) := by
  unfold approx_sum set_fun
  simp [approx_set_cover' i]
  ext u
  have : (approx_set_cover' i u).choose = round_down i u := by
    apply approx_set_unique
    exact Exists.choose_spec (approx_set_cover' i u)
  rw[this]
--Obige resultate anwenden !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

def approx_sum_mul(F : ι → (ι → ℤ) → ℝ): ι → (ι → ℝ) → ℝ :=
  fun i ↦ approx_sum i (F i)

def interlude_sum(k : ι → ℤ)(i : ι)(f : (ι → ℤ) → ℝ): ℝ → ℝ :=
  set_fun (fun a _ ↦ f (k + unit i (a + ∑ r : ι, k r))) (fun (a : ℤ) ↦ Ico a (a+1)) --unnötig?
--analog
def incl_fun{α : Type*}[AddMonoid α]: (ι → (ι → ℕ) → α) → (ι → (ι → ℤ) → α) :=
  fun f i k ↦ if ∀ j : ι, 0 ≤ k j then f i (fun t ↦ (k t).toNat) else (0 : α)

theorem og_sum(i : ι)(F : (ι → ℤ) → ℝ)(x : ι → ℝ): approx_sum i F x = ∑' j : ι → ℤ, (F (j + unit i (j i - ∑ r : ι, j r)) * ((approx_set i j).indicator 1 x)) := by
  rw[approx_sum_round_down]
  simp
  calc
    F (round_down i x + unit i (round_down i x i - ∑ r, round_down i x r)) =
    F (round_down i x + unit i (round_down i x i - ∑ r, round_down i x r)) *  (approx_set i (round_down i x)).indicator 1 x := by
      rw[← mul_one (F (round_down i x + unit i (round_down i x i - ∑ r, round_down i x r)))]
      congr
      · rw[mul_one]
      unfold indicator
      simp
      exact approx_set_cover i x
    _ = ∑' (j : ι → ℤ), F (j + unit i (j i - ∑ r, j r)) * (approx_set i j).indicator 1 x := by
      symm
      apply tsum_eq_single
      intro k kh
      simp
      right
      contrapose kh
      simp_all
      exact approx_set_unique kh

theorem og_sum'(i : ι)(F : (ι → ℤ) → ℝ)(x : ι → ℝ): ‖approx_sum i F x‖ₑ = ∑' j : ι → ℤ, ‖(F (j + unit i (j i - ∑ r : ι, j r)) * ((approx_set i j).indicator 1 x))‖ₑ := by
  rw[approx_sum_round_down]
  calc
    ‖F (round_down i x + unit i (round_down i x i - ∑ r, round_down i x r))‖ₑ =
    ‖F (round_down i x + unit i (round_down i x i - ∑ r, round_down i x r)) *  (approx_set i (round_down i x)).indicator 1 x‖ₑ:= by
      rw[← mul_one (F (round_down i x + unit i (round_down i x i - ∑ r, round_down i x r)))]
      congr
      · rw[mul_one]
      unfold indicator
      simp
      exact approx_set_cover i x
    _ = ∑' (j : ι → ℤ), ‖F (j + unit i (j i - ∑ r, j r)) * (approx_set i j).indicator 1 x‖ₑ := by
      symm
      apply tsum_eq_single
      intro k kh
      simp
      right
      contrapose kh
      simp_all
      exact approx_set_unique kh


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
/-Show that these cover everything and each vector is in exactly one (round down) (and there is one where a given function isnt in it)-/


@[fun_prop] lemma approx_sum_measurable (i : ι) {F : (ι → ℤ) → ℝ}: Measurable (approx_sum i F) := by --(h : Measurable F)
  rw[approx_sum_round_down]
  fun_prop

@[fun_prop] lemma approx_sum_mul_measurable(F : ι → (ι → ℤ) → ℝ): ∀ i : ι, Measurable (approx_sum_mul F i) := by
  intro i
  unfold approx_sum_mul
  apply approx_sum_measurable

lemma approx_sum_nonneg(i : ι)(F : (ι → ℤ) → ℝ)(hF: 0 ≤ F): 0 ≤ approx_sum i F := by
  intro x
  simp
  rw[approx_sum_round_down]
  simp
  apply hF

lemma approx_sum_rpow(i : ι)(s : ℝ)(F : (ι → ℤ) → ℝ)(x : ι → ℝ): (approx_sum i F x)^s = approx_sum i (F^s) x := by
  rw[approx_sum_round_down, approx_sum_round_down]
  simp


/-
{ι : Type u_4} [Fintype ι] {α : ι → Type v} {β : ι → Type u_5}
 [(i : ι) → MeasurableSpace (α i)] [(i : ι) → MeasurableSpace (β i)]
(μ : (i : ι) → MeasureTheory.Measure (α i))
(ν : (i : ι) → MeasureTheory.Measure (β i))
{f : (i : ι) → α i → β i} [∀ (i : ι), MeasureTheory.SigmaFinite (ν i)]
(hf : ∀ (i : ι), MeasureTheory.MeasurePreserving (f i) (μ i) (ν i)) :
MeasureTheory.MeasurePreserving (fun a i => f i (a i)) (MeasureTheory.Measure.pi μ) (MeasureTheory.Measure.pi ν)
-/

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

def sumbij(i : ι ) : (ι → ℤ) ≃ (ι → ℤ) where
  toFun := fun (j : ι → ℤ) ↦ ((j + unit i (j i - ∑ r, j r)) : ι → ℤ)
  invFun := fun (j : ι → ℤ) ↦ ((j + unit i (-j i + ∑ r, j r)) : ι → ℤ)
  left_inv := by
    intro j
    simp
    ext x
    unfold unit
    simp
    by_cases ix: i = x <;> simp [ix]
    ring_nf
    calc
      ∑ x_1, (j x_1 + if x = x_1 then j x - ∑ r, j r else 0) = (∑ x_1, j x_1) + ∑ x_1, if x = x_1 then j x - ∑ r, j r else 0 := by
          rw [@Finset.sum_add_distrib]
        _ = (∑ x_1, j x_1) + (j x - ∑ r, j r) := by
          congr
          rw[Fintype.sum_eq_single (a := x)]
          · simp
          intro y yx
          simp [Ne.symm yx]
        _ = j x := by
          simp
  right_inv := by
    intro j
    ext x
    unfold unit
    simp
    by_cases ix: i = x <;> simp [ix]
    ring_nf
    rw[Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring

#check set_fun_rpow
theorem lintegral_approx_sum(i : ι)(F : (ι → ℤ) → ℝ){s : ℝ}(hs: 0 ≤ s): ∫⁻ x : ι → ℝ, ‖approx_sum i F x‖ₑ^s = ∑' k : ι → ℤ, ‖F k‖ₑ^s := by
  calc
    ∫⁻ x : ι → ℝ, ‖approx_sum i F x‖ₑ^s
       = ∫⁻ x : ι → ℝ, ‖approx_sum i |F| x‖ₑ^s := by
        congr
        ext x
        congr 1
        unfold approx_sum set_fun
        simp
        by_cases h': ∃ i_1, x ∈ approx_set i i_1
        all_goals simp [h']
    _  = ∫⁻ x : ι → ℝ, ‖(approx_sum i |F| x)^s‖ₑ := by
        congr
        ext x
        rw[Real.enorm_rpow_of_nonneg]
        · apply approx_sum_nonneg
          simp
        exact hs
    _ = ∫⁻ x : ι → ℝ, ‖(approx_sum i (|F|^s) x)‖ₑ := by
        congr
        ext x
        rw[approx_sum_rpow]
    _ = ∫⁻ x : ι → ℝ, ‖∑' (j : ι → ℤ), (|F| ^ s) (j + unit i (j i - ∑ r, j r)) * (approx_set i j).indicator 1 x‖ₑ := by congr; ext x; rw[og_sum]
    _ = ∫⁻ x : ι → ℝ, ∑' (j : ι → ℤ), ‖(|F| ^ s) (j + unit i (j i - ∑ r, j r)) * (approx_set i j).indicator 1 x‖ₑ := by
        congr
        ext x
        rw [Real.enorm_eq_ofReal_abs]
        simp
        have : |∑' (j : ι → ℤ), |F (j + unit i (j i - ∑ r, j r))| ^ s * (approx_set i j).indicator 1 x| = ∑' (j : ι → ℤ), |F (j + unit i (j i - ∑ r, j r))| ^ s * (approx_set i j).indicator 1 x := by
          simp
          apply tsum_nonneg
          intro j
          apply mul_nonneg
          · apply rpow_nonneg
            simp
          unfold indicator
          by_cases hx: x ∈ approx_set i j <;> simp [hx]
        rw[this]
        rw[ENNReal.ofReal_tsum_of_nonneg]
        · congr
          ext n
          rw [← enorm_mul, Real.enorm_eq_ofReal_abs]
          congr
          rw[abs_mul]
          congr
          · symm
            simp
            apply rpow_nonneg
            simp
          symm
          simp
          by_cases hx: x ∈ approx_set i n <;> simp [hx]
        · intro j
          apply mul_nonneg
          · apply rpow_nonneg
            simp
          unfold indicator
          by_cases hx: x ∈ approx_set i j <;> simp [hx]
        apply summable_of_finite_support
        suffices : support (fun j ↦ |F (j + unit i (j i - ∑ r, j r))| ^ s * (approx_set i j).indicator 1 x) ⊆ {round_down i x}
        · apply Set.Finite.subset (ht := this)
          simp
        intro j
        simp
        intro _ xj
        exact approx_set_unique xj
    _ = ∑' (j : ι → ℤ), ∫⁻ x : ι → ℝ, ‖(|F| ^ s) (j + unit i (j i - ∑ r, j r)) * (approx_set i j).indicator 1 x‖ₑ := by
        rw[MeasureTheory.lintegral_tsum]
        intro k
        apply Measurable.aemeasurable
        apply Measurable.enorm
        apply Measurable.mul
        · fun_prop
        apply Measurable.indicator
        · fun_prop
        measurability
    _ = ∑' (j : ι → ℤ), ∫⁻ x : ι → ℝ in (approx_set i j), ‖(|F| ^ s) (j + unit i (j i - ∑ r, j r)) * (approx_set i j).indicator 1 x‖ₑ := by
        congr
        ext j
        refine Eq.symm (setLIntegral_eq_of_support_subset ?_)
        intro x
        simp
    _ = ∑' (j : ι → ℤ), ∫⁻ x : ι → ℝ in (approx_set i j), ‖(|F| ^ s) (j + unit i (j i - ∑ r, j r))‖ₑ := by
        congr
        ext j
        refine setLIntegral_congr_fun ?_ ?_
        · exact approx_set_measurable i j
        intro x xh
        simp [xh]
    _ = ∑' (j : ι → ℤ), ‖(|F| ^ s) (j + unit i (j i - ∑ r, j r))‖ₑ := by
        simp
        congr
        ext j
        rw[approx_set_volume, mul_one]
    _ = ∑' k : ι → ℤ, ‖(|F|^s) k‖ₑ := by
        nth_rw 2[← Equiv.tsum_eq (e := (sumbij i))]
        congr
    _ = ∑' k : ι → ℤ, ‖F k‖ₑ^s := by
        congr
        ext k
        simp
        rw[Real.enorm_rpow_of_nonneg]
        · simp only [enorm_abs]
        · simp only [abs_nonneg]
        exact hs
/-
lemma setup_discrete_ver'_norm_one {q : ι → ℝ} (hq : (∀ (i : ι), 0 < q i))
    (F : ι → (ι → ℤ) → ℝ) (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1) (i : ι):
    (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i) = 1 := by
  specialize hF' i
  refine (toReal_eq_one_iff (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i)).mp ?_
  rw[← hF']
  have : ∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i = ∑' (k : ι → ℤ), ‖|F i k| ^ (q i)‖ₑ := by
    congr
    ext k
    rw[enorm_rpow_of_nonneg]
    · simp only [enorm_abs]
    · apply abs_nonneg
    exact le_of_lt (hq i)
  rw[this, ell_p_coe]
  intro k
  apply rpow_nonneg
  apply abs_nonneg
-/
/-
lemma enorm_abs_sum {q : ι → ℝ} (hq : (∀ (i : ι), 0 < q i))
    (F : ι → (ι → ℤ) → ℝ) (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1) (i : ι):
    (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i) = 1 := by
-/
theorem approx_sum_memlp
    {F : (ι → ℤ) → ℝ} {s : ℝ≥0∞} (hs : s ≠ 0) (hs' : s ≠ ∞) (hF: Memℓp F s) :
    ∀ (i : ι), MeasureTheory.MemLp (approx_sum i F) s := by
  intro i
  unfold MemLp
  constructor
  · apply Measurable.aestronglyMeasurable
    exact approx_sum_measurable i
  unfold eLpNorm eLpNorm'
  simp only [hs, ↓reduceIte, hs', one_div]
  rw[lintegral_approx_sum (hs := by apply toReal_nonneg)]
  refine (rpow_lt_top_iff_of_pos ?_).mpr ?_
  · simp only [inv_pos]
    exact toReal_pos hs hs'
  unfold Memℓp at hF
  simp only [hs, ↓reduceIte, hs', norm_eq_abs] at hF
  have nn  : ∀ i, 0 ≤ |F i| ^ s.toReal := by
    intros
    apply rpow_nonneg
    apply abs_nonneg
  apply (NNReal.summable_mk nn).2 at hF
  apply ENNReal.tsum_coe_ne_top_iff_summable.2 at hF
  let g : (ι → ℤ) → ℝ≥0 := fun b ↦ ⟨|F b| ^ s.toReal, nn b⟩
  suffices : ∑' (b : ι → ℤ), (↑(g b) : ℝ≥0∞) =  ∑' (k : ι → ℤ), ‖F k‖ₑ ^ s.toReal
  · unfold g at this
    rw[← this]
    exact Ne.lt_top' (id (Ne.symm hF))
  unfold g
  congr
  ext b
  have : ‖F b‖ₑ = ‖|F b|‖ₑ := by simp only [enorm_abs]
  rw[this]
  rw[← enorm_rpow_of_nonneg] <;> try simp
  rw [Real.enorm_eq_ofReal_abs]
  refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_ <;> simp
  symm
  simp only [abs_eq_self]
  apply rpow_nonneg
  apply abs_nonneg

def equisum(k : ι → ℤ)(i : ι): {j : ι → ℤ | ∀ j' : ι, j' ≠ i → j j' = k j'} ≃ ℤ where
  toFun := fun a ↦ a.1 i
  invFun := fun n ↦ ⟨Function.update k i n, by
    intro j ji
    simp [ji]⟩
  left_inv := by
    intro ⟨j,jh⟩
    ext r
    simp
    simp at jh
    by_cases ri: r = i
    · unfold update
      simp [ri]
    specialize jh r ri
    unfold update
    simp_all
  right_inv := by
    intro n
    simp only [update_self]

theorem tsum_prod_set{α β : Type*}(s : Finset β)(ne : s ≠ ∅){f : β → α → ENNReal}(h : ∀ a a' : α, ∀ i i' : β, a ≠ a' → i ≠ i' → f i a * f i' a' = 0):
  ∏ i ∈ s, ∑' a : α, f i a = ∑' a : α, ∏ i ∈ s,  f i a := by
    revert s
    apply Finset.induction
    · simp only [Finset.prod_empty]
      tauto
    intro j s is ih _
    by_cases se: s = ∅
    · rw[se]
      simp
    specialize ih se
    rw [Finset.prod_insert is, ih]
    rw [← @ENNReal.tsum_mul_left]
    congr
    ext b
    rw [← @ENNReal.tsum_mul_right]
    rw [Finset.prod_insert is]
    refine tsum_eq_single b ?_
    intro a ab
    have: s.Nonempty := Finset.nonempty_iff_ne_empty.mpr se
    obtain ⟨r,rh⟩ := Finset.Nonempty.exists_mem this
    calc
      f j a * ∏ i ∈ s, f i b = f j a * (f r b * ∏ i ∈ s \ {r}, f i b) := by
          congr
          exact Finset.prod_eq_mul_prod_diff_singleton rh fun x ↦ f x b
        _ = 0 := by
          have jr : j ≠ r := by
            contrapose is
            simp_all
          rw[← mul_assoc, h a b j r ab jr, zero_mul]

theorem tsum_prod [Nonempty ι]{α : Type*}{f : ι → α → ENNReal}(h : ∀ a a' : α, ∀ i i' : ι, a ≠ a' → i ≠ i' → f i a * f i' a' = 0):
  ∏ i : ι, ∑' a : α, f i a = ∑' a : α, ∏ i : ι,  f i a := by
    refine tsum_prod_set ?_ ?_ h
    by_contra h0
    have := Finset.univ_eq_empty_iff.1 h0
    contrapose this
    simp

theorem tsum_prod_set_real{α β : Type*}(s : Finset β)(ne : s ≠ ∅){f : β → α → ℝ}(h : ∀ a a' : α, ∀ i i' : β, a ≠ a' → i ≠ i' → f i a * f i' a' = 0):
  ∏ i ∈ s, ∑' a : α, f i a = ∑' a : α, ∏ i ∈ s,  f i a := by
    revert s
    apply Finset.induction
    · simp only [Finset.prod_empty]
      tauto
    intro j s is ih _
    by_cases se: s = ∅
    · rw[se]
      simp
    specialize ih se
    rw [Finset.prod_insert is, ih]
    rw [← @_root_.tsum_mul_left]
    congr
    ext b
    rw [← @_root_.tsum_mul_right]
    rw [Finset.prod_insert is]
    refine tsum_eq_single b ?_
    intro a ab
    have: s.Nonempty := Finset.nonempty_iff_ne_empty.mpr se
    obtain ⟨r,rh⟩ := Finset.Nonempty.exists_mem this
    calc
      f j a * ∏ i ∈ s, f i b = f j a * (f r b * ∏ i ∈ s \ {r}, f i b) := by
          congr
          exact Finset.prod_eq_mul_prod_diff_singleton rh fun x ↦ f x b
        _ = 0 := by
          have jr : j ≠ r := by
            contrapose is
            simp_all
          rw[← mul_assoc, h a b j r ab jr, zero_mul]

theorem tsum_prod_real [Nonempty ι]{α : Type*}{f : ι → α → ℝ}(h : ∀ a a' : α, ∀ i i' : ι, a ≠ a' → i ≠ i' → f i a * f i' a' = 0):
  ∏ i : ι, ∑' a : α, f i a = ∑' a : α, ∏ i : ι,  f i a := by
    refine tsum_prod_set_real ?_ ?_ h
    by_contra h0
    have := Finset.univ_eq_empty_iff.1 h0
    contrapose this
    simp


theorem fact5_4_lemma [Nonempty ι](k : ι → ℤ)(α : ι → ℝ)(F : ι → (ι → ℤ) → ℝ){t : NNReal}:
  ∑' (a : ℤ), ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t), ‖∏ j, (F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s‖ₑ =
  ∑' (i : ℤ), volume (Ico (↑i : ℝ) (↑i + 1) ∩ Ico (∑ i, (↑(k i) + α i)) (↑t + ∑ i, (↑(k i) + α i))) *
  ∏ j_1, ‖F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o‖ₑ := by
    calc
      ∑' (a : ℤ), ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t), ‖∏ j, (F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s‖ₑ
        = ∑' (a : ℤ), ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t), ∏ j, ‖(F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s‖ₑ := by
          congr
          ext a
          congr
          ext s
          rw[Real.enorm_eq_ofReal_abs]
          rw[Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg]
          · congr
            ext
            rw[Real.enorm_eq_ofReal_abs]
          intros
          simp
      _ = ∑' (i : ℤ), volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ i, (↑(k i) + α i)) (↑t + ∑ i, (↑(k i) + α i))) *
        ∏ j_1, ‖F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o‖ₑ := by
          congr
          ext n
          rw[mul_comm]
          rw[← MeasureTheory.setLIntegral_const]
          rw[← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator]
          congr
          ext a
          simp
          unfold indicator Ico
          simp
          rw[add_comm (∑ i, (↑(k i) + α i))]
          by_cases h1: (∑ i, (↑(k i) + α i) ≤ a ∧ a < ↑t + ∑ i, (↑(k i) + α i))
          · simp only [h1]
            by_cases h2: (↑n : ℝ) ≤ a ∧ a < (↑n : ℝ) + 1
            · simp only [h2]
              simp --enden passen nicht :/
              rfl
            simp only [h2]
            simp
          simp only [h1]
          simp
          repeat measurability

lemma sum_of_finite_of_finite_support_ne_top {α : Type*}{f : α → ENNReal}(ne: ∀ a : α, f a ≠ ⊤)
  (fin: (support f).Finite): ∑' a : α, f a ≠ ⊤ := by
    have inst: Fintype ↑(support f) := fin.fintype
    rw[← tsum_subtype_support]
    have : ∑' (x : ↑(support f)), f ↑x = ∑' (x : ↑(↑((support f).toFinset) : Set α)), f ↑x := by
      have : (↑((support f).toFinset) : Set α) = support f := by simp
      rw[this]
    rw[this]
    simp_all

lemma int_set_finite_lower_and_upper_bound{s : Set ℤ}(hlow: ∃ a : ℤ, ∀ x ∈ s, a ≤ x)
  (hup: ∃ a : ℤ, ∀ x ∈ s, x ≤ a): s.Finite := by
    obtain ⟨a,ah⟩ := hlow
    obtain ⟨b,bh⟩ := hup
    suffices : s ⊆ Icc a b
    · exact Set.Finite.subset (s := Icc a b) (finite_Icc a b) this
    unfold Icc
    intro x xs
    simp
    exact ⟨ah x xs, bh x xs⟩

/- This also works for ι empty, but is a bit of a pain-/
theorem fact5_4 [Nonempty ι](k : ι → ℤ)(α : ι → ℝ)(hα: ∀(i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ){t : NNReal}(ht : 0 < t): --also make a version for ℕ, hopefully follows easily
  (multilinear_avg_spec (approx_sum_mul F) t (fun j ↦ k j + α j)) =
  (1/t * ∑' i : ℤ, (volume (Ico (i:ℝ) (i+1) ∩ Ico (∑ (j : ι), (k j + α j)) (t+∑ (j : ι), (k j + α j)))).toReal *
  ∏(j_1 : ι), (F j_1) (fun o ↦ ((k o : ℤ) + unit j_1 (i - (∑ (r : ι), (k r))) o))):= by --stated wrongly i think! glaub vorzeichen ist falsch, also LHS
    rw[fact5_1]
    swap
    · contrapose ht
      simp_all
    congr
    unfold approx_sum_mul
    --((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))
    calc
      ∫ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, approx_sum j (F j) ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))
      /-_ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ‖∏ j, (∑' (j' : ι → ℤ), (F j) (j' + unit j (j' j - ∑ r, j' r)) * (approx_set j j').indicator 1
      ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i))))‖ₑ := by
        congr
        ext s
        congr
        ext j
        rw[og_sum]
      -/
      _ = ∫ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, approx_sum j (F j) ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i))) := by
        congr
      _ = ∫ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, ∑' (j' : ι → ℤ), (F j) (j' + unit j (j' j - ∑ r, j' r)) * (approx_set j j').indicator 1 ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i))) := by
        congr
        ext s
        congr
        ext j
        rw[og_sum]
      _ = ∫ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, ∑' (a : ℤ), (F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s := by
        congr
        ext s
        congr
        ext i
        set h := fun j' : ι → ℤ ↦ F i (j' + unit i (j' i - ∑ r, j' r)) *
        (approx_set i j').indicator 1 ((fun i ↦ ↑(k i) + α i) + unit i (s - ∑ i, (↑(k i) + α i)))
        have hs: support h ⊆ {j : ι → ℤ | ∀ j' : ι, j' ≠ i → j j' = k j'} := by
          intro j
          simp
          intro hj
          contrapose hj
          simp_all
          obtain ⟨r,rh⟩ := hj
          unfold h
          simp
          right
          unfold approx_set
          simp
          intros
          use r
          simp [rh]
          have : unit i (s - ∑ i, (↑(k i) + α i)) r = 0 := by
            unfold unit
            simp
            intros
            tauto
          rw[this]
          rw[add_zero]
          intro h
          have : j r < k r := by
            contrapose rh
            simp_all
            intro _
            apply le_antisymm
            · contrapose h
              simp at *
              have : k r + 1 ≤ j r := by exact h
              calc
                ↑(k r) + α r < ↑(k r) + 1 := by specialize hα r; linarith
                  _ = ↑(k r + 1) := by simp
                  _ ≤ j r := by simp [-Int.cast_add, -Int.cast_one, this]
            exact rh
          contrapose this
          simp_all
          suffices g: k r < (↑(j r) : ℝ) + 1
          · have : (↑(j r) : ℝ) + 1 = (↑(j r + 1) : ℝ) := by simp
            rw[this] at g
            simp [-Int.cast_add, -Int.cast_one] at g
            exact (Int.add_le_add_iff_right 1).mp g
          specialize hα r
          linarith
        set A := {j : ι → ℤ | ∀ j' : ι, j' ≠ i → j j' = k j'}
        calc
          tsum h = ∑' j' : A, h ↑j' := by
            exact Eq.symm (tsum_subtype_eq_of_support_subset hs)
          _ = ∑' (a : ℤ), F i (k + unit i (a - ∑ r, k r)) * (Ico (↑a) (↑a + 1)).indicator 1 s := by
            rw[← Equiv.tsum_eq (e := equisum k i) (f := fun a ↦ F i (k + unit i (a - ∑ r, k r)) * (Ico (↑a : ℝ) ((↑a : ℝ) + 1)).indicator 1 s)]
            unfold A
            congr
            ext ⟨j',j'h⟩
            unfold h equisum
            simp [-enorm_mul]
            congr 2
            · ext r
              unfold unit
              by_cases ir: i = r
              · simp [ir]
                rw[← ir]
                have : ∑ x, j' x = j' i - k i + ∑ x, k x := by
                  calc
                    ∑ x, j' x = ∑ x, (unit i (j' i - k i) x + k x) := by
                        congr
                        ext x
                        unfold unit
                        by_cases xi: x = i
                        · rw[xi]
                          simp
                        simp at j'h
                        simp [Ne.symm xi, j'h x xi]
                      _= (∑ x, unit i (j' i - k i) x) + ∑ x, k x := by
                        rw[Finset.sum_add_distrib]
                      _= j' i - k i + ∑ x, k x := by
                        simp
                        rw[Fintype.sum_eq_single (a := i)]
                        · unfold unit
                          simp
                        intro j ji
                        unfold unit
                        simp [Ne.symm ji]
                rw[this]
                ring
              simp [ir]
              simp at j'h
              exact j'h r (Ne.symm ir)
            --unfold approx_set
            have : ∑ x, (↑(k x) + α x + unit i (s - ∑ i, (↑(k i) + α i)) x) = s := by
              rw[Finset.sum_add_distrib]
              have : ∑ x, unit i (s - ∑ i, (↑(k i) + α i)) x = s - ∑ i, (↑(k i) + α i) := by
                rw[Fintype.sum_eq_single (a := i)]
                · unfold unit
                  simp
                intro j ji
                unfold unit
                simp [Ne.symm ji]
              rw[this]
              simp
            by_cases hs: s ∈ Ico (↑(j' i) : ℝ) (↑(j' i) + 1)
            · simp [hs]
              unfold indicator approx_set
              simp at *
              rw[this]
              simp [hs]
              intro j ji
              rw[j'h j ji]
              specialize hα j
              unfold unit
              simp [Ne.symm ji, hα]
            simp [hs]
            unfold approx_set
            simp
            intro hi1 hi2
            contrapose hi2
            simp at hi2
            simp
            rw[this]
            rw[this] at hi1
            simp at hs
            by_cases h': ↑(j' i) ≤ s
            · specialize hs h'
              linarith
            contradiction
      _ = ∫ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∑' (a : ℤ), ∏ j, (F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s := by
        congr
        ext s
        rw[tsum_prod_real]
        intro a b i j ab ij
        simp
        by_cases hs: (↑a ≤ s → ↑a + 1 ≤ s)
        · tauto
        right
        right
        simp at hs
        intro bs
        have : a < b ∨ b < a := by
          contrapose ab
          simp_all
        obtain ⟨hs1, hs2⟩ := hs
        obtain this|this := this
        · contrapose bs
          simp
          calc
            s < ↑a + 1 := hs2
            _≤ b := by
              have : (↑a : ℝ) + 1 = (↑(a + 1) : ℝ) := by simp
              rw[this]
              simp [-Int.cast_add, -Int.cast_one]
              assumption
        --prob not in mathlib
        calc
          (↑b : ℝ) + 1 ≤ a := by
              rw[←Int.cast_one, ← Int.cast_add]
              simp [-Int.cast_add, -Int.cast_one]
              assumption
            _ ≤ s := hs1
      _ = ∑' (a : ℤ), ∫ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, (F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s := by
        rw[MeasureTheory.integral_tsum]--bedingungen für F iwie nötig :/ (für original version hab ich nichts gebraucht)
        --besser (da fast keine conditions nötig wäre zu zeigen, dass die summen je endlich sind)
        · intro i
          apply Measurable.aestronglyMeasurable
          refine Finset.measurable_prod Finset.univ ?_
          intro j _
          apply Measurable.mul
          · simp
          refine Measurable.indicator ?_ ?_
          · fun_prop
          measurability
        rw[fact5_4_lemma]
        apply sum_of_finite_of_finite_support_ne_top
        · intro a
          apply ENNReal.mul_ne_top
          · apply lt_top_iff_ne_top.1
            calc
              volume (Ico (↑a) (↑a + 1) ∩ Ico (∑ i, (↑(k i) + α i)) (↑t + ∑ i, (↑(k i) + α i)))
                ≤ volume (Ico (↑a : ℝ) (↑a + 1)) := by apply measure_mono; simp
              _ < ⊤ := by simp
          apply ENNReal.prod_ne_top
          intros
          simp
        apply int_set_finite_lower_and_upper_bound
        · use ((∑ i, k i) - 2)
          intro x
          simp
          intro xh _
          contrapose xh
          simp_all
          suffices : (Ico (↑x : ℝ) (↑x + 1) ∩ Ico (∑ i, (↑(k i) + α i)) (↑t + ∑ i, (↑(k i) + α i))) = ∅
          · rw[this]
            simp
          ext s
          simp
          intro xs sx sums
          contrapose sums
          clear sums
          simp
          calc
            s < ↑x + 2 := by linarith
            _ = (↑(x + 2) : ℝ) := by simp
            _ < (↑(∑ r, k r) : ℝ) := by simp [-Int.cast_natCast, -Int.cast_sum, -Int.cast_add, *]
            _ = ∑ r, (↑(k r) : ℝ) := by simp
            _ ≤ ∑ r, (↑(k r) + α r) := by
              gcongr
              rename_i i _
              specialize hα i
              linarith
        use (1 + ⌈t + ∑ i, (↑(k i) + α i)⌉)
        intro x
        simp
        intro xh _
        contrapose xh
        simp_all
        suffices : (Ico (↑x : ℝ) (↑x + 1) ∩ Ico (∑ i, (↑(k i) + α i)) (↑t + ∑ i, (↑(k i) + α i))) = ∅
        · rw[this]
          simp
        ext s
        simp
        intro xs sx sums
        apply le_of_lt
        calc
          (↑t : ℝ) + ∑ i, (↑(k i) + α i) ≤ (↑⌈(↑t : ℝ) + ∑ i, (↑(k i) + α i)⌉ : ℝ) := by apply Int.le_ceil
            _ <  (↑(1 + ⌈(↑t : ℝ) + ∑ i, (↑(k i) + α i)⌉) : ℝ) := by simp
            _ < (↑x : ℝ) := by simp [-Int.cast_natCast, -Int.cast_sum, -Int.cast_add, *]
            _ ≤ s := by assumption
        /-
        apply MeasureTheory.lintegral_tsum
        intro n
        apply Measurable.aemeasurable
        apply Finset.measurable_prod
        intro j _
        apply Measurable.enorm
        apply Measurable.mul
        · fun_prop
        refine Measurable.indicator ?_ ?_
        all_goals measurability
        -/
      /-
      _ = ∑' a : ℤ, ∫⁻ (s : ℝ) in ((Ico (↑a : ℝ) (a+1)) ∩ (Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t))),
      ∏ j, ∑' (j' : ι → ℤ), ‖(F j) (j' + unit j (j' j - ∑ r, j' r)) * (approx_set j j').indicator 1 ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))‖ₑ := by
        sorry
      -/

     /- _ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
    ‖∏ j,
        if h : ∃ i, (fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)) ∈ approx_set j i then
          (fun j_1 x ↦ F j (j_1 + unit j (j_1 j - ∑ r, j_1 r))) h.choose
            ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))
        else default‖ₑ := by
        unfold approx_sum_mul approx_sum set_fun
        exact rfl
      _ = ∫⁻ (u : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ‖∏ i : ι, (interlude_sum k i (F i) u)‖ₑ := by
        apply MeasureTheory.setLIntegral_congr_fun
        · measurability
        intro u uh
        simp
        congr
        sorry-/
      _ = ∑' (i : ℤ), (volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑t + ∑ j, (↑(k j) + α j)))).toReal *
          ∏ j_1, F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o:= by
          congr
          ext n
          rw[← MeasureTheory.integral_indicator]
          swap
          · exact measurableSet_Ico
          have : ∫ (x : ℝ), (Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t)).indicator
            (fun s ↦ ∏ j, F j (k + unit j (n - ∑ r, k r)) * (Ico (↑n) ((↑n : ℝ) + 1)).indicator 1 s) x = ∫ (x : ℝ), ((Ico (↑n) ((↑n : ℝ) + 1)) ∩ (Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t))).indicator
            (fun s ↦ ∏ j, F j (k + unit j (n - ∑ r, k r))) x := by
              congr
              ext x
              by_cases xh1: x ∈ Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t) <;> simp [xh1]
              by_cases xh2: x ∈ (Ico (↑n) ((↑n : ℝ) + 1)) <;> simp [xh1,xh2]
          /-have : ∫ (x : ℝ), (Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t)).indicator
      (fun s ↦ ∏ j, F j (k + unit j (n - ∑ r, k r)) * (Ico (↑n) (↑n + 1)).indicator 1 s) x =
        ∫ (x : ℝ), (Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t)).indicator
        (fun s ↦ ∏ j, F j (k + unit j (n - ∑ r, k r)) * (Ico (↑n) (↑n + 1)).indicator 1 s) x := by sorry
          -/
          rw[this, MeasureTheory.integral_indicator]
          swap
          · measurability
          clear this
          simp
          congr
          rw[add_comm (↑t : ℝ)]

lemma finset_sum_of_nonneg_le_two_mul_union {α : Type*}{s u : Finset α}{f : α → ℝ}(hf: 0 ≤ f):
  ∑ a ∈ s, f a + ∑ a ∈ u, f a ≤ 2 * ∑ a ∈ (s ∪ u), f a := by
    calc
      ∑ a ∈ s, f a + ∑ a ∈ u, f a
        ≤ ∑ a ∈ (s ∪ u), f a + ∑ a ∈ (s ∪ u), f a := by
          gcongr
          all_goals simp
          repeat
            intro i _ _
            specialize hf i
            simp_all
      _ = 2 * ∑ a ∈ (s ∪ u), f a := by ring

theorem multilinear_avg_spec_discrete_avg_est_c_big [Nonempty ι](k : ι → ℤ)(α : ι → ℝ)(hα: ∀(i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ)(h: n < Fintype.card ι):
  |(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k| ≤
    2/n * ∑ i ∈ Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (Fintype.card ι + (↑n : ℤ)), |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))| := by
    by_cases hn: n = 0
    · rw[hn]
      unfold discrete_avg' multilinear_avg_spec multilinear_avg
      simp
    have hn': 0 < (↑n : NNReal) := by
      simp
      exact Nat.zero_lt_of_ne_zero hn
    rw[fact5_4 k α hα F hn']
    rw[fact5_3']
    simp
    let r : ℤ → ℝ := fun i ↦ ∏ j_1 : ι, F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o
    set a : ℤ → ℝ := fun i ↦ (volume (Ico (↑i : ℝ) (↑i + 1) ∩ (Ico (∑ j, ((↑(k j) : ℝ) + α j)) (((↑n : ℝ) + ∑ j, (↑(k j) + α j)))))).toReal
    calc
      |(↑n)⁻¹ *
        (∑' (i : ℤ), (volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))).toReal *
              ∏ j_1, F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o) -
      (↑n)⁻¹ * ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, F j_1 (k + unit j_1 (i - ∑ r, k r))|
          = |(↑n)⁻¹ * (∑' (i : ℤ), (a i * r i)) - (↑n)⁻¹ *
          ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
        _ = (↑n)⁻¹ * |(∑' (i : ℤ), (a i * r i)) -
          ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            rw[← mul_sub, abs_mul]
            simp
    have : 2/(↑n : ℝ) * ∑ x ∈ Finset.Ico (0 : ℤ) ↑(Fintype.card ι) ∪ Finset.Icc (↑n) (↑(Fintype.card ι) + ↑n), |∏ x_1, F x_1 (k + unit x_1 x)|
     = (↑n)⁻¹ * (2*∑ x ∈ Finset.Ico (0 : ℤ) ↑(Fintype.card ι) ∪ Finset.Icc (↑n) (↑(Fintype.card ι) + ↑n), |∏ x_1, F x_1 (k + unit x_1 x)|) := by
        set a := ∑ x ∈ Finset.Ico (0 : ℤ) ↑(Fintype.card ι) ∪ Finset.Icc (↑n) (↑(Fintype.card ι) + ↑n), |∏ x_1, F x_1 (k + unit x_1 x)|
        have : 0 < (↑n : ℝ) := by simp; exact Nat.zero_lt_of_ne_zero hn
        field_simp
    rw[this]
    gcongr
    set C := (Fintype.card ι : ℤ)
    calc
      |(∑' (i : ℤ), (a i * r i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i|
          = |(∑' i : Icc (∑ r, k r) (C+↑n + ∑ r, k r), (a ↑i * r ↑i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr 2
            rw[← tsum_subtype_eq_of_support_subset (s := Icc (∑ r, k r) (C+↑n + ∑ r, k r))]
            intro i
            simp
            intro ih _
            contrapose ih
            simp
            simp at ih
            unfold a
            suffices : Ico (↑i) ((↑i : ℝ) + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)) = ∅
            · rw[this]
              simp
            by_cases ih' : ∑ r, k r ≤ i
            · specialize ih ih'
              ext s
              simp
              intro is sip sums
              apply le_of_lt
              calc
                (↑n : ℝ) + ∑ j, (↑(k j) + α j) < ↑n + ((∑ j, ↑(k j)) + C) := by
                    rw[Finset.sum_add_distrib]
                    gcongr
                    calc
                      ∑ x, α x < ∑ x, (1 : ℝ) := by
                        refine Finset.sum_lt_sum_of_nonempty ?_ ?_
                        · simp
                        intro i _
                        exact (hα i).2
                      _ = ↑C := by
                        unfold C
                        simp
                  _ = (↑(C + (↑n : ℤ) + ∑ r, k r) : ℝ) := by simp; ring
                  _ < (↑i : ℝ) := by simp [-Int.cast_natCast, -Int.cast_sum, -Int.cast_add, ih]
                  _ ≤ s := is
            clear ih
            ext s
            simp
            intro is si sums
            simp at ih'
            contrapose sums
            clear sums
            simp
            calc
              s < (↑i : ℝ) + 1 := si
              _ = ↑(i + 1) := by simp
              _ ≤ ∑ r, (k r) := by
                simp [- Int.cast_add, -Int.cast_one, -Int.cast_sum]
                exact ih'
              _ = ∑ r, (↑(k r) : ℝ) := by simp
              _ ≤ ∑ j, (↑(k j) + α j) := by
                rw[Finset.sum_add_distrib]
                simp
                apply Finset.sum_nonneg
                intro a _
                exact (hα a).1
        _ = |(∑ i ∈ Icc (∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            simp
            set s := Icc (∑ r, k r) (C + (↑n : ℤ) + ∑ r, k r)
            have : ∑ x ∈ Finset.Icc (∑ r, k r) (C + ↑n + ∑ r, k r), a x * r x
                = ∑ x ∈ s, a x * r x := by unfold s; simp
            rw[this]
            clear this
            have : ∑' (i : ↑s), a ↑i * r ↑i = ∑' (i : ↑(↑(s.toFinset) : Set ℤ)), a ↑i * r ↑i := by
              suffices : (↑(s.toFinset) : Set ℤ) = s
              · rw[this]
              unfold s
              simp
            rw[this]
            rw[Finset.tsum_subtype' (s := s.toFinset) (f := fun i ↦ a ↑i * r ↑i)]
        _ = |(∑ i ∈ Finset.Icc (∑ r, k r) (C+↑n + ∑ r, k r), (a ↑i * r ↑i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            simp
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))
           - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            have : Disjoint (Finset.Ico (∑ r, k r) (↑n + ∑ r, k r)) (Finset.Icc (↑n + ∑ r, k r) (C + ↑n + ∑ r, k r)) := by
              refine Finset.disjoint_left.mpr ?_
              simp
              intros
              linarith
            rw[← Finset.sum_disjUnion this]
            congr 1
            ext x
            simp
            set b := C + ↑n + ∑ r, k r
            set c := ↑n + ∑ r, k r
            set a := ∑ r, k r
            constructor
            · intro h
              simp [h]
              exact Int.lt_or_le x c
            intro h
            obtain h|h := h
            · simp [h]
              suffices : c ≤ b
              · linarith
              unfold b c C
              simp
            simp [h]
            suffices: a ≤ c
            · linarith
            unfold a c
            simp
    ---------------------------------------------------------------------------
    calc
        _ = |(∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), (a i * r i - r i)) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i))| := by
            rw[Finset.sum_sub_distrib]
            ring_nf
        _ = |(∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), (a i - 1) * r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i))| := by
            congr
            ext
            rw[sub_mul, one_mul]
        _ ≤ |(∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), (a i - 1) * r i)| + |(∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i))| := by
            apply abs_add
        _ ≤ (∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), |(a i - 1) * r i|) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |(a i * r i)|) := by
            gcongr <;> apply Finset.abs_sum_le_sum_abs
        _ = (∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), |(a i - 1)| * |r i|) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |a i| * |r i|) := by
            congr
            repeat
              ext
              rw[abs_mul]
        _ ≤ (∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), |(a i - 1)| * |r i|) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |a i| * |r i|) := by
            gcongr
            unfold C
            simp [le_of_lt h]
        _ ≤ (∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), |r i|) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |r i|) := by
            have (i : ℤ): 0 ≤ a i ∧ a i ≤ 1 := by
              unfold a
              simp
              calc
                (volume (Ico (↑i : ℝ) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))).toReal
                ≤ (volume (Ico (↑i : ℝ) (↑i + 1))).toReal := by
                  gcongr
                  all_goals simp
              _ = 1 := by simp
            gcongr
            repeat
              rename_i i ih
              nth_rw 2[← one_mul |r i|]
              gcongr
              apply abs_le.2
              specialize this i
              constructor <;> linarith
        _ = ∑ a ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), |r a| + ∑ a ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |r a| := by rfl
        _ ≤ 2 * ∑ a ∈ (Finset.Ico (∑ r, k r) (C + ∑ r, k r) ∪ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r)), |r a| := by
            have s1 := finset_sum_of_nonneg_le_two_mul_union (α := ℤ) (s := Finset.Ico (∑ r, k r) (C + ∑ r, k r)) (u := Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r)) (f := fun i ↦ |r i|)
            simp_all
            have : 0 ≤ fun i ↦ |r i| := by intro _; simp
            have s2 := s1 this
            clear this s1
            refine le_trans s2 ?_
            simp
            apply le_of_eq
            congr 1
            ext x
            simp --wtf is this
    gcongr
    apply le_of_eq
    calc
        _ = ∑ i ∈ (Finset.Ico 0 C ∪ (Finset.Icc ↑n (C+↑n))), |r (i + ∑ r, k r)| := by
          apply Finset.sum_bijective (s := (Finset.Ico (∑ r, k r) (C + ∑ r, k r) ∪ (Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r)))) (e := fun i ↦ i - ∑ r : ι, k r)
          · exact AddGroup.addRight_bijective (-∑ r, k r)
          · intro i
            simp
            constructor
            · intro h
              obtain ⟨h1,h2⟩|⟨h1,h2⟩ := h
              · left
                constructor
                · exact h1
                linarith
              right
              constructor
              · linarith
              exact h2
            intro h
            obtain ⟨h1,h2⟩|⟨h1,h2⟩ := h
            · left
              constructor
              · exact h1
              linarith
            right
            constructor
            · linarith
            exact h2
          intros
          simp
        _ = ∑ i ∈ Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (Fintype.card ι + (↑n : ℤ)), |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))| := by
          unfold r C
          congr
    unfold C
    simp
    --_ = ∑ i ∈ (Finset.Ico (∑ r, k r) (C + ∑ r, k r) ∪ (Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r))), |r i| := by
    --set a : ℤ → ℝ := fun i ↦ (volume (Ico (↑i : ℝ) (↑i + 1) ∩ (Ico (∑ j, ((↑(k j) : ℝ) + α j)) (((↑n : ℝ) + ∑ j, (↑(k j) + α j)))))).toReal


--ACHTUNG AUF 2 AUFPASSEN!
set_option maxHeartbeats 300000 in
--i wish it wasnt necessary
theorem multilinear_avg_spec_discrete_avg_est [Nonempty ι](k : ι → ℤ)(α : ι → ℝ)(hα: ∀(i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ):
  |(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k| ≤
    2/n * ∑ i ∈ Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (Fintype.card ι + (↑n : ℤ)), |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))| := by
    by_cases hn: n = 0
    · rw[hn]
      unfold discrete_avg' multilinear_avg_spec multilinear_avg
      simp
    have hn': 0 < (↑n : NNReal) := by
      simp
      exact Nat.zero_lt_of_ne_zero hn
    let C := (Fintype.card ι : ℤ)
    by_cases Cn: n < C
    · unfold C at Cn
      simp at Cn
      exact multilinear_avg_spec_discrete_avg_est_c_big k α hα F n Cn
    rw[fact5_4 k α hα F hn']
    rw[fact5_3']
    simp
    let r : ℤ → ℝ := fun i ↦ ∏ j_1 : ι, F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o
    set a : ℤ → ℝ := fun i ↦ (volume (Ico (↑i : ℝ) (↑i + 1) ∩ (Ico (∑ j, ((↑(k j) : ℝ) + α j)) (((↑n : ℝ) + ∑ j, (↑(k j) + α j)))))).toReal
    calc
      |(↑n)⁻¹ *
        (∑' (i : ℤ), (volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))).toReal *
              ∏ j_1, F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o) -
      (↑n)⁻¹ * ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, F j_1 (k + unit j_1 (i - ∑ r, k r))|
          = |(↑n)⁻¹ * (∑' (i : ℤ), (a i * r i)) - (↑n)⁻¹ *
          ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
        _ = (↑n)⁻¹ * |(∑' (i : ℤ), (a i * r i)) -
          ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            rw[← mul_sub, abs_mul]
            simp
    gcongr
    · field_simp
      gcongr
      simp
    calc
      |(∑' (i : ℤ), (a i * r i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i|
          = |(∑' i : Icc (∑ r, k r) (C+↑n + ∑ r, k r), (a ↑i * r ↑i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr 2
            rw[← tsum_subtype_eq_of_support_subset (s := Icc (∑ r, k r) (C+↑n + ∑ r, k r))]
            intro i
            simp
            intro ih _
            contrapose ih
            simp
            simp at ih
            unfold a
            suffices : Ico (↑i) ((↑i : ℝ) + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)) = ∅
            · rw[this]
              simp
            by_cases ih' : ∑ r, k r ≤ i
            · specialize ih ih'
              ext s
              simp
              intro is sip sums
              apply le_of_lt
              calc
                (↑n : ℝ) + ∑ j, (↑(k j) + α j) < ↑n + ((∑ j, ↑(k j)) + C) := by
                    rw[Finset.sum_add_distrib]
                    gcongr
                    calc
                      ∑ x, α x < ∑ x, (1 : ℝ) := by
                        refine Finset.sum_lt_sum_of_nonempty ?_ ?_
                        · simp
                        intro i _
                        exact (hα i).2
                      _ = ↑C := by
                        unfold C
                        simp
                  _ = (↑(C + (↑n : ℤ) + ∑ r, k r) : ℝ) := by simp; ring
                  _ < (↑i : ℝ) := by simp [-Int.cast_natCast, -Int.cast_sum, -Int.cast_add, ih]
                  _ ≤ s := is
            clear ih
            ext s
            simp
            intro is si sums
            simp at ih'
            contrapose sums
            clear sums
            simp
            calc
              s < (↑i : ℝ) + 1 := si
              _ = ↑(i + 1) := by simp
              _ ≤ ∑ r, (k r) := by
                simp [- Int.cast_add, -Int.cast_one, -Int.cast_sum]
                exact ih'
              _ = ∑ r, (↑(k r) : ℝ) := by simp
              _ ≤ ∑ j, (↑(k j) + α j) := by
                rw[Finset.sum_add_distrib]
                simp
                apply Finset.sum_nonneg
                intro a _
                exact (hα a).1
        _ = |(∑ i ∈ Icc (∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            simp
            set s := Icc (∑ r, k r) (C + (↑n : ℤ) + ∑ r, k r)
            have : ∑ x ∈ Finset.Icc (∑ r, k r) (C + ↑n + ∑ r, k r), a x * r x
                = ∑ x ∈ s, a x * r x := by unfold s; simp
            rw[this]
            clear this
            have : ∑' (i : ↑s), a ↑i * r ↑i = ∑' (i : ↑(↑(s.toFinset) : Set ℤ)), a ↑i * r ↑i := by
              suffices : (↑(s.toFinset) : Set ℤ) = s
              · rw[this]
              unfold s
              simp
            rw[this]
            rw[Finset.tsum_subtype' (s := s.toFinset) (f := fun i ↦ a ↑i * r ↑i)]
        _ = |(∑ i ∈ Finset.Icc (∑ r, k r) (C+↑n + ∑ r, k r), (a ↑i * r ↑i)) - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            simp
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))
           - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            have : Disjoint (Finset.Ico (∑ r, k r) (↑n + ∑ r, k r)) (Finset.Icc (↑n + ∑ r, k r) (C + ↑n + ∑ r, k r)) := by
              refine Finset.disjoint_left.mpr ?_
              simp
              intros
              linarith
            rw[← Finset.sum_disjUnion this]
            congr 1
            ext x
            simp
            set b := C + ↑n + ∑ r, k r
            set c := ↑n + ∑ r, k r
            set a := ∑ r, k r
            constructor
            · intro h
              simp [h]
              exact Int.lt_or_le x c
            intro h
            obtain h|h := h
            · simp [h]
              suffices : c ≤ b
              · linarith
              unfold b c C
              simp
            simp [h]
            suffices: a ≤ c
            · linarith
            unfold a c
            simp
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))
           - ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), r i| := by
            congr
            have : Disjoint (Finset.Ico (∑ r, k r) (C + ∑ r, k r)) (Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r)) := by
              refine Finset.disjoint_left.mpr ?_
              simp
              intros
              linarith
            rw[← Finset.sum_disjUnion (f := fun i ↦ a i * r i) (h := this)]
            congr
            simp
            ext s
            by_cases hs: s < C + ∑ r, k r <;> simp [hs]
            · constructor
              · intro h
                left
                exact h.1
              intro h
              obtain h|h := h
              · simp [h] --C ≤ n :(
                simp at Cn
                linarith
              linarith
            intro h
            simp_all
            have : 0 ≤ C := by unfold C; simp
            linarith
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))
           - ((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), r i) + ∑ i ∈ Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r), r i)| := by
            congr
            have : Disjoint (Finset.Ico (∑ r, k r) (C + ∑ r, k r)) (Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r)) := by
              refine Finset.disjoint_left.mpr ?_
              simp
              intros
              linarith
            rw[← Finset.sum_disjUnion (f := r) (h := this)]
            congr
            simp
            ext s
            by_cases hs: s < C + ∑ r, k r <;> simp [hs]
            · constructor
              · intro h
                left
                exact h.1
              intro h
              obtain h|h := h
              · simp [h] --C ≤ n :(
                simp at Cn
                linarith
              linarith
            intro h
            simp_all
            have : 0 ≤ C := by unfold C; simp
            linarith
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r), r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))
           - ((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), r i) + ∑ i ∈ Finset.Ico (C + ∑ r, k r) (↑n + ∑ r, k r), r i)| := by
            congr 4
            apply Finset.sum_congr rfl
            intro u uh
            suffices : a u = 1
            · rw[this, one_mul]
            unfold a
            suffices : (Ico (↑u : ℝ) ((↑u : ℝ) + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j))) = Ico (↑u : ℝ) ((↑u : ℝ) + 1)
            · rw[this]
              simp
            simp
            intro s
            simp at *
            intro us su
            constructor
            · rw[Finset.sum_add_distrib]
              calc
                ∑ x, (↑(k x) : ℝ) + ∑ x, α x
                  ≤ ∑ x, (↑(k x) : ℝ) + ∑ x : ι, 1 := by
                  gcongr
                  rename_i i _
                  exact le_of_lt (hα i).2
                _ = (↑(C + ∑ x, k x) : ℝ) := by
                  unfold C
                  simp
                  rw[add_comm]
                _ ≤ u := by
                  simp [-Int.cast_add, -Int.cast_sum, uh.1]
                _ ≤ s := us
            calc
              s < ↑u + 1:= su
              _ = (↑(u + 1) : ℝ) := by simp
              _ ≤ (↑(↑n + ∑ r, k r) : ℝ) := by simp [-Int.cast_add, -Int.cast_sum]; exact uh.2
              _ ≤ ↑n + ∑ j, (↑(k j) + α j) := by
                rw[Finset.sum_add_distrib]
                simp
                apply Finset.sum_nonneg
                intro i _
                exact (hα i).1
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), a i * r i) + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))
           - (∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), r i)| := by ring_nf
        _ = |((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), (a i - 1) * r i)
           + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)))| := by
            have : (∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), (a i - 1) * r i) = ∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), (a i * r i - r i) := by
              congr
              ext
              ring_nf
            rw[this, Finset.sum_sub_distrib]
            ring_nf
        _ ≤ |∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), (a i - 1) * r i|
           + |∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i)| := by
            exact abs_add_le (∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), (a i - 1) * r i) (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (a i * r i))
        _ ≤ ((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), |(a i - 1) * r i|)
           + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (|a i * r i|))) := by
            gcongr <;> apply Finset.abs_sum_le_sum_abs
        _ = ((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), |(a i - 1)| * |r i|)
           + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), (|a i| * |r i|))) := by
            congr
            repeat
              ext
              rw[abs_mul]
        _ ≤ ((∑ i ∈ Finset.Ico (∑ r, k r) (C + ∑ r, k r), |r i|)
           + (∑ i ∈ Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |r i|)) := by
            have (i : ℤ): 0 ≤ a i ∧ a i ≤ 1 := by
              unfold a
              simp
              calc
                (volume (Ico (↑i : ℝ) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))).toReal
                  ≤ (volume (Ico (↑i : ℝ) (↑i + 1))).toReal := by
                    have : volume (Ico (↑i : ℝ) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j))) ≤ volume (Ico (↑i : ℝ) (↑i + 1)) := by
                      refine measure_mono ?_
                      simp
                    refine ENNReal.toReal_mono ?_ this
                    simp
                _ = 1 := by simp
            gcongr
            repeat
              rename_i i _
              nth_rw 2[← one_mul |r i|]
              gcongr
              specialize this i
              apply abs_le.2
              constructor <;> linarith
        _ = ((∑ i ∈ Ico (∑ r, k r) (C + ∑ r, k r), |r i|) + (∑ i ∈ Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r), |r i|)) := by
          congr 2
          repeat simp
        _ = ∑ i ∈ (Finset.Ico (∑ r, k r) (C + ∑ r, k r) ∪ (Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r))), |r i| := by
          have : Disjoint (Finset.Ico (∑ r, k r) (C + ∑ r, k r)) (Finset.Icc (↑n + ∑ r, k r) (C + ↑n + ∑ r, k r)) := by
            refine Finset.disjoint_left.mpr ?_
            simp
            intros
            linarith
          rw[Set.toFinset_Ico, Set.toFinset_Icc]
          rw[← Finset.sum_disjUnion (h := this)]
          congr
          simp
        _ = ∑ i ∈ (Finset.Ico 0 C ∪ (Finset.Icc ↑n (C+↑n))), |r (i + ∑ r, k r)| := by
          apply Finset.sum_bijective (s := (Finset.Ico (∑ r, k r) (C + ∑ r, k r) ∪ (Finset.Icc (↑n + ∑ r, k r) (C+↑n + ∑ r, k r)))) (e := fun i ↦ i - ∑ r : ι, k r)
          · exact AddGroup.addRight_bijective (-∑ r, k r)
          · intro i
            simp
            constructor
            · intro h
              obtain ⟨h1,h2⟩|⟨h1,h2⟩ := h
              · left
                constructor
                · exact h1
                linarith
              right
              constructor
              · linarith
              exact h2
            intro h
            obtain ⟨h1,h2⟩|⟨h1,h2⟩ := h
            · left
              constructor
              · exact h1
              linarith
            right
            constructor
            · linarith
            exact h2
          intros
          simp
        _ = ∑ i ∈ Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (Fintype.card ι + (↑n : ℤ)), |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))| := by
          unfold r C
          congr
    simp


lemma ennreal_two_mul_le_add_sq (a b : ℝ≥0∞) : 2 * a * b ≤ a^2 + b^2 := by
  by_cases ai: a = ∞
  · rw[ai]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_top, top_pow, top_add, le_top]
  by_cases bi : b = ∞
  · rw[bi]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, top_pow, add_top, le_top]
  refine (toReal_le_toReal ?_ ?_).mp ?_
  · refine mul_ne_top ?_ bi
    refine mul_ne_top ?_ ai
    simp only [ne_eq, ofNat_ne_top, not_false_eq_true]
  · simp only [ne_eq, add_eq_top, pow_eq_top_iff, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
    not_or]
    tauto
  simp only [toReal_mul, toReal_ofNat]
  rw[ENNReal.toReal_add]
  · rw [toReal_pow, toReal_pow]
    exact two_mul_le_add_sq a.toReal b.toReal
  · contrapose ai
    simp_all only [ne_eq, pow_eq_top_iff, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
      Decidable.not_not, not_true_eq_false]
  contrapose bi
  simp_all only [ne_eq, pow_eq_top_iff, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
    Decidable.not_not, not_true_eq_false]

lemma ennreal_sq_sum_le_card_mul_sum_sq {α : Type*} (f : α → ENNReal) {s : Finset α} (hs : s.Nonempty):
    (∑ x ∈ s, f x)^2 ≤ s.card * (∑ x ∈ s, (f x)^2) := by
  revert s
  apply Finset.induction
  · simp only [Finset.not_nonempty_empty, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.card_empty, CharP.cast_eq_zero, mul_zero, le_refl,
    implies_true]
  intro a s asn se as
  rw [@Finset.card_insert_eq_ite, Finset.sum_insert asn]
  simp only [asn, ↓reduceIte, Nat.cast_add, Nat.cast_one, not_false_eq_true, Finset.sum_insert]
  rw[add_sq]
  calc
    f a ^ 2 + 2 * f a * ∑ x ∈ s, f x + (∑ x ∈ s, f x) ^ 2
      = f a ^ 2 + 2 * ∑ x ∈ s, f a * f x + (∑ x ∈ s, f x) ^ 2 := by
      congr 2
      rw [mul_assoc, @Finset.mul_sum]
    _ ≤ f a ^ 2 + 2 * ∑ x ∈ s, f a * f x + s.card * (∑ x ∈ s, f x ^2) := by
      gcongr
      by_cases h : s.Nonempty
      · exact se h
      rw[Finset.not_nonempty_iff_eq_empty.mp h]
      simp only [Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.card_empty, CharP.cast_eq_zero, mul_zero, le_refl]
    _ = f a ^ 2 + ∑ x ∈ s, 2 * f a * f x + s.card * (∑ x ∈ s, f x ^2) := by
      congr 2
      rw[Finset.mul_sum]
      ring_nf
    _ ≤ f a ^ 2 + ∑ x ∈ s, (f a ^ 2 + f x ^ 2) + s.card * (∑ x ∈ s, f x ^2) := by
      gcongr
      apply ennreal_two_mul_le_add_sq
    _ = (↑s.card + 1) * (f a ^ 2 + ∑ x ∈ s, f x ^ 2) := by
      rw[Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

lemma real_sum_nonneg_singleton {f : ι → ℝ} (hf : 0 ≤ f) (i : ι): f i ≤ ∑ j, f j := by
  calc
    f i = (fun (r : ι) ↦ if r = i then f r else 0) i := by simp only [↓reduceIte]
      _ = ∑ j, (fun (r : ι) ↦ if r = i then f r else 0) j := by
        refine Eq.symm (Fintype.sum_eq_single i ?_)
        intro x hx
        simp only [hx, ↓reduceIte]
      _ ≤ ∑ j, f j := by
        gcongr
        rename_i s _
        by_cases si : s = i <;> simp only [si, ↓reduceIte, le_refl]
        exact hf s

lemma tsum_sum_interchange_ennreal {α β : Type*} (s : Finset β) (f : β → α → ℝ≥0∞) :
    ∑' a : α, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑' a : α, f b a := by
  revert s
  apply Finset.induction
  · simp only [Finset.sum_empty, tsum_zero]
  intro c s bs h
  calc
     ∑' (a : α), ∑ b ∈ insert c s, f b a
      = ∑' (a : α), (f c a + ∑ b ∈ s, f b a) := by
      congr
      ext
      rw [Finset.sum_insert bs]
    _ = ∑' (a : α), f c a + ∑' (a : α), ∑ b ∈ s, f b a := by rw [← @ENNReal.tsum_add]
    _ = ∑' (a : α), f c a + ∑ b ∈ s, ∑' (a : α), f b a := by rw[h]
    _ = ∑ b ∈ insert c s, ∑' (a : α), f b a := by rw [Finset.sum_insert bs]


theorem ennreal_geom_mean_le_arith_mean {ι : Type*} (s : Finset ι)
  (z : ι → ENNReal) (w : ι → NNReal) (hw' : ∑ i ∈ s, w i = 1) (hw'' : ∀ i ∈ s, 0 < w i):
    ∏ i ∈ s, z i ^ (↑(w i) : ℝ) ≤ ∑ i ∈ s, w i * z i := by
  by_cases hz : ∃ i ∈ s, z i = ∞
  · suffices : ∑ i ∈ s, w i * z i = ∞
    · rw[this]
      apply le_top
    simp
    obtain ⟨a,ah⟩ := hz
    use a
    constructor
    · exact ah.1
    refine mul_eq_top.mpr ?_
    left
    constructor
    · simp only [ne_eq, ENNReal.coe_eq_zero]
      contrapose hw''
      refine not_forall_of_exists_not ?_
      use a
      simp_all only [Decidable.not_not, lt_self_iff_false, imp_false, not_true_eq_false,
        not_false_eq_true]
    exact ah.2
  simp only [not_exists, not_and] at hz
  refine (ENNReal.toNNReal_le_toNNReal ?_ ?_).mp ?_
  · by_contra h0
    apply (prod_eq_top_iff _ _).1 at h0
    contrapose h0
    simp
    tauto
  · simp only [ne_eq, sum_eq_top, not_exists, not_and]
    intro x xs
    refine mul_ne_top ?_ (hz x xs)
    simp only [ne_eq, coe_ne_top, not_false_eq_true]
  rw [@toNNReal_prod]
  rw[toNNReal_sum]
  swap
  · intro a ah
    refine mul_ne_top ?_ (hz a ah)
    simp only [ne_eq, coe_ne_top, not_false_eq_true]
  calc
    ∏ i ∈ s, (z i ^ (↑(w i) : ℝ)).toNNReal
      = ∏ i ∈ s, (z i).toNNReal ^ (↑(w i) : ℝ) := by
      congr
      ext i
      simp only [toNNReal_rpow, NNReal.coe_rpow]
    _ ≤ ∑ a ∈ s, w a * (z a).toNNReal := by
      exact NNReal.geom_mean_le_arith_mean_weighted s w (fun i ↦ (z i).toNNReal) hw'
    _ = ∑ a ∈ s, (↑(w a) * z a).toNNReal := by
      congr
      ext i
      simp only [NNReal.coe_mul, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

lemma tsum_sum_finset_card {α β γ : Type*} (s : Finset β) (f : γ → ℝ≥0∞) (g : α → β → γ)
    (h : ∀ b, Injective (fun a ↦ (g a b))) :
    ∑ b ∈ s, ∑' a : α, f (g a b) ≤ s.card * ∑' c : γ, f c := by
  revert s
  apply Finset.induction
  · simp only [Finset.sum_empty, Finset.card_empty, CharP.cast_eq_zero, zero_mul, le_refl]
  intro b s bs h
  rw [Finset.sum_insert bs, Finset.card_insert_of_notMem bs]
  simp only [Nat.cast_add, Nat.cast_one]
  rw[add_mul, add_comm]
  gcongr
  rw[one_mul]
  (expose_names; exact tsum_comp_le_tsum_of_injective (h_1 b) f)

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
  · simp only [Finset.sum_empty, NNReal.mk_zero]
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


theorem tsum_sum_sum_est_ennreal'
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

theorem tsum_sum_sum_est_ennreal
    (f : γ × α → ℝ≥0∞) {g : γ → β → α → α}
    (hg: ∀ r, ∀ j, Injective (g r j)):
    ∑' i : α, ∑ j ∈ m, ∑ r ∈ s, f (r, (g r j i)) ≤ m.card * ∑' i : α, ∑ r ∈ s, f (r, i) := by
  rw[tsum_sum_interchange_ennreal s fun b a ↦ f (b, a)]
  exact tsum_sum_sum_est_ennreal' m s f hg

end technical_sum

lemma enorm_le_enorm {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b): ‖a‖ₑ ≤ ‖b‖ₑ := by
  refine enorm_le_iff_norm_le.mpr ?_
  refine norm_le_norm_of_abs_le_abs ?_
  exact abs_le_abs_of_nonneg ha h


--Since the thing here ONLY requires the definitions and above lemma, i comment out much now and leave the versy first sorry
theorem multilinear_avg_approx_sum_discrete_avg_ell_two [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2):
  ∑' k : ι → ℤ, ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2
    ≤ ((64*(Fintype.card ι)^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1) := by
    let C := 2*Fintype.card ι
    let M := Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (Fintype.card ι + (↑n : ℤ))
    by_cases n0: 0 < n
    swap
    · simp only [not_lt, nonpos_iff_eq_zero] at n0
      rw[n0]
      unfold discrete_avg' approx_sum_mul approx_sum multilinear_avg_spec multilinear_avg
      simp only [CharP.cast_eq_zero, NNReal.coe_zero, _root_.div_zero, zero_mul, mem_Ico, le_refl,
        zero_lt_one, and_self, indicator_of_mem, Pi.one_apply, one_mul, Finset.range_zero,
        Finset.sum_empty, mul_zero, sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, tsum_zero, ENNReal.coe_zero, zero_le]
    calc
          ∑' k : ι → ℤ, ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2
      _ ≤ ∑' k : ι → ℤ, ‖2/n * ∑ i ∈ M, |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))|‖ₑ^2 := by
        gcongr with k
        nth_rw 1[← Real.enorm_abs]
        apply enorm_le_enorm
        · apply abs_nonneg
        apply multilinear_avg_spec_discrete_avg_est (hα := hα)
      _ = (4/(↑n^2 : NNReal))* ∑' k : ι → ℤ, ‖∑ i ∈ M, |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))|‖ₑ^2 := by
        rw [← @ENNReal.tsum_mul_left]
        congr
        ext i
        rw[enorm_mul, mul_pow]
        congr
        simp only [ENNReal.coe_pow, coe_natCast]
        suffices : ‖2 / (↑n : ℝ)‖ₑ = 2 / n
        · rw[this]
          rw [← ENNReal.rpow_two, ENNReal.div_rpow_of_nonneg]
          · congr 1
            · norm_num
            rw [ENNReal.rpow_two]
          simp only [Nat.ofNat_nonneg]
        rw [Real.enorm_eq_ofReal_abs]
        have : |2 / (↑n : ℝ)| = 2 / (↑n : ℝ) := by
          simp only [abs_eq_self]
          apply div_nonneg <;> simp only [Nat.ofNat_nonneg, Nat.cast_nonneg]
        rw[this]
        rw[ENNReal.ofReal_div_of_pos]
        simp only [ofReal_ofNat, ofReal_natCast]
        exact Nat.cast_pos'.mpr n0
      _ = (4/(↑n^2 : NNReal))* ∑' k : ι → ℤ, (∑ i ∈ M, ∏ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ)^2 := by
        congr
        ext k
        rw [Real.enorm_eq_ofReal_abs]
        have : abs (∑ i ∈ M, |∏ j_1 : ι, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))|) = ∑ i ∈ M, |∏ j_1, F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))| := by
          simp
          apply Finset.sum_nonneg
          simp
        rw[this, ENNReal.ofReal_sum_of_nonneg]
        · congr
          ext i
          rw[Finset.abs_prod]
          rw[ENNReal.ofReal_prod_of_nonneg]
          · congr
            ext i
            rw [Real.enorm_eq_ofReal_abs]
          simp
        simp
      _ ≤ (4/(↑n^2 : NNReal))* ∑' k : ι → ℤ, M.card * ∑ i ∈ M, (∏ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ)^2 := by
        gcongr
        rename_i k
        apply ennreal_sq_sum_le_card_mul_sum_sq
        unfold M
        simp
      _ ≤ (4/(↑n^2 : NNReal))* ∑' k : ι → ℤ, (2*C) * ∑ i ∈ M, (∏ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ)^2 := by
        gcongr
        unfold M
        have : 2 * (↑C : ℝ≥0∞) = (↑((2 : ℕ) * C) : ℝ≥0∞) := by simp only [Nat.cast_mul,
          Nat.cast_ofNat]
        rw[this]
        simp only [Nat.cast_le, ge_iff_le]
        calc
          (Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (↑(Fintype.card ι) + (↑n : ℤ))).card
            ≤ (Finset.Ico 0 (↑(Fintype.card ι) : ℤ)).card +
              (Finset.Icc (↑n) ((↑(Fintype.card ι) : ℤ) + (↑n : ℤ))).card := by
            apply Finset.card_union_le
          _ ≤ C + C := by
            apply add_le_add
            · unfold C
              simp only [Int.card_Ico, sub_zero, Int.toNat_natCast]
              linarith
            unfold C
            simp
            have : 0 < (↑(Fintype.card ι) : ℤ) := by simp only [Int.natCast_pos]; exact Fintype.card_pos
            linarith
          _ = 2*C := by ring
      _ = ((8*C)/(↑n^2 : NNReal))* ∑' k : ι → ℤ, ∑ i ∈ M, (∏ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ)^2 := by
        rw[ENNReal.tsum_mul_left]
        rw[← mul_assoc]
        congr 1
        set t := (↑((↑n : NNReal)^2) : ℝ≥0∞)
        rw [@ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
      _ = ((8*C)/(↑n^2 : NNReal))* ∑' k : ι → ℤ, ∑ i ∈ M, ∏ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ^2 := by
        congr
        ext
        congr
        ext
        rw [@Finset.prod_pow]
      _ ≤ ((8*C)/(↑n^2 : NNReal))* ∑' k : ι → ℤ, ∑ i ∈ M, ∑ j_1, 2/(q j_1).toNNReal * ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ^(q j_1) := by
        gcongr
        rename_i k n hn
        let h := fun j_1 ↦ ‖F j_1 (k + unit j_1 (n + ∑ r, k r - ∑ r, k r))‖ₑ
        suffices : ∏ j_1, (h j_1)^2 ≤ ∑ j_1, 2 / ↑(q j_1).toNNReal * (h j_1) ^ q j_1
        · unfold h at this
          simp_all only [one_div, add_sub_cancel_right]
        calc
          ∏ j_1, h j_1 ^ 2
            = ∏ j_1, (h j_1 ^ q j_1) ^ (↑(2 / q j_1).toNNReal : ℝ) := by
            congr
            ext i
            rw [← ENNReal.rpow_mul, ← ENNReal.rpow_two]
            congr
            simp only [coe_toNNReal']
            have : max (2 / q i) 0 = 2 / q i := by
              simp only [sup_eq_left]
              apply div_nonneg
              · linarith
              exact le_of_lt (hq.1 i)
            rw[this]
            refine Eq.symm (mul_div_cancel₀ 2 ?_)
            have := hq.1 i
            contrapose this
            simp_all only [one_div, sup_eq_left, ne_eq, Decidable.not_not, lt_self_iff_false,
              not_false_eq_true]
          _ ≤ ∑ j_1, (2 / q j_1).toNNReal * (h j_1 ^ q j_1) := by
            apply ennreal_geom_mean_le_arith_mean
            · rw[← Real.toNNReal_sum_of_nonneg]
              · simp only [toNNReal_eq_one]
                calc
                  ∑ a, 2 / q a
                    = ∑ a, 2 * (1 / q a) := by
                    congr
                    ext a
                    simp only [one_div]
                    rw [@Field.div_eq_mul_inv]
                  _ = 2 * ∑ a, 1 / q a := by rw [@Finset.mul_sum]
                  _ = 1 := by
                    rw[hq.2]
                    norm_num
              intro i _
              apply div_nonneg
              · linarith
              exact le_of_lt (hq.1 i)
            intro i _
            simp only [Real.toNNReal_pos, Nat.ofNat_pos, div_pos_iff_of_pos_left]
            exact hq.1 i
          _ = ∑ j_1, 2 / (↑(q j_1) : ℝ).toNNReal * h j_1 ^ q j_1 := by
            congr
            ext i
            congr
            rw[Real.toNNReal_div]
            simp only [Real.toNNReal_ofNat]
            refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
            · simp only [ne_eq, coe_ne_top, not_false_eq_true]
            · refine div_ne_top ?_ ?_
              · simp only [ne_eq, ofNat_ne_top, not_false_eq_true]
              simp only [ne_eq, ENNReal.coe_eq_zero, toNNReal_eq_zero, not_le]
              exact hq.1 i
            simp only [coe_toReal, NNReal.coe_div, NNReal.coe_ofNat, coe_toNNReal', toReal_div,
              toReal_ofNat]
            linarith
      _ ≤ ((8*C)/(↑n^2 : NNReal))* ∑' k : ι → ℤ, ∑ i ∈ M, ∑ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ^(q j_1) := by
        gcongr
        rename_i a b hb d hd
        rw[← one_mul (‖F d (a + unit d (b + ∑ r, a r - ∑ r, a r))‖ₑ ^ q d)]
        gcongr
        swap
        · simp only [add_sub_cancel_right, one_mul, le_refl]
        have : 2 / (↑(q d).toNNReal : ℝ≥0∞) = (↑(2 / (q d)).toNNReal : ℝ≥0∞) := by
          refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
          · refine div_ne_top ?_ ?_ <;> simp
            exact hq.1 d
          · simp only [ne_eq, coe_ne_top, not_false_eq_true]
          simp only [toReal_div, toReal_ofNat, coe_toReal, coe_toNNReal']
          have : max (q d) 0 = q d := by
            simp only [sup_eq_left]
            exact le_of_lt (hq.1 d)
          rw[this]
          have : max (2 / q d) 0 = 2 / q d := by
            simp only [sup_eq_left]
            apply div_nonneg
            · simp only [Nat.ofNat_nonneg]
            exact le_of_lt (hq.1 d)
          rw[this]
        rw[this]
        simp only [coe_le_one_iff, toNNReal_le_one, ge_iff_le]
        calc
          2 / (q d)
            = 2 * (1 / (q d)) := div_eq_mul_one_div 2 (q d)
          _ ≤ 2 * ∑ i, 1 / q i := by
            gcongr
            apply real_sum_nonneg_singleton (f := fun i ↦ 1 / q i)
            intro i
            simp only [Pi.zero_apply, one_div, inv_nonneg]
            exact (le_of_lt (hq.1 i))
          _ = 1 := by rw[hq.2]; ring
      _ ≤ ((8*C)/(↑n^2 : NNReal))* ∑' k : ι → ℤ, (2*C) * ∑ j_1, ‖F j_1 k‖ₑ^(q j_1) := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        swap
        · apply zero_le
        let h : (ι → ℤ) → ℝ≥0∞ := fun k ↦ ∑ j_1, ‖F j_1 k‖ₑ ^ (q j_1)
        suffices : ∑' (k : ι → ℤ), ∑ i ∈ M, ∑ j_1, ‖F j_1 (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))‖ₑ ^ q j_1
          ≤ M.card * ∑' (k : ι → ℤ), ∑ j_1, ‖F j_1 k‖ₑ ^ q j_1
        · apply le_trans this
          rw[ENNReal.tsum_mul_left]
          gcongr
          unfold M
          have : 2 * (↑C : ℝ≥0∞) = (↑((2 : ℕ) * C) : ℝ≥0∞) := by simp only [Nat.cast_mul,
              Nat.cast_ofNat]
          rw[this]
          simp only [Nat.cast_le, ge_iff_le]
          calc
            (Finset.Ico 0 (↑(Fintype.card ι) : ℤ) ∪ Finset.Icc (↑n) (↑(Fintype.card ι) + (↑n : ℤ))).card
              ≤ (Finset.Ico 0 (↑(Fintype.card ι) : ℤ)).card +
                (Finset.Icc (↑n) ((↑(Fintype.card ι) : ℤ) + (↑n : ℤ))).card := by
              apply Finset.card_union_le
            _ ≤ C + C := by
              apply add_le_add
              · unfold C
                simp only [Int.card_Ico, sub_zero, Int.toNat_natCast]
                linarith
              unfold C
              simp
              have : 0 < (↑(Fintype.card ι) : ℤ) := by simp only [Int.natCast_pos]; exact Fintype.card_pos
              linarith
            _ = 2*C := by ring
        have := tsum_sum_sum_est_ennreal (f := fun (j_1, k) ↦ (‖F j_1 k‖ₑ ^ q j_1)) (g := fun j_1 i k ↦ (k + unit j_1 (i + ∑ r, k r - ∑ r, k r))) (m := M) (s := Finset.univ (α := ι))
        simp at this
        simp
        apply this
        intro r j
        intro _ _ kk'
        simp at kk'
        exact kk'
      _ = ((16*C^2)/(↑n^2 : NNReal))* ∑' k : ι → ℤ, ∑ j_1, ‖F j_1 k‖ₑ^(q j_1) := by
        rw[ENNReal.tsum_mul_left]
        rw[← mul_assoc, ← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
      _ = ((16*C^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1) := by
        congr
        apply tsum_sum_interchange_ennreal
      _ = ((64*(Fintype.card ι)^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1) := by
        congr 2
        unfold C
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring

theorem multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
  ∑' k : ι → ℤ, ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2
    ≤ ((64*(Fintype.card ι)^3)/(↑n^2 : NNReal)) := by
  have og := multilinear_avg_approx_sum_discrete_avg_ell_two hα F n hq
  suffices : ((64*(Fintype.card ι)^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1) =
      ((64*(Fintype.card ι)^3)/(↑n^2 : NNReal))
  · rwa [this] at og
  have : (((64*(Fintype.card ι)^3)/(↑n^2 : NNReal)) : ℝ≥0∞) =
      (((64*(Fintype.card ι)^2)/(↑n^2 : NNReal)) : ℝ≥0∞) * (Fintype.card ι) := by
    rw [← ENNReal.mul_div_right_comm]
    congr 1
    ring
  rw[this]
  congr
  calc
    ∑ j_1, ∑' (k : ι → ℤ), ‖F j_1 k‖ₑ ^ q j_1
      = ∑ j_1 : ι, 1 := by
      congr
      ext j
      exact hF j
    _ = (Fintype.card ι) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  /-
  calc
    (((64*(Fintype.card ι)^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1) : ℝ≥0∞)
      = ((64*(↑(Fintype.card ι) : ℝ≥0∞)^2)/(↑n^2 : NNReal)) * ∑ j_1 : ι, 1 := by
      congr
      ext j
      exact hF j
    _ = ((64*(Fintype.card ι)^3)/(↑n^2 : NNReal)) := by
      simp only [ENNReal.coe_pow, coe_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
      by_cases hn : n = 0
      · rw[hn]
        simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        rw [ENNReal.div_zero, ENNReal.div_zero]
        · apply
      refine (ENNReal.eq_div_iff ?_ ?_).mpr ?_

      sorry-/

theorem multilinear_avg_approx_sum_discrete_avg_ell_two' [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1) (F : ι → (ι → ℤ) → ℝ) (n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2):
  (∑' k : ι → ℤ, ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2)^((2 : ℝ)⁻¹)
    ≤ ((8*(Fintype.card ι))/(↑n : NNReal))* (∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1))^((2 : ℝ)⁻¹) := by
  suffices : ((8*(Fintype.card ι))/(↑n : NNReal))* (∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1))^((2 : ℝ)⁻¹) =
    (((64*(Fintype.card ι)^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1))^(2 : ℝ)⁻¹
  · rw[this]
    apply ENNReal.rpow_le_rpow
    · exact multilinear_avg_approx_sum_discrete_avg_ell_two hα F n hq
    simp only [inv_nonneg, Nat.ofNat_nonneg]
  have : 0 ≤ (2 : ℝ)⁻¹ := by simp only [inv_nonneg, Nat.ofNat_nonneg]
  rw [ENNReal.mul_rpow_of_nonneg (hz := this)]
  rw [ENNReal.div_rpow_of_nonneg (hz := this)]
  congr
  · rw [ENNReal.mul_rpow_of_nonneg (hz := this)]
    congr
    · norm_num
      refine Eq.symm ((fun {x y} hx hy ↦ (toReal_eq_toReal_iff' hx hy).mp) ?_ ?_ ?_)
      · simp only [one_div, ne_eq, rpow_eq_top_iff, OfNat.ofNat_ne_zero, inv_neg'', false_and,
        ofNat_ne_top, inv_pos, Nat.ofNat_pos, and_true, or_self, not_false_eq_true]
      · simp only [ne_eq, ofNat_ne_top, not_false_eq_true]
      simp only [one_div, toReal_ofNat]
      rw[← ENNReal.toReal_rpow]
      simp only [toReal_ofNat]
      refine (rpow_inv_eq ?_ ?_ ?_).mpr ?_ <;> simp
      norm_num
    rw [← ENNReal.rpow_natCast_mul]
    simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
      ENNReal.rpow_one]
  rw [rpow_ofNNReal this]
  congr
  rw [← NNReal.rpow_natCast_mul]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
    NNReal.rpow_one]

lemma ennreal_rpow_inv {a b : ℝ≥0∞} {z : ℝ} (hz: z ≠ 0) (h : a^ z = b) : b ^ z⁻¹ = a := by
  rw[← h]
  exact ENNReal.rpow_rpow_inv hz a

theorem multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one' [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
  (∑' k : ι → ℤ, ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2) ^ (1 / (2 : ℝ))
    ≤ ((8*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑n : NNReal))) := by
  suffices : ((8*(Fintype.card ι) ^ (3 / (2 : ℝ))/((↑(↑n : NNReal)) : ℝ≥0∞))) = (((64*(Fintype.card ι)^3)/(↑n^2 : NNReal))) ^ (1 / (2 : ℝ))
  · rw[this]
    apply ENNReal.rpow_le_rpow
    · exact multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one hα F n hq hF
    norm_num
  simp only [coe_natCast, ENNReal.coe_pow, one_div]
  rw[ENNReal.div_rpow_of_nonneg]
  swap
  · norm_num
  congr
  · rw[ENNReal.mul_rpow_of_nonneg]
    swap
    · norm_num
    congr 1
    · symm
      apply ennreal_rpow_inv
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      simp only [ENNReal.rpow_ofNat]
      norm_num
    rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
    congr
  rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, ENNReal.rpow_one]

lemma ennreal_lp_add_le'_lem
    {ι : Type*} (f g : ι → ENNReal) {p : ℝ} (hp : 1 ≤ p)
    (hf : ∑' i, f i ^ p ≠ ⊤) (hg : ∑' i, g i ^ p ≠ ⊤):
    (∑' (i : ι), (f i + g i) ^ p) ^ (1 / p) ≠ ⊤ := by
  refine rpow_ne_top_of_nonneg ?_ ?_
  · simp only [one_div, inv_nonneg]
    linarith
  refine lt_top_iff_ne_top.mp ?_
  calc
    ∑' (i : ι), (f i + g i) ^ p
    _ ≤ ∑' (i : ι), 2 ^ (p - 1) * (f i ^ p + g i ^ p) := by
      gcongr
      apply ENNReal.rpow_add_le_mul_rpow_add_rpow
      exact hp
    _ = 2 ^ (p - 1) * ∑' (i : ι), f i ^ p + 2 ^ (p - 1) * ∑' (i : ι), g i ^ p := by
      rw[ENNReal.tsum_mul_left, ENNReal.tsum_add, mul_add]
    _ < ⊤ := by
      simp only [add_lt_top]
      constructor
      · refine mul_lt_top ?_ ?_
        · refine rpow_lt_top_of_nonneg ?_ ?_ <;> simp [hp]
        exact Ne.lt_top' (id (Ne.symm hf))
      refine mul_lt_top ?_ ?_
      · refine rpow_lt_top_of_nonneg ?_ ?_ <;> simp [hp]
      exact Ne.lt_top' (id (Ne.symm hg))

lemma ennreal_lp_add_le_lem'
    {ι : Type*} (f : ι → ENNReal) {p : ℝ} (hp : 1 ≤ p)
    (hf : ∑' i, f i ^ p ≠ ⊤) (i : ι):
    f i ≠ ⊤ := by
  contrapose hf
  simp_all only [ne_eq, Decidable.not_not]
  apply eq_top_iff.mpr
  calc
    ⊤ = (f i)^ p := by
      rw[hf]
      symm
      simp only [rpow_eq_top_iff, top_ne_zero, false_and, true_and, false_or]
      linarith
    _ ≤ ∑' i, f i ^ p := by exact ENNReal.le_tsum i

lemma ennreal_lp_add_le' {ι : Type*} (f g : ι → ENNReal) {p : ℝ}:
    1 ≤ p → (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
    (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  intro hp
  by_cases inf: ∑' i, f i ^ p = ⊤ ∨ ∑' i, g i ^ p = ⊤
  · have : (⊤ : ℝ≥0∞) ^ (1 / p) = ⊤ := by
      simp only [one_div, rpow_eq_top_iff, top_ne_zero, inv_neg'', false_and, inv_pos, true_and,
        false_or]
      linarith
    obtain inf|inf := inf <;> rw[inf, this] <;> simp
  simp only [not_or] at inf
  have hf: (∑' i, f i ^ p) ^ (1 / p) ≠ ⊤ := by
    refine rpow_ne_top_of_nonneg ?_ inf.1
    simp only [one_div, inv_nonneg]
    linarith
  have hg: (∑' i, g i ^ p) ^ (1 / p) ≠ ⊤ := by
    refine rpow_ne_top_of_nonneg ?_ inf.2
    simp only [one_div, inv_nonneg]
    linarith
  refine (toNNReal_le_toNNReal ?_ ?_).mp ?_
  · exact ennreal_lp_add_le'_lem  f g hp inf.1 inf.2
  · simp only [ne_eq, add_eq_top, not_or]
    exact ⟨hf, hg⟩
  rw [toNNReal_add hf hg, toNNReal_rpow, toNNReal_rpow, toNNReal_rpow]
  rw[ENNReal.tsum_toNNReal_eq, ENNReal.tsum_toNNReal_eq, ENNReal.tsum_toNNReal_eq]
  swap
  · intro i
    refine rpow_ne_top_of_nonneg ?_ ?_
    · linarith
    exact ennreal_lp_add_le_lem' g hp inf.2 i
  swap
  · intro i
    refine rpow_ne_top_of_nonneg ?_ ?_
    · linarith
    exact ennreal_lp_add_le_lem' f hp inf.1 i
  swap
  · intro i
    refine rpow_ne_top_of_nonneg ?_ ?_
    · linarith
    simp only [ne_eq, add_eq_top, not_or]
    exact ⟨ennreal_lp_add_le_lem' f hp inf.1 i, ennreal_lp_add_le_lem' g hp inf.2 i⟩
  calc
    (∑' (a : ι), ((f a + g a) ^ p).toNNReal) ^ (1 / p)
      = (∑' (a : ι), (((f a).toNNReal + (g a).toNNReal) ^ p)) ^ (1 / p) := by
      congr
      ext i
      rw[toNNReal_rpow, ENNReal.toNNReal_add]
      · exact ennreal_lp_add_le_lem' f hp inf.1 i
      exact ennreal_lp_add_le_lem' g hp inf.2 i
    _ ≤ (∑' (a : ι), (f a).toNNReal ^ p) ^ (1 / p) + (∑' (a : ι), ((g a).toNNReal ^ p)) ^ (1 / p) := by
      apply NNReal.Lp_add_le_tsum' hp
      · apply ENNReal.tsum_coe_ne_top_iff_summable.1
        contrapose inf
        simp
        intro temp
        contrapose temp
        simp at ⊢ inf
        rw[← inf]
        congr
        ext i
        rw[← toNNReal_rpow]
        refine Eq.symm (coe_toNNReal ?_)
        refine rpow_ne_top_of_nonneg ?_ ?_
        · linarith
        apply ennreal_lp_add_le_lem' f hp ?_ i
        contrapose hf
        simp only [ne_eq, Decidable.not_not]
        refine (rpow_eq_top_iff_of_pos ?_).mpr ?_
        · simp
          linarith
        tauto
      apply ENNReal.tsum_coe_ne_top_iff_summable.1
      contrapose inf
      simp at ⊢ inf
      intro
      rw[← inf]
      congr
      ext i
      rw[← toNNReal_rpow]
      refine Eq.symm (coe_toNNReal ?_)
      refine rpow_ne_top_of_nonneg ?_ ?_
      · linarith
      apply ennreal_lp_add_le_lem' g hp ?_ i
      contrapose hg
      simp only [ne_eq, Decidable.not_not]
      refine (rpow_eq_top_iff_of_pos ?_).mpr ?_
      · simp
        linarith
      tauto
    _ = (∑' (a : ι), (f a ^ p).toNNReal) ^ (1 / p) + (∑' (a : ι), (g a ^ p).toNNReal) ^ (1 / p) := by
      congr <;> ext <;> simp only [coe_rpow, toNNReal_rpow]

def ell_two {α : Type*}: (α → ℝ) → ℝ≥0∞ :=
  fun f ↦ (∑' a : α, ‖f a‖ₑ ^ 2) ^ (2 : ℝ)⁻¹

lemma ell_two' {α : Type*} (f : α → ℝ):
    ell_two f = (∑' a : α, (‖f a‖ₑ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  unfold ell_two
  simp only [ENNReal.rpow_ofNat, one_div]

lemma ell_two_symm {α : Type*} (f : α → ℝ): ell_two (-f) = ell_two f := by
  unfold  ell_two
  simp only [Pi.neg_apply, enorm_neg]

lemma ell_two_triangle {α : Type*} (f g : α → ℝ):
    ell_two (f + g) ≤ ell_two f + ell_two g := by
  calc
    ell_two (f + g)
      = (∑' a : α, ‖f a + g a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      rw[ell_two']
      simp only [Pi.add_apply, ENNReal.rpow_ofNat, one_div]
    _ ≤ (∑' a : α, (‖f a‖ₑ + ‖g a‖ₑ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      gcongr
      apply ENormedAddMonoid.enorm_add_le
    _ ≤ (∑' a : α, (‖f a‖ₑ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) +
        (∑' a : α, (‖g a‖ₑ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      apply ennreal_lp_add_le'
      norm_num
    _ = ell_two f + ell_two g := by rw [ell_two', ell_two']

theorem multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one'' [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
  ell_two (fun k ↦ (multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k)
    ≤ ((8*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑n : NNReal))) := by
  suffices : ell_two (fun k ↦
    (multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k) =
    (∑' k : ι → ℤ,
    ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2) ^ (1 / (2 : ℝ))
  · rw[this]
    exact multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one' hα F n hq hF
  unfold ell_two
  congr
  simp only [one_div]

theorem multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one''' [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
  ell_two ((fun k ↦ (multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j))) - (fun k ↦ discrete_avg' n F k))
    ≤ ((8*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑n : NNReal))) := by
  apply le_trans (multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one'' hα F n hq hF)
  rfl

def k_set (k : ι → ℤ) := (Set.univ.pi fun (r : ι) => Set.Ico (↑(k r) : ℝ) ((↑(k r) : ℝ) + 1))

@[measurability] lemma k_set_measurable (k : ι → ℤ) : MeasurableSet (k_set k) := by
  unfold k_set
  refine MeasurableSet.univ_pi ?_
  simp only [measurableSet_Ico, implies_true]

lemma k_set_disjoint {k k' : ι → ℤ} (h : k ≠ k') : k_set k ∩ k_set k' = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro xh
  contrapose h
  simp_all only [Decidable.not_not, ne_eq]
  ext i
  unfold k_set at *
  simp_all only [mem_pi, mem_univ, mem_Ico, forall_const]
  specialize xh i
  specialize h i
  apply le_antisymm
  · have s: (↑(k i) : ℝ) < (↑(k' i) : ℝ) + 1 := by linarith
    have : (↑(k' i) : ℝ) + 1 = (↑((k' i) +1) : ℝ) := by simp only [Int.cast_add, Int.cast_one]
    rw[this] at s
    simp [-Int.cast_add, -Int.cast_one] at s
    exact (Int.add_le_add_iff_right 1).mp s
  have s: (↑(k' i) : ℝ) < (↑(k i) : ℝ) + 1 := by linarith
  have : (↑(k i) : ℝ) + 1 = (↑((k i) +1) : ℝ) := by simp only [Int.cast_add, Int.cast_one]
  rw[this] at s
  simp [-Int.cast_add, -Int.cast_one] at s
  exact (Int.add_le_add_iff_right 1).mp s

omit [Fintype ι]  in
lemma x_mem_k_set (x : ι → ℝ) : x ∈ k_set (fun i ↦ ⌊x i⌋) := by
  unfold k_set
  simp only [mem_pi, mem_univ, mem_Ico, Int.lt_floor_add_one, and_true, forall_const]
  intro i
  exact Int.floor_le (x i)

lemma x_mem_k_set' {x : ι → ℝ} {k : ι → ℤ} (h : x ∈ k_set k) : k = (fun i ↦ ⌊x i⌋) := by
  by_contra h0
  suffices : x ∈ k_set k ∩ (k_set (fun i ↦ ⌊x i⌋))
  · rw[k_set_disjoint h0] at this
    exact this
  constructor
  · exact h
  exact x_mem_k_set x

lemma lintegral_shift {f : (ι → ℝ) → ENNReal} {s : Set (ι → ℝ)} {p : ι → ℝ} (hf : Measurable f)
    (hs : MeasurableSet s):
    ∫⁻ x in ((fun t : (ι → ℝ) ↦ t + p))⁻¹' s, f (x + p) = ∫⁻  x in s, f x := by
  let g := fun x ↦ x + p
  have : ∫⁻ x in ((fun t : (ι → ℝ) ↦ t + p))⁻¹' s, f (x + p)
      = ∫⁻ x in g ⁻¹' s, f (g x) := by
    unfold g
    rfl
  rw[this]
  rw[MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage]
  · unfold g
    exact measurePreserving_add_right volume p
  · exact hs
  exact hf

theorem ell_two_l_two_norm {f : (ι → ℝ) → ℝ} (hf : Measurable f):
    (∫⁻ x in (Set.univ.pi fun (_ : ι) => Set.Ico (0 : ℝ) 1), (∑' k : ι → ℤ, ‖f ((fun i ↦ (↑(k i) : ℝ)) + x)‖ₑ^2)) =
    ∫⁻ x, ‖f x‖ₑ^2 := by
  calc
    ∫⁻ x in (Set.univ.pi fun (r : ι) => Set.Ico (0 : ℝ) 1), (∑' k : ι → ℤ, ‖f ((fun i ↦ (↑(k i) : ℝ)) + x)‖ₑ^2)
      = ∑' k : ι → ℤ, ∫⁻ x in (Set.univ.pi fun (r : ι) => Set.Ico (0 : ℝ) 1), (‖f ((fun i ↦ (↑(k i) : ℝ)) + x)‖ₑ^2) := by
        rw[MeasureTheory.lintegral_tsum]
        intro i
        fun_prop
    _ = ∑' k : ι → ℤ, ∫⁻ (a : ι → ℝ), (univ.pi fun r ↦ Ico 0 1).indicator (fun x ↦ ‖f ((fun i ↦ ↑(k i)) + x)‖ₑ ^ 2) a   := by
        congr
        ext k
        rw[← MeasureTheory.lintegral_indicator]
        refine MeasurableSet.univ_pi ?_
        simp only [measurableSet_Ico, implies_true]
    _ = ∑' k : (ι → ℤ), ∫⁻ a in (k_set k), ‖f a‖ₑ^2 := by
        congr
        ext k
        let k' : ι → ℝ := fun i ↦ (↑(k i) : ℝ)
        rw[← lintegral_shift (p := k')]
        · rw [lintegral_indicator]
          · congr
            · ext x
              unfold k_set
              simp only [mem_pi, mem_univ, mem_Ico, forall_const, mem_preimage, Pi.add_apply]
              constructor
              · intro h i
                specialize h i
                unfold k'
                simp only [le_add_iff_nonneg_left]
                constructor
                · exact h.1
                linarith
              intro h i
              unfold k' at h
              specialize h i
              simp_all only [le_add_iff_nonneg_left, true_and]
              linarith
            ext a
            rw[add_comm]
          refine MeasurableSet.univ_pi ?_
          simp only [measurableSet_Ico, implies_true]
        · fun_prop
        measurability
    _ = ∑' k : (ι → ℤ), ∫⁻ a, (k_set k).indicator (fun x ↦ ‖f x‖ₑ^2) a := by
        congr
        ext k
        rw[MeasureTheory.lintegral_indicator]
        measurability
    _ = ∫⁻ a, ∑' k : (ι → ℤ), (k_set k).indicator (fun x ↦ ‖f x‖ₑ^2) a := by
        rw[MeasureTheory.lintegral_tsum]
        intro k
        apply Measurable.aemeasurable
        refine Measurable.indicator ?_ ?_
        · fun_prop
        measurability
    _ = ∫⁻ a, ‖f a‖ₑ^2 := by
        congr
        ext x
        calc
          ∑' (k : ι → ℤ), (k_set k).indicator (fun x ↦ ‖f x‖ₑ ^ 2) x
            = (k_set (fun i ↦ ⌊x i⌋)).indicator (fun x ↦ ‖f x‖ₑ ^ 2) x := by
            refine tsum_eq_single (fun i ↦ ⌊x i⌋) ?_
            intro k kh
            suffices : x ∉ k_set k
            · simp only [this, not_false_eq_true, indicator_of_notMem]
            contrapose kh
            simp_all only [Decidable.not_not, ne_eq]
            exact x_mem_k_set' kh
          _ = ‖f x‖ₑ ^ 2 := by simp only [x_mem_k_set, indicator_of_mem]

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

lemma L_two_mono
    {f g : (ι → ℝ) → ℝ≥0∞} (h : ∀ a ∈ univ.pi fun (_ : ι) ↦ Ico 0 1, f a ≤ g a)
    (hg : Measurable g):
    L_two f ≤ L_two g := by
  unfold L_two
  apply ENNReal.rpow_le_rpow (h₂ := by norm_num)
  apply MeasureTheory.setLIntegral_mono
  · fun_prop
  intro a ah
  apply ENNReal.rpow_le_rpow (h₂ := by norm_num)
  exact h a ah

lemma L_two_edist_le
    {f g : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (h : (L_two f) ≤ (L_two g)) :
    edist (L_two f) (L_two g) ≤ L_two fun x ↦ (edist (f x) (g x)) := by
  rw [ennreal_edist_le' h]
  apply tsub_le_iff_left.mpr
  calc
    L_two g
      ≤ L_two (f + fun x ↦ edist (f x) (g x)) := by
      apply L_two_mono
      intro a ah
      · apply ennreal_add_edist_le
      unfold edist
      fun_prop
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

theorem L_two_ell_two_norm {f : (ι → ℝ) → ℝ} (hf : Measurable f):
    L_two (fun x ↦ ell_two (fun (k : ι → ℤ) ↦ f ((fun i ↦ (↑(k i) : ℝ)) + x))) =
    (∫⁻ x, ‖f x‖ₑ^(2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have : ∫⁻ x, ‖f x‖ₑ^(2 : ℝ) = ∫⁻ x, ‖f x‖ₑ^ 2 := by
    congr
    ext
    rw [ENNReal.rpow_two]
  rw[this]
  rw[← ell_two_l_two_norm hf]
  unfold L_two ell_two
  congr
  ext x
  dsimp
  rw[← ENNReal.rpow_mul]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀, ENNReal.rpow_one]


/-
def good (g : ℕ → ENNReal)(q : ι → ℝ): Prop :=
  ∃ C : NNReal, ∀(m : ℕ)(idx : Fin (m+1) → NNReal)(mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(F : ι → (ι → ℝ) → ℝ) --WRONG, ι is used twice which seem bad
  (hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i)), ∑ i : Fin m, (∫⁻ (a : ι → ℝ), (multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)^2)^(1/2) ≤ C * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))
-/
/-Note: This is slightly weaker than the theorem in the paper, for the theorem in the paper one would replace "ℕ" with "ℤ".
The proof stays the same, only thing that needs to be changed would be to change iterate.
However Corollary 4 is never used (in the entire paper) except for this proof, for which the ℕ version suffices...-/
#check Summable
/-ℤ version:-/ --First prove the ℕ thing from this, to make sure!

def u_diff (m : ℕ) (F : ι → (ι → ℤ) → ℝ) (idx : Fin (m+1) → ℕ) (i : Fin m) :=
  multilinear_avg_spec (approx_sum_mul F) (idx i.succ) - multilinear_avg_spec (approx_sum_mul F) (idx ⟨i, get_rid i⟩)

#check approx_sum_measurable
@[fun_prop]
theorem u_diff_meausurable
    (m : ℕ) (F : ι → (ι → ℤ) → ℝ) (idx : Fin (m+1) → ℕ) (i : Fin m) :
    Measurable (u_diff m F idx i) := by
  unfold u_diff
  fun_prop

lemma gz {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (m : ℕ):
    0 ≤ ((256 * (Fintype.card ι)^3 * π ^2) / 3 + 2 * ↑(good_const hg)) * ↑(g m) := by
  apply mul_nonneg
  · apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg, pow_nonneg]
        apply sq_nonneg
      simp only [Nat.ofNat_nonneg]
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, zero_le_coe]
  simp only [zero_le_coe]


--(good_const h) * g m
/-
theorem fact5_2{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q)(m : ℕ)(idx : Fin (m+1) → NNReal)
  (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(F : ι → (ι → ℝ) → ℝ)(hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal):
    ∑ i : Fin m, (∫⁻ (a : ι → ℝ), ‖(multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)‖ₑ^2) ≤
    (good_const h) * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)) := (Exists.choose_spec h.2) m idx mon F hF
-/

-- (256 * (Fintype.card ι)^3 * π ^2) / 3

--theorem lintegral_approx_sum(i : ι)(F : (ι → ℤ) → ℝ){s : ℝ}(hs: 0 ≤ s): ∫⁻ x : ι → ℝ, ‖approx_sum i F x‖ₑ^s = ∑' k : ι → ℤ, ‖F k‖ₑ^s := by
/-Norms = 1-/
--ENNReal.tsum_coe_ne_top_iff_summable
#check ENNReal.tsum_coe_ne_top_iff_summable
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



lemma setup_discrete_ver'_norm_one {q : ι → ℝ} (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
    (F : ι → (ι → ℤ) → ℝ) (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1) (i : ι):
    (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i) = 1 := by
  specialize hF' i
  refine (toReal_eq_one_iff (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i)).mp ?_
  rw[← hF']
  have : ∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i = ∑' (k : ι → ℤ), ‖|F i k| ^ (q i)‖ₑ := by
    congr
    ext k
    rw[enorm_rpow_of_nonneg]
    · simp only [enorm_abs]
    · apply abs_nonneg
    exact le_of_lt (hq.1 i)
  rw[this, ell_p_coe]
  intro k
  apply rpow_nonneg
  apply abs_nonneg

lemma setup_discrete_ver'_norm_two {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):
    ∑ i : Fin m, (∫⁻ (a : ι → ℝ),
    ‖u_diff m F idx i a‖ₑ^2)
    ≤ (good_const hg) * g m * (∏ (i : ι),
    (∫⁻ (a : ι → ℝ), ‖approx_sum i (F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))) := by
  unfold u_diff
  apply fact5_2 (F := fun i ↦ approx_sum i (F i)) (h := hg) (m := m) (idx := fun i ↦ (↑(idx i) : NNReal)) -- (mon := mon) (m := m) (idx := idx) (hidx := hidx)
  · intro a b ab
    simp only [Nat.cast_le]
    exact mon ab
  · intro a b ab
    simp only [Nat.cast_inj] at ab
    exact hidx ab
  · simp only [Nat.cast_pos, hidx']
  intro i
  apply approx_sum_memlp
  · simp only [ne_eq, ENNReal.coe_eq_zero, toNNReal_eq_zero, not_le]
    exact hq.1 i
  · simp only [ne_eq, coe_ne_top, not_false_eq_true]
  exact hF i

lemma setup_discrete_ver'_norm_three {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1):
    ∑ i : Fin m, ∫⁻ (a : ι → ℝ), ‖u_diff m F idx i a‖ₑ^2 < ⊤ := by
  calc
    ∑ i : Fin m, ∫⁻ (a : ι → ℝ), ‖u_diff m F idx i a‖ₑ^2
      ≤ (good_const hg) * g m * (∏ (i : ι),
        (∫⁻ (a : ι → ℝ), ‖approx_sum i (F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))) := by
      apply setup_discrete_ver'_norm_two (hq := hq) (mon := mon) (hidx := hidx) (hidx' := hidx') (hF := hF)
    _ = (good_const hg) * g m  *
        (∏ (i : ι), (∑' k : ι → ℤ, ‖(F i) k‖ₑ^(q i)) ^ (1 / q i)).toNNReal:= by
      /-
      rw[lintegral_approx_sum]
      · rw[setup_discrete_ver'_norm_one hq F hF']
        simp only [one_div, ENNReal.one_rpow]
      exact le_of_lt (hq i)
      -/
      congr
      set u := (∏ i, (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i) ^ (1 / q i))
      have : (↑(u.toNNReal) : ℝ≥0∞) = u := by
        refine ENNReal.coe_toNNReal ?_
        unfold u
        suffices : ∏ i, (∑' k : ι → ℤ, ‖(F i) k‖ₑ^(q i)) ^ (1 / q i) = ∏ i : ι, 1 ^ (1 / q i)
        · rw[this]
          simp only [one_div, ENNReal.one_rpow, Finset.prod_const_one, ne_eq, one_ne_top,
            not_false_eq_true]
        congr
        ext i
        rw[setup_discrete_ver'_norm_one hq]
        exact hF'
      rw[this]
      unfold u
      congr
      ext i
      rw[lintegral_approx_sum]
      exact le_of_lt (hq.1 i)
    _ = (good_const hg) * g m  *
        (∏ (i : ι), 1 ^ (1 / q i)) := by
      congr
      have : ∏ i, (∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i) ^ ((1 : ℝ) / q i) = ∏ i : ι, 1 ^ ((1 : ℝ) / q i) := by
        congr
        ext i
        rw[setup_discrete_ver'_norm_one hq]
        exact hF'
      rw[this]
      simp only [one_div, ENNReal.one_rpow, Finset.prod_const_one, ENNReal.toNNReal_one,
        ENNReal.coe_one]
    _ = (good_const hg) * g m := by
      simp only [one_div, ENNReal.one_rpow, Finset.prod_const_one, mul_one]
    _ < ⊤ := compareOfLessAndEq_eq_lt.mp rfl

lemma setup_discrete_ver'_norm_four {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1):
    ∀ i : Fin m, ∫⁻ (a : ι → ℝ), ‖u_diff m F idx i a‖ₑ^2 < ⊤ := by
  intro i
  calc
    ∫⁻ (a : ι → ℝ), ‖u_diff m F idx i a‖ₑ ^ 2
      ≤ ∑ j : Fin m, ∫⁻ (a : ι → ℝ), ‖u_diff m F idx j a‖ₑ^2 := by
      rw[← tsum_fintype]
      apply ENNReal.le_tsum (f := fun i ↦ ∫⁻ (a : ι → ℝ), ‖u_diff m F idx i a‖ₑ ^ 2)
    _ < ⊤ := setup_discrete_ver'_norm_three hg hq m idx mon hidx hidx' F hF hF'


/-
theorem multilinear_avg_approx_sum_discrete_avg_ell_two [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2):
  ∑' k : ι → ℤ, ‖(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k‖ₑ^2
    ≤ ((64*(Fintype.card ι)^2)/(↑n^2 : NNReal))* ∑ j_1, ∑' k : ι → ℤ, ‖F j_1 k‖ₑ^(q j_1) := by
-/

/-
theorem multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one'' [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
  (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
  ell_two (fun k ↦ (multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)) - discrete_avg' n F k)
    ≤ ((8*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑n : NNReal))) := by
-/

--multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one'''

theorem multilinear_avg_approx_edist [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
    (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ) (m : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (i : Fin m)
    (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
    edist (ell_two ((fun (k : ι → ℤ) ↦
    (multilinear_avg_spec (approx_sum_mul F) ↑(idx i.succ) (fun j ↦ k j + α j))) -
    (fun (k : ι → ℤ) ↦ (multilinear_avg_spec (approx_sum_mul F) ↑(idx ⟨i, get_rid i⟩) (fun j ↦ k j + α j)))))
    (ell_two ((fun (k : ι → ℤ) ↦ discrete_avg' (idx i.succ) F k) - (fun (k : ι → ℤ) ↦ discrete_avg' (idx ⟨i, get_rid i⟩) F k)))
    ≤ ((16*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑(idx ⟨i, get_rid i⟩) : NNReal))) := by
  set K := 8 * (↑(Fintype.card ι) : ℝ≥0∞) ^ (3 / (2 : ℝ))
  set a := (fun (k : ι → ℤ) ↦
    (multilinear_avg_spec (approx_sum_mul F) ↑(idx i.succ) (fun j ↦ k j + α j)))
  set b := (fun (k : ι → ℤ) ↦ (multilinear_avg_spec (approx_sum_mul F) ↑(idx ⟨i, get_rid i⟩) (fun j ↦ k j + α j)))
  set c := (fun (k : ι → ℤ) ↦ discrete_avg' (idx i.succ) F k)
  set d := (fun (k : ι → ℤ) ↦ discrete_avg' (idx ⟨i, get_rid i⟩) F k)
  let n := (↑(idx ⟨i, get_rid i⟩) : NNReal)
  calc
    edist (ell_two (a - b)) (ell_two (c - d))
      ≤ ell_two (a - c) + ell_two (b - d) := by
      apply ennreal_norm_edist_swap
      · exact fun x y ↦ ell_two_triangle x y
      exact fun x ↦ ell_two_symm x
    _ ≤ K / ↑↑(idx i.succ) + K / ↑n := by
      gcongr
      · exact multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one''' hα F (idx i.succ) hq hF
      exact multilinear_avg_approx_sum_discrete_avg_ell_two_norms_one''' hα F (idx ⟨i, get_rid i⟩) hq hF
    _ ≤ K / ↑n + K / ↑n := by
      gcongr
      unfold n
      simp only [coe_natCast, Nat.cast_le]
      apply mon
      obtain ⟨i, _⟩ := i
      simp only [Fin.succ_mk, Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
    _ = ((16*(Fintype.card ι) ^ (3 / (2 : ℝ))/ ↑n)) := by
      rw [@ENNReal.div_add_div_same]
      congr
      unfold K
      ring

theorem multilinear_avg_approx_edist_udiff' [Nonempty ι] {α : ι → ℝ} {q : ι → ℝ}
    (hα: ∀ (i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ) (m : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (i : Fin m)
    (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
    edist (ell_two (fun (k : ι → ℤ) ↦ ((u_diff m F idx i) (fun j ↦ (↑(k j) : ℝ) + α j))))
    (ell_two ((fun (k : ι → ℤ) ↦ discrete_avg' (idx i.succ) F k) - (fun (k : ι → ℤ) ↦ discrete_avg' (idx ⟨i, get_rid i⟩) F k)))
    ≤ ((16*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑(idx ⟨i, get_rid i⟩) : NNReal))) := by
  exact multilinear_avg_approx_edist hα F m hq idx mon i hF

--MeasureTheory.eLpNorm
--nope

variable [Nonempty ι]

/-
lemma L_two_edist {f g : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g):
    edist (L_two f) (L_two g) ≤ L_two fun x ↦ (edist (f x) (g x)) := by
-/

omit [Nonempty ι] in
lemma volume_unit_cube : volume (univ.pi fun (_ : ι) ↦ (Ico 0 1 : Set ℝ)) = 1 := by
  rw [@volume_pi_pi]
  simp only [volume_Ico, sub_zero, ofReal_one, Finset.prod_const_one]

theorem multilinear_avg_approx_edist_udiff {q : ι → ℝ}
    (F : ι → (ι → ℤ) → ℝ) (m : ℕ) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (i : Fin m)
    (hF : ∀ i : ι, ∑' k : ι → ℤ, ‖F i k‖ₑ^(q i) = 1):
    edist ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^((1 : ℝ) / (2 : ℝ)))
    (ell_two ((fun (k : ι → ℤ) ↦ discrete_avg' (idx i.succ) F k) -
    (fun (k : ι → ℤ) ↦ discrete_avg' (idx ⟨i, get_rid i⟩) F k)))
    ≤ (16*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑(idx ⟨i, get_rid i⟩) : NNReal)) := by
  set h := (fun (k : ι → ℤ) ↦ discrete_avg' (idx i.succ) F k) -
    (fun (k : ι → ℤ) ↦ discrete_avg' (idx ⟨i, get_rid i⟩) F k)
  set K := 16*(↑(Fintype.card ι) : ℝ≥0∞) ^ (3 / (2 : ℝ))/(↑(idx ⟨i, get_rid i⟩) : NNReal)
  calc
    edist ((∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x ^ (2 : ℝ)‖ₑ) ^ (1 / (2 : ℝ))) (ell_two h)
      = edist ((∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) (ell_two h) := by
      congr
      ext x
      nth_rw 2[← enorm_abs]
      rw[← enorm_rpow_of_nonneg] <;> simp
    _ = edist (L_two fun x ↦ ell_two fun (k : ι → ℤ) ↦ u_diff m F idx i ((fun i ↦ (↑(k i) : ℝ)) + x)) (L_two (fun (x : ι → ℝ) ↦ (ell_two h))) := by
      rw[← L_two_ell_two_norm]
      swap
      · fun_prop
      congr 1
      unfold L_two
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
        univ_inter, one_div]
      rw[volume_unit_cube, mul_one, ← ENNReal.rpow_mul]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, ENNReal.rpow_one]
    _ ≤ L_two fun x ↦ edist (ell_two fun (k : ι → ℤ) ↦ u_diff m F idx i ((fun i ↦ (↑(k i) : ℝ)) + x)) (ell_two h) := by
      --apply L_two_edist
      --fun_prop
      apply L_two_edist
      · unfold ell_two
        apply Measurable.pow
        swap
        · fun_prop
        apply Measurable.ennreal_tsum
        intro
        fun_prop
      fun_prop
    _ ≤ L_two fun (x : ι → ℝ) ↦ K := by
      apply L_two_mono
      intro x xh
      dsimp
      apply multilinear_avg_approx_edist_udiff' (hq := hq)
      · simp_all only [one_div, mem_pi, mem_univ, mem_Ico, forall_const, and_self]
      · exact mon
      · exact hF
      fun_prop
    _ = K := by
      unfold L_two
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
        univ_inter, one_div]
      rw[volume_unit_cube, mul_one, ← ENNReal.rpow_mul]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, ENNReal.rpow_one]


lemma real_hassum_tsum {α : Type*} {f : α → ℝ} {t : ℝ} (ht : t ≠ 0) (h : ∑' a : α, f a = t) :
    HasSum f t := by
  refine (Summable.hasSum_iff ?_).mpr h
  contrapose ht
  rw[← h]
  simp only [ne_eq, Decidable.not_not]
  exact tsum_eq_zero_of_not_summable ht

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

theorem discrete_ver'_norm_one_individual_preadd {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1) (i : Fin m):
    |((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toNNReal -
    (∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2)^(2⁻¹ : ℝ)|
    ≤ 16*(Fintype.card ι) ^ (3 / (2 : ℝ)) / ↑(idx ⟨i, get_rid i⟩) := by
  refine (ofReal_le_ofReal_iff ?_).mp ?_
  · apply div_nonneg <;> simp
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  have : ENNReal.ofReal (16*(Fintype.card ι) ^ (3 / (2 : ℝ)) / ↑(idx ⟨i, get_rid i⟩)) --wrong
      = (16*(Fintype.card ι) ^ (3 / (2 : ℝ))/(↑(idx ⟨i, get_rid i⟩) : NNReal)) := by
    rw[ENNReal.ofReal_div_of_pos]
    swap
    · simp only [Nat.cast_pos]
      calc
        0 < idx 0 := hidx'
        _ ≤ idx ⟨i, get_rid i⟩ := by
          apply mon
          simp only [Fin.zero_le]
    congr
    · rw[ENNReal.ofReal_mul]
      · simp only [ofReal_ofNat]
        rw[← ENNReal.ofReal_rpow_of_nonneg] <;> try simp
        norm_num
      norm_num
    simp only [ofReal_natCast, coe_natCast]

  rw[this]
  have s1 := multilinear_avg_approx_edist_udiff F m hq idx mon i
  --setup_discrete_ver'_norm_one
  have s2 : ∀ (i : ι), ∑' (k : ι → ℤ), ‖F i k‖ₑ ^ q i = 1 := by
    intro
    apply setup_discrete_ver'_norm_one hq F hF'
  specialize s1 s2
  apply le_trans' s1
  rw[edist_real]
  · simp only [Real.rpow_ofNat, enorm_pow, one_div]
    set p := (∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x‖ₑ ^ 2) ^ (2 : ℝ)⁻¹
    rw [Real.enorm_eq_ofReal_abs]
    apply le_of_eq
    congr
    unfold ell_two
    rw[← ENNReal.toReal_rpow]
    congr
    rw[ENNReal.tsum_toReal_eq]
    swap
    · intro
      simp only [Pi.sub_apply, ne_eq, pow_eq_top_iff, enorm_ne_top, OfNat.ofNat_ne_zero,
        not_false_eq_true, and_true]
    congr
    ext a
    rw[← sq_abs, ENNReal.toReal_pow]
    congr
  · refine rpow_ne_top_of_nonneg ?_ ?_
    · norm_num
    refine lt_top_iff_ne_top.mp ?_
    calc
      ∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x ^ (2 : ℝ)‖ₑ
        = ∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x‖ₑ ^ 2 := by
        congr
        ext
        simp only [Real.rpow_ofNat, enorm_pow]
      _ < ⊤ := by
        apply setup_discrete_ver'_norm_four hg hq m idx mon hidx hidx' F
        · intro j
          unfold Memℓp
          simp only [ENNReal.coe_eq_zero, toNNReal_eq_zero, ne_eq, coe_ne_top, ↓reduceIte,
            norm_eq_abs, coe_toReal, coe_toNNReal']
          have : ¬ q j ≤ 0 := by simp [hq.1 j]
          simp only [this, ↓reduceIte, le_of_lt (hq.1 j), sup_of_le_left]
          apply HasSum.summable (a := 1)
          apply real_hassum_tsum
          · norm_num
          exact hF' j
        intro j
        apply enorm_norm_sum_one
        · intro
          apply rpow_nonneg
          apply abs_nonneg
        rw[← s2 j]
        congr
        ext a
        rw[Real.enorm_rpow_of_nonneg]
        · simp only [enorm_abs]
        · apply abs_nonneg
        exact le_of_lt (hq.1 j)
  refine lt_top_iff_ne_top.mp ?_
  set p := ell_two ((fun k ↦ discrete_avg' (idx i.succ) F k) - fun k ↦ discrete_avg' (idx ⟨↑i, get_rid i⟩) F k)
  set q := (∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x ^ (2 : ℝ)‖ₑ) ^ (1 / (2 : ℝ))
  by_contra h0
  simp at h0
  have : edist q ⊤ < ∞ := by
    nth_rw 1[← h0]
    apply lt_of_le_of_lt (c := ⊤) (b := ((16 * (Fintype.card ι) ^ (3 / (2 : ℝ))/(↑(↑(idx ⟨↑i, get_rid i⟩) : NNReal) : ℝ≥0∞))))
    · exact s1
    apply ENNReal.div_lt_top
    · apply ENNReal.mul_ne_top <;> simp
    simp only [coe_natCast, ne_eq, Nat.cast_eq_zero]
    refine Nat.pos_iff_ne_zero.mp ?_
    calc
      0 < idx 0 := hidx'
      _ ≤ idx ⟨i, get_rid i⟩ := by
        apply mon
        simp only [Fin.zero_le]
  apply edist_top_lt_top at this
  contrapose this
  unfold q
  simp only [Real.rpow_ofNat, enorm_pow, one_div, rpow_eq_top_iff, inv_neg'', inv_pos,
    Nat.ofNat_pos, and_true, not_or, not_and, not_lt, Nat.ofNat_nonneg, implies_true, true_and]
  refine lt_top_iff_ne_top.mp ?_
  apply setup_discrete_ver'_norm_four hg hq m idx mon hidx hidx' F hF hF'


  /-
  apply lt_of_le_of_lt (c := ⊤) (b := ((16 * (Fintype.card ι) ^ (3 / (2 : ℝ))/(↑(↑(idx ⟨↑i, get_rid i⟩) : NNReal) : ℝ≥0∞))))
  · sorry
  apply ENNReal.div_lt_top
  · apply ENNReal.mul_ne_top <;> simp
  simp
  refine Nat.pos_iff_ne_zero.mp ?_
  calc
    0 < idx 0 := hidx'
    _ ≤ idx ⟨i, get_rid i⟩ := by
      apply mon
      simp only [Fin.zero_le]-/

theorem discrete_ver'_norm_one_individual_add {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1) (i : Fin m):
    (∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2)^(2⁻¹ : ℝ)
    ≤ 16*(Fintype.card ι) ^ (3 / (2 : ℝ)) / ↑(idx ⟨i, get_rid i⟩) + ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toNNReal := by
  have := discrete_ver'_norm_one_individual_preadd hg hq m idx mon hidx hidx' F hF hF' i
  set a := (∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2)^(2⁻¹ : ℝ)
  set b := 16*(Fintype.card ι) ^ (3 / (2 : ℝ)) / (↑(idx ⟨i, get_rid i⟩) : ℝ)
  set c := ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toNNReal
  refine (OrderedSub.tsub_le_iff_right a (↑c) b).mp ?_
  apply le_trans' this
  refine le_abs.mpr ?_
  right
  simp only [neg_sub, le_refl]
  /-apply le_trans' this
  rw[abs_sub_comm (↑c) a]
  exact le_abs_self (a - ↑c)-/

theorem discrete_ver'_norm_one_individual_add_sq {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1) (i : Fin m):
    (∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2)
    ≤ (16*(Fintype.card ι) ^ (3 / (2 : ℝ)) / ↑(idx ⟨i, get_rid i⟩) + ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toNNReal)^2 := by
  set b := (16*(Fintype.card ι) ^ (3 / (2 : ℝ)) / (↑(idx ⟨i, get_rid i⟩) : ℝ) + ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toNNReal)
  set a := (∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2)
  calc
    a = (a ^ (2⁻¹ : ℝ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀, Real.rpow_one]
      apply tsum_nonneg
      intro
      apply sq_nonneg
    _ ≤ b ^2  := by
      refine pow_le_pow_left₀ ?_ ?_ 2
      · apply rpow_nonneg
        apply tsum_nonneg
        intro
        apply sq_nonneg
      exact discrete_ver'_norm_one_individual_add hg hq m idx mon hidx hidx' F hF hF' i

theorem discrete_ver'_norm_one_part_one {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1):
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2
    ≤ 2 * ∑ i : Fin m, (4 * (8*(↑(Fintype.card ι) : ℝ) ^ (3 / (2 : ℝ))) ^ 2 / (↑(idx ⟨i, get_rid i⟩) : ℝ≥0)^2 + ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ).toReal)) := by
  by_cases hm : m = 0
  · have : IsEmpty (Fin m) := by
      rw[hm]
      exact Fin.isEmpty'
    simp only [Finset.univ_eq_empty, Finset.sum_empty, NNReal.coe_natCast, Real.rpow_ofNat,
      enorm_pow, mul_zero, le_refl]
  set K := 8*(↑(Fintype.card ι) : ℝ) ^ (3 / (2 : ℝ)) --falsch, we did 2 * (64*(Fintype.card ι)^3) -> 16*(Fintype.card ι) ^ (3 / (2 : ℝ)), also war K = (64*(Fintype.card ι)^3)
  calc
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2
    _ ≤ ∑ i : Fin m, (↑((2 * K / ↑(idx ⟨i, get_rid i⟩) + ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toNNReal)^(2 : ℝ)) : ℝ) := by
      gcongr with i
      have := discrete_ver'_norm_one_individual_add_sq hg hq m idx mon hidx hidx' F hF hF' i
      apply le_trans this
      apply le_of_eq
      unfold K
      simp only [Real.rpow_ofNat, enorm_pow, toNNReal_rpow, coe_rpow]
      congr 3
      ring
    _ ≤ ∑ i : Fin m, 2 * ((2 * K / ↑(idx ⟨i, get_rid i⟩))^2 + (((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹).toReal)^(2 : ℝ)) := by
      gcongr
      rename_i i _
      set a := (2 * K / (↑(idx ⟨i, get_rid i⟩) : ℝ))
      set b := (∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ)^(2 : ℝ)⁻¹
      have s2: (↑b.toNNReal : ℝ) = b.toReal := by exact rfl
      rw[s2]
      simp
      apply add_sq_le
  apply le_of_eq
  rw[Finset.mul_sum]
  congr 1
  ext i
  rw[mul_add, mul_add]
  congr
  · simp
    rw[div_pow, mul_pow]
    congr
    norm_num
  rw[ENNReal.toReal_rpow, ← ENNReal.rpow_mul]
  simp only [Real.rpow_ofNat, enorm_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    inv_mul_cancel₀, ENNReal.rpow_one]

lemma trick_lemma {a b c : ℝ} (hb : a ≤ b) (bc : b = c) : a ≤ c := by
  rw[← bc]
  exact hb

theorem discrete_ver'_norm_one_part_two {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1):
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2
    ≤ (8 * (8*(↑(Fintype.card ι) : ℝ) ^ (3 / (2 : ℝ))) ^ 2 * (π^2 / 6)) + 2 * (∑ i : Fin m, ∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)‖ₑ^(2 : ℝ)).toNNReal := by
  by_cases hm : m = 0
  · have : IsEmpty (Fin m) := by
      rw[hm]
      exact Fin.isEmpty'
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ENNReal.rpow_ofNat, ENNReal.toNNReal_zero,
      NNReal.coe_zero, mul_zero, add_zero, ge_iff_le]
    apply mul_nonneg
    · apply mul_nonneg
      · norm_num
      apply sq_nonneg
    apply div_nonneg
    · apply sq_nonneg
    norm_num
  set K := 8*(↑(Fintype.card ι) : ℝ) ^ (3 / (2 : ℝ))
  calc
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2
      ≤ 2 * ∑ i : Fin m, (4 * K ^ 2 / (↑(idx ⟨i, get_rid i⟩) : ℝ≥0)^2 + ((∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ).toReal)) := by
      exact discrete_ver'_norm_one_part_one hg hq m idx mon hidx hidx' F hF hF'
    _ = 8 * K ^ 2 * ∑ i : Fin m, (1 / (↑(idx ⟨i, get_rid i⟩))^2) + 2 * ∑ i : Fin m, (∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ).toReal := by
      rw[Finset.sum_add_distrib]
      simp only [NNReal.coe_natCast, Real.rpow_ofNat, enorm_pow, one_div]
      rw[mul_add]
      congr 1
      rw[Finset.mul_sum, Finset.mul_sum]
      congr
      ext i
      by_cases h : (↑(idx ⟨i, get_rid i⟩) : ℝ) ^ 2 = 0
      · rw[h]
        simp only [_root_.div_zero, mul_zero, _root_.inv_zero]
      field_simp
      ring
    _ ≤ 8 * K ^ 2 * ∑' n : ℕ, (1 / (↑n : ℝ)^2) + 2 * ∑ i : Fin m, (∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ).toReal := by
      gcongr
      let h := fun (i : Fin m) ↦ idx ⟨↑i, get_rid i⟩
      let f := fun (n : ℕ) ↦ 1 / (↑n : ℝ)^ 2
      calc
        ∑ i : Fin m, 1 / ↑(idx ⟨i, get_rid i⟩) ^ 2
          = ∑ i, f (h i) := rfl
        _ = ∑' i, f (h i) := by
          exact Eq.symm (tsum_fintype fun b ↦ f ↑(h b))
        _ ≤ ∑' i : ℕ, f i := by
          apply real_tsum_comp_le_tsum_of_inj_of_nonneg
          · unfold f
            intro n
            simp only [Pi.zero_apply, one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg]
          · unfold f
            apply HasSum.summable (a := (Real.pi^2 / 6))
            exact hasSum_zeta_two
          unfold h
          intro x y xy
          simp only at xy
          apply hidx at xy
          simp only [Fin.mk.injEq] at xy
          exact Fin.eq_of_val_eq xy
        _ = ∑' (n : ℕ), 1 / ↑n ^ 2 := rfl
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * ∑ i : Fin m, (∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)^(2 : ℝ)‖ₑ).toReal := by
      rw [HasSum.tsum_eq hasSum_zeta_two]
  simp only [Real.rpow_ofNat, enorm_pow, ENNReal.rpow_ofNat, add_le_add_iff_left, Nat.ofNat_pos,
    _root_.mul_le_mul_left]
  rw[ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_sum]
  intro a _
  refine lt_top_iff_ne_top.mp ?_
  apply setup_discrete_ver'_norm_four hg hq m idx mon hidx hidx' F hF hF'

--∑ i, ∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x‖ₑ ^ 2
--set_option maxHeartbeats 300000 in --i wanna cry
theorem discrete_ver'_norm_one {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) (m : ℕ)
    (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal)
    (hF': ∀ (j : ι), ∑' a : ι → ℤ, |(F j a)|^(q j) = 1):  --(hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal) unnötig i think, da 0 *  ⊤ = 0 NVM
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2  ≤ --NOTE: ∑' does coercion to ℝ, at some point (Fact 5.4 or smth) note that this is summable
    (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m := by
  by_cases hm : m = 0
  · have : IsEmpty (Fin m) := by
      rw[hm]
      exact Fin.isEmpty'
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ge_iff_le]
    exact gz hg m
  set K := 8*(↑(Fintype.card ι) : ℝ) ^ (3 / (2 : ℝ)) --falsch
  calc
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2
      ≤ (8 * K ^ 2 * (π^2 / 6)) + 2 * (∑ i : Fin m, ∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)‖ₑ^(2 : ℝ)).toNNReal := by
      apply trick_lemma (discrete_ver'_norm_one_part_two hg hq m idx mon hidx hidx' F hF hF')
      unfold K
      simp only [ENNReal.rpow_ofNat]
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * (∑ i : Fin m, ∫⁻ x : ι → ℝ, ‖(u_diff m F idx i x)‖ₑ^(2 : ℕ)).toNNReal := by
      congr
      ext i
      congr
      ext x
      rw [ENNReal.rpow_two]
    _ ≤ (8 * K ^ 2 * (π^2 / 6)) + 2 * ((good_const hg) * g m  *
        (∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖approx_sum i (F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))).toNNReal) := by
      gcongr
      calc
        (↑((∑ i, ∫⁻ (x : ι → ℝ), ‖u_diff m F idx i x‖ₑ ^ (2 : ℕ)).toNNReal) : ℝ)
          ≤ (↑(↑(good_const hg) * ↑(g m) *
            (∏ i, (∫⁻ (a : ι → ℝ), ‖approx_sum i (F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)))).toNNReal) := by
          gcongr
          · apply lt_top_iff_ne_top.1
            refine mul_lt_top ?_ ?_
            · refine mul_lt_top ?_ ?_ <;> simp
            --apply setup_discrete_ver'_norm_three hg hq m m idx mon hidx hidx' F hF
            suffices : ∏ i, (∫⁻ (a : ι → ℝ), ‖approx_sum i (F i) a‖ₑ ^ q i) ^ (1 / q i) = ∏ i : ι, 1 ^ (1 / q i)
            · rw[this]
              simp only [one_div, ENNReal.one_rpow, Finset.prod_const_one, one_lt_top]
            congr
            ext i
            congr
            rw[lintegral_approx_sum]
            · exact setup_discrete_ver'_norm_one hq F hF' i
            exact le_of_lt (hq.1 i)
          exact setup_discrete_ver'_norm_two hg hq m idx mon hidx hidx' F hF
        _ = ↑(good_const hg) * ↑(g m) * ↑(∏ i, (∫⁻ (a : ι → ℝ),
            ‖approx_sum i (F i) a‖ₑ ^ q i) ^ (1 / q i)).toNNReal := by
          simp only [one_div, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe, toNNReal_prod,
            toNNReal_rpow, NNReal.coe_mul, coe_prod, coe_rpow]
      --setup_discrete_ver'_norm_two
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * (good_const hg) * g m  *
        (∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖approx_sum i (F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))).toNNReal:= by
      ring
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * (good_const hg) * g m  *
        (∏ (i : ι), ∑' k : ι → ℤ, ‖(F i) k‖ₑ^(q i)).toNNReal:= by
      congr
      ext i
      rw[lintegral_approx_sum i (F i)]
      · rw[setup_discrete_ver'_norm_one hq F hF']
        simp only [one_div, ENNReal.one_rpow]
      exact le_of_lt (hq.1 i)
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * (good_const hg) * g m  *
        (∏ (i : ι), ∑' k : ι → ℤ, |(F i) k|^(q i)) := by
      congr
      rw [@toNNReal_prod, @coe_prod]
      congr
      ext i
      rw[← ell_p_coe]
      swap
      · intro k
        apply rpow_nonneg
        apply abs_nonneg
      rw[ENNReal.coe_toNNReal_eq_toReal]
      congr
      ext k
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      have : |(|F i k| ^ (q i))| = |F i k| ^ (q i) := by
        simp only [abs_eq_self]
        apply rpow_nonneg
        apply abs_nonneg
      rw[this]
      refine ofReal_rpow_of_nonneg ?_ ?_
      · apply abs_nonneg
      exact le_of_lt (hq.1 i)
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * (good_const hg) * g m  *
        (∏ (i : ι), 1) := by
      congr
      ext i
      rw[← hF' i]
    _ = (8 * K ^ 2 * (π^2 / 6)) + 2 * (good_const hg) * g m := by
      simp only [Finset.prod_const_one, mul_one]
    _ ≤ (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m := by
      rw[add_mul]
      refine add_le_add ?_ ?_
      swap
      · simp only [le_refl]
      rw[← mul_one (8 * K ^ 2 * (π ^ 2 / 6))]
      unfold K
      gcongr
      swap
      · simp only [one_le_coe]
        apply hg.1
        exact Nat.one_le_iff_ne_zero.mpr hm
      rw[← Real.rpow_natCast, Real.mul_rpow, ← Real.rpow_mul]
      simp
      field_simp
      rw[div_eq_of_eq_mul (a := 8 * (8 ^ 2 * ↑(Fintype.card ι) ^ 3) * π ^ 2)]
      all_goals try simp
      · norm_num
        rw[mul_comm (256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3)]
        rw[mul_div_assoc, ← mul_assoc (a := 6), ← mul_div_assoc]
        field_simp
        ring
      apply rpow_nonneg
      simp only [Nat.cast_nonneg]


lemma tsum_eq_zero {α : Type*} {f : α → ℝ} (hf : f = 0) : ∑' a, f a = 0 := by
  calc
    ∑' a, f a
      = ∑' a, 0 := by congr
    _ = 0 := by simp only [tsum_zero]


omit [Nonempty ι] in
lemma discrete'_avg_mul (n : ℕ) (F : ι → (ι → ℤ) → ℝ) (c : ι  → ℝ) (a : ι → ℤ) :
    discrete_avg' n (fun i k ↦ ((c i) * F i k)) a = (∏ i, c i) * discrete_avg' n F a := by
  unfold discrete_avg'
  rw[← mul_assoc, mul_comm (∏ i, c i), mul_assoc]
  congr
  rw[Finset.mul_sum]
  congr
  ext j
  rw [@Finset.prod_mul_distrib]

omit [Nonempty ι] in
theorem mul_corollary (m : ℕ) (idx : Fin (m+1) → ℕ) (F : ι → (ι → ℤ) → ℝ) (c : ι  → ℝ):
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) (fun i k ↦ ((c i) * F i k)) a -
    discrete_avg' (idx ⟨i, get_rid i⟩) (fun i k ↦ ((c i) * F i k)) a)^2 =
    (∏ i, (c i)^2) * ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a -
    discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2 := by
  rw[Finset.mul_sum]
  congr
  ext i
  rw[← _root_.tsum_mul_left]
  congr
  ext k
  rw [discrete'_avg_mul, discrete'_avg_mul, ← mul_sub, mul_pow, Finset.prod_pow]

--∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2
--fun i k ↦ ((c i) * F i k)

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

def normalised_discrete (F : (ι → ℤ) → ℝ) (q : ℝ) : (ι → ℤ) → ℝ :=
  fun k ↦ ((∑' a, |F a|^ q) ^ (q⁻¹))⁻¹ * F k

lemma rpow_inv_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ): (x ^ y)⁻¹ ^ z = (x ^ (y * z))⁻¹ := by
  rw [Real.rpow_mul hx y z, ← Real.inv_rpow (x := x ^ y)]
  exact rpow_nonneg hx y

omit [Fintype ι] [Nonempty ι] in
lemma normalised_discrete_norm {F : (ι → ℤ) → ℝ} {q : ℝ} (hq : q ≠ 0) (h : 0 < ∑' a, |F a|^ q) :
    ∑' a, |(normalised_discrete F q) a|^ q = 1 := by
  unfold normalised_discrete
  calc
    ∑' (a : ι → ℤ), |((∑' a, |F a|^ q) ^ (q⁻¹))⁻¹ * F a| ^ q
    _ = ∑' (a : ι → ℤ), (|((∑' a, |F a|^ q) ^ (q⁻¹))⁻¹| * |F a|) ^ q := by
      congr
      ext a
      rw[abs_mul]
    _ = ∑' (a : ι → ℤ), |((∑' (a : ι → ℤ), |F a| ^ q) ^ q⁻¹)⁻¹| ^ q * |F a| ^ q := by
      congr
      ext a
      rw[Real.mul_rpow] <;> apply abs_nonneg
    _ = |((∑' (a : ι → ℤ), |F a| ^ q) ^ q⁻¹)⁻¹| ^ q *  ∑' (a : ι → ℤ), |F a| ^ q := by
      rw[_root_.tsum_mul_left]
    _ = ((∑' (a : ι → ℤ), |F a| ^ q) ^ q⁻¹)⁻¹ ^ q *  ∑' (a : ι → ℤ), |F a| ^ q := by
      congr
      simp
      apply rpow_nonneg
      apply tsum_nonneg
      intros
      apply rpow_nonneg
      apply abs_nonneg
    _ = ((∑' (a : ι → ℤ), |F a| ^ q) )⁻¹ *  ∑' (a : ι → ℤ), |F a| ^ q := by
      congr
      rw[rpow_inv_mul]
      · field_simp
      apply tsum_nonneg
      intros
      apply rpow_nonneg
      apply abs_nonneg
    _ = 1 := by
      refine inv_mul_cancel₀ ?_
      exact Ne.symm (ne_of_lt h)

omit [Fintype ι] [Nonempty ι] in
theorem normalised_discrete_mul {F : (ι → ℤ) → ℝ} {q : ℝ} (h : 0 < ∑' a, |F a|^ q) :
    (fun b ↦ (∑' a, |F a|^ q) ^ (q⁻¹) * normalised_discrete F q b) = F := by
  ext b
  unfold normalised_discrete
  field_simp

omit [Nonempty ι] in
lemma normalised_discrete_discrete'_avg_mul
    (n : ℕ) (q : ι → ℝ) (F : ι → (ι → ℤ) → ℝ) (a : ι → ℤ) (h : ∀ i,  0 < ∑' a, |F i a|^ q i):
    discrete_avg' n (fun i k ↦ ((∑' a, |F i a|^ q i) ^ ((q i)⁻¹) *
    normalised_discrete (F i) (q i) k)) a = discrete_avg' n F a := by
  congr
  ext i
  rename_i k
  nth_rw 3[← normalised_discrete_mul (h i)]

omit [Nonempty ι] in
lemma normalised_discrete_discrete'_avg_mul'
    (n : ℕ) (q : ι → ℝ) (F : ι → (ι → ℤ) → ℝ) (a : ι → ℤ) (h : ∀ i,  0 < ∑' a, |F i a|^ q i):
    (∏ i, (∑' a, |F i a|^ q i) ^ ((q i)⁻¹)) *
    discrete_avg' n (fun i k ↦ normalised_discrete (F i) (q i) k) a = discrete_avg' n F a := by
  rw [← normalised_discrete_discrete'_avg_mul n q F a h, discrete'_avg_mul]

omit [Fintype ι] [Nonempty ι] in
theorem normalised_discrete_memℓp {F : (ι → ℤ) → ℝ} (q : ℝ) {p : ℝ≥0∞} (h : Memℓp F p) :
    Memℓp (normalised_discrete F q) p := by
  unfold normalised_discrete
  exact Memℓp.const_mul h ((∑' (a : ι → ℤ), |F a| ^ q) ^ q⁻¹)⁻¹

theorem discrete_ver' {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
    (m : ℕ) (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℤ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):  --(hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal) unnötig i think, da 0 *  ⊤ = 0 NVM
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2  ≤ --NOTE: ∑' does coercion to ℝ, at some point (Fact 5.4 or smth) note that this is summable
    (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m * ∏ (j : ι), (∑' a : ι → ℤ, |(F j a)|^(q j))^(2/(q j)) := by
  by_cases hm : m = 0
  · have : IsEmpty (Fin m) := by
      rw[hm]
      exact Fin.isEmpty'
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ge_iff_le]
    apply mul_nonneg
    · exact gz hg m
    refine Finset.prod_nonneg ?_
    intros
    apply rpow_nonneg
    apply tsum_nonneg
    intros
    apply rpow_nonneg
    apply abs_nonneg
  set K := ((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg) --falsch
  by_cases h : ∃ i, F i = 0
  · obtain ⟨i, ih⟩ := h
    have : ∏ j, (∑' (a : ι → ℤ), |F j a| ^ q j) ^ (2 / q j) = 0 := by
      refine Finset.prod_eq_zero_iff.mpr ?_
      use i
      rw[ih]
      simp only [Finset.mem_univ, Pi.zero_apply, abs_zero, _root_.tsum_const, nsmul_eq_mul,
        true_and]
      have : (0 : ℝ) ^ q i = 0 := by
        refine Real.zero_rpow ?_
        exact Ne.symm (ne_of_lt (hq.1 i))
      rw[this]
      simp only [mul_zero]
      refine Real.zero_rpow ?_
      simp only [ne_eq, _root_.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or]
      exact Ne.symm (ne_of_lt (hq.1 i))
    rw[this]
    simp only [mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro x _
    apply tsum_eq_zero
    ext a
    simp
    suffices (n : ℕ): discrete_avg' n F a = 0
    · rw[this, this]
      simp only [sub_self]
    unfold discrete_avg'
    apply mul_eq_zero.2
    right
    apply Finset.sum_eq_zero
    intro t _
    refine Finset.prod_eq_zero_iff.mpr ?_
    use i
    rw[ih]
    simp only [Finset.mem_univ, Pi.zero_apply, and_self]
  simp only [not_exists] at h
  have po : ∀ i, 0 < ∑' a, |F i a|^ q i := by
    intro i
    apply mem_lp_neq_zero_sub_abs_gt_zero <;> tauto
  let p := (∏ i, (∑' a, |F i a|^ q i) ^ ((q i)⁻¹))
  calc
    ∑ i : Fin m, ∑' (a : ι → ℤ),
    (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨↑i, get_rid i⟩) F a) ^ 2
      = ∑ i : Fin m, ∑' (a : ι → ℤ), ((p * discrete_avg' (idx i.succ)
        (fun i k ↦ normalised_discrete (F i) (q i) k) a)
        - (p * discrete_avg' (idx ⟨↑i, get_rid i⟩)
        (fun i k ↦ normalised_discrete (F i) (q i) k) a)) ^ 2 := by
      congr
      ext i
      congr
      ext k
      unfold p
      rw[normalised_discrete_discrete'_avg_mul' (h := po),
        normalised_discrete_discrete'_avg_mul' (h := po)]
    _ = ∑ i : Fin m, ∑' (a : ι → ℤ), (p^2 * ((discrete_avg' (idx i.succ)
        (fun i k ↦ normalised_discrete (F i) (q i) k) a)
        - (discrete_avg' (idx ⟨↑i, get_rid i⟩)
        (fun i k ↦ normalised_discrete (F i) (q i) k) a)) ^ 2) := by
      congr
      ext i
      ring_nf
    _ = p^2 * ∑ i : Fin m, ∑' (a : ι → ℤ), (((discrete_avg' (idx i.succ)
        (fun i k ↦ normalised_discrete (F i) (q i) k) a)
        - (discrete_avg' (idx ⟨↑i, get_rid i⟩)
        (fun i k ↦ normalised_discrete (F i) (q i) k) a)) ^ 2) := by
      rw[Finset.mul_sum]
      congr
      ext
      rw[← _root_.tsum_mul_left]
    _ ≤ p^2 * ((((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m) := by
      gcongr
      apply discrete_ver'_norm_one <;> try assumption
      · intro i
        apply normalised_discrete_memℓp
        exact hF i
      intro i
      apply normalised_discrete_norm
      · exact Ne.symm (ne_of_lt (hq.1 i))
      exact po i
    _ = (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m * p ^ 2 := by
      ring
    _ = (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m * ∏ (j : ι), (∑' a : ι → ℤ, |(F j a)|^(q j))^(2/(q j)) := by
      congr
      unfold p
      rw[← Finset.prod_pow]
      congr
      ext i
      rw[← Real.rpow_two, ← Real.rpow_mul]
      · congr 1
        exact inv_mul_eq_div (q i) 2
      apply tsum_nonneg
      intro
      apply rpow_nonneg
      apply abs_nonneg

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


/-ℕ version:-/ --The condition Nontrival MIGHT be necessray, if yes, remove the IsEmpty condition
theorem discrete_ver {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q)
  (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) [unι: Nontrivial ι]
    (m : ℕ) (idx : Fin (m+1) → ℕ) (mon : Monotone idx)
    (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℕ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):
    ∑ i : Fin m, ∑' a : ι → ℕ,
    (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2
     ≤(((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg))
     * g m * ∏ (j : ι), (∑' a : ι → ℕ, |(F j a)|^(q j))^(2/(q j)) := by


    obtain ⟨hq, hq'⟩ := hq
    /-

    by_cases hι: IsEmpty ι
    · unfold discrete_avg
      simp only [one_div, Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, _root_.tsum_const, Nat.card_eq_fintype_card,
        Fintype.card_unique, one_smul]
      let S : Set (Fin (m + 1)) := {x | idx x = 0}
      by_cases hm : m = 0
      · have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
            (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 = 0 := by
          have : IsEmpty (Fin m) := by
            rw[hm]
            exact Fin.isEmpty'
          (expose_names; refine Finset.sum_of_isEmpty Finset.univ)
        rw[this]
        exact gz hg m

      by_cases hS : S.toFinset.Nonempty
      swap
      · unfold S at hS
        simp only [toFinset_setOf, Finset.not_nonempty_iff_eq_empty] at hS
        have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
            (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x _
          have (n : Fin (m+1)) : ((↑(idx n)) : ℝ)⁻¹ * ↑(idx n) = 1 := by
            refine inv_mul_cancel₀ ?_
            contrapose hS
            simp_all only [IsEmpty.forall_iff, Finset.mem_univ, ne_eq, Nat.cast_eq_zero,
              Decidable.not_not]
            refine Finset.nonempty_iff_ne_empty.mp ?_
            use n
            simp only [Finset.mem_filter, Finset.mem_univ, hS, and_self]
          rw[this, this]
          simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        rw[this]
        exact gz hg m
      let y := S.toFinset.max' hS
      have s1 {n : Fin (m+1)} (hn : n ≤ y): idx n = 0 := by
        suffices : idx n ≤ 0
        · exact Nat.eq_zero_of_le_zero this
        calc
          idx n
            ≤ idx y := mon hn
          _ = 0 := by
            suffices : y ∈ S
            · unfold S at this
              simp_all only [IsEmpty.forall_iff, mem_setOf_eq]
            refine mem_toFinset.mp ?_
            exact Finset.max'_mem S.toFinset hS
      have s2 {n : Fin (m+1)} (hn : y < n): ((idx n)⁻¹ : ℝ) * (idx n) = 1 := by
        refine inv_mul_cancel₀ ?_
        refine LT.lt.ne' ?_
        simp only [Nat.cast_pos]
        by_cases yh : y = (⟨m, lt_add_one m⟩  : Fin (m+1))
        · rw[yh] at hn
          contrapose hn
          simp only [not_lt]
          obtain ⟨n, hn'⟩ := n
          simp_all only [IsEmpty.forall_iff, not_lt, nonpos_iff_eq_zero, Fin.mk_le_mk]
          exact Nat.le_of_lt_succ hn'
        have yp: y.val + 1 < m + 1 := by
          obtain ⟨y, yh'⟩ := y
          simp_all only [IsEmpty.forall_iff, toFinset_nonempty, Fin.mk.injEq, add_lt_add_iff_right]
          contrapose yh
          simp_all only [not_lt, Decidable.not_not]
          linarith
        calc
          0 < idx ⟨y.val + 1, yp⟩ := by
            by_contra h0
            simp only [not_lt, nonpos_iff_eq_zero] at h0
            have : ⟨↑y + 1, yp⟩ ∈ S.toFinset := by
              unfold S
              simp only [toFinset_setOf, Finset.mem_filter, Finset.mem_univ, h0, and_self]
            have : ⟨↑y + 1, yp⟩ ≤ y := Finset.le_max' S.toFinset ⟨↑y + 1, yp⟩ this
            obtain ⟨y, yh'⟩ := y
            simp only [Fin.mk_le_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
              one_ne_zero] at this
          _ ≤ idx n := by
            apply mon
            obtain ⟨n, hn'⟩ := n
            obtain ⟨y, yh'⟩ := y
            simp_all only [IsEmpty.forall_iff, toFinset_nonempty, Fin.mk.injEq, Fin.mk_lt_mk,
              Fin.mk_le_mk]
            exact hn
      by_cases yh : y = (⟨m, lt_add_one m⟩  : Fin (m+1))
      · have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
            (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x _
          rw[s1, s1]
          · simp only [CharP.cast_eq_zero, _root_.inv_zero, mul_zero, sub_self, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
          · rw[yh]
            simp only [Fin.mk_le_mk, Fin.is_le']
          rw[yh]
          obtain ⟨x, xh⟩ := x
          simp only [Fin.succ_mk, Fin.mk_le_mk]
          exact xh
        rw[this]
        exact gz hg m
      have yp: y.val + 1 < m + 1 := by
        obtain ⟨y, yh'⟩ := y
        simp_all only [IsEmpty.forall_iff, toFinset_nonempty, Fin.mk.injEq, add_lt_add_iff_right]
        contrapose yh
        simp_all only [not_lt, Decidable.not_not]
        linarith
      have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
          (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 =
          (((↑(idx (⟨↑y, lt_add_one_down yp⟩ : Fin m).succ)) : ℝ)⁻¹ * ↑(idx (⟨↑y, lt_add_one_down yp⟩ : Fin m).succ) -
          (↑(idx ⟨↑(⟨↑y, lt_add_one_down yp⟩ : Fin m), get_rid (⟨↑y, lt_add_one_down yp⟩ : Fin m)⟩))⁻¹
          * ↑(idx ⟨↑(⟨↑y, lt_add_one_down yp⟩ : Fin m), get_rid (⟨↑y, lt_add_one_down yp⟩ : Fin m)⟩)) ^ 2 := by
        rw[← tsum_fintype]
        apply tsum_eq_single (b := (⟨↑y, lt_add_one_down yp⟩ : Fin m))
        intro b bh
        obtain ⟨b, bh'⟩ := b
        obtain ⟨y, yh'⟩ := y
        simp_all only [toFinset_nonempty, Fin.mk.injEq, ne_eq, Fin.succ_mk, OfNat.ofNat_ne_zero,
          not_false_eq_true, pow_eq_zero_iff]
        by_cases bh'': b < y
        · rw[s1, s1]
          · simp only [CharP.cast_eq_zero, _root_.inv_zero, mul_zero, sub_self]
          · simp only [Fin.mk_le_mk]
            exact (le_of_lt bh'')
          simp only [Fin.mk_le_mk]
          exact bh''
        have bh''': y < b := by
          contrapose bh
          simp_all only [add_lt_add_iff_right, not_lt, Decidable.not_not]
          linarith
        rw[s2, s2]
        · norm_num
        · exact bh'''
        simp only [Fin.mk_lt_mk]
        linarith
      rw[this]
      rw[s2, s1]
      · simp only [CharP.cast_eq_zero, _root_.inv_zero, mul_zero, sub_zero, one_pow, ge_iff_le]
        rw[← one_mul 1]
        gcongr
        · rw[← add_zero 1]
          gcongr
          · refine (one_le_div₀ ?_).mpr ?_
            · simp only [Nat.ofNat_pos]
            rw[← mul_one 3]
            gcongr
            · norm_num
            norm_num
            have : abs π = π := by
              simp only [abs_eq_self]
              exact pi_nonneg
            rw[this]
            apply le_of_lt
            calc
             1 < 3 := by simp only [Nat.one_lt_ofNat]
              _< π := pi_gt_three
          simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, zero_le_coe]
        have := hg.1 m
        simp only [one_le_coe, ge_iff_le]
        apply this
        exact Nat.one_le_iff_ne_zero.mpr hm
      · simp only [Fin.eta, le_refl]
      obtain ⟨y, yh⟩ := y
      simp only [Fin.succ_mk, Fin.mk_lt_mk, lt_add_iff_pos_right, zero_lt_one]
    -/
    --simp only [not_isEmpty_iff] at hι
    let A := {k : ι → ℤ | ∀ j : ι, 0 ≤ k j}
    have mem_A(u : ↑A)(i : ι): incl_fun F i ↑u = F i fun t ↦ ((↑u : ι → ℤ) t).toNat := by
      unfold incl_fun
      obtain ⟨u,uh⟩ := u
      unfold A at uh
      dsimp at uh
      simp [uh]
    have not_mem_A (u : ↑Aᶜ) (i : ι): incl_fun F i ↑u = 0 := by
      unfold incl_fun
      suffices : ¬ ∀ (j : ι), 0 ≤ (↑u : ι → ℤ) j
      · simp only [this, ↓reduceIte]
      obtain ⟨u,uh⟩ := u
      simp only
      simp only [mem_compl_iff, mem_setOf_eq, A] at uh
      exact uh
    let h: ↑A → ι → ℕ := fun ⟨k, _⟩ ↦ fun i ↦ (k i).toNat
    have bij: Bijective h := by
      refine bijective_iff_has_inverse.mpr ?_
      let g : (ι → ℕ) → (↑A : Type u_1) :=
        fun k ↦ ⟨fun i ↦ (↑(k i) : ℤ), by
          unfold A
          simp only [mem_setOf_eq, Nat.cast_nonneg, implies_true]⟩
      use g
      constructor
      · intro ⟨k, kh⟩
        unfold g h
        simp only [Int.ofNat_toNat, Subtype.mk.injEq]
        ext i
        unfold A at kh
        simp_all only [Subtype.forall, mem_compl_iff,
          mem_setOf_eq, sup_of_le_left]
      intro k
      ext i
      unfold g h A
      simp only [Int.toNat_natCast]
    have sum_eq(i : ι): ∑' (a : ι → ℤ), |incl_fun F i a| ^ q i = ∑' (a : ι → ℕ), |F i a| ^ q i := by
      calc
        ∑' (a : ι → ℤ), |incl_fun F i a| ^ q i
        /-  = ∑' a : ↑(A ∪ Aᶜ), |incl_fun F i ↑a| ^ q i := by rw [@union_compl_self, ← tsum_univ]
        _ = ∑' a : ↑A, |incl_fun F i ↑a| ^ q i + ∑' a : ↑Aᶜ, |incl_fun F i ↑a| ^ q i := by
          sorry-/
        _ = ∑' a : ↑A, |incl_fun F i ↑a| ^ q i := by
          rw[← tsum_subtype_eq_of_support_subset]
          intro k hk
          contrapose hk
          unfold A at hk
          unfold incl_fun
          simp only [mem_setOf_eq] at hk
          simp [hk]
          apply Real.zero_rpow
          specialize hq i
          contrapose hq
          simp_all
        _ = ∑' a : ↑A, |F i fun t ↦ ((↑a : ι → ℤ) t).toNat| ^ q i := by
          apply tsum_congr
          intro b
          rw[mem_A]
        _ = ∑' (a : ι → ℕ), |F i a| ^ q i := by
          let h: ↑A → ι → ℕ := fun ⟨k, _⟩ ↦ fun i ↦ (k i).toNat
          have bij: Bijective h := by
            refine bijective_iff_has_inverse.mpr ?_
            let g : (ι → ℕ) → (↑A : Type u_1) :=
              fun k ↦ ⟨fun i ↦ (↑(k i) : ℤ), by
                unfold A
                simp only [mem_setOf_eq, Nat.cast_nonneg, implies_true]⟩
            use g
            constructor
            · intro ⟨k, kh⟩
              unfold g h
              simp only [Int.ofNat_toNat, Subtype.mk.injEq]
              ext i
              unfold A at kh
              simp_all only [Subtype.forall, mem_compl_iff,
                mem_setOf_eq, sup_of_le_left]
            intro k
            ext i
            unfold g h A
            simp only [Int.toNat_natCast]
          rw [tsum_swap (hh := bij) (g:= fun a ↦ |F i a| ^ q i)]
          intro a
          apply rpow_nonneg
          apply abs_nonneg
    have prod_eq: ∏ j, (∑' (a : ι → ℤ), |incl_fun F j a| ^ q j) ^ (2 / q j) = ∏ j, (∑' (a : ι → ℕ), |F j a| ^ q j) ^ (2 / q j) := by
      apply Finset.prod_congr rfl
      intros
      rw[sum_eq]
    rw[← prod_eq]
    suffices : ∑ i : Fin m, ∑' (a : ι → ℕ), (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨↑i, get_rid i⟩) F a) ^ 2 =
       ∑ i : Fin m, ∑' (a : ι → ℤ), (discrete_avg' (idx i.succ) (incl_fun F) a - discrete_avg' (idx ⟨↑i, get_rid i⟩) (incl_fun F) a) ^ 2
    · rw[this]
      clear this prod_eq sum_eq
      apply discrete_ver' hg ⟨hq, hq'⟩ m idx mon hidx hidx' (incl_fun F)
      intro i
      unfold Memℓp
      simp only [ENNReal.coe_eq_zero, toNNReal_eq_zero, ne_eq, coe_ne_top, ↓reduceIte, norm_eq_abs,
        coe_toReal, coe_toNNReal']
      have : ¬q i ≤ 0 := by
        simp only [not_le]
        exact hq i
      simp only [this, ↓reduceIte]
      have mm: max (q i) 0 = q i := by
        simp
        exact le_of_lt (hq i)
      rw[mm]
      specialize hF i
      unfold Memℓp at hF
      have : (↑(q i).toNNReal : ℝ≥0∞) ≠ 0 ∧ (↑(q i).toNNReal : ℝ≥0∞) ≠ ⊤ := by
        simpa only [ne_eq, ENNReal.coe_eq_zero,
          toNNReal_eq_zero, not_le, coe_ne_top, not_false_eq_true, and_true]
      simp only [this, ↓reduceIte, norm_eq_abs, coe_toReal, coe_toNNReal'] at hF
      rw[mm] at hF
      apply (NNReal.summable_mk _).mp ?_
      · intro n
        refine rpow_nonneg ?_ (q i)
        apply abs_nonneg
      apply ENNReal.tsum_coe_ne_top_iff_summable.1
      apply (NNReal.summable_mk _).mpr at hF
      apply ENNReal.tsum_coe_ne_top_iff_summable.2 at hF
      set g := fun b ↦ ((↑⟨|incl_fun F i b| ^ q i, rpow_nonneg (abs_nonneg (incl_fun F i b)) (q i)⟩ : ℝ≥0) : ℝ≥0∞)
      set f' : (ι → ℕ) → ℝ≥0 := fun b ↦ (⟨|F i b| ^ q i, rpow_nonneg (abs_nonneg (F i b)) (q i)⟩ : ℝ≥0)
      set f:= fun b ↦ (↑(f' b) : ℝ≥0∞)
      suffices : ∑' (b : ι → ℤ), g b = ∑' (b : ι → ℕ), f b
      · rw[this]
        exact hF
      calc
        ∑' (b : ι → ℤ), g b
          = ∑' b : ↑A, g ↑b := by
          rw[← tsum_subtype_eq_of_support_subset]
          intro k hk
          contrapose hk
          unfold A at hk
          unfold g
          unfold incl_fun
          simp only [mem_setOf_eq] at hk
          simp only [mem_support, hk, ↓reduceIte, abs_zero, ne_eq, ENNReal.coe_eq_zero,
            Decidable.not_not]
          ext
          simp only [coe_mk, NNReal.coe_zero]
          refine Real.zero_rpow ?_
          exact Ne.symm (ne_of_lt (hq i))
        _ = ∑' (b : ι → ℕ), f b := by
          rw[← tsum_swap_ennreal (hh := bij)]
          congr
          ext ⟨x, xh⟩
          unfold g f h f'
          simp only [ENNReal.coe_inj]
          congr
          unfold incl_fun
          unfold A at xh
          simp_all only [Subtype.forall, mem_compl_iff, not_le, sup_eq_left, ne_eq,
            ENNReal.coe_eq_zero, toNNReal_eq_zero, coe_ne_top, not_false_eq_true, and_self,
            mem_setOf_eq, implies_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro i _
    symm
    calc
      ∑' (a : ι → ℤ), (discrete_avg' (idx i.succ) (incl_fun F) a - discrete_avg' (idx ⟨↑i, get_rid i⟩) (incl_fun F) a) ^ 2
      _ = ∑' (a : ↑A), (discrete_avg' (idx i.succ) (incl_fun F) ↑a - discrete_avg' (idx ⟨↑i, get_rid i⟩) (incl_fun F) ↑a) ^ 2 := by
        rw[← tsum_subtype_eq_of_support_subset]
        intro k hk
        contrapose hk
        unfold A at hk
        unfold incl_fun
        simp only [mem_setOf_eq] at hk
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, support_pow, mem_support,
          Decidable.not_not]

        simp only [not_forall, not_le] at hk
        obtain ⟨x, xh⟩ := hk
        have h0: ∃ j : ι, x ≠ j := by
          obtain ⟨j, jh⟩ := exists_ne x
          use j
          exact Ne.symm jh
        obtain ⟨j, xj⟩ := h0
        have (n : ℕ) : discrete_avg' n (fun i k ↦ if ∀ (j : ι), 0 ≤ k j then F i fun t ↦ (k t).toNat else 0) k = 0 := by --this may just not be true if ι has only one element
          unfold discrete_avg'
          simp only [mul_eq_zero]
          right
          apply Finset.sum_eq_zero
          intro z _
          apply Finset.prod_eq_zero (i := j)
          · simp only [Finset.mem_univ]
          suffices : ¬ ∀ (j_1 : ι), 0 ≤ (k + unit j (↑z : ℤ)) j_1
          · set P := ∀ (j_1 : ι), 0 ≤ (k + unit j (↑z : ℤ)) j_1
            have : (if ∀ (j_1 : ι), 0 ≤ (k + unit j (↑z : ℤ)) j_1 then F j fun t ↦ ((k + unit j (↑z : ℤ)) t).toNat else 0) =
                (if P then F j fun t ↦ ((k + unit j (↑z : ℤ)) t).toNat else 0) := by congr
            rw[this]
            clear this
            simp only [this, ↓reduceIte]
          simp only [Pi.add_apply, not_forall, not_le]
          use x
          unfold unit
          simp [Ne.symm xj, xh]
        rw[this,this, sub_zero]
      _ = ∑' (a : ι → ℕ), (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨↑i, get_rid i⟩) F a) ^ 2 := by
        set f := fun a ↦ (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨↑i, get_rid i⟩) F a) ^ 2
        calc
          ∑' (a : ↑A), (discrete_avg' (idx i.succ) (incl_fun F) ↑a - discrete_avg' (idx ⟨↑i, get_rid i⟩) (incl_fun F) ↑a) ^ 2
            = ∑' (a : ↑A), f (h a) := by
            congr
            ext ⟨a, ah⟩
            unfold f h discrete_avg discrete_avg' incl_fun
            unfold A at ah
            simp_all only [Subtype.forall, mem_compl_iff, Finset.mem_univ,
              one_div, Pi.add_apply]
            congr
            repeat
              ext r
              congr
              ext i
              have :  ∀ (j : ι), 0 ≤ a j + unit i (↑r) j := by
                intro j
                calc
                  0 ≤ a j := by
                    simp_all only [mem_setOf_eq]
                  _ ≤ a j + unit i (↑r) j := by
                    unfold unit
                    simp only [le_add_iff_nonneg_right]
                    by_cases ij : i = j <;> simp only [ij, ↓reduceIte, Nat.cast_nonneg, le_refl]
              simp only [this, implies_true, ↓reduceIte]
              congr
              ext j
              simp only [Pi.add_apply]
              unfold unit
              by_cases ij : i = j <;> simp only [ij, ↓reduceIte, add_zero]
              rw [Int.toNat_add_nat (ah j) r]
          _ = ∑' (a : ι → ℕ), f a := by
            apply tsum_swap bij
            unfold f
            intro i
            simp
            apply sq_nonneg




theorem discrete_ver_isempty {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q)
    (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) [unι: IsEmpty ι]
    (m : ℕ) (idx : Fin (m+1) → ℕ) (mon : Monotone idx)
    (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℕ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):
    ∑ i : Fin m, ∑' a : ι → ℕ,
    (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2
     ≤(((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg))
     * g m * ∏ (j : ι), (∑' a : ι → ℕ, |(F j a)|^(q j))^(2/(q j)) := by
  unfold discrete_avg
  simp only [one_div, Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, _root_.tsum_const, Nat.card_eq_fintype_card,
    Fintype.card_unique, one_smul]
  let S : Set (Fin (m + 1)) := {x | idx x = 0}
  by_cases hm : m = 0
  · have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
        (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 = 0 := by
      have : IsEmpty (Fin m) := by
        rw[hm]
        exact Fin.isEmpty'
      (expose_names; refine Finset.sum_of_isEmpty Finset.univ)
    rw[this]
    exact gz hg m

  by_cases hS : S.toFinset.Nonempty
  swap
  · unfold S at hS
    simp only [toFinset_setOf, Finset.not_nonempty_iff_eq_empty] at hS
    have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
        (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _
      have (n : Fin (m+1)) : ((↑(idx n)) : ℝ)⁻¹ * ↑(idx n) = 1 := by
        refine inv_mul_cancel₀ ?_
        contrapose hS
        simp_all only [IsEmpty.forall_iff, Finset.mem_univ, ne_eq, Nat.cast_eq_zero,
          Decidable.not_not]
        refine Finset.nonempty_iff_ne_empty.mp ?_
        use n
        simp only [Finset.mem_filter, Finset.mem_univ, hS, and_self]
      rw[this, this]
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw[this]
    exact gz hg m
  let y := S.toFinset.max' hS
  have s1 {n : Fin (m+1)} (hn : n ≤ y): idx n = 0 := by
    suffices : idx n ≤ 0
    · exact Nat.eq_zero_of_le_zero this
    calc
      idx n
        ≤ idx y := mon hn
      _ = 0 := by
        suffices : y ∈ S
        · unfold S at this
          simp_all only [IsEmpty.forall_iff, mem_setOf_eq]
        refine mem_toFinset.mp ?_
        exact Finset.max'_mem S.toFinset hS
  have s2 {n : Fin (m+1)} (hn : y < n): ((idx n)⁻¹ : ℝ) * (idx n) = 1 := by
    refine inv_mul_cancel₀ ?_
    refine LT.lt.ne' ?_
    simp only [Nat.cast_pos]
    by_cases yh : y = (⟨m, lt_add_one m⟩  : Fin (m+1))
    · rw[yh] at hn
      contrapose hn
      simp only [not_lt]
      obtain ⟨n, hn'⟩ := n
      simp_all only [IsEmpty.forall_iff, not_lt, nonpos_iff_eq_zero, Fin.mk_le_mk]
      exact Nat.le_of_lt_succ hn'
    have yp: y.val + 1 < m + 1 := by
      obtain ⟨y, yh'⟩ := y
      simp_all only [IsEmpty.forall_iff, toFinset_nonempty, Fin.mk.injEq, add_lt_add_iff_right]
      contrapose yh
      simp_all only [not_lt, Decidable.not_not]
      linarith
    calc
      0 < idx ⟨y.val + 1, yp⟩ := by
        by_contra h0
        simp only [not_lt, nonpos_iff_eq_zero] at h0
        have : ⟨↑y + 1, yp⟩ ∈ S.toFinset := by
          unfold S
          simp only [toFinset_setOf, Finset.mem_filter, Finset.mem_univ, h0, and_self]
        have : ⟨↑y + 1, yp⟩ ≤ y := Finset.le_max' S.toFinset ⟨↑y + 1, yp⟩ this
        obtain ⟨y, yh'⟩ := y
        simp only [Fin.mk_le_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
          one_ne_zero] at this
      _ ≤ idx n := by
        apply mon
        obtain ⟨n, hn'⟩ := n
        obtain ⟨y, yh'⟩ := y
        simp_all only [IsEmpty.forall_iff, toFinset_nonempty, Fin.mk.injEq, Fin.mk_lt_mk,
          Fin.mk_le_mk]
        exact hn
  by_cases yh : y = (⟨m, lt_add_one m⟩  : Fin (m+1))
  · have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
        (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _
      rw[s1, s1]
      · simp only [CharP.cast_eq_zero, _root_.inv_zero, mul_zero, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      · rw[yh]
        simp only [Fin.mk_le_mk, Fin.is_le']
      rw[yh]
      obtain ⟨x, xh⟩ := x
      simp only [Fin.succ_mk, Fin.mk_le_mk]
      exact xh
    rw[this]
    exact gz hg m
  have yp: y.val + 1 < m + 1 := by
    obtain ⟨y, yh'⟩ := y
    simp_all only [IsEmpty.forall_iff, toFinset_nonempty, Fin.mk.injEq, add_lt_add_iff_right]
    contrapose yh
    simp_all only [not_lt, Decidable.not_not]
    linarith
  have : ∑ x : Fin m, (((↑(idx x.succ)) : ℝ)⁻¹ * ↑(idx x.succ) -
      (↑(idx ⟨↑x, get_rid x⟩))⁻¹ * ↑(idx ⟨↑x, get_rid x⟩)) ^ 2 =
      (((↑(idx (⟨↑y, lt_add_one_down yp⟩ : Fin m).succ)) : ℝ)⁻¹ * ↑(idx (⟨↑y, lt_add_one_down yp⟩ : Fin m).succ) -
      (↑(idx ⟨↑(⟨↑y, lt_add_one_down yp⟩ : Fin m), get_rid (⟨↑y, lt_add_one_down yp⟩ : Fin m)⟩))⁻¹
      * ↑(idx ⟨↑(⟨↑y, lt_add_one_down yp⟩ : Fin m), get_rid (⟨↑y, lt_add_one_down yp⟩ : Fin m)⟩)) ^ 2 := by
    rw[← tsum_fintype]
    apply tsum_eq_single (b := (⟨↑y, lt_add_one_down yp⟩ : Fin m))
    intro b bh
    obtain ⟨b, bh'⟩ := b
    obtain ⟨y, yh'⟩ := y
    simp_all only [toFinset_nonempty, Fin.mk.injEq, ne_eq, Fin.succ_mk, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff]
    by_cases bh'': b < y
    · rw[s1, s1]
      · simp only [CharP.cast_eq_zero, _root_.inv_zero, mul_zero, sub_self]
      · simp only [Fin.mk_le_mk]
        exact (le_of_lt bh'')
      simp only [Fin.mk_le_mk]
      exact bh''
    have bh''': y < b := by
      contrapose bh
      simp_all only [add_lt_add_iff_right, not_lt, Decidable.not_not]
      linarith
    rw[s2, s2]
    · norm_num
    · exact bh'''
    simp only [Fin.mk_lt_mk]
    linarith
  rw[this]
  rw[s2, s1]
  · simp
    rw[← one_mul 1]
    gcongr
    · apply le_trans (b := (2 : ℝ) * (1 : NNReal))
      · simp only [NNReal.coe_one, mul_one, Nat.one_le_ofNat]
      unfold good_const
      gcongr
      exact le_max_left 1 (good_const' hg)
    simp
    apply hg.1
    exact Nat.one_le_iff_ne_zero.mpr hm
  · simp only [Fin.eta, le_refl]
  obtain ⟨y, yh⟩ := y
  simp only [Fin.succ_mk, Fin.mk_lt_mk, lt_add_iff_pos_right, zero_lt_one]

theorem discrete_ver_single {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q)
    (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) [hι : Nonempty ι] [ιn : Subsingleton ι]
    (m : ℕ) (idx : Fin (m+1) → ℕ) (mon : Monotone idx)
    (hidx : Injective idx) (hidx': 0 < idx 0)
    (F : ι → (ι → ℕ) → ℝ) (hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):
    ∑ i : Fin m, ∑' a : ι → ℕ,
    (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2
     ≤(((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg))
     * g m * ∏ (j : ι), (∑' a : ι → ℕ, |(F j a)|^(q j))^(2/(q j)) := by
  sorry

variable {X : Type*} (f : ι → X → ℝ) {S : ι → X → X} (N : ℕ) [Nontrivial ι]

omit [Nonempty ι] [Nontrivial ι]
theorem fact5_5(hS: pairwise_commuting S)(hN: ∀(i : ι), (k i + n) < 2 * N)(x : X):
  ergodic_avg n S f (iterate S k x) = discrete_avg n ((push_forward_many N S f) x) k := by
    unfold ergodic_avg nergodic_avg
    unfold discrete_avg
    simp
    left
    apply Finset.sum_congr
    · rfl
    intro u uh
    apply Fintype.prod_congr
    intro i
    rw[← iterate_unit]
    unfold push_forward_many push_forward
    suffices : ∀ (i_1 : ι), (k + unit i u) i_1 < 2 * N
    · simp only [this]
      simp
      suffices : (iterate S (unit i u) (iterate S k x)) = (iterate S (k + unit i u) x)
      · rw[this]
      rw[add_comm, iterate_add' hS]
      simp
    simp
    intro j
    calc
      (k j + unit i u j) ≤ k j + n := by
        simp
        unfold unit
        by_cases ij: i = j
        · simp [ij]
          exact Finset.mem_range_le uh
        simp [ij]
                    _  < 2*N := hN j

    /-
    calc
      ∑ x, (k x + unit i u x) ≤ ∑ x, (k x + n) := by
        refine Finset.sum_le_sum ?_
        intro j jh
        simp
        unfold unit
        by_cases ij: i = j
        · simp [ij]
          exact Finset.mem_range_le uh
        simp [ij]
          _ = n*(Fintype.card ι) + ∑ x, k x := by
            rw[add_comm]
            rw[Finset.sum_add_distrib]
            suffices : ∑ (x : ι), n = n * (Fintype.card ι)
            · rw[this]
            simp
            rw[mul_comm]
          _ ≤ 2 * N + 1 := hN-/



def bound_set: Set (ι → ℕ) := setOf (fun k ↦ ∀(i : ι), k i < n)

omit [Nonempty ι] [Nontrivial ι]
theorem bound_set_encard [h : Nonempty ι]: encard (α := ι → ℕ) (bound_set N) = N^(Fintype.card ι) := by --yesssss
  by_cases hN: N = 0
  · unfold bound_set
    simp [hN]
  suffices : @bound_set ι N ≃ @Fintype.piFinset ι _ _ (fun _ ↦ ℕ) (fun _ ↦ Finset.range N)
  · suffices ass: encard (↑(@Fintype.piFinset ι _ _ (fun _ ↦ ℕ) (fun _ ↦ Finset.range N)) : Set (ι → ℕ)) = N^(Fintype.card ι)
    · rw[← ass]
      exact encard_congr this
    rw[Set.encard_eq_coe_toFinset_card]
    simp
  unfold bound_set
  simp
  rfl
/-
theorem bound_set_encard [h : Nonempty ι]: encard (α := ι → ℕ) (bound_set N) = N^(Fintype.card ι) := by --maybe split this up
  by_cases hN: N = 0
  · rw[hN]
    unfold bound_set
    simp
  by_cases hN': N = 1
  · unfold bound_set
    simp [hN']
    refine encard_eq_one.mpr ?_
    use 0
    ext k
    simp
    constructor
    · intro kh
      ext
      simp [kh]
    intro kh
    simp [kh]
  have hN'': 2 ≤ N := by
    contrapose hN'
    simp_all
    apply le_antisymm
    · linarith
    contrapose hN
    simp_all
  have : (↑N : ENat)^ Fintype.card ι = (↑((N : ℕ)^ Fintype.card ι) : ENat) := by simp
  rw[this]
  clear this
  rw[← Set.Nat.encard_range]
  refine encard_congr ?_
  simp
  let h : ((bound_set N) → ℕ) := fun (⟨k, _⟩ : bound_set (ι := ι) N) ↦ (∑ (i : ι), N ^ (↑(Finite.equivFin ι i) : ℕ) *(k i : ℕ))
  have h_well(k : bound_set (ι := ι) N): h k < N ^ Fintype.card ι := by
    obtain ⟨k,kh⟩ := k
    unfold bound_set at kh
    simp at kh
    calc
      h ⟨k,kh⟩ = ∑ (i : ι), N ^ (↑(Finite.equivFin ι i) : ℕ) *(k i : ℕ) := by rfl
            _  ≤ ∑ (i : ι), N ^ (↑(Finite.equivFin ι i) : ℕ) *(N-1) := by
              apply Finset.sum_le_sum
              intro i _
              gcongr
              exact Nat.le_sub_one_of_lt (kh i)
            _ = (N-1) * ∑ (i : ι), N ^ (↑(Finite.equivFin ι i) : ℕ) := by
              rw[mul_comm]
              rw[Finset.sum_mul]
            _ = (N-1) * ∑ i ∈ Finset.range (Fintype.card ι), N ^ ↑i := by
              congr
              sorry
            _ = N^ (Fintype.card ι) - 1 := by
              rw[Nat.geomSum_eq hN'']
              refine Nat.mul_div_cancel' ?_
              refine Nat.dvd_of_mod_eq_zero ?_
              refine Nat.sub_mod_eq_zero_of_mod_eq ?_
              rw [Nat.pow_mod]
              by_cases hN''': N = 2
              · rw[hN''']
                simp
              have ho: 1 % (N-1) = 1 := by
                rw[Nat.one_mod_eq_one.2]
                contrapose hN'''
                simp_all
              have : N % (N - 1) = 1 := by
                refine Nat.mod_eq_iff.mpr ?_
                right
                constructor
                · contrapose hN'''
                  simp_all
                  apply le_antisymm
                  · exact hN'''
                  exact hN''
                use (1 : ℕ)
                refine (Nat.sub_eq_iff_eq_add ?_).mp ?_
                · linarith
                rw[mul_one]
              rw[this]
              simp
            _ < N^ (Fintype.card ι) := by
              refine sub_one_lt ?_ ?_
              · simp
              simp
              exact hN
  let g : ((bound_set N) → Fin (N ^ Fintype.card ι)) := (fun k ↦ ⟨h k, h_well k⟩)
  let f : (Fin (N^ Fintype.card ι) → (ι → ℕ)) := (fun ⟨n,hn⟩ i ↦ (n / N^↑(Finite.equivFin ι i)) % N)
  have f_well(m : (Fin (N^ Fintype.card ι))): (f m) ∈ bound_set N := by
    unfold bound_set
    obtain ⟨m,_⟩ := m
    intro i
    unfold f
    simp
    apply Nat.mod_lt
    contrapose hN
    simp_all
  let u : (Fin (N^ Fintype.card ι) → bound_set N) := fun m ↦ ⟨f m, f_well m⟩
  refine Equiv.trans (β := Fin (N^ Fintype.card ι)) ?_ (Fin.equivSubtype)
  refine Equiv.ofBijective g ?_
  refine bijective_iff_has_inverse.mpr ?_
  use u
  constructor
  · intro ⟨k,kh⟩
    unfold u g f h
    ext i
    simp

    #check Fintype.sum_eq_single
    /-rw[Fintype.sum_eq_single i] --not yet
    swap
    · intro j ji
      sorry
    --Fintype.sum_eq_single a
    sorry
    -/
    sorry
  intro ⟨i,ih⟩
  unfold u g f h
  ext
  simp
  have ih': i < N ^ Nat.card ι := by simp [ih]
  rw[Fintype.sum_eq_single ((Finite.equivFin ι).symm (⟨i,ih'⟩ : Fin (N ^ Nat.card ι)))]
  sorry
-/

instance bound_set_fintype [h : Nonempty ι]: Fintype (@bound_set ι N) := by
  refine Finite.fintype ?_
  refine encard_lt_top_iff.mp ?_
  rw[bound_set_encard]
  simp

theorem push_forward_bound_set(F : X → ℝ)(x : X): support (push_forward N S F x) ⊆ (bound_set (2*N))  := by
  intro k kh
  contrapose kh
  simp
  by_cases N0: N ≤ 0
  · unfold push_forward bound_set at *
    simp_all
  unfold bound_set at kh
  unfold push_forward
  simp only [mem_setOf_eq] at kh
  simp [kh]

theorem push_forward_not_in_bound_set{k : ι → ℕ}(F : X → ℝ)(x : X)(hk : k ∉ @bound_set ι (2*N)): push_forward N S F x k = 0 := by
  contrapose hk
  simp
  exact (push_forward_bound_set N F x) hk

--[CommMonoid Y][AddCommMonoid Y]

instance bound_set_finite [h : Nonempty ι]: Finite (bound_set (ι := ι) N) := by
  refine finite_coe_iff.mpr ?_
  refine encard_ne_top_iff.mp ?_
  rw[bound_set_encard]
  exact ENat.coe_toNat_eq_self.mp rfl

theorem fact5_6 (a b : ℕ)[MeasurableSpace X](μ : Measure X)(hS: pairwise_commuting S)(hS': MMeasurePreserving μ S)
  (hN: a ≤ N ∧ b ≤ N)(hf : ∀ (i : ι), Measurable (f i)):
  ∫⁻ (x : X), ‖(ergodic_avg a S f x - ergodic_avg b S f x)‖ₑ ^ 2 ∂μ ≤
  1 / N^(Fintype.card ι) * ∫⁻ (x : X), ‖(∑' k : ι → ℕ, (discrete_avg a ((push_forward_many N S f) x) k - discrete_avg b ((push_forward_many N S f) x) k)^2)‖ₑ ∂μ := by
  by_cases hN: N = 0
  · rw[hN]
    simp
    have ha: a = 0 := by linarith
    have hb: b = 0 := by linarith
    simp [ha, hb]
  by_cases hι: IsEmpty ι
  · simp
    unfold ergodic_avg nergodic_avg push_forward_many push_forward discrete_avg
    simp
  simp at hι
  let p := (Fintype.card ι)
  have : ∫⁻ (x : X), ‖(ergodic_avg a S f x - ergodic_avg b S f x)‖ₑ ^ 2 ∂μ = 1 / N^p * ∑ x ∈ (@bound_set ι N).toFinset, ∫⁻ (x : X), ‖(ergodic_avg a S f x - ergodic_avg b S f x)‖ₑ ^ 2 ∂μ := by
    set k := ∫⁻ (x : X), ‖(ergodic_avg a S f x - ergodic_avg b S f x)‖ₑ ^ 2 ∂μ
    simp
    have : (Fintype.card (@bound_set ι N)) = encard (α := ι → ℕ) (bound_set N) := by simp
    have : (Fintype.card (@bound_set ι N)) = (encard (α := ι → ℕ) (bound_set N)).toNat := by
      rw[← this]
      rfl
    rw[this, bound_set_encard]
    have : ((↑N : ENat) ^ Fintype.card ι).toNat = N^ p := by rfl
    rw[this]
    simp
    rw[← mul_assoc]
    suffices : ((↑N : ENNReal) ^ p)⁻¹ * ↑N ^ p = 1
    · rw[this, one_mul]
    refine ENNReal.inv_mul_cancel ?_ ?_
    · simp
      tauto
    simp
  rw[this]
  clear this
  have meas: ∀(i : ι), Measurable (S i) := by
      intro i
      specialize hS' i
      exact hS'.measurable
  suffices : ∑ k ∈ (@bound_set ι N).toFinset, ∫⁻ (x : X), ‖ergodic_avg a S f x - ergodic_avg b S f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ (x : X), ‖∑' k : ι → ℕ, (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2‖ₑ ∂μ
  · unfold p
    apply mul_le_mul
    all_goals simp only [one_div, le_refl, zero_le, this]
  calc
        ∑ k ∈ (bound_set N).toFinset, ∫⁻ (x : X), ‖ergodic_avg a S f x - ergodic_avg b S f x‖ₑ ^ 2 ∂μ =
        ∑ k ∈ (bound_set N).toFinset, ∫⁻ (x : X), ‖ergodic_avg a S f (iterate S  k x) - ergodic_avg b S f (iterate S  k x)‖ₑ ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro k _
          rw[MeasureTheory.MeasurePreserving.lintegral_comp (μ := μ) (ν := μ) (f := fun x ↦ ‖ergodic_avg a S f x - ergodic_avg b S f x‖ₑ ^ 2) (g := fun x ↦ iterate S k x)]
          · apply iterate_measurepreserving
            exact hS'
          refine Measurable.pow_const ?_ 2
          apply Measurable.enorm
          apply Measurable.sub
          all_goals apply ergodic_avg_measurable; exact hf
          all_goals intro i; specialize hS' i; exact hS'.measurable
    _ = ∫⁻ (x : X), ∑ k ∈ (bound_set N).toFinset, ‖ergodic_avg a S f (iterate S  k x) - ergodic_avg b S f (iterate S  k x)‖ₑ ^ 2 ∂μ := by
          rw[MeasureTheory.lintegral_finset_sum] --instancs fucking me over welp
          intro k _
          fun_prop
    _ = ∫⁻ (x : X), ∑ k ∈ (bound_set N).toFinset, ‖discrete_avg a ((push_forward_many N S f) x) k - discrete_avg b ((push_forward_many N S f) x) k‖ₑ ^ 2 ∂μ := by
          apply lintegral_congr
          intro k
          apply Finset.sum_congr rfl
          intro x _
          rw[← fact5_5 (hS := hS), ← fact5_5 (hS := hS)]
          repeat
            intro i
            rename_i hh
            unfold bound_set at hh
            simp at hh
            specialize hh i
            linarith
    _ = ∫⁻ (x : X), ∑ k ∈ (bound_set N).toFinset, ‖(discrete_avg a ((push_forward_many N S f) x) k - discrete_avg b ((push_forward_many N S f) x) k)^2‖ₑ ∂μ := by
          apply lintegral_congr
          intro x
          apply Finset.sum_congr rfl
          intros
          rw[← @enorm_pow]
    _ = ∫⁻ (x : X), ‖∑ k ∈ (bound_set N).toFinset, (discrete_avg a ((push_forward_many N S f) x) k - discrete_avg b ((push_forward_many N S f) x) k)^2‖ₑ ∂μ := by
          apply lintegral_congr
          intro x
          rw [enorm_eq_ofReal_abs]
          set h := fun k ↦ (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2
          have : ∑ k ∈ (bound_set N).toFinset,
    ‖(discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2‖ₑ = ∑ k ∈ (bound_set N).toFinset, ENNReal.ofReal |h k|:= by
            unfold h
            simp
            apply Finset.sum_congr rfl
            intro x _
            rw[← enorm_pow]
            rw[enorm_eq_ofReal_abs]
            simp
          rw[this]
          clear this
          refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
          all_goals simp
          rw[ENNReal.toReal_sum]
          simp
          calc
            ∑ x ∈ (bound_set N).toFinset, |h x| = ∑ x ∈ (bound_set N).toFinset, h x := by
                apply Finset.sum_congr rfl
                intro x _
                simp
                unfold h
                apply sq_nonneg
             _ = |(bound_set N).toFinset.sum h| := by
                have : (bound_set N).toFinset.sum h = ∑ k ∈ bound_set N, h k := rfl
                rw[this]
                symm
                simp
                apply Finset.sum_nonneg
                unfold h
                intros
                apply sq_nonneg
          simp
    _ ≤ ∫⁻ (x : X), ‖∑ k ∈ (bound_set (2*N)).toFinset, (discrete_avg a ((push_forward_many N S f) x) k - discrete_avg b ((push_forward_many N S f) x) k)^2‖ₑ ∂μ := by
          apply lintegral_mono
          intro x
          simp
          rw [enorm_eq_ofReal_abs, enorm_eq_ofReal_abs]
          simp
          refine le_abs.mpr ?_
          left
          suffices : |∑ k ∈ (bound_set N).toFinset,
      (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2| = ∑ k ∈ (bound_set N).toFinset,
            (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2
          · rw[this]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            unfold bound_set
            simp
            intro k kh i
            specialize kh i
            linarith
            intros
            apply sq_nonneg
          simp
          apply Finset.sum_nonneg
          intros
          apply sq_nonneg
    _ = ∫⁻ (x : X), ‖∑' k : ι → ℕ, (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2‖ₑ ∂μ := by
          apply lintegral_congr
          intro x
          suffices : ∑ k ∈ (bound_set (2 * N)).toFinset,
      (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2 = ∑' (k : ι → ℕ), (discrete_avg a (push_forward_many N S f x) k - discrete_avg b (push_forward_many N S f x) k) ^ 2
          · rw[this]
          refine Eq.symm (tsum_eq_sum' ?_)
          intro u uh
          contrapose uh
          unfold bound_set at uh
          simp_all
          unfold push_forward_many push_forward
          unfold discrete_avg
          suffices : ∀ n : ℕ,  ∑ i ∈ Finset.range n,
        ∏ j : ι, ((fun j k ↦ (if ∀ (i : ι), k i < 2 * N then f j (iterate S k x) else 0)) j (u + unit j i)) = 0
          · rw[this a, this b]
            simp
          intro n
          apply Finset.sum_eq_zero
          intro k _
          simp
          obtain ⟨i,_⟩ := (exists_true_iff_nonempty (α := ι)).2 hι
          apply Finset.prod_eq_zero (i := i)
          · simp
          suffices : ¬∀ (i_1 : ι), u i_1 + unit i k i_1 < 2 * N
          · simp [this]
          simp
          obtain ⟨y,yh⟩ := uh
          use y
          linarith




--here make lemma about norm of pushfordward, which is needed for 5.7 (that the sum is sum over certain set and this set has cardinality 2^pN^p)
theorem fact5_7 [MeasurableSpace X](μ : Measure X)(q : ℝ)(hS: MMeasurePreserving μ S)(f : X → ℝ)(hf : Measurable f)(hq: 0 < q):--vermutlich kann man hq vermeiden, aber sonst mach 0^q probleme mit coercions, ein calc step ist dann au jeden fall einfach falsch wenn q=0 (der erste if i am not mistaken)
  ∫⁻ (x : X), ‖∑' (k : ι → ℕ), |(push_forward N S f x k)|^q‖ₑ ∂μ = 2^(Fintype.card ι) * N^(Fintype.card ι) * ∫⁻ x : X, ‖f x‖ₑ^q ∂μ := by
    by_cases hι: IsEmpty ι
    · unfold push_forward iterate iterate'
      simp
      apply lintegral_congr
      intro x
      rw[Real.enorm_rpow_of_nonneg]
      all_goals simp [hq, le_of_lt]
    simp at hι
    calc
      ∫⁻ (x : X), ‖∑' (k : ι → ℕ), |push_forward N S f x k| ^ q‖ₑ ∂μ
        = ∫⁻ (x : X), ∑' (k : ι → ℕ), ‖push_forward N S f x k‖ₑ^ q ∂μ := by
          apply lintegral_congr
          intro x
          rw[enorm_eq_ofReal_abs]
          have : |∑' (k : ι → ℕ), |push_forward N S f x k| ^ q| = ∑' (k : ι → ℕ), |push_forward N S f x k| ^ q := by
            simp
            apply tsum_nonneg
            intro k
            apply rpow_nonneg
            simp
          rw[this]
          clear this
          rw[ENNReal.ofReal_tsum_of_nonneg]
          · apply tsum_congr
            intro k
            rw[enorm_eq_ofReal_abs]
            rw[ENNReal.ofReal_rpow_of_nonneg] --warum 0 ≤ p nötig? wohl wegen 0 bruh
            simp
            exact le_of_lt hq

          intro k
          apply rpow_nonneg
          simp
          apply summable_of_finite_support
          suffices : support (fun k ↦ |push_forward N S f x k| ^ q) ⊆ bound_set (ι := ι) (2*N)
          · apply Set.Finite.subset (ht := this)
            exact toFinite (bound_set (2 * N))
          intro k kh
          contrapose kh
          unfold bound_set push_forward at *
          simp_all [-not_forall]
          rw[Real.zero_rpow]
          linarith
      _ = ∫⁻ (x : X), ∑ k ∈ bound_set (2*N), ‖push_forward N S f x k‖ₑ^ q ∂μ := by
          apply lintegral_congr
          intro x
          refine tsum_eq_sum' ?_
          intro k kh
          contrapose kh
          unfold bound_set push_forward at *
          simp_all [-not_forall]
      _ = ∑ k ∈ bound_set (2*N), ∫⁻ (x : X), ‖push_forward N S f x k‖ₑ^ q ∂μ := by
          rw[MeasureTheory.lintegral_finset_sum]
          intro b _
          apply Measurable.pow
          apply Measurable.enorm
          rename_i inst bh
          apply push_forward_measurable (N := N) (k := b) (S := S) (F := f) (hF := hf)
          unfold MMeasurePreserving at hS
          intro i
          exact (hS i).measurable
          fun_prop
      _ = ∑ k ∈ bound_set (ι := ι) (2*N), ∫⁻ (x : X), ‖f x‖ₑ^ q ∂μ := by
          apply Finset.sum_congr rfl
          intro k kh
          have : ∫⁻ (x : X), ‖push_forward N S f x k‖ₑ ^ q ∂μ = ∫⁻ (x : X), ‖f (iterate S k x)‖ₑ ^ q ∂μ := by
            apply lintegral_congr
            intro x
            unfold bound_set at kh
            unfold push_forward
            simp_all
          rw[this]
          apply MeasureTheory.MeasurePreserving.lintegral_comp (g := fun x ↦ iterate S k x) (f := fun x ↦ ‖f x‖ₑ^q)
          have : (fun x ↦ iterate S k x) = iterate S k := rfl
          rw[this]
          apply iterate_measurepreserving
          exact hS
          fun_prop [hf]
      _ = 2^(Fintype.card ι) * N^(Fintype.card ι) * ∫⁻ x : X, ‖f x‖ₑ^q ∂μ := by
          simp
          --have : Fintype.card (bound_set (2 * N)) = encard (α := ι → ℕ) (bound_set (ι := ι) (2*N)) := by
          have : (↑(Fintype.card (bound_set (ι := ι) (2 * N))) : ENNReal) = encard (α := ι → ℕ) (bound_set (ι := ι) (2*N)) := by
            suffices : Fintype.card (bound_set (ι := ι) (2 * N)) = encard (α := ι → ℕ) (bound_set (ι := ι) (2*N))
            · rw[← this]
              dsimp
            simp
          rw[this, bound_set_encard]
          simp
          rw[mul_pow]

--2 ^ q * ↑N ^ q * ∫⁻ (x : X), ‖f x‖ₑ ^ q ∂μ
--phew
lemma le_sum(f : ι → ℝ)(hf : 0 ≤ f)(i : ι): f i ≤ ∑ (j : ι), f j := by
  let g : ι → ℝ := fun j ↦ if i=j then f i else 0
  calc
    f i = ∑ j : ι, g j := by exact Eq.symm (Fintype.sum_ite_eq i fun j ↦ f i)
      _ ≤ ∑ j : ι, f j := by
        apply Finset.sum_le_sum
        intro j _
        unfold g
        by_cases ij: i = j
        · simp [ij]
        simp [ij]
        exact hf j

variable [Nonempty ι] [Nontrivial ι]

theorem fact5_8{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)(hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) --look at corollary 4 again and check
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(F : ι → (ι → ℕ) → ℝ)(hF: ∀(j : ι), Memℓp (F j) (((q j).toNNReal))):
    ∑ i : Fin m, ∑' a : ι → ℕ, (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2  ≤ --NOTE: ∑' does coercion to ℝ, at some point (Fact 5.4 or smth) note that this is summable
    (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m * ∑ (j : ι), (∑' a : ι → ℕ, |(F j a)|^(q j)) := by
      set h : ι → ℝ := fun j ↦ ∑' a : ι → ℕ, |(F j a)|^(q j)
      have : ∑ j, (∑' (a : ι → ℕ), |F j a| ^ (q j)) = ∑ j, h j := by unfold h; simp
      rw[this]
      clear this
      set C := (((256 * (Fintype.card ι)^3 * π ^2) / 3) + 2*(good_const hg)) * g m
      calc
        ∑ i : Fin m, ∑' a : ι → ℕ, (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2  ≤
          C * ∏ (j : ι), (h j)^(2/ (q j)) := discrete_ver hg hq m idx mon hidx hidx' F hF
        _ ≤ C * ∑ (j : ι), h j := by
          apply mul_le_mul_of_nonneg_left
          swap
          unfold C
          repeat apply mul_nonneg
          apply add_nonneg
          apply div_nonneg
          apply mul_nonneg
          all_goals try apply sq_nonneg
          all_goals try simp
          rw[← toFinset_univ]
          have hq': ∑ x, 2 / q x = 2 * ∑ x, 1 / q x := by
            rw [@Finset.mul_sum]
            simp
            apply Finset.sum_congr
            · rfl
            intros
            rw [@Field.div_eq_mul_inv]
          calc
            ∏ j ∈ univ.toFinset, (h j)^(2 / q j) = (∏ j ∈ univ.toFinset, ((h j) ^(2 / q j))) ^(∑ (j ∈ univ.toFinset), 2 / (q j))⁻¹ := by
                simp
                suffices : ∑ x, 2 / q x = 2 * ∑ x, 1 / q x
                · rw[this, hq.2]
                  simp
                exact hq'
              _ ≤ (∑ i ∈ univ.toFinset, 2 / q i * h i) / ∑ i ∈ univ.toFinset, 2 / q i := by
                apply Real.geom_mean_le_arith_mean
                intro i _
                simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, hq.1 i, le_of_lt]
                simp
                rw[hq', hq.2]
                simp
                intro i _
                unfold h
                apply tsum_nonneg
                intro j
                apply rpow_nonneg
                simp only [abs_nonneg]
              _= (∑ i ∈ univ.toFinset, 2 / q i * h i) := by
                simp only [toFinset_univ]
                rw[hq', hq.2]
                simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
                  div_one]
              _ ≤ ∑ j ∈ univ.toFinset, h j := by
                simp
                apply Finset.sum_le_sum
                intro i _
                rw[← one_mul (h i)]
                apply mul_le_mul
                all_goals try simp
                swap
                unfold h
                apply tsum_nonneg
                intro j
                apply rpow_nonneg
                simp only [abs_nonneg]
                rw[hq.2] at hq'
                simp at hq'
                calc
                  2 / q i ≤ ∑ x, 2 / q x := by
                      apply le_sum (f := fun i ↦ 2 / q i)
                      intro i
                      simp
                      apply div_nonneg
                      all_goals simp [hq.1 i, le_of_lt]
                    _ = 1 := hq'

omit [Nonempty ι] in
theorem goal' [h: Nonempty ι]{f : ι → X → ℝ}{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)[MeasurableSpace X](μ : Measure X)(hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(hS: MMeasurePreserving μ S)(hS': pairwise_commuting S)(hf: ∀(i : ι), Measurable (f i)): --(hf : ∀(i : ι), MeasureTheory.MemLp (f i) (q i) μ) Probably hf isnt needed, maybe (aestrongly)measurable or smth??? Something along those lines definetely (else integrals become zero on RHS)
    ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ ≤
    2^(Fintype.card ι) * (((256 * (Fintype.card ι)^3 * π ^2) / 3).toNNReal + 2*(good_const hg)) *
     g m * ∑(i : ι), (∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ)  := by
      set C := (↑(256 * (↑(Fintype.card ι) : ℝ) ^ 3 * π ^ 2 / 3).toNNReal : ENNReal) + 2 * ↑(good_const hg)
      let N := idx (⟨m, lt_add_one m⟩ : Fin (m+1)) + 1
      have hN: ∀(a : Fin (m+1)), idx a ≤ N := by
        intro a
        unfold N
        suffices : idx a ≤ idx (⟨m, lt_add_one m⟩ : Fin (m+1))
        · linarith
        apply mon
        obtain ⟨a,ah⟩ := a
        simp
        linarith
      calc
            ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ
        _ ≤ ∑ i : Fin m, 1 / N^(Fintype.card ι) * ∫⁻ (x : X), ‖(∑' k : ι → ℕ, (discrete_avg (idx i.succ) ((push_forward_many N S f) x) k - discrete_avg (idx ⟨i,get_rid i⟩) ((push_forward_many N S f) x) k)^2)‖ₑ ∂μ := by
            apply Finset.sum_le_sum
            intro i _
            apply fact5_6
            · exact hS'
            · exact hS
            · simp [hN]
            exact hf
        _ = 1 / N^(Fintype.card ι) * ∑ i : Fin m, ∫⁻ (x : X), ‖(∑' k : ι → ℕ, (discrete_avg (idx i.succ) ((push_forward_many N S f) x) k - discrete_avg (idx ⟨i,get_rid i⟩) ((push_forward_many N S f) x) k)^2)‖ₑ ∂μ := by rw [@Finset.mul_sum]
        _ = 1 / N^(Fintype.card ι) * ∫⁻ (x : X), ∑ i : Fin m, ‖(∑' k : ι → ℕ, (discrete_avg (idx i.succ) ((push_forward_many N S f) x) k - discrete_avg (idx ⟨i,get_rid i⟩) ((push_forward_many N S f) x) k)^2)‖ₑ ∂μ := by
            rw[MeasureTheory.lintegral_finset_sum]
            intro b _
            have : (fun x ↦ ‖∑' (k : ι → ℕ),
          (discrete_avg (idx b.succ) (push_forward_many N S f x) k -
              discrete_avg (idx ⟨↑b, get_rid b⟩) (push_forward_many N S f x) k) ^
            2‖ₑ) = (fun x ↦ ‖∑ k ∈ bound_set (2*N), (discrete_avg (idx b.succ) (push_forward_many N S f x) k -
              discrete_avg (idx ⟨↑b, get_rid b⟩) (push_forward_many N S f x) k) ^
            2‖ₑ) := by
              ext x
              suffices : ∑' (k : ι → ℕ),
          (discrete_avg (idx b.succ) (push_forward_many N S f x) k -
              discrete_avg (idx ⟨↑b, get_rid b⟩) (push_forward_many N S f x) k) ^
            2 = ∑ k ∈ bound_set (2*N), (discrete_avg (idx b.succ) (push_forward_many N S f x) k -
              discrete_avg (idx ⟨↑b, get_rid b⟩) (push_forward_many N S f x) k) ^
            2
              · rw[this]
              apply tsum_eq_sum
              intro k kh
              unfold push_forward_many discrete_avg
              suffices : ∀(n : ℕ), ∑ i ∈ Finset.range n, ∏ j, (fun j k ↦ push_forward N S (f j) x k) j (k + unit j i) = 0
              · rw[this, this]
                simp
              intro n
              apply Finset.sum_eq_zero
              intro i _
              obtain ⟨j,_⟩ := exists_true_iff_nonempty.2 h
              apply Finset.prod_eq_zero (i := j)
              · simp
              simp
              apply push_forward_not_in_bound_set
              contrapose kh
              unfold bound_set at *
              simp
              simp at kh
              intro x
              specialize kh x
              linarith
            rw[this]
            apply Measurable.comp
            · exact measurable_enorm
            refine Finset.measurable_sum (bound_set (2 * N)).toFinset ?_
            intro k _
            unfold push_forward_many
            refine Measurable.pow_const ?_ 2
            apply Measurable.sub
            repeat
              unfold discrete_avg
              apply Measurable.const_mul
              apply Finset.measurable_sum
              intro k' hk'
              apply Finset.measurable_prod
              intro j jh
              apply push_forward_measurable
              intro i
              exact (hS i).measurable
              exact hf j
        _ ≤ 1 / N^(Fintype.card ι) * ∫⁻ (x : X), C * ↑(g m) * ∑ (j : ι), ‖(∑' a : ι → ℕ, |((push_forward_many N S f) x) j a|^(q j))‖ₑ ∂μ := by
            gcongr
            unfold C
            rename_i x
            have : ∑ i : Fin m, ‖∑' (k : ι → ℕ), (discrete_avg (idx i.succ) (push_forward_many N S f x) k -
            discrete_avg (idx ⟨↑i, get_rid i⟩) (push_forward_many N S f x) k) ^
          2‖ₑ = ‖ ∑ i : Fin m, ∑' (k : ι → ℕ), (discrete_avg (idx i.succ) (push_forward_many N S f x) k -
            discrete_avg (idx ⟨↑i, get_rid i⟩) (push_forward_many N S f x) k) ^ 2‖ₑ := by
              refine Eq.symm ((fun {x y} hx hy ↦ (toReal_eq_toReal_iff' hx hy).mp) ?_ ?_ ?_)
              all_goals simp
              rw[ENNReal.toReal_sum]
              simp
              have : |∑ i : Fin m, ∑' (k : ι → ℕ), (discrete_avg (idx i.succ) (push_forward_many N S f x) k -
            discrete_avg (idx ⟨↑i, get_rid i⟩) (push_forward_many N S f x) k) ^ 2| = ∑ i : Fin m, ∑' (k : ι → ℕ), (discrete_avg (idx i.succ) (push_forward_many N S f x) k -
            discrete_avg (idx ⟨↑i, get_rid i⟩) (push_forward_many N S f x) k) ^ 2 := by
                simp
                apply Finset.sum_nonneg
                intros
                apply tsum_nonneg
                intros
                apply sq_nonneg
              rw[this]
              apply Finset.sum_congr rfl
              intros
              symm
              simp
              apply tsum_nonneg
              intros
              apply sq_nonneg
              intros
              simp
            rw[this]
            clear this
            have : (↑(256 * (↑(Fintype.card ι) : ℝ) ^ 3 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * ↑(g m) *
    ∑ j, ‖∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j‖ₑ = ‖(↑(256 * (↑(Fintype.card ι) : ℝ) ^ 3 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * ↑(g m) *
    ∑ j, ∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j‖ₑ := by
              rw[enorm_mul]
              congr
              · rw[enorm_mul]
                congr
                · refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
                  all_goals simp
                  · exact not_eq_of_beq_eq_false rfl
                  have : max (256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3) 0 = 256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3 := by
                    simp
                    apply div_nonneg
                    · apply mul_nonneg
                      · apply mul_nonneg
                        · norm_num
                        apply pow_nonneg
                        simp
                      apply sq_nonneg
                    norm_num
                  rw[this]
                  clear this
                  have : |256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3 + 2 * ↑(good_const hg)| = 256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3 + 2 * ↑(good_const hg) := by
                    simp
                    apply add_nonneg
                    · apply div_nonneg
                      · apply mul_nonneg
                        · apply mul_nonneg
                          · norm_num
                          apply pow_nonneg
                          simp
                        apply sq_nonneg
                      norm_num
                    norm_num
                  rw[this]
                  rw[ENNReal.toReal_add]
                  all_goals try simp
                  · apply div_nonneg
                    · apply mul_nonneg
                      · apply mul_nonneg
                        · norm_num
                        apply pow_nonneg
                        simp
                      apply sq_nonneg
                    norm_num
                  exact not_eq_of_beq_eq_false rfl
                simp
              rw [enorm_eq_ofReal_abs]
              have : |∑ j, ∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j| = ∑ j, ∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j := by
                simp
                apply Finset.sum_nonneg
                intros
                apply tsum_nonneg
                intros
                apply Real.rpow_nonneg
                simp
              rw[this]
              clear this
              rw[ENNReal.ofReal_sum_of_nonneg]
              · apply Finset.sum_congr rfl
                intro y _
                rw [enorm_eq_ofReal_abs]
                suffices : |∑' (a : ι → ℕ), |push_forward_many N S f x y a| ^ q y| = ∑' (a : ι → ℕ), |push_forward_many N S f x y a| ^ q y
                · rw[this]
                simp
                apply tsum_nonneg
                intros
                apply Real.rpow_nonneg
                simp
              intros
              apply tsum_nonneg
              intros
              apply Real.rpow_nonneg
              simp
            rw[this]
            clear this
            rw [enorm_eq_ofReal_abs, enorm_eq_ofReal_abs]
            simp
            have : max (256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3) 0 = 256 * ↑(Fintype.card ι) ^ 3 * π ^ 2 / 3 := by
              simp
              apply div_nonneg
              · apply mul_nonneg
                · apply mul_nonneg
                  · norm_num
                  apply pow_nonneg
                  simp
                apply sq_nonneg
              norm_num
            rw[this]
            clear this
            have : |∑ i : Fin m, ∑' (k : ι → ℕ), (discrete_avg (idx i.succ) (push_forward_many N S f x) k -
            discrete_avg (idx ⟨↑i, get_rid i⟩) (push_forward_many N S f x) k) ^ 2| = ∑ i : Fin m, ∑' (k : ι → ℕ), (discrete_avg (idx i.succ) (push_forward_many N S f x) k -
            discrete_avg (idx ⟨↑i, get_rid i⟩) (push_forward_many N S f x) k) ^ 2 := by
                simp
                apply Finset.sum_nonneg
                intros
                apply tsum_nonneg
                intros
                apply sq_nonneg
            rw[this]
            clear this
            apply le_abs.2
            left
            apply fact5_8 (hq := hq) (mon := mon) (hidx := hidx) (hidx' := hidx')
            intro i
            specialize hf i
            have : ¬q i ≤ 0 := by
              simp
              exact hq.1 i
            unfold Memℓp
            simp [this]
            clear this
            apply summable_of_finite_support
            have : max (q i) 0 = q i := by simp [hq.1 i, le_of_lt]
            rw[this]
            clear this
            apply Set.Finite.subset (s := bound_set (ι := ι) (2*N))
            · exact toFinite (bound_set (2 * N))
            intro k hk
            contrapose hk
            unfold support push_forward_many
            simp
            rw[push_forward_not_in_bound_set]
            · simp
              apply Real.zero_rpow
              have := hq.1 i
              contrapose this
              simp_all
            exact hk
        _ = 1 / N^(Fintype.card ι) * C * ↑(g m) * ∫⁻ (x : X), ∑ (j : ι), ‖(∑' a : ι → ℕ, |((push_forward_many N S f) x) j a|^(q j))‖ₑ ∂μ := by
            rw[MeasureTheory.lintegral_const_mul']
            · repeat rw[mul_assoc]
            exact Ne.symm (not_eq_of_beq_eq_false rfl)
        _ = 1 / N^(Fintype.card ι) * C * ↑(g m) * ∑ (j : ι), ∫⁻ (x : X), ‖(∑' a : ι → ℕ, |((push_forward_many N S f) x) j a|^(q j))‖ₑ ∂μ := by
            congr
            rw[MeasureTheory.lintegral_finset_sum]
            intro b _
            refine Measurable.enorm ?_
            have : (fun x ↦ ∑' (a : ι → ℕ), |push_forward_many N S f x b a| ^ q b) = (fun x ↦ ∑ a ∈ bound_set (2*N), |push_forward_many N S f x b a| ^ q b) := by
              ext x
              apply tsum_eq_sum
              intro k kh
              unfold push_forward_many
              rw[push_forward_not_in_bound_set (k := k) (S := S)]
              simp
              refine zero_rpow ?_
              by_contra
              obtain ⟨hq,_⟩ := hq
              specialize hq b
              repeat simp_all
            rw[this]
            refine Finset.measurable_sum (bound_set (2 * N)).toFinset ?_
            intro k _
            unfold push_forward_many
            refine Measurable.pow_const ?_ (q b)
            apply Measurable.abs
            apply push_forward_measurable
            intro i
            exact (hS i).measurable
            exact hf b
        _ = 1 / N^(Fintype.card ι) * C * ↑(g m) * ∑ (j : ι), (2^(Fintype.card ι) * N^(Fintype.card ι) * ∫⁻ x_1 : X, ‖f j x_1‖ₑ^(q j) ∂μ) := by
            suffices : ∑ j, ∫⁻ (x : X), ‖∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j‖ₑ ∂μ = ∑ (j : ι), (2^(Fintype.card ι) * N^(Fintype.card ι) * ∫⁻ x_1 : X, ‖f j x_1‖ₑ^(q j) ∂μ)
            · rw[this]
            apply Finset.sum_congr rfl
            intro i _
            rw[← fact5_7 (S := S)]
            · rfl
            · exact hS
            · exact hf i
            exact hq.1 i
        _ = 2 ^ Fintype.card ι * C * ↑(g m) * ∑ i, ∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ := by
            rw [← @Finset.mul_sum]
            repeat rw[← mul_assoc]
            congr 1
            have : 1 / ↑N ^ Fintype.card ι * C * ↑(g m) * 2 ^ Fintype.card ι * ↑N ^ Fintype.card ι
              = (1 / ↑N ^ Fintype.card ι * ↑N ^ Fintype.card ι) * 2 ^ Fintype.card ι * C * g m := by
                ring
            rw[this]
            clear this
            suffices : 1 / (↑N : ENNReal)^ Fintype.card ι * ↑N ^ Fintype.card ι = 1
            · rw[this]
              ring
            simp
            refine ENNReal.inv_mul_cancel ?_ ?_
            · simp
              intro hN'
              unfold N at hN'
              simp_all
            simp

omit [Nonempty ι] [Nontrivial ι] in
lemma ergodic_avg_mul(n : ℕ)(f : ι → X → ℝ)(h: ι → ℝ)(x : X): ergodic_avg n S (fun i y ↦ (h i) * (f i y)) x = (∏(i : ι), h i) * ergodic_avg n S f x := by
  unfold ergodic_avg nergodic_avg
  rw[← mul_assoc, mul_comm (∏ i, h i), mul_assoc]
  congr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp
  rw [@Finset.prod_mul_distrib]





theorem goal
  {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) [MeasurableSpace X] (μ : Measure X) (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)(hS: MMeasurePreserving μ S)(hS': pairwise_commuting S)(hf: ∀(i : ι), Measurable (f i)): --(hf : ∀(i : ι), MeasureTheory.MemLp (f i) (q i) μ) Probably hf isnt needed, maybe (aestrongly)measurable or smth??? Something along those lines definetely (else integrals become zero on RHS)
    ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ ≤
    (Fintype.card ι)*2^(Fintype.card ι) * (((256 * (Fintype.card ι)^3 * π ^2) / 3).toNNReal + 2*(good_const hg)) *
     g m * ∏(i : ι), (∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ)^(2/(q i))  := by
      by_cases hm: m = 0
      · have : IsEmpty (Fin m) := by rw[hm]; exact Fin.isEmpty'
        simp
      by_cases h': ∃(i : ι), ∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ = 0
      · obtain ⟨j,jh⟩ := h'
        have : ∏ i, (∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ) ^ (2 / q i) = 0 := by
          apply Finset.prod_eq_zero_iff.2
          use j
          simp [jh]
          exact hq.1 j
        rw[this]
        simp
        intro ⟨n,hn⟩
        refine (lintegral_eq_zero_iff ?_).mpr ?_
        · apply Measurable.pow
          apply Measurable.enorm
          suffices (r : Fin (m+1)): Measurable (fun x ↦ ergodic_avg (idx r) S f x)
          · apply Measurable.sub
            repeat simp [this]
          apply ergodic_avg_measurable
          all_goals try simp [*]
          intro j
          exact (hS j).measurable
        simp
        have : (0 : X → ENNReal) = fun (x : X) ↦ ‖(0 : ℝ)‖ₑ^2  := by
          ext
          simp
        rw[this]
        apply Filter.EventuallyEq.fun_comp (h := fun (x : ℝ) ↦ ‖x‖ₑ^2)
        clear this
        have g (r : Fin (m+1)): (fun x ↦ ergodic_avg (idx r) S f x) =ᶠ[ae μ] fun x ↦ 0 := by
          unfold ergodic_avg nergodic_avg
          have : (fun (x : X)↦ (0 : ℝ)) = (1 / ↑(idx r) * ∑ i ∈ Finset.range (idx r), (fun (x : X)↦ (0 : ℝ))) := by
            ext
            simp
          rw[this]
          apply Filter.EventuallyEq.mul
          · rfl
          have : (fun x ↦ ∑ i ∈ Finset.range (idx r), ∏ j, f j ((S j)^[i] x)) = (∑ i ∈ Finset.range (idx r), ∏ j, (fun x ↦  f j ((S j)^[i] x))) := by
            rw [← @Finset.sum_fn]
            apply Finset.sum_congr rfl
            intros
            rw[Finset.prod_fn]
          rw[this]
          clear this
          apply eventuallyEq_sum
          intro i _
          --refine (sub_ae_eq_zero (∏ j, fun x ↦ f j ((S j)^[i] x)) fun x ↦ 0).mp ?_

          --apply?
          --apply eventuallyEq_prod
          --intro j _
          have : (fun (x : X)↦ (0 : ℝ)) = (∏ i' : ι, (fun (x : X) ↦ if i' = j then 0 else (f i' ((S i')^[i] x)))) := by --maybe generalise this
            ext x
            simp
            symm
            apply Finset.prod_eq_zero (i := j)
            · exact Finset.mem_univ j
            simp
          rw[this]
          refine eventuallyEq_prod ?_
          intro j' _
          by_cases hj': j' = j
          all_goals simp [hj']
          clear this
          --have meas: Measurable fun x ↦ ‖f j x‖ₑ ^ q j := by sorry
          --apply (MeasureTheory.lintegral_eq_zero_iff meas).1 at jh
          --apply?
          have : (fun x ↦ ‖f j ((S j)^[i] x)‖ₑ) =ᵐ[μ] 0 := by
            apply ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero (p := q j)
            · exact le_of_lt (hq.1 j)
            · apply Measurable.aemeasurable
              apply Measurable.enorm
              apply Measurable.comp
              exact hf j
              apply Measurable.iterate
              exact (hS j).measurable
            rw[MeasureTheory.MeasurePreserving.lintegral_comp (μ := μ) (ν := μ) (g := (S j)^[i]) (f := fun x ↦ ‖f j x‖ₑ^(q j))]
            · exact jh
            apply MeasurePreserving.iterate
            · exact hS j
            apply Measurable.pow_const
            apply Measurable.enorm
            exact hf j
          exact (enorm_ae_zero_iff μ (fun x ↦ f j ((S j)^[i] x))).1 this
        have : (fun (x : X)↦ (0 : ℝ)) = (fun (x : X)↦ (0 : ℝ) - 0) := by simp
        rw[this]
        exact Filter.EventuallyEq.sub (g ⟨n + 1, Nat.succ_lt_succ hn⟩) (g ⟨n, get_rid ⟨n, hn⟩⟩)
      simp at h'
      set r := fun (i : ι) ↦ (∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ) ^ (1 / (q i))
      set C := ↑(Fintype.card ι) * 2 ^ Fintype.card ι * (↑(256 * (↑(Fintype.card ι) : ℝ) ^ 3 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * (↑(g m) : ENNReal)
      let C' := 2 ^ Fintype.card ι * (↑(256 * (↑(Fintype.card ι) : ℝ) ^ 3 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * (↑(g m) : ENNReal)
      by_cases h'': ∃i : ι, ∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ = ⊤
      · suffices : C * ∏ i, (∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ) ^ (2 / q i) = ⊤
        · rw[this]
          simp
        refine mul_eq_top.mpr ?_
        left
        constructor
        · unfold C
          simp
          constructor
          · intro hh
            contrapose hh
            simp
            apply _root_.mul_pos
            · apply _root_.mul_pos
              · norm_num
              apply pow_pos
              simp
              exact Fintype.card_pos
            refine sq_pos_of_pos ?_
            exact Real.pi_pos
          have := hg.1 m (Nat.one_le_iff_ne_zero.mpr hm)
          contrapose this
          simp_all
        apply (prod_eq_top_iff _ _).2
        simp [h', hq, h'']
        intro a _
        apply div_nonneg
        · norm_num
        exact le_of_lt (hq.1 a)
      simp at h''
      have rh: ∀ i : ι, r i ≠ ⊤ := by
        intro i
        specialize h'' i
        unfold r
        exact rpow_ne_top_of_ne_zero (h' i) h''
      have rh': ∀ i : ι, r i ≠ 0 := by
        intro i
        unfold r
        simp
        tauto
      calc
        ∑ i : Fin m, ∫⁻ (x : X), ‖ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨↑i, get_rid i⟩) S f x‖ₑ ^ 2 ∂μ
        _ = ∑ i : Fin m, ∫⁻ (x : X), ‖ergodic_avg (idx i.succ) S (fun j y ↦ (r j).toReal * ((f j y)/((r j).toReal))) x - ergodic_avg (idx ⟨↑i, get_rid i⟩) S (fun j y ↦ (r j).toReal * ((f j y)/((r j).toReal))) x‖ₑ ^ 2 ∂μ := by
          suffices : (fun j y ↦ (r j).toReal * ((f j y)/(r j).toReal)) = f
          · rw[this]
          ext j y
          have : (r j).toReal ≠ 0 := by
            have := hq.1 j
            contrapose this
            simp_all
            obtain hh|hh := (ENNReal.toReal_eq_zero_iff _).1 this
            · unfold r at hh
              simp at hh
              tauto
            unfold r at hh
            simp at hh
            tauto
          field_simp
        _ = ∑ i : Fin m, ∫⁻ (x : X), ‖(∏ i : ι, (r i).toReal) * (ergodic_avg (idx i.succ) S (fun j y ↦ ((f j y)/(r j).toReal)) x - ergodic_avg (idx ⟨↑i, get_rid i⟩) S (fun j y ↦ ((f j y)/(r j).toReal)) x)‖ₑ ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro n hn
          apply lintegral_congr
          intro x
          rw[ergodic_avg_mul, ergodic_avg_mul, mul_sub (∏ i, (r i).toReal)]
        _ = ∑ i : Fin m, ∫⁻ (x : X), ‖(∏ i : ι, (r i).toReal)‖ₑ^2 * ‖(ergodic_avg (idx i.succ) S (fun j y ↦ ((f j y)/(r j).toReal)) x - ergodic_avg (idx ⟨↑i, get_rid i⟩) S (fun j y ↦ ((f j y)/(r j).toReal)) x)‖ₑ ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro k _
          apply lintegral_congr
          intro x
          rw[← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_two]
          rw[← ENNReal.mul_rpow_of_nonneg]
          swap
          · simp only [Nat.ofNat_nonneg]
          congr
          rw [← @enorm_mul]
        _ = ∑ i : Fin m, ‖(∏ i : ι, (r i).toReal)‖ₑ^2 * ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S (fun j y ↦ ((f j y)/(r j).toReal)) x - ergodic_avg (idx ⟨↑i, get_rid i⟩) S (fun j y ↦ ((f j y)/(r j).toReal)) x)‖ₑ ^ 2 ∂μ := by
          apply Finset.sum_congr rfl
          intro k _
          rw[MeasureTheory.lintegral_const_mul]
          refine Measurable.pow_const ?_ 2
          apply Measurable.enorm
          apply Measurable.sub
          all_goals apply ergodic_avg_measurable
          fun_prop
          intro i
          exact (hS i).measurable
          fun_prop
          intro i
          exact (hS i).measurable
        _ = ‖∏ i : ι, (r i).toReal‖ₑ^2 *  ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S (fun j y ↦ ((f j y)/(r j).toReal)) x - ergodic_avg (idx ⟨↑i, get_rid i⟩) S (fun j y ↦ ((f j y)/(r j).toReal)) x)‖ₑ ^ 2 ∂μ := by rw[Finset.mul_sum]
        _ ≤ ‖∏ i : ι, (r i).toReal‖ₑ^2 * (2 ^ Fintype.card ι * (↑(256 * (↑(Fintype.card ι) : ℝ) ^ 3 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * ↑(g m) * ∑ i, ∫⁻ (x : X), ‖(fun j y ↦ f j y / (r j).toReal) i x‖ₑ ^ q i ∂μ) := by
          apply mul_le_mul
          · apply le_refl
          · apply goal' (f := (fun j y ↦ ((f j y)/(r j).toReal))) hg μ hq m idx mon hidx hidx' hS hS'
            intro i
            fun_prop
          · apply Finset.sum_nonneg
            intros
            (expose_names;
              exact
                zero_le
                  (∫⁻ (x : X),
                    ‖ergodic_avg (idx i.succ) S (fun j y ↦ f j y / (r j).toReal) x -
                          ergodic_avg (idx ⟨↑i, get_rid i⟩) S (fun j y ↦ f j y / (r j).toReal) x‖ₑ ^
                      2 ∂μ))
          exact zero_le (‖∏ i, (r i).toReal‖ₑ ^ 2)
        _ = ‖∏ i : ι, (r i).toReal‖ₑ^2 * (C' * ∑ i, ∫⁻ (x : X), ‖(fun j y ↦ f j y / (r j).toReal) i x‖ₑ ^ q i ∂μ) := by rfl
        _ = (∏ i : ι, (r i)^2) * (C' * ∑ i : ι, (∫⁻ (x : X), ‖(fun j y ↦ ((f j y)/(r j).toReal)) i x‖ₑ^(q i) ∂μ)) := by
          congr
          rw [enorm_eq_ofReal_abs]
          rw [@Finset.abs_prod]
          rw[ENNReal.ofReal_prod_of_nonneg]
          · rw [← ENNReal.rpow_two]
            rw [← ENNReal.prod_rpow_of_nonneg]
            apply Finset.prod_congr rfl
            intro i _
            simp
            congr 1
            refine ofReal_toReal_eq_iff.mpr ?_
            exact rh i
            simp
          simp only [Finset.mem_univ, abs_nonneg, imp_self, implies_true]
        _ = (∏ i : ι, (r i)^2) * (C' * ∑ i : ι, 1) := by
          congr
          ext i
          simp
          calc
            ∫⁻ (x : X), ‖f i x / (r i).toReal‖ₑ ^ q i ∂μ
            _ = ∫⁻ (x : X), (‖f i x‖ₑ/ ‖(r i).toReal‖ₑ) ^ q i ∂μ := by
              congr
              ext x
              congr
              repeat rw[enorm_eq_ofReal_abs]
              rw[← ENNReal.ofReal_div_of_pos]
              congr
              rw [@abs_div]
              by_contra h0
              simp at h0
              have : (r i).toReal = 0 := by
                apply le_antisymm
                · exact h0
                simp only [toReal_nonneg]
              apply (ENNReal.toReal_eq_zero_iff (r i)).1 at this
              tauto
            _ = ∫⁻ (x : X), (‖f i x‖ₑ^(q i)/ ‖(r i).toReal‖ₑ^(q i)) ∂μ := by
              apply lintegral_congr
              intro x
              refine div_rpow_of_nonneg ‖f i x‖ₑ ‖(r i).toReal‖ₑ ?_
              exact le_of_lt (hq.1 i)
            _ = ∫⁻ (x : X), ((1/‖(r i).toReal‖ₑ^(q i)) * ‖f i x‖ₑ^(q i)) ∂μ := by
              apply lintegral_congr
              intro x
              simp
              exact ENNReal.div_eq_inv_mul
            _ = (1/‖(r i).toReal‖ₑ^(q i)) * ∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ := by
              rw[lintegral_const_mul]
              fun_prop
            _ = (1/((r i)^(q i))) * ∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ := by
              congr
              rw [Real.enorm_eq_ofReal_abs]
              have : |(r i).toReal| = (r i).toReal := by
                unfold r
                simp
              rw[this]
              simp [rh i]
            _ = (1/((r i)^(q i))) * (r i)^(q i) := by
              congr
              unfold r
              rw[← ENNReal.rpow_mul]
              suffices: (1 / q i * q i) = 1
              · rw[this, ENNReal.rpow_one]
              simp
              refine inv_mul_cancel₀ ?_
              have := hq.1 i
              contrapose this
              simp_all
            _ = 1 := by
              simp
              refine ENNReal.inv_mul_cancel ?_ ?_
              · simp
                tauto
              simp
              tauto
        _ = C * ∏ i, (∫⁻ (x : X), ‖f i x‖ₑ ^ q i ∂μ) ^ (2 / q i) := by
          simp
          rw[mul_comm]
          congr 1
          · unfold C C'
            ring
          apply Finset.prod_congr rfl
          intro i _
          unfold r
          have : 2 / q i = 2 * (1/ q i) := by
            have : q i ≠ 0 := by
              have := hq.1 i
              contrapose this
              simp_all
            field_simp
          rw[this, mul_comm 2, ENNReal.rpow_mul]
          simp

/-The same theorem with the constant stated implicitly:-/

theorem og_goal
    {ι X : Type*} [Fintype ι] [Nontrivial ι] [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → NNReal} {q : ι → ℝ} (hg: good g q) {f : ι → X → ℝ} {S : ι → X → X}
    (hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
    (m : ℕ) (idx : Fin (m+1) → ℕ) (mon : Monotone idx) (hidx : Injective idx) (hidx': 0 < idx 0)
    (hS: MMeasurePreserving μ S) (hS': pairwise_commuting S) (hf: ∀(i : ι), Measurable (f i)):
    ∃ C : NNReal, ∑ i : Fin m, ∫⁻ (x : X),
    ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ ≤
    C * g m * ∏(i : ι), (∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ)^(2/(q i))  := by
  use (Fintype.card ι) * 2 ^(Fintype.card ι) * (((256 * (Fintype.card ι) ^ 3 * π ^ 2) / 3).toNNReal + 2 * (good_const hg))
  exact goal f hg μ hq m idx mon hidx hidx' hS hS' hf



end Calderon
#min_imports
