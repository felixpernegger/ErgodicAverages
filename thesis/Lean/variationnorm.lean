import Mathlib
open Function Set
noncomputable section
set_option linter.style.commandStart false


open scoped NNReal ENNReal Topology UniformConvergence
open Set Filter

/-
class PseudoEMetricSpace (α : Type u) : Type u extends EDist α  where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by rfl
-/
universe u

class WeakPseudoEMetricSpace (α : Type u) : Type u extends EDist α where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z

instance {α : Type*} [PseudoEMetricSpace α] : WeakPseudoEMetricSpace α where
  edist := edist
  edist_self := fun x ↦ edist_self x
  edist_comm := fun x ↦ edist_comm x
  edist_triangle := fun x ↦ edist_triangle x

instance : WeakPseudoEMetricSpace ℝ≥0∞ where
  edist := fun x y ↦ (x - y) + (y - x)
  edist_self := by simp only [tsub_self, add_zero, implies_true]
  edist_comm := by simp only [add_comm, implies_true]
  edist_triangle := by
    intro x y z
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

namespace VariationNorm

section lp_enorm
variable {J : Type*} {B : Type*} [EDist B] (I I' : Set J) (a : J → B) (r : ℝ≥0∞)

def diff_fun (n : ℕ) (t : ℕ → J) (a : J → B): Fin n → ℝ≥0∞ :=
  fun i ↦ edist (a (t (i.val + 1))) (a (t i.val))


/-Lp norm : I didnt find a proper versions for sums,
only for measures. TODO: Replace this definition-/
variable {α : Type*} (p : ℝ≥0∞) (f : α → ℝ≥0∞)
def lp_enorm : ℝ≥0∞ :=
  if p = 0 then
    (Function.support f).encard
  else if p = ∞ then
    ⨆ a : α, f a
  else
    (∑' x : α, (f x) ^ p.toReal) ^ (p.toReal)⁻¹


theorem lp_enorm_zero : lp_enorm 0 f = (Function.support f).encard := by
  unfold lp_enorm
  simp only [↓reduceIte]


theorem lp_enorm_top : lp_enorm ∞ f = ⨆ a : α, f a := by
  unfold lp_enorm
  simp only [ENNReal.top_ne_zero, ↓reduceIte]

theorem lp_enorm_ne_zero_ne_top (h : p ≠ 0) (h': p ≠ ∞):
    lp_enorm p f = (∑' x : α, (f x) ^ p.toReal) ^ (p.toReal)⁻¹ := by
  unfold lp_enorm
  simp only [↓reduceIte, h, h']

theorem lp_enorm_ne_zero_ne_top_finitype [Fintype α] (h : p ≠ 0) (h': p ≠ ∞) :
    lp_enorm p f = (∑ x : α, (f x) ^ p.toReal) ^ (p.toReal)⁻¹ := by
  rw[lp_enorm_ne_zero_ne_top p f h h', tsum_fintype fun b ↦ f b ^ p.toReal]

end lp_enorm

variable {J : Type*} {B : Type*}
  [LinearOrder J] [WeakPseudoEMetricSpace B] (I I' : Set J) (a : J → B) (r r' : ℝ≥0∞)
/-
noncomputable def eVariationOn (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))-/

def r_eVariationOn
    (r : ℝ≥0∞) {J B : Type*} [LinearOrder J] [WeakPseudoEMetricSpace B] (I : Set J) (a : J → B):
      ℝ≥0∞ :=
  ⨆ p : ℕ  × { t : ℕ → J // Monotone t ∧ ∀ i, t i ∈ I}, lp_enorm r (diff_fun p.1 p.2.1 a)

#check r_eVariationOn


instance eVartionOnTypeInhabited (h : I.Nonempty):
    Inhabited (ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I }) := by
  refine { default := ?_ }
  constructor
  · exact 0
  refine Classical.indefiniteDescription (fun x ↦ Monotone x ∧ ∀ (i : ℕ), x i ∈ I) ?_
  use fun x ↦ h.some
  constructor
  · exact monotone_const
  intros
  exact Nonempty.some_mem h

theorem r_eVariationOn_mono (h : I ⊆ I'):
    r_eVariationOn r I a ≤ r_eVariationOn r I' a := by
  unfold r_eVariationOn
  refine iSup_mono' ?_
  intro ⟨n, u, mon, mem⟩
  use ⟨n, u, mon, fun i ↦ h (mem i)⟩

@[simp] theorem r_eVariationOn_emptyset :
    r_eVariationOn r ∅ a = 0 := by
  unfold r_eVariationOn
  simp only [ENNReal.iSup_eq_zero, Prod.forall, Subtype.forall, mem_empty_iff_false, forall_const,
    and_false, IsEmpty.forall_iff, implies_true]

theorem r_eVariationOn_pow_r_mono (h : I ⊆ I'):
    (r_eVariationOn r I a)^r.toReal ≤ (r_eVariationOn r I' a)^r.toReal := by
  gcongr
  exact r_eVariationOn_mono I I' a r h

theorem r_eVariationOn_ne_zero_ne_top (h : r ≠ 0) (h' : r ≠ ∞):
    r_eVariationOn r I a = ⨆ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)^r.toReal⁻¹ := by
  unfold r_eVariationOn
  congr
  ext p
  rw[lp_enorm_ne_zero_ne_top r _ h h']
  congr
  unfold diff_fun
  rw[tsum_fintype, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x xh
  simp only [Finset.mem_range] at xh
  simp only [xh, ↓reduceDIte]

/-So r=1 gives us exactly the eVariation-/

theorem r_eVariationOn_one_eq_eVariationOn {B : Type*} [PseudoEMetricSpace B] (a : J → B) :
    r_eVariationOn 1 I a = eVariationOn a I := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, ENNReal.one_ne_top,
    r_eVariationOn_ne_zero_ne_top, ENNReal.toReal_one, ENNReal.rpow_one, inv_one, eVariationOn]
#check ENNReal.le_of_forall_pos_le_add

theorem iSup_cont_ennreal'
    (s : Set ℝ≥0∞) (g : ℝ≥0∞ → ℝ≥0∞) (h : Continuous g) (h' : Monotone g):
    ⨆ a ∈ s, g a = g (⨆ a ∈ s, a) := by
  sorry

theorem iSup_cont_ennreal
    {α : Type*} (f : α → ℝ≥0∞) (g : ℝ≥0∞ → ℝ≥0∞) (h : Continuous g) (h' : Monotone g):
    (⨆ a : α, g (f a)) = g (⨆ a : α, (f a)) := by
  apply le_antisymm
  · exact Monotone.le_map_iSup h'
  apply ENNReal.le_of_forall_pos_le_add
  intro ε εp h
  have : g (⨆ a, f a) < ⊤ := by
    contrapose! h
    simp_all only [top_le_iff]
    refine ENNReal.eq_top_of_forall_nnreal_le ?_
    intro r
    contrapose h
    simp_all only [not_le]
    suffices: g (⨆ a, f a) ≤ r
    · contrapose this
      simp_all only [Decidable.not_not, top_le_iff, ENNReal.coe_ne_top, not_false_eq_true]
    sorry
  sorry

theorem iSup_pow_ennreal {α : Type*} (f : α → ℝ≥0∞) (p : ℝ) (hp: 0 ≤ p):
    (⨆ a : α, (f a)^p) = (⨆ a : α, (f a))^p := by
  apply iSup_cont_ennreal (g := fun x ↦ x^p)
  · exact ENNReal.continuous_rpow_const
  exact ENNReal.monotone_rpow_of_nonneg hp

theorem r_eVariationOn_ne_zero_ne_top' (h : r ≠ 0) (h' : r ≠ ∞):
    r_eVariationOn r I a = (⨆ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    (∑ i ∈ Finset.range p.1, edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal))^(r.toReal⁻¹) := by
  rw[r_eVariationOn_ne_zero_ne_top I a r h h', iSup_pow_ennreal]
  simp only [inv_nonneg, ENNReal.toReal_nonneg]

theorem r_eVariationOn_pow_r_eq_sup (h : r ≠ 0) (h' : r ≠ ∞) :
    (r_eVariationOn r I a)^r.toReal = (⨆ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    (∑ i ∈ Finset.range p.1, edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)) := by
  rw[r_eVariationOn_ne_zero_ne_top' I a r h h', ← ENNReal.rpow_mul]
  have : (r.toReal⁻¹ * r.toReal) = 1 := by
    refine (inv_mul_eq_one₀ ?_).mpr rfl
    exact ENNReal.toReal_ne_zero.mpr ⟨h,h'⟩
  simp only [this, ENNReal.rpow_one]

theorem sum_le_eVariationOn' (p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I })
    (h : r ≠ 0) (h' : r ≠ ∞) :
    (∑ i ∈ Finset.range p.1,
    edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r.toReal)^r.toReal⁻¹ ≤
    (r_eVariationOn r I a) := by
  rw[r_eVariationOn_ne_zero_ne_top I a r h h']
  exact le_iSup_iff.mpr fun b a ↦ a p

theorem sum_le_eVariationOn
    (h : r ≠ 0) (h' : r ≠ ∞) (m : ℕ) {u : ℕ → J} (mon : Monotone u) (hu : ∀ i, u i ∈ I) :
    (∑ i ∈ Finset.range m, edist (a (u (i + 1))) (a (u i))^r.toReal)^(r.toReal⁻¹)
    ≤ r_eVariationOn r I a := by
      rw[r_eVariationOn_ne_zero_ne_top' I a r h h']
      gcongr
      let p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I } := ⟨m, ⟨u, mon, hu⟩⟩
      have : ∑ i ∈ Finset.range m, edist (a (u (i + 1))) (a (u i)) ^ r.toReal =
          ∑ i ∈ Finset.range p.1,
          edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r.toReal := by
        congr
      rw[this]
      exact le_iSup_iff.mpr fun b a ↦ a p

theorem sum_le_eVariationOn_pow_r' (p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I })
    (h : r ≠ 0) (h' : r ≠ ∞) :
    ∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r.toReal ≤
    (r_eVariationOn r I a)^r.toReal := by
  rw[r_eVariationOn_pow_r_eq_sup I a r h h']
  exact le_iSup_iff.mpr fun b a ↦ a p

theorem sum_le_eVariationOn_pow_r
    (h : r ≠ 0) (h' : r ≠ ∞) (m : ℕ) {u : ℕ → J} (mon : Monotone u) (hu : ∀ i, u i ∈ I) :
    (∑ i ∈ Finset.range m, edist (a (u (i + 1))) (a (u i))^r.toReal)
    ≤ (r_eVariationOn r I a)^r.toReal := by
  rw[r_eVariationOn_pow_r_eq_sup I a r h h']
  let p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I } := ⟨m, ⟨u, mon, hu⟩⟩
  have : ∑ i ∈ Finset.range m, edist (a (u (i + 1))) (a (u i)) ^ r.toReal =
      ∑ i ∈ Finset.range p.1,
      edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r.toReal := by
    congr
  rw[this]
  exact le_iSup_iff.mpr fun b a ↦ a p

open Fin.NatCast

variable (m : ℕ) (u : Fin (m + 1) → J)

def extend_fun : ℕ → J :=
  fun n ↦ if hn : n < m + 1 then u ⟨n, hn⟩ else u m

lemma extend_fun_mon (mon : Monotone u) : Monotone (extend_fun m u) := by
  intro x y xy
  unfold extend_fun
  by_cases hy : y < m + 1
  · simp only [Nat.lt_of_le_of_lt xy hy, ↓reduceDIte, hy]
    exact mon xy
  by_cases hx : x < m + 1
  · simp only [hx, ↓reduceDIte, hy, Fin.natCast_eq_last]
    apply mon
    exact Fin.le_last ⟨x, of_eq_true (eq_true hx)⟩
  simp only [hx, ↓reduceDIte, Fin.natCast_eq_last, hy, le_refl]

omit [LinearOrder J] in
lemma extend_fun_mem (hu : ∀ i, u i ∈ I) : ∀ i, (extend_fun m u) i ∈ I := by
  intro i
  unfold extend_fun
  by_cases hi: i < m + 1 <;> simp only [hi, ↓reduceDIte] <;> apply hu

omit [LinearOrder J] in
lemma extend_fun_sum :
    ∑ i : Fin m, edist (a (u (i.succ))) (a (u (↑i : Fin (m+1))))^r.toReal =
    ∑ i ∈ Finset.range m, (edist (a (extend_fun m u (i + 1))) (a (extend_fun m u i)))^r.toReal := by
  rw [@Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x xh
  simp only [Finset.mem_range] at xh
  unfold extend_fun
  simp [xh, Nat.lt_add_right 1 xh]
  congr
  exact Fin.natCast_eq_mk (of_eq_true (eq_true (Nat.lt_add_right 1 xh)))


section pair_fun

variable (j j' : ↑I)

def pair_fun : Fin 2 → J :=
  fun n ↦ if n = 0 then min j j' else max j j'

lemma pair_fun_mon : Monotone (pair_fun I j j') := by
  intro x y xy
  unfold pair_fun
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · simp only [hx, Fin.isValue, ↓reduceIte, hy, le_refl]
    simp only [hx, Fin.isValue, ↓reduceIte, hy, le_sup_iff, inf_le_left, inf_le_right, or_self]
  by_cases hy : y = 0
  · contrapose hx
    simp_all only [Fin.isValue, Fin.le_zero_iff, Nat.reduceAdd, ↓reduceIte, le_refl,
      not_true_eq_false]
  simp only [Fin.isValue, hx, ↓reduceIte, hy, le_refl]

lemma pair_fun_mem : ∀ i, (pair_fun I j j') i ∈ I := by
  intro i
  unfold pair_fun
  by_cases hi : i = 0
  · simp only [Fin.isValue, ↓reduceIte, hi]
    by_cases jj': j ≤ j'
    · simp_all only [Fin.isValue, Subtype.coe_le_coe, inf_of_le_left, Subtype.coe_prop]
    have :  min (↑j : J) (↑j' : J) = j' := by
      simp only [inf_eq_right]
      apply le_of_lt
      simp_all only [Fin.isValue, not_le, Subtype.coe_lt_coe]
    rw[this]
    exact Subtype.coe_prop j'
  simp only [Fin.isValue, hi, ↓reduceIte]
  by_cases jj': j ≤ j'
  · have :  max (↑j : J) (↑j' : J) = j' := by
      simp_all only [Fin.isValue, Subtype.coe_le_coe, sup_of_le_right]
    rw[this]
    exact Subtype.coe_prop j'
  have :  max (↑j : J) (↑j' : J) = j := by
    simp only [sup_eq_left]
    apply le_of_lt
    simp_all only [Fin.isValue, not_le, Subtype.coe_lt_coe]
  rw[this]
  exact Subtype.coe_prop j

def pair_fun' : ℕ × { t // Monotone t ∧ ∀ (i : ℕ), t i ∈ I } :=
    ⟨2, extend_fun 1 (pair_fun I j j'),
    extend_fun_mon 1 (pair_fun I j j') (pair_fun_mon I j j'),
    fun i ↦ extend_fun_mem I 1 (pair_fun I j j') (pair_fun_mem I j j') i⟩

end pair_fun

theorem infty_eVariationOn_eq_sup_edist :
    (r_eVariationOn ∞ I a) = ⨆ j : I × I, edist (a j.1) (a j.2) := by
  unfold r_eVariationOn lp_enorm diff_fun
  simp only [ENNReal.top_ne_zero, ↓reduceIte]
  apply le_antisymm
  · refine iSup₂_le_iff.mpr ?_
    intro p j
    refine le_iSup_iff.mpr ?_
    intro b bh
    have (n : ℕ) : ((↑p.2 : ℕ → J) n) ∈ I := by
      obtain ⟨_, _, _, _⟩ := p
      simp_all only [Prod.forall, Subtype.forall]
    let k : ↑I × ↑I :=
      ⟨⟨((↑p.2 : ℕ → J) (↑j + 1)), this (↑j + 1)⟩, ⟨((↑p.2 : ℕ → J) (↑j)), this ↑j⟩⟩
    suffices :
      edist (a ↑k.1) (a ↑k.2) = edist (a ((↑p.2 : ℕ → J) ((↑j : ℕ) + 1))) (a ((↑p.2 : ℕ → J) ↑j))
    · rw[this]
      exact bh k
    unfold k
    simp only
  refine iSup_le_iff.mpr ?_
  intro ⟨j, j'⟩
  refine le_iSup_iff.mpr ?_
  intro b bh
  let p : ℕ × { t // Monotone t ∧ ∀ (i : ℕ), t i ∈ I } := pair_fun' I j j'
  suffices : edist (a ↑(j, j').1) (a ↑(j, j').2) =
    ⨆ a_1 : Fin p.1, edist (a ((↑p.2 : ℕ → J) (↑a_1 + 1))) (a ((↑p.2 : ℕ → J) ↑a_1))
  · rw[this]
    exact bh p
  unfold p
  simp only
  have :  edist (a ↑j) (a ↑j') =
    edist (a (pair_fun I j j' (↑(0 : Fin 2) + 1))) (a (pair_fun I j j' ↑(0 : Fin 2))) := by
    unfold pair_fun
    simp only [Fin.isValue, zero_add, one_ne_zero, ↓reduceIte]
    by_cases jj' : (↑j : J) ≤ ↑j'
    · simp only [jj', sup_of_le_right, inf_of_le_left]
      exact WeakPseudoEMetricSpace.edist_comm (a ↑j) (a ↑j')
    simp_all only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp, Subtype.coe_le_coe, not_le,
      Subtype.coe_lt_coe, le_of_lt, sup_of_le_left, inf_of_le_right]
  apply le_antisymm
  · rw[this]
    apply le_iSup_iff.mpr
    intro b h
    have : (pair_fun' I j j').1 = 2 := by
      unfold pair_fun'
      simp
    rw[this] at h
    exact h 0
  refine iSup_le_iff.mpr ?_
  intro ⟨i, ih⟩
  by_cases i0: i = 0
  · simp_all only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp, pair_fun, Fin.isValue,
    zero_add, one_ne_zero, ↓reduceIte, pair_fun', extend_fun, Nat.reduceAdd, Nat.one_lt_ofNat,
    ↓reduceDIte, Fin.mk_one, Nat.ofNat_pos, Fin.zero_eta, le_refl]
  have i1: i = 1 := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ ih
    exact Nat.one_le_iff_ne_zero.mpr i0
  simp_all only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp, pair_fun, Fin.isValue, zero_add,
    one_ne_zero, ↓reduceIte, not_false_eq_true, pair_fun', Nat.reduceAdd, extend_fun,
    lt_self_iff_false, ↓reduceDIte, Nat.cast_one, Nat.one_lt_ofNat, Fin.mk_one, ge_iff_le]
  rw [WeakPseudoEMetricSpace.edist_self]
  simp only [zero_le]

theorem fin_sum_le_eVariationOn
    (h : r ≠ 0) (h' : r ≠ ∞) (mon : Monotone u) (hu : ∀ i, u i ∈ I) :
    (∑ i : Fin m, edist (a (u (i.succ))) (a (u (↑i : Fin (m+1))))^r.toReal)^(r.toReal⁻¹)
    ≤ r_eVariationOn r I a := by
  rw[extend_fun_sum]
  exact sum_le_eVariationOn I a r h h' m (extend_fun_mon m u mon) (extend_fun_mem I m u hu)

theorem pair_le_eVariationOn_infty (j : I × I) :
    edist (a j.1) (a j.2) ≤ r_eVariationOn ∞ I a := by
  rw[infty_eVariationOn_eq_sup_edist]
  exact le_iSup_iff.mpr fun b a ↦ a j

theorem r_eVariationOn_infty_infty (h : r_eVariationOn ∞ I a = ∞) (L : ℝ≥0):
    ∃ j : ↑I × ↑I, L < edist (a j.1) (a j.2) := by
  rw[infty_eVariationOn_eq_sup_edist] at h
  refine lt_iSup_iff.mp ?_
  rw[h]
  simp only [ENNReal.coe_lt_top]

theorem eVariationOn_infty
    (h : r ≠ 0) (h' : r ≠ ∞) (hv : r_eVariationOn r I a = ∞) (L : ℝ≥0) :
    ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    L < (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)^(r.toReal⁻¹) := by
  rw[r_eVariationOn_ne_zero_ne_top I a r h h'] at hv
  refine lt_iSup_iff.mp ?_
  rw[hv]
  simp only [ENNReal.coe_lt_top]

theorem eVariationOn_infty'
    (h : r ≠ 0) (h' : r ≠ ∞) (hv : r_eVariationOn r I a = ∞) (L : ℝ≥0) :
    ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    L < (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal) := by
  obtain ⟨p, hp⟩ := eVariationOn_infty I a r h h' hv (L^(r.toReal)⁻¹)
  use p
  apply (ENNReal.rpow_lt_rpow_iff (z := r.toReal⁻¹) ?_).mp
  · have : (↑L : ℝ≥0∞)^ r.toReal⁻¹ = (↑(L ^ r.toReal⁻¹) : ℝ≥0∞) := by
      apply ENNReal.rpow_ofNNReal
      simp only [inv_nonneg, ENNReal.toReal_nonneg]
    rw[this]
    exact hp
  simp only [inv_pos, ENNReal.toReal_pos h h']

theorem eVariationOn_infty''
    (h : r ≠ 0) (h' : r ≠ ∞) (hv : r_eVariationOn r I a = ∞) (L : ℝ≥0) :
    ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    L < (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)^r.toReal⁻¹ := by
  obtain ⟨p, hp⟩ := eVariationOn_infty' I a r h h' hv (L^r.toReal)
  use p
  refine (ENNReal.lt_rpow_inv_iff ?_).mpr ?_
  · exact ENNReal.toReal_pos h h'
  have : (↑(L ^ r.toReal) : ℝ≥0∞) = ((↑L : ℝ≥0∞) ^ r.toReal) := by
    refine Eq.symm (ENNReal.rpow_ofNNReal ?_)
    simp only [ENNReal.toReal_nonneg]
  rw[← this]
  exact hp

lemma ENNReal_add_eq_left (a b : ENNReal) : a + b ≤ a ↔ a = ∞ ∨ b = 0 := by
  constructor
  · intro h
    contrapose h
    simp_all only [not_or, not_le]
    nth_rw 1[← add_zero a]
    refine ENNReal.add_lt_add_left h.1 ?_
    exact pos_of_ne_zero h.2
  intro h
  obtain h|h := h <;> rw[h] <;> simp only [top_add, add_zero , le_refl]


lemma ENNReal_sup_lt_infty
    {α : Type*} [Inhabited α] {f : α → ℝ≥0∞}
    (h : ⨆ a : α, f a ≠ ∞) {ε : NNReal} (hε : 0 < ε) :
    ∃ b : α, ⨆ a : α, f a < f b + ε := by
  by_contra h0
  simp only [not_exists, not_lt] at h0
  have : ⨆ a, f a ≤ (⨆ a, f a) - ε := by
    refine iSup_le ?_
    intro x
    specialize h0 x
    contrapose h0
    simp_all only [not_le]
    by_cases h1: (⨆ a, f a) < ε
    · calc
        ⨆ a, f a < ε := by exact h1
               _ ≤ f x + ε := le_add_self
    simp only [not_lt] at h1
    rw[Eq.symm (tsub_add_cancel_of_le h1)]
    refine (ENNReal.add_lt_add_iff_right ?_).mpr h0
    simp only [ne_eq, ENNReal.coe_ne_top, not_false_eq_true]
  contrapose this
  simp only [not_le]
  refine ENNReal.sub_lt_self ?_ ?_ ?_
  · exact h
  · contrapose h0
    simp_all only [not_false_eq_true, ne_eq, ENNReal.iSup_eq_zero, not_forall,
      not_exists, Decidable.not_not, zero_add, ciSup_const, nonpos_iff_eq_zero, ENNReal.coe_eq_zero,
      forall_const]
    exact pos_iff_ne_zero.mp hε
  simp only [ne_eq, ENNReal.coe_eq_zero]
  contrapose hε
  simp_all only [not_false_eq_true, Decidable.not_not, lt_self_iff_false]

theorem eVariationOn_pow_r_lt_infty (h : r ≠ 0) (h' : r ≠ ∞)
    (hv : r_eVariationOn r I a ≠ ∞) {ε : NNReal} (hε : 0 < ε) (hI: I.Nonempty):
    ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I }, (r_eVariationOn r I a)^r.toReal <
    (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal) + ε := by
  have powr: (r_eVariationOn r I a)^r.toReal ≠ ∞ := by
    contrapose hv
    simp_all only [ne_eq, ENNReal.rpow_eq_top_iff, not_or, not_and, not_lt,
      ENNReal.toReal_nonneg, implies_true, true_and, Classical.not_imp, not_le, not_true_eq_false,
      not_false_eq_true]
  rw[r_eVariationOn_pow_r_eq_sup I a r h h'] at *
  have : Inhabited (ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I }) := by
    apply eVartionOnTypeInhabited
    exact hI
  exact (ENNReal_sup_lt_infty (h := powr) (hε := hε))


theorem eVariationOn_lt_infty (h : r ≠ 0) (h' : r ≠ ∞)
    (hv : r_eVariationOn r I a ≠ ∞) {ε : NNReal} (hε : 0 < ε) (hI: I.Nonempty):
    ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I }, r_eVariationOn r I a <
    (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)^(r.toReal⁻¹) + ε := by
  rw[r_eVariationOn_ne_zero_ne_top I a r h h'] at *
  have : Inhabited (ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I }) := by
    apply eVartionOnTypeInhabited
    exact hI
  exact (ENNReal_sup_lt_infty (h := hv) (hε := hε))

theorem eVariationOn_infty_lt_infty
    (hv : r_eVariationOn ∞ I a ≠ ∞) {ε : NNReal} (hε : 0 < ε) (hI: I.Nonempty):
    ∃ j : I × I, r_eVariationOn ∞ I a <
    edist (a j.1) (a j.2) + ε := by
  rw [@infty_eVariationOn_eq_sup_edist] at *
  have : Inhabited (↑I × ↑I) := by
    refine Classical.inhabited_of_nonempty ?_
    refine nonempty_prod.mpr ?_
    constructor <;> exact Nonempty.to_subtype hI
  exact (ENNReal_sup_lt_infty (h := hv) (hε := hε))


def comb : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I } →
    ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I' } →
    (ℕ → J) :=
  fun u u' k ↦ if k ≤ u.1 then u.2.1 k else u'.2.1 (k-u.1-1)


theorem comb_mono (p : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I })
    (p' : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I'}) (h : p.2.1 p.1 ≤ p'.2.1 0):
    Monotone (comb I I' p p') := by
  intro x y xy
  unfold comb
  by_cases hx: x ≤ p.1
  · by_cases hy : y ≤ p.1
    · simp only [hx, ↓reduceIte, hy]
      exact p.2.2.1 xy
    simp only [hy, hx, ↓reduceIte]
    calc
      (↑p.2 : ℕ → J) x ≤ (↑p.2 : ℕ → J) p.1 := by exact p.2.2.1 hx
          _ ≤ (↑p'.2 : ℕ → J) 0 := h
          _ ≤ (↑p'.2 : ℕ → J) (y - p.1 - 1) := p'.2.2.1 (zero_le (y - p.1 - 1))
  have hy: ¬y ≤ p.1 := by linarith
  simp only [hx, ↓reduceIte, hy, ge_iff_le]
  apply p'.2.2.1
  gcongr

theorem comb_mem (p : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I })
    (p' : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I' }) :
    ∀ n : ℕ, comb I I' p p' n ∈ I ∪ I' := by
  intro n
  unfold comb
  by_cases hn : n ≤ p.1
  · simp only [hn, ↓reduceIte, mem_union]
    left
    exact p.2.2.2 n
  simp only [hn, ↓reduceIte, mem_union]
  right
  exact p'.2.2.2 (n- p.1 - 1)

def comb' (p : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I })
    (p' : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I' }) (h : p.2.1 p.1 ≤ p'.2.1 0):
    ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I ∪ I' } :=
  ⟨p.1 + p'.1 + 1, comb I I' p p', comb_mono I I' p p' h, comb_mem I I' p p'⟩

theorem comb'_sum (p : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I })
    (p' : ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ I' }) (h : p.2.1 p.1 ≤ p'.2.1 0):
    ∑ i ∈ Finset.range p.1, edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal +
    ∑ i ∈ Finset.range p'.1, edist (a (p'.2.1 (i + 1))) (a (p'.2.1 i))^r.toReal ≤
    ∑ i ∈ Finset.range (comb' I I' p p' h).1,
    edist (a ((comb' I I' p p' h).2.1 (i + 1))) (a ((comb' I I' p p' h).2.1 i))^r.toReal := by
  nth_rw 1[comb']
  simp only
  rw[add_assoc, Finset.sum_range_add, add_comm p'.1, Finset.sum_range_add]
  nth_rw 3[add_comm]
  rw[← add_assoc, ← add_zero
    (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r.toReal +
    ∑ i ∈ Finset.range p'.1,
    edist (a ((↑p'.2 : ℕ → J) (i + 1))) (a ((↑p'.2 : ℕ → J) i)) ^ r.toReal)]
  gcongr with i ih
  · simp at ih
    have ih' : i + 1 ≤ p.1 := ih
    unfold comb' comb
    simp only [ih', ↓reduceIte, ih, le_of_lt, le_refl]
  · rename_i i ih
    simp only [Finset.mem_range] at ih
    unfold comb' comb
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, Nat.add_eq_zero, one_ne_zero, false_and,
      ↓reduceIte, add_tsub_cancel_left]
    have s1: ¬ p.1 + (1 + i) + 1 ≤ p.1 := by linarith
    simp only [s1, ↓reduceIte, ge_iff_le]
    suffices : p.1 + (1 + i) + 1 - p.1 - 1 = i + 1
    · rw[this]
    calc
      p.1 + (1 + i) + 1 - p.1 - 1
        = 1 + (p.1 + (1 + i)) - p.1 - 1 := by rw [Nat.add_comm]
      _ = 1 + p.1 + (1 + i) - p.1 - 1 := by rw [Nat.add_assoc]
      _ = 1 + p.1 + (1 + i) - (p.1 + 1) := by rw [Nat.sub_sub]
      _ = (1 + i) + (1 + p.1) - (p.1 + 1) := by rw [Nat.add_comm]
      _ = (1 + i) + (p.1 + 1) - (p.1 + 1) := by rw [Nat.add_comm p.1]
      _ = 1 + i := by rw [Nat.add_sub_cancel_right]
      _ = i + 1 := by rw [add_comm]
  simp only [Finset.range_one, Finset.sum_singleton, add_zero, zero_le]


theorem r_eVariationOn_superadditivity
    (h : r ≠ 0) (h' : r ≠ ∞) (II': ∀ i ∈ I, ∀ i' ∈ I', i ≤ i') :
    (r_eVariationOn r I a)^r.toReal + (r_eVariationOn r I' a)^r.toReal
    ≤ (r_eVariationOn r (I ∪ I') a)^r.toReal := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε inf
  have infI: r_eVariationOn r I a ^ r.toReal < ⊤ := by
    refine lt_of_le_of_lt ?_ inf
    refine r_eVariationOn_pow_r_mono I (I ∪ I') a r ?_
    exact subset_union_left
  have infI': r_eVariationOn r I' a ^ r.toReal < ⊤ := by
    refine lt_of_le_of_lt ?_ inf
    refine r_eVariationOn_pow_r_mono I' (I ∪ I') a r ?_
    exact subset_union_right
  have pz: (0 : ℝ≥0∞) ^ r.toReal = 0 := by
    simp only [ENNReal.rpow_eq_zero_iff, true_and, ENNReal.zero_ne_top, false_and, or_false]
    exact ENNReal.toReal_pos h h'
  by_cases hI: I.Nonempty
  swap
  · rw[Set.not_nonempty_iff_eq_empty.1 hI]
    simp only [r_eVariationOn_emptyset, empty_union, pz, zero_add, self_le_add_right]
  by_cases hI':  I'.Nonempty
  swap
  · rw[Set.not_nonempty_iff_eq_empty.1 hI']
    simp only [r_eVariationOn_emptyset, union_empty, pz, add_zero, self_le_add_right]
  have h'I : r_eVariationOn r I a ≠ ∞ := by
    contrapose infI
    simp_all only [ne_eq, ENNReal.rpow_eq_zero_iff, true_and, ENNReal.zero_ne_top, false_and,
      or_false, Decidable.not_not, ENNReal.top_rpow_of_pos, lt_self_iff_false, not_false_eq_true]
  have h'I' : r_eVariationOn r I' a ≠ ∞ := by
    contrapose infI'
    simp_all only [ne_eq, ENNReal.rpow_eq_zero_iff, true_and, ENNReal.zero_ne_top, false_and,
      or_false, Decidable.not_not, ENNReal.top_rpow_of_pos, lt_self_iff_false, not_false_eq_true]
  have h'ε: 0 < ε/2 := by
    simp only [hε, div_pos_iff_of_pos_left, Nat.ofNat_pos]
  obtain ⟨p, ph⟩ := eVariationOn_pow_r_lt_infty I a r h h' h'I h'ε hI
  obtain ⟨p', p'h⟩ := eVariationOn_pow_r_lt_infty I' a r h h' h'I' h'ε hI'
  have pp': p.2.1 p.1 ≤ p'.2.1 0 := by
    apply II'
    · exact p.2.2.2 p.1
    exact p'.2.2.2 0
  apply le_of_lt
  calc
    r_eVariationOn r I a ^ r.toReal + r_eVariationOn r I' a ^ r.toReal
    _ < (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i))
        ^ r.toReal + ↑(ε / 2)) + (∑ i ∈ Finset.range p'.1, edist (a ((↑p'.2 : ℕ → J) (i + 1)))
         (a ((↑p'.2 : ℕ → J) i)) ^ r.toReal + ↑(ε / 2)) := by
      gcongr
    _ = (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J) (i + 1))) (a ((↑p.2 : ℕ → J) i))
        ^ r.toReal  + ∑ i ∈ Finset.range p'.1, edist (a ((↑p'.2 : ℕ → J) (i + 1)))
         (a ((↑p'.2 : ℕ → J) i)) ^ r.toReal) + ε := by
      ring_nf
      have : (↑(ε / 2) : ℝ≥0∞) * 2 = ε := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div,
          ENNReal.coe_ofNat]
        refine ENNReal.div_mul_cancel ?_ ?_ <;> norm_num
      rw[this]
      ring
    _ ≤ ∑ i ∈ Finset.range (comb' I I' p p' pp').1, edist (a ((comb' I I' p p' pp').2.1 (i + 1)))
        (a ((comb' I I' p p' pp').2.1 i))^r.toReal + ε := by
      gcongr
      exact comb'_sum I I' a r p p' pp'
    _ ≤ r_eVariationOn r (I ∪ I') a ^ r.toReal + ↑ε := by
      gcongr
      exact sum_le_eVariationOn_pow_r' (I ∪ I') a r (comb' I I' p p' pp') h h'

lemma ennreal_sum_rpow_le_rpow_sum (m : ℕ) (u : ℕ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p):
    ∑ n ∈ Finset.range m, (u n)^p ≤ (∑ n ∈ Finset.range m, u n)^p := by
  induction' m with m hm
  · simp only [Finset.range_zero, Finset.sum_empty, zero_le]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  calc
    ∑ x ∈ Finset.range m, u x ^ p + u m ^ p
      ≤ (∑ x ∈ Finset.range m, u x) ^ p + u m ^ p := by gcongr
    _ ≤ (∑ x ∈ Finset.range m, u x + u m) ^ p :=
      ENNReal.add_rpow_le_rpow_add (∑ x ∈ Finset.range m, u x) (u m) hp

lemma sum_lp_mono_p (m : ℕ) (u : ℕ → ℝ≥0∞) {p q : ℝ} (hp : 0 < p) (pq : p ≤ q):
    (∑ n ∈ Finset.range m, (u n)^q)^ q⁻¹ ≤ (∑ n ∈ Finset.range m, (u n)^p)^ p⁻¹ := by
  calc
    (∑ n ∈ Finset.range m, (u n)^q)^ q⁻¹
      = (∑ n ∈ Finset.range m, ((u n)^p)^(q/p))^ q⁻¹ := by
      congr
      ext i
      rw [← ENNReal.rpow_mul]
      field_simp
    _ ≤ ((∑ n ∈ Finset.range m, ((u n)^p))^(q/p))^ q⁻¹ := by
      refine ENNReal.rpow_le_rpow ?_ ?_
      · apply ennreal_sum_rpow_le_rpow_sum
        exact (one_le_div₀ hp).mpr pq
      simp only [inv_nonneg]
      linarith
    _ = (∑ n ∈ Finset.range m, (u n)^p)^ p⁻¹ := by
      rw [← ENNReal.rpow_mul]
      congr
      field_simp
      rw[mul_comm]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp
      constructor <;> linarith

lemma summand_le_fin_sum {α : Type*} {s : Finset α} {a : α} (ha : a ∈ s) (f : α → ℝ≥0∞) :
    f a ≤ ∑ x ∈ s, f x := by
  exact CanonicallyOrderedAddCommMonoid.single_le_sum ha

lemma summand_le_fin_sum_lp
    {α : Type*} {s : Finset α} {a : α} (ha : a ∈ s) (f : α → ℝ≥0∞) {p : ℝ} (hp : 0 < p):
    f a ≤ (∑ x ∈ s, (f x)^p) ^ p⁻¹ := by
  calc
    f a = ((f a)^p)^p⁻¹ := by rw [ENNReal.rpow_rpow_inv (Ne.symm (ne_of_lt hp)) (f a)]
      _ ≤ (∑ x ∈ s, (f x)^p) ^ p⁻¹ := by
        gcongr
        exact summand_le_fin_sum ha fun x ↦ f x ^ p

#check eVariationOn_infty'

theorem eVariationOn_infty'_inv (h : r ≠ 0) (h' : r ≠ ∞)
    (hL : ∀ L : ℝ≥0, ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    L < (∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)):
    r_eVariationOn r I a = ∞ := by
  suffices : (r_eVariationOn r I a)^r.toReal = ∞
  · simp_all only [ne_eq, Prod.exists, Subtype.exists, exists_prop, ENNReal.rpow_eq_top_iff]
    have : ¬ r.toReal < 0 := by
      simp_all only [not_lt, ENNReal.toReal_nonneg]
    tauto
  refine ENNReal.eq_top_of_forall_nnreal_le ?_
  intro L
  obtain ⟨p, hp⟩ := hL L
  apply le_of_lt at hp
  apply le_trans hp
  exact sum_le_eVariationOn_pow_r' I a r p h h'

theorem eVariationOn_infty''_inv (h : r ≠ 0) (h' : r ≠ ∞)
    (hL : ∀ L : ℝ≥0, ∃ p : ℕ × { u : ℕ → J // Monotone u ∧ ∀ i, u i ∈ I },
    L < ((∑ i ∈ Finset.range p.1,
    edist (a (p.2.1 (i + 1))) (a (p.2.1 i))^r.toReal)) ^ (r.toReal⁻¹)):
    r_eVariationOn r I a = ∞ := by
  apply eVariationOn_infty'_inv I a r h h'
  intro L
  obtain ⟨p, hp⟩ := hL (L^r.toReal⁻¹)
  use p
  refine (ENNReal.rpow_lt_rpow_iff (z := r.toReal⁻¹) ?_).mp ?_
  · simp only [inv_pos]
    exact ENNReal.toReal_pos h h'
  have : (↑(L ^ r.toReal⁻¹) : ℝ≥0∞) = ((↑L : ℝ≥0∞) ^ r.toReal⁻¹) := by
    refine Eq.symm (ENNReal.rpow_ofNNReal ?_)
    simp only [inv_nonneg, ENNReal.toReal_nonneg]
  rw[← this]
  exact hp

theorem r_eVariationOn_infty_infty_inv (hL : ∀ L : ℝ≥0∞, ∃ j : ↑I × ↑I, L < edist (a j.1) (a j.2)) :
    r_eVariationOn ∞ I a = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le ?_
  intro L
  obtain ⟨p, hp⟩ := hL L
  apply le_of_lt at hp
  apply le_trans hp
  exact pair_le_eVariationOn_infty I a p

theorem r_eVariationOn_on_mono_lt_infty  (hr : r ≠ 0) (hr' : r' ≠ ∞) (rr': r ≤ r'):
    r_eVariationOn r' I a ≤ r_eVariationOn r I a := by
  have h'r : r ≠ ∞ := by
    contrapose hr'
    simp_all only [ne_eq, Decidable.not_not, ENNReal.top_ne_zero, not_false_eq_true, top_le_iff]
  have h'r' : r' ≠ 0 := by
    contrapose hr
    simp_all only [ne_eq, Decidable.not_not, ENNReal.zero_ne_top, not_false_eq_true,
      nonpos_iff_eq_zero]
  by_cases hI: I.Nonempty
  swap
  · rw[not_nonempty_iff_eq_empty.mp hI]
    simp only [r_eVariationOn_emptyset, le_refl]
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε fin
  have fin': r_eVariationOn r' I a ≠ ⊤ := by
    contrapose fin
    simp_all only [ne_eq, Decidable.not_not, not_lt, top_le_iff]
    apply eVariationOn_infty''_inv
    · exact hr
    · exact h'r
    intro L
    obtain ⟨p, hp⟩ := eVariationOn_infty'' I a r' h'r' hr' fin L
    use p
    calc
      ↑L < (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J) (i + 1)))
              (a ((↑p.2 : ℕ → J) i)) ^ r'.toReal)^r'.toReal⁻¹ := by exact hp
        _≤ (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J) (i + 1)))
              (a ((↑p.2 : ℕ → J) i)) ^ r.toReal)^r.toReal⁻¹ := by
            apply sum_lp_mono_p
            · exact ENNReal.toReal_pos hr h'r
            exact (ENNReal.toReal_le_toReal h'r hr').mpr rr'
  have inf : r_eVariationOn r I a ≠ ⊤ := LT.lt.ne_top fin
  obtain ⟨p, ph⟩ := eVariationOn_lt_infty I a r' h'r' hr' fin' hε hI
  apply le_of_lt at ph
  apply le_trans ph
  gcongr
  calc
    (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J)
         (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r'.toReal) ^ r'.toReal⁻¹
    _ ≤ (∑ i ∈ Finset.range p.1, edist (a ((↑p.2 : ℕ → J)
         (i + 1))) (a ((↑p.2 : ℕ → J) i)) ^ r.toReal) ^ r.toReal⁻¹ := by
      apply sum_lp_mono_p
      · exact ENNReal.toReal_pos hr h'r
      exact (ENNReal.toReal_le_toReal h'r hr').mpr rr'
    _ ≤ r_eVariationOn r I a := by
      exact sum_le_eVariationOn' I a r p hr h'r

lemma edist_eq_pair_fun_lp (j j' : ↑I) (h: r ≠ 0) (h': r ≠ ∞):
    edist (a ↑j) (a ↑j') = (∑ i ∈ Finset.range (pair_fun' I j j').1,
    edist (a ((↑(pair_fun' I j j').2 : ℕ → J)
    (i + 1))) (a ((↑(pair_fun' I j j').2 : ℕ → J) i)) ^ r.toReal)^r.toReal⁻¹ := by
  unfold pair_fun' pair_fun extend_fun
  simp only [Nat.reduceAdd, Fin.isValue, Fin.mk_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false,
    ↓reduceIte, Nat.cast_one, dite_eq_ite, ite_self]
  rw [@Finset.sum_range_succ_comm]
  have : 0 < r.toReal := by exact ENNReal.toReal_pos h h'
  simp only [Nat.one_lt_ofNat, ↓reduceIte, one_ne_zero, WeakPseudoEMetricSpace.edist_self, this,
    ENNReal.zero_rpow_of_pos, Finset.range_one, Finset.sum_singleton, Nat.ofNat_pos, zero_add]
  rw [← ENNReal.rpow_mul]
  field_simp
  by_cases jj': ↑j ≤ ↑j'
  · simp only [Subtype.coe_le_coe, jj', sup_of_le_right, inf_of_le_left]
    rw [@WeakPseudoEMetricSpace.edist_comm]
  simp_all only [ne_eq, not_le, Subtype.coe_lt_coe, le_of_lt, sup_of_le_left, inf_of_le_right]

theorem infty_variation_le_r_eVariation (hr : r ≠ 0) :
    r_eVariationOn ∞ I a ≤ r_eVariationOn r I a := by
  by_cases h'r : r = ∞
  · rw[h'r]
  by_cases hI: I.Nonempty
  swap
  · rw[not_nonempty_iff_eq_empty.mp hI]
    simp only [r_eVariationOn_emptyset, le_refl]
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε fin
  have fin': r_eVariationOn ⊤ I a ≠ ⊤ := by
    contrapose fin
    simp_all only [ne_eq, Decidable.not_not, not_lt, top_le_iff]
    apply eVariationOn_infty''_inv
    · exact hr
    · exact h'r
    intro L
    obtain ⟨p, hp⟩ := r_eVariationOn_infty_infty I a fin L
    use (pair_fun' I p.1 p.2)
    rw[← edist_eq_pair_fun_lp I a r p.1 p.2 hr h'r]
    exact hp
  have inf : r_eVariationOn r I a ≠ ⊤ := LT.lt.ne_top fin
  obtain ⟨p, ph⟩ := eVariationOn_infty_lt_infty I a fin' hε hI
  apply le_of_lt at ph
  apply le_trans ph
  gcongr
  rw[edist_eq_pair_fun_lp I a r p.1 p.2 hr h'r]
  exact sum_le_eVariationOn' I a r (pair_fun' I p.1 p.2) hr h'r

theorem r_eVariation_on_mono (hr : r ≠ 0) (h : r ≤ r') :
    r_eVariationOn r' I a ≤ r_eVariationOn r I a := by
  by_cases h'r' : r' = ∞
  · rw[h'r']
    exact infty_variation_le_r_eVariation I a r hr
  exact r_eVariationOn_on_mono_lt_infty I a r r' hr h'r' h

end VariationNorm

def zero_add_one : Nat := by exact Nat.add 0 1

example : zero_add_one = 1 := by
  unfold zero_add_one
  exact zero_add 1

#check Nat.add
#min_imports
