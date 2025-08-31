import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
open Function Set Classical MeasureTheory
noncomputable section

namespace Calderon
open ENNReal Real
#check MeasurePreserving

variable{ι X Y Z : Type*} [Fintype ι] [MeasurableSpace Z] (μ : Measure Z)
#check Lex ι
--variable{a b : ι}(n : ℕ)

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
def multilinear_avg(φ : ℝ → ℝ)(F : ι → (ι → ℝ) → ℝ)(t : NNReal): (ι → ℝ) → ENNReal := --maybe wrong, bc no norm in original, omg i hate ENNReal
  fun x ↦ 1/t * ∫⁻ (s : ℝ), ‖φ (1/t * s) * ∏(j : ι), (F j) (x + unit j s)‖ₑ
/-With the most important case:-/
def multilinear_avg_spec(F : ι → (ι → ℝ) → ℝ)(t : NNReal): (ι → ℝ) → ENNReal :=
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
  obtain ⟨i,ih⟩ := i
  simp
  linarith

def good(g : ℕ → NNReal)(q : ι → ℝ): Prop :=
  (∀(i : ℕ), 1 ≤ i → 1 ≤ g i) ∧ ∃ C : NNReal, ∀(m : ℕ)(idx : Fin (m+1) → NNReal)(mon : Monotone idx)(F : ι → (ι → ℝ) → ℝ) --WRONG, ι is used twice which seem bad
  (hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal), ∑ i : Fin m, (∫⁻ (a : ι → ℝ), (multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)^2)^(1/2) ≤ C * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))
--The most important case

def good_const{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q) : NNReal := Exists.choose h.2

theorem good_const_good{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q)(m : ℕ)(idx : Fin (m+1) → NNReal)
  (mon : Monotone idx)(F : ι → (ι → ℝ) → ℝ)(hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal):
    ∑ i : Fin m, (∫⁻ (a : ι → ℝ), (multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)^2)^(1/2) ≤ (good_const h) * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)) := (Exists.choose_spec h.2) m idx mon F hF

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
open ENNReal Real

variable{ι α β γ : Type*}[Fintype ι] [Inhabited β] (k : ι → ℕ) (n : ℕ)

lemma shift_lemma_ico(f : ℝ → ENNReal)(a b c : ℝ): ∫⁻ (x : ℝ) in Ico a b, f x = ∫⁻ (x : ℝ) in Ico (a+c) (b+c), f (x - c) := by
  rw[← MeasureTheory.lintegral_indicator measurableSet_Ico, ← MeasureTheory.lintegral_indicator measurableSet_Ico]
  rw[← lintegral_add_right_eq_self ((Ico a b).indicator f) (-c)]
  apply lintegral_congr
  intro x
  unfold indicator
  unfold Ico
  simp
  by_cases h: a + c ≤ x ∧ x < b + c
  all_goals simp only [h, and_self, ↓reduceIte]
  rfl


/- HERE COME FACTS; LATER EXPORT THIS TO SEPERATE FILE -/
theorem fact5_1(F : ι → (ι → ℝ) → ℝ)(t : NNReal)(t0: t ≠ 0)(x : ι → ℝ):
  multilinear_avg_spec F t x = (1/t) * ∫⁻ (s : ℝ) in Ico (∑ (i : ι), x i) ((∑ (i : ι), x i) + t), ‖∏(j : ι), (F j) (x + Calderon.unit j (s - ∑ (j : ι), (x j)))‖ₑ := by
    unfold multilinear_avg_spec multilinear_avg
    --by_cases t0: t = 0
    --· rw[t0]
    --  simp
    suffices : ∫⁻ (s : ℝ), ‖(Ico 0 1).indicator 1 (1 / ↑t * s) * ∏ j, F j (x + unit j s)‖ₑ =
  ∫⁻ (s : ℝ) in Ico (∑ i, x i) (∑ i, x i + ↑t), ‖∏ j, F j (x + unit j (s - ∑ (j : ι), x j))‖ₑ
    · rw[this]
    calc
      ∫⁻ (s : ℝ), ‖(Ico 0 1).indicator 1 (1 / ↑t * s) * ∏ j, F j (x + unit j s)‖ₑ =  ∫⁻ (s : ℝ), ‖(Ico 0 1).indicator 1 (1 / ↑t * s)‖ₑ * ‖∏ j, F j (x + unit j s)‖ₑ := by --prob wrong
        apply lintegral_congr
        simp
        intro a
        rfl
    _ = ∫⁻ (s : ℝ) in Ico 0 ↑t, ‖∏ j, F j (x + unit j s)‖ₑ := by
      rw[← MeasureTheory.lintegral_indicator measurableSet_Ico]
      apply lintegral_congr
      intro a
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

    _ = ∫⁻ (s : ℝ) in Ico (∑ i, x i) (∑ i, x i + ↑t), ‖∏ j, F j (x + unit j (s - ∑ (j : ι), x j))‖ₑ := by
      rw[add_comm (∑ i, x i) (↑t)]
      rw[shift_lemma_ico _ 0 (↑t : ℝ) (∑ i, x i)]
      simp

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


/-This is only for completion, this is a direct copy of good_const_is_good-/
theorem fact5_2{g : ℕ → NNReal}{q : ι → ℝ}(h : good g q)(m : ℕ)(idx : Fin (m+1) → NNReal)
  (mon : Monotone idx)(F : ι → (ι → ℝ) → ℝ)(hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i).toNNReal):
    ∑ i : Fin m, (∫⁻ (a : ι → ℝ), (multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)^2)^(1/2) ≤ (good_const h) * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ)) := (Exists.choose_spec h.2) m idx mon F hF


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


@[fun_prop] lemma approx_sum_measurable(i : ι){F : (ι → ℤ) → ℝ}: Measurable (approx_sum i F) := by --(h : Measurable F)
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

lemma approx_set_volume(i : ι)(j : ι → ℤ): volume (approx_set i j) = 1 := by
  unfold approx_set
  simp --not easy at all, mathlib (very) needed
  sorry

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
    simp
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
        · simp
        · simp
        exact hs

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
    simp

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


/- This also works for ι empty, but is a bit of a pain-/
theorem fact5_4 [Nonempty ι](k : ι → ℤ)(α : ι → ℝ)(hα: ∀(i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ){t : NNReal}(ht : 0 < t): --also make a version for ℕ, hopefully follows easily
  (multilinear_avg_spec (approx_sum_mul F) t (fun j ↦ k j + α j)) =
  1/t * ∑' i : ℤ, ‖(volume (Ico (i:ℝ) (i+1) ∩ Ico (∑ (j : ι), (k j + α j)) (t+∑ (j : ι), (k j + α j))))‖ₑ *
  ∏(j_1 : ι), ‖(F j_1) (fun o ↦ ((k o : ℤ) + unit j_1 (i - (∑ (r : ι), (k r))) o))‖ₑ:= by --stated wrongly i think! glaub vorzeichen ist falsch, also LHS
    rw[fact5_1]
    swap
    · contrapose ht
      simp_all
    congr
    simp
    unfold approx_sum_mul
    --((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))
    calc
      ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ‖∏ j, approx_sum j (F j) ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))‖ₑ
      /-_ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ‖∏ j, (∑' (j' : ι → ℤ), (F j) (j' + unit j (j' j - ∑ r, j' r)) * (approx_set j j').indicator 1
      ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i))))‖ₑ := by
        congr
        ext s
        congr
        ext j
        rw[og_sum]
      -/
      _ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, ‖approx_sum j (F j) ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))‖ₑ := by
        congr
        ext s
        rw [Real.enorm_eq_ofReal_abs]
        rw [@Finset.abs_prod]
        rw[ENNReal.ofReal_prod_of_nonneg]
        swap
        · intro i _
          simp
        congr
        ext i
        rw [Real.enorm_eq_ofReal_abs]
      _ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, ∑' (j' : ι → ℤ), ‖(F j) (j' + unit j (j' j - ∑ r, j' r)) * (approx_set j j').indicator 1 ((fun i ↦ ↑(k i) + α i) + unit j (s - ∑ i, (↑(k i) + α i)))‖ₑ := by
        congr
        ext s
        congr
        ext j
        rw[og_sum']
      _ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, ∑' (a : ℤ), ‖(F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s‖ₑ := by
        congr
        ext s
        congr
        ext i
        set h := fun j' : ι → ℤ ↦ ‖F i (j' + unit i (j' i - ∑ r, j' r)) *
        (approx_set i j').indicator 1 ((fun i ↦ ↑(k i) + α i) + unit i (s - ∑ i, (↑(k i) + α i)))‖ₑ
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
          _ = ∑' (a : ℤ), ‖F i (k + unit i (a - ∑ r, k r)) * (Ico (↑a) (↑a + 1)).indicator 1 s‖ₑ := by
            rw[← Equiv.tsum_eq (e := equisum k i) (f := fun a ↦ ‖F i (k + unit i (a - ∑ r, k r)) * (Ico (↑a : ℝ) ((↑a : ℝ) + 1)).indicator 1 s‖ₑ)]
            unfold A
            congr
            ext ⟨j',j'h⟩
            unfold h equisum
            simp [-enorm_mul]
            congr 3
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
      _ = ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∑' (a : ℤ), ∏ j, ‖(F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s‖ₑ := by
        congr
        ext s
        rw[tsum_prod]
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
      _ = ∑' (a : ℤ), ∫⁻ (s : ℝ) in Ico (∑ i, (↑(k i) + α i)) (∑ i, (↑(k i) + α i) + ↑t),
      ∏ j, ‖(F j) (k + unit j (a - ∑ r, k r)) * (Ico (↑a : ℝ) (a+1)).indicator 1 s‖ₑ := by
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

theorem multilinear_avg_spec_discrete_avg_est [Nonempty ι](k : ι → ℤ)(α : ι → ℝ)(hα: ∀(i : ι), 0 ≤ α i ∧ α i < 1)(F : ι → (ι → ℤ) → ℝ)(n : ℕ):
  |(multilinear_avg_spec (approx_sum_mul F) ↑n (fun j ↦ k j + α j)).toReal - discrete_avg' n |F| k| ≤ 1/n * ∑ i ∈ {0,1,n,n+1}, |∏ j : ι, F j (k + unit j (↑i : ℤ))| := by
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
    let r : ℤ → ℝ := fun i ↦ |∏ j_1 : ι, F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o|
    set a : ℤ → ℝ := fun i ↦ (volume (Ico (↑i : ℝ) (↑i + 1) ∩ (Ico (∑ j, ((↑(k j) : ℝ) + α j)) (((↑n : ℝ) + ∑ j, (↑(k j) + α j)))))).toReal
    calc
      |(↑n)⁻¹ *
        (∑' (i : ℤ), volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j))) *
              ∏ j_1, ‖F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o‖ₑ).toReal -
      (↑n)⁻¹ * ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, |F| j_1 (k + unit j_1 (i - ∑ r, k r))|
        = |(↑n)⁻¹ *
        (∑' (i : ℤ), (volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j))) *
              ∏ j_1, ‖F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o‖ₑ).toReal) -
      (↑n)⁻¹ * ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, |F| j_1 (k + unit j_1 (i - ∑ r, k r))| := by
          congr
          rw[ENNReal.tsum_toReal_eq]
          intro a
          simp
          refine mul_ne_top ?_ ?_
          · apply lt_top_iff_ne_top.1
            calc
              volume (Ico (↑a : ℝ) (↑a + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))
              ≤ volume (Ico (↑a : ℝ) (↑a + 1)) := by
                refine measure_mono ?_
                simp
              _ < ⊤ := by simp
          by_contra h0
          obtain ⟨_,h2⟩ := (prod_eq_top_iff (s := (Finset.univ (α := ι))) (fun j_1 : ι ↦ ‖F j_1 fun o ↦ k o + unit j_1 (a - ∑ r, k r) o‖ₑ)).1 h0
          obtain ⟨j,_,jh⟩ := h2
          simp at jh
        _ = |(↑n)⁻¹ *
        (∑' (i : ℤ), ((volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))).toReal *
              (∏ j_1, ‖F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o‖ₑ).toReal)) -
      (↑n)⁻¹ * ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, |F| j_1 (k + unit j_1 (i - ∑ r, k r))| := by
          congr
          ext i
          rw[toReal_mul]
        _ = |(↑n)⁻¹ *
        (∑' (i : ℤ), ((volume (Ico (↑i) (↑i + 1) ∩ Ico (∑ j, (↑(k j) + α j)) (↑n + ∑ j, (↑(k j) + α j)))).toReal *
              (∏ j_1, (‖F j_1 fun o ↦ k o + unit j_1 (i - ∑ r, k r) o‖ₑ).toReal))) -
      (↑n)⁻¹ * ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, |F| j_1 (k + unit j_1 (i - ∑ r, k r))| := by
          congr
          ext i
          congr
          rw[ENNReal.toReal_prod]
        _ = |(↑n)⁻¹ * (∑' (i : ℤ), (a i * r i)) - (↑n)⁻¹ *
          ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, |F| j_1 (k + unit j_1 (i - ∑ r, k r))| := by
          congr
          ext i
          congr
          unfold r
          simp
          rw[Finset.abs_prod]
        _ = |(↑n)⁻¹ * (∑' (i : ℤ), (a i * r i)) - (↑n)⁻¹ *
          ∑ i ∈ Finset.Ico (∑ r, k r) (↑n + ∑ r, k r), ∏ j_1, F j_1 (k + unit j_1 (i - ∑ r, k r))| := by sorry --fuckifuck
        _ ≤ (↑n)⁻¹ * ∑ i ∈ {0, 1, n, n + 1}, |∏ j, F j (k + unit j ↑i)| := by
          sorry

/-
def good(g : ℕ → ENNReal)(q : ι → ℝ): Prop :=
  ∃ C : NNReal, ∀(m : ℕ)(idx : Fin (m+1) → NNReal)(mon : Monotone idx)(F : ι → (ι → ℝ) → ℝ) --WRONG, ι is used twice which seem bad
  (hF: ∀(i : ι), MeasureTheory.MemLp (F i) (q i)), ∑ i : Fin m, (∫⁻ (a : ι → ℝ), (multilinear_avg_spec F (idx i.succ) a - multilinear_avg_spec F (idx ⟨i, get_rid i⟩) a)^2)^(1/2) ≤ C * g m * ∏ (i : ι), (∫⁻ (a : ι → ℝ), ‖(F i) a‖ₑ ^ (↑(q i) : ℝ)) ^ (1 / (↑(q i) : ℝ))
-/
/-

/-Note: This is slightly weaker than the theorem in the paper, for the theorem in the paper one would replace "ℕ" with "ℤ".
The proof stays the same, only thing that needs to be changed would be to change iterate.
However Corollary 4 is never used (in the entire paper) except for this proof, for which the ℕ version suffices...-/
#check Summable
/-ℤ version:-/ --First prove the ℕ thing from this, to make sure!
theorem corollary4'{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)(hq : (∀(i : ι), 0 < q i))
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx)(F : ι → (ι → ℤ) → ℝ)(hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):  --(hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal) unnötig i think, da 0 *  ⊤ = 0 NVM
    ∑ i : Fin m, ∑' a : ι → ℤ, (discrete_avg' (idx i.succ) F a - discrete_avg' (idx ⟨i, get_rid i⟩) F a)^2  ≤ --NOTE: ∑' does coercion to ℝ, at some point (Fact 5.4 or smth) note that this is summable
    (((1024 * π^2)/3) + 2*(good_const hg)) * g m * ∏ (j : ι), (∑' a : ι → ℤ, |(F j a)|^(q j))^(2/(q j)) := sorry --use norms not abs :(

--lemma tsum_disjoint_union_zero

/-ℕ version:-/
theorem corollary4{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)(hq : (∀(i : ι), 0 < q i))
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx)(F : ι → (ι → ℕ) → ℝ)(hF: ∀(j : ι), Memℓp (F j) (q j).toNNReal):
    ∑ i : Fin m, ∑' a : ι → ℕ, (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2  ≤ --NOTE: ∑' does coercion to ℝ, at some point (Fact 5.4 or smth) note that this is summable
    (((1024 * π^2)/3) + 2*(good_const hg)) * g m * ∏ (j : ι), (∑' a : ι → ℕ, |(F j a)|^(q j))^(2/(q j)) := by
    by_cases hι: IsEmpty ι
    · unfold discrete_avg
      simp
      sorry --funnily enough this is true
    simp at hι
    by_cases unι: ¬(Nontrivial ι)
    · --simp at unι
      sorry
    let A := {k : ι → ℤ | ∀ j : ι, 0 ≤ k j}
    have mem_A(u : ↑A)(i : ι): incl_fun F i ↑u = F i fun t ↦ ((↑u : ι → ℤ) t).toNat := by
      unfold incl_fun
      obtain ⟨u,uh⟩ := u
      unfold A at uh
      dsimp at uh
      simp [uh]
    have not_mem_A(u : ↑Aᶜ)(i : ι): incl_fun F i ↑u = 0 := sorry
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
        _ = ∑' (a : ι → ℕ), |F i a| ^ q i := by sorry
    have prod_eq: ∏ j, (∑' (a : ι → ℤ), |incl_fun F j a| ^ q j) ^ (2 / q j) = ∏ j, (∑' (a : ι → ℕ), |F j a| ^ q j) ^ (2 / q j) := by
      apply Finset.prod_congr rfl
      intros
      rw[sum_eq]
    rw[← prod_eq]
    suffices : ∑ i : Fin m, ∑' (a : ι → ℕ), (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨↑i, get_rid i⟩) F a) ^ 2 =
       ∑ i : Fin m, ∑' (a : ι → ℤ), (discrete_avg' (idx i.succ) (incl_fun F) a - discrete_avg' (idx ⟨↑i, get_rid i⟩) (incl_fun F) a) ^ 2
    · rw[this]
      clear this prod_eq sum_eq
      apply corollary4' hg hq m idx mon (incl_fun F)
      intro i
      unfold Memℓp
      simp
      sorry
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
        simp
        have(n : ℕ): discrete_avg' n (fun i k ↦ if ∀ (j : ι), 0 ≤ k j then F i fun t ↦ (k t).toNat else 0) k = 0 := by --this may just not be true if ι has only one element
          unfold discrete_avg'
          simp
          right
          apply Finset.sum_eq_zero
          intro x _
          obtain ⟨j,_⟩ := exists_true_iff_nonempty.2 hι
          apply Finset.prod_eq_zero (i := j)
          · simp

          sorry
        rw[this,this, sub_zero]
      _ = ∑' (a : ι → ℕ), (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨↑i, get_rid i⟩) F a) ^ 2 := by
        sorry

variable{X : Type*}(f : ι → X → ℝ){S : ι → X → X}(N : ℕ)

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

theorem fact5_8{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)(hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2) --look at corollary 4 again and check
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx)(F : ι → (ι → ℕ) → ℝ)(hF: ∀(j : ι), Memℓp (F j) (((q j).toNNReal))):
    ∑ i : Fin m, ∑' a : ι → ℕ, (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2  ≤ --NOTE: ∑' does coercion to ℝ, at some point (Fact 5.4 or smth) note that this is summable
    (((1024 * π^2)/3) + 2*(good_const hg)) * g m * ∑ (j : ι), (∑' a : ι → ℕ, |(F j a)|^(q j)) := by
      set h : ι → ℝ := fun j ↦ ∑' a : ι → ℕ, |(F j a)|^(q j)
      have : ∑ j, (∑' (a : ι → ℕ), |F j a| ^ (q j)) = ∑ j, h j := by unfold h; simp
      rw[this]
      clear this
      set C := (1024 * π ^ 2 / 3 + 2 * ↑(good_const hg)) * ↑(g m)

      calc
        ∑ i : Fin m, ∑' a : ι → ℕ, (discrete_avg (idx i.succ) F a - discrete_avg (idx ⟨i, get_rid i⟩) F a)^2  ≤
          C * ∏ (j : ι), (h j)^(2/ (q j)) := corollary4 hg hq.1 m idx mon F hF
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

theorem goal' [h: Nonempty ι]{f : ι → X → ℝ}{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)[MeasurableSpace X](μ : Measure X)(hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx)(hS: MMeasurePreserving μ S)(hS': pairwise_commuting S)(hf: ∀(i : ι), Measurable (f i)): --(hf : ∀(i : ι), MeasureTheory.MemLp (f i) (q i) μ) Probably hf isnt needed, maybe (aestrongly)measurable or smth??? Something along those lines definetely (else integrals become zero on RHS)
    ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ ≤
    2^(Fintype.card ι) * (((1024 * π^2)/3).toNNReal + 2*(good_const hg)) *
     g m * ∑(i : ι), (∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ)  := by
      set C := (↑(1024 * π ^ 2 / 3).toNNReal : ENNReal) + 2 * ↑(good_const hg)
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
            have : (↑(1024 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * ↑(g m) *
    ∑ j, ‖∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j‖ₑ = ‖(↑(1024 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * ↑(g m) *
    ∑ j, ∑' (a : ι → ℕ), |push_forward_many N S f x j a| ^ q j‖ₑ := by
              rw[enorm_mul]
              congr
              · rw[enorm_mul]
                congr
                · refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
                  all_goals simp
                  · exact not_eq_of_beq_eq_false rfl
                  have : max (1024 * π ^ 2 / 3) 0 = 1024 * π ^ 2 / 3 := by
                    simp
                    nlinarith
                  rw[this]
                  clear this
                  have : |1024 * π ^ 2 / 3 + 2 * ↑(good_const hg)| = 1024 * π ^ 2 / 3 + 2 * ↑(good_const hg) := by
                    simp
                    apply add_nonneg
                    · nlinarith
                    simp
                  rw[this]
                  rw[ENNReal.toReal_add]
                  all_goals try simp
                  · nlinarith
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
            have : max (1024 * π ^ 2 / 3) 0 = 1024 * π ^ 2 / 3 := by
              simp
              nlinarith
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
            apply fact5_8
            · exact hq
            · exact mon
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
set_option linter.unusedTactic false
lemma ergodic_avg_mul(n : ℕ)(f : ι → X → ℝ)(h: ι → ℝ)(x : X): ergodic_avg n S (fun i y ↦ (h i) * (f i y)) x = (∏(i : ι), h i) * ergodic_avg n S f x := by
  unfold ergodic_avg nergodic_avg
  rw[← mul_assoc, mul_comm (∏ i, h i), mul_assoc]
  congr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp
  rw [@Finset.prod_mul_distrib]

--Some statements about enorm (like mul, div...) could be added to mathlib, also the following two lemmas (and prod_eq_ae_zero):

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

theorem goal [h: Nonempty ι]{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)[MeasurableSpace X](μ : Measure X)(hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx)(hS: MMeasurePreserving μ S)(hS': pairwise_commuting S)(hf: ∀(i : ι), Measurable (f i)): --(hf : ∀(i : ι), MeasureTheory.MemLp (f i) (q i) μ) Probably hf isnt needed, maybe (aestrongly)measurable or smth??? Something along those lines definetely (else integrals become zero on RHS)
    ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ ≤
    (Fintype.card ι)*2^(Fintype.card ι) * (((1024 * π^2)/3).toNNReal + 2*(good_const hg)) *
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
      set C := ↑(Fintype.card ι) * 2 ^ Fintype.card ι * (↑(1024 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * (↑(g m) : ENNReal)
      let C' := 2 ^ Fintype.card ι * (↑(1024 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * (↑(g m) : ENNReal)
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
            refine lt_sq_of_sqrt_lt ?_
            simp
            exact pi_pos
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
        _ ≤ ‖∏ i : ι, (r i).toReal‖ₑ^2 * (2 ^ Fintype.card ι * (↑(1024 * π ^ 2 / 3).toNNReal + 2 * ↑(good_const hg)) * ↑(g m) * ∑ i, ∫⁻ (x : X), ‖(fun j y ↦ f j y / (r j).toReal) i x‖ₑ ^ q i ∂μ) := by
          apply mul_le_mul
          · apply le_refl
          · apply goal' (f := (fun j y ↦ ((f j y)/(r j).toReal))) hg μ hq m idx mon hS hS'
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

theorem og_goal [h: Nonempty ι]{g : ℕ → NNReal}{q : ι → ℝ}(hg: good g q)[MeasurableSpace X](μ : Measure X)(hq : (∀(i : ι), 0 < q i) ∧ ∑ (i : ι), 1/(q i) = 1 / 2)
  (m : ℕ)(idx : Fin (m+1) → ℕ)(mon : Monotone idx)(hS: MMeasurePreserving μ S)(hS': pairwise_commuting S)(hf: ∀(i : ι), Measurable (f i)): --(hf : ∀(i : ι), MeasureTheory.MemLp (f i) (q i) μ) Probably hf isnt needed, maybe (aestrongly)measurable or smth??? Something along those lines definetely (else integrals become zero on RHS)
    ∃ C : NNReal, ∑ i : Fin m, ∫⁻ (x : X), ‖(ergodic_avg (idx i.succ) S f x - ergodic_avg (idx ⟨i,get_rid i⟩) S f x)‖ₑ ^ 2 ∂μ ≤
    C * g m * ∏(i : ι), (∫⁻ (x : X), ‖f i x‖ₑ^(q i) ∂μ)^(2/(q i))  := by
      use (Fintype.card ι)*2^(Fintype.card ι) * (((1024 * π^2)/3).toNNReal + 2*(good_const hg))
      exact @goal ι _ X f S _ g q hg _ μ hq m idx mon hS hS' hf
-/
end Calderon
