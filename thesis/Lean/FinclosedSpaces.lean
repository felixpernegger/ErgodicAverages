import Mathlib
--set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.longLine false
--set_option linter.style.commandStart false
open Function Set Classical
noncomputable section

namespace Finclosed
universe u v

example : ℕ := 1
/-
Few things to do: FinclosedSpace would have been better with a predicate (yeahhh),
maybe redo that if you have time, at least
do it for the presentation.

Secondly a few things (in particular integrability of x^s is in mathlib!)
can be shortened significantly!

-/

def IsFinclosed {X : Type u} (F : Set (Finset X)): Prop :=
  ∅ ∈ F ∧ ∃ k : ℝ, ∀ (u : Finset X), (∃v ∈ F, u ⊆ v) →
  (∃u' ∈ F, u ⊆ u' ∧ (↑u' : Finset X).card ≤ k * u.card)

def sIsClosed {X : Type u} (F : Set (Finset X)) (u : Finset X) : Prop :=
  u ∈ F

def sIsSemiclosed {X : Type u} (F : Set (Finset X)) (u : Finset X) : Prop :=
  ∃ (v : Finset X), u ⊆ v ∧ sIsClosed F v


theorem sclosed_semiclosed {X : Type*} {F : Set (Finset X)} {u : Finset X} (h : sIsClosed F u):
  sIsSemiclosed F u := by use u
/-(Unfortunately), we have to do *something* about the empty set.
Either we require ∅ ∈ F or IsFinclosed as above-/

theorem sissemiclosed_mono
  {X : Type*} {F : Set (Finset X)} {u v : Finset X} (uh : sIsSemiclosed F u) (vu : v ⊆ u):
  sIsSemiclosed F v := by
  obtain ⟨o,oh⟩ := uh
  use o
  tauto

structure FinclosedSpace where
  X : Type u
  F : Set (Finset X)
  SpaceFinclosed : IsFinclosed F

example : FinclosedSpace where
  X := ℝ
  F := {∅, {1}}
  SpaceFinclosed := by
    constructor
    · simp only [mem_insert_iff, mem_singleton_iff, true_or]
    use 1
    intro u ⟨v,vh,_⟩
    by_cases ue : u = ∅
    · simp
      tauto
    use v
    simp_all only [mem_insert_iff, mem_singleton_iff, one_mul, Nat.cast_le, true_and]
    obtain _|_ := vh <;> simp_all

instance univ (U : Type u) : FinclosedSpace where
  X := U
  F := @Set.univ (Finset U)
  SpaceFinclosed := by
    constructor
    · trivial
    use 1
    intro u _
    use u
    simp only [mem_univ, subset_refl, one_mul, le_refl, and_self]

theorem empty_mem_finclosedspace (S : FinclosedSpace): ∅ ∈ S.F := S.SpaceFinclosed.1

theorem f_isfinclosed (S : FinclosedSpace): IsFinclosed S.F := S.SpaceFinclosed

def IsClosed {S : FinclosedSpace} (u : Finset S.X) : Prop :=
  sIsClosed S.F u

def carrier (S : FinclosedSpace): Set S.X :=
  {(x: S.X) | ∃ (u : Finset S.X), x ∈ u ∧ IsClosed u}

theorem isclosed_empty (S : FinclosedSpace): @IsClosed S ∅ := empty_mem_finclosedspace S

def IsSemiclosed {S : FinclosedSpace} (u : Finset S.X) : Prop :=
  sIsSemiclosed S.F u

def issemiclosed_mono {S : FinclosedSpace} {u v : Finset S.X} (uh : IsSemiclosed u) (vu : v ⊆ u):
  IsSemiclosed v := sissemiclosed_mono uh vu

theorem carrier_semiclosed {S : FinclosedSpace} {x : S.X} (h : x ∈ carrier S) :
  IsSemiclosed {x} := by
  obtain ⟨u,xu,uh⟩ := h
  use u
  unfold IsClosed at uh
  simp_all

theorem semiclosed_def {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u) :
  ∃ (v : Finset S.X), u ⊆ v ∧ IsClosed v := by
  unfold IsSemiclosed IsClosed at *
  obtain ⟨v,vh⟩ := h
  use v

theorem closed_semiclosed {S : FinclosedSpace} {u : Finset S.X} (h : IsClosed u):
  IsSemiclosed u := sclosed_semiclosed h

def Closureset {S : FinclosedSpace} (u : Set S.X) : Set (Finset S.X) :=
  {v : Finset S.X | u ⊆ v ∧ IsClosed v}

theorem closureset_def {S : FinclosedSpace}
    {u : Set S.X} {v : Finset S.X} (uv : u ⊆ v) (vc : IsClosed v):
    v ∈ Closureset u := by tauto

theorem closureset_mem {S : FinclosedSpace} {u : Set S.X} {s : Finset S.X} (h : s ∈ Closureset u):
      u ⊆ s := by unfold Closureset at h; simp_all

theorem closureset_closed {S : FinclosedSpace} {u s : Finset S.X} (h : s ∈ Closureset u):
 IsClosed s := by unfold Closureset at h; simp_all

theorem closed_mem_closureset {S : FinclosedSpace} {u : Finset S.X} (h : IsClosed u) :
  u ∈ Closureset (↑u : Set S.X) := by
  apply closureset_def <;> simp_all

theorem closureset_nonempty {S : FinclosedSpace} (u : Finset S.X):
  Nonempty (Closureset (↑u : Set S.X)) ↔ IsSemiclosed u := by
  unfold IsSemiclosed sIsSemiclosed Closureset
  simp only [Finset.coe_subset, coe_setOf, nonempty_subtype]
  rfl

theorem closureset_notsemiclosed {S : FinclosedSpace} {u : Finset S.X} (h : ¬IsSemiclosed u): Closureset (↑u : Set S.X) = ∅ := by
  contrapose h
  simp only [nonempty_iff_ne_empty'.mpr h, (closureset_nonempty u).1, not_true_eq_false, not_false_eq_true]

@[simp] theorem closureset_notfinite {S : FinclosedSpace} {u : Set S.X} (h : ¬Finite u): Closureset u = ∅ := by
  contrapose h
  simp_all
  obtain ⟨v,vh⟩ := nonempty_iff_ne_empty'.mpr h
  exact Finite.Set.subset (↑v) vh.1

example : sInf (∅ : Set ℝ) = 0 := by exact Real.sInf_empty

def ClosureFactorSet {S : FinclosedSpace} (u : Set S.X): ℝ :=
  sInf {x : ℝ | ∃ (v : Finset S.X), v ∈ Closureset (↑u : Set S.X) ∧ x = v.card / u.ncard}


theorem closurefactor_set_nonneg {S : FinclosedSpace} (u : Set S.X): 0 ≤ ClosureFactorSet u := by
  unfold ClosureFactorSet
  apply Real.sInf_nonneg
  intro _ xh
  simp_all
  obtain ⟨a,ah⟩ := xh
  rw [ah.2]
  apply div_nonneg <;> simp

@[simp] theorem closurefactor_set_emptyset (S : FinclosedSpace): @ClosureFactorSet S ∅ = 0 := by
  refine le_antisymm ?_ (@closurefactor_set_nonneg S ∅)
  unfold ClosureFactorSet
  apply Real.sInf_nonpos'
  use 0
  unfold Closureset
  simp only [empty_subset, true_and, mem_setOf_eq, ncard_empty, CharP.cast_eq_zero, div_zero,
    exists_and_right, and_true, le_refl]
  use ∅
  exact isclosed_empty S

theorem closurefactor_set_notsemiclosed {S : FinclosedSpace} {u : Finset S.X} (h : ¬IsSemiclosed u): ClosureFactorSet (↑u : Set S.X) = 0 := by
  simp only [ClosureFactorSet, closureset_notsemiclosed h, mem_empty_iff_false, false_and,
    exists_const, setOf_false, Real.sInf_empty]

theorem one_le_closurefactor_set_semiclosed {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u) (ne : u ≠ ∅): 1 ≤ ClosureFactorSet (↑u : Set S.X) := by
  unfold ClosureFactorSet IsSemiclosed sIsSemiclosed at *
  apply le_csInf
  · obtain ⟨v,uv,vh⟩ := h
    use v.card/u.card
    simp only [ncard_coe_Finset, mem_setOf_eq]
    use v
    tauto
  intro b bh
  obtain ⟨v,vh⟩ := bh
  rw [vh.2]
  unfold Closureset at vh
  simp_all
  refine (one_le_div ?_).mpr ?_
  · simp only [Nat.cast_pos, Finset.card_pos]
    exact Finset.nonempty_iff_ne_empty.mpr ne
  simp only [Nat.cast_le]
  exact Finset.card_le_card vh.1.1


theorem closurefactor_set_zero {S : FinclosedSpace} (u : Finset S.X):
    ClosureFactorSet (↑u : Set S.X) = 0 ↔ u = ∅ ∨ ¬IsSemiclosed u := by
  constructor
  swap
  · intro h
    obtain h|h := h
    · rw [h]
      simp only [Finset.coe_empty, closurefactor_set_emptyset]
    exact closurefactor_set_notsemiclosed h
  intro h
  by_cases uh : u = ∅
  · exact Or.inl uh
  right
  by_contra h0
  have := one_le_closurefactor_set_semiclosed h0 uh
  linarith

theorem bddbelow_closureset_quot {S : FinclosedSpace} (u : Set S.X):
    BddBelow {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑u.ncard} := by
  refine bddBelow_def.mpr ?_
  use 0
  intro x xh
  simp only [mem_setOf_eq] at xh
  obtain ⟨v,vh⟩ := xh
  rw [vh.2]
  apply div_nonneg <;> simp

theorem closurefactor_set_closed {S : FinclosedSpace} {u : Finset S.X} (ue : u ≠ ∅) (h : IsClosed u): ClosureFactorSet (↑u : Set S.X) = 1 := by
  apply le_antisymm
  swap
  · exact one_le_closurefactor_set_semiclosed (closed_semiclosed h) ue
  unfold ClosureFactorSet
  have onemem : 1 ∈ {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑(↑u : Set S.X).ncard} := by
    simp only [ncard_coe_Finset, mem_setOf_eq]
    use u
    simp [closed_mem_closureset h]
    have : 0 < (↑u.card : ℝ) := by
      simp only [Nat.cast_pos, Finset.card_pos]
      exact Finset.nonempty_iff_ne_empty.mpr ue
    field_simp
  apply (Real.sInf_le_iff (bddbelow_closureset_quot (↑u : Set S.X)) (Exists.intro 1 onemem)).2
  intro ε hε
  use 1
  simp_all

theorem nonempty_closureset_quot {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u): {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑((↑u : Set S.X)).ncard}.Nonempty := by
  obtain ⟨v,uv,vc⟩ := semiclosed_def h
  use ↑v.card / (↑(↑u : Set S.X).ncard : ℝ)
  simp only [ncard_coe_Finset, mem_setOf_eq]
  use v
  exact ⟨closureset_def uv vc, rfl⟩
--theorem closurefactor_set_ex{S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u): ∃ (x : )
set_option linter.unusedTactic false

theorem closurefactor_set_def {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u): ∃ (u' : Finset S.X), u' ∈ Closureset u ∧ u'.card = (ClosureFactorSet (↑u : Set S.X))*(u.card) := by
  by_cases ue : u = ∅
  · use ∅
    rw [ue]
    simp only [Finset.coe_empty, Finset.card_empty, CharP.cast_eq_zero, closurefactor_set_emptyset,
      mul_zero, and_true]
    apply closureset_def
    · simp only [Finset.coe_empty, subset_refl]
    exact isclosed_empty S
  have ucard : 0 < (↑u.card : ℝ) := by
      simp only [Nat.cast_pos, Finset.card_pos]
      exact Finset.nonempty_iff_ne_empty.mpr ue
  obtain ⟨v,uv,vc⟩ := semiclosed_def h
  unfold ClosureFactorSet
  have : 0 < 1/ (↑(↑u : Set S.X).ncard : ℝ) := by
    simp only [ncard_coe_Finset, one_div, inv_pos, Nat.cast_pos, Finset.card_pos]
    exact Finset.nonempty_iff_ne_empty.mpr ue
  have se : {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑(↑u : Set S.X).ncard}.Nonempty := by
    use (↑v.card : ℝ)/ ↑(↑u : Set S.X).ncard
    simp only [ncard_coe_Finset, mem_setOf_eq]
    use v
    simp only [Finset.coe_subset, closureset_def, and_self, uv, vc]
  obtain ⟨e,eh1,eh2⟩ := Real.lt_sInf_add_pos se this
  simp only [ncard_coe_Finset, mem_setOf_eq] at eh1
  obtain ⟨r,rc,re⟩ := eh1
  use r
  constructor
  · assumption
  rw [re] at eh2
  suffices g : (↑r.card : ℝ)/ ↑u.card = sInf {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑(↑u : Set S.X).ncard}
  · set t := sInf {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑(↑u : Set S.X).ncard}
    rw [← g]
    field_simp
  have quotmem : (↑r.card : ℝ) / ↑u.card ∈ {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑(↑u : Set S.X).ncard} := by
    simp only [ncard_coe_Finset, mem_setOf_eq]
    use r
  set T := {x : ℝ | ∃ v ∈ Closureset (↑u : Set S.X), x = ↑v.card / ↑(↑u : Set S.X).ncard}
  set q := (↑r.card : ℝ) / ↑u.card
  have qpos : 0 ≤ q := by
    unfold q
    apply div_nonneg <;> simp
  apply le_antisymm
  swap
  · refine (Real.sInf_le_iff ?_ se).mpr ?_
    · exact bddbelow_closureset_quot (↑u : Set S.X)
    intro ε εh
    use q
    simp only [lt_add_iff_pos_right, and_self, quotmem, εh]
  by_contra q0
  simp only [not_le] at q0
  have : 0 < q - sInf T := by linarith
  obtain ⟨f,fh1,fh2⟩ := Real.lt_sInf_add_pos se this
  have fh1' := fh1
  unfold T at fh1
  simp only [ncard_coe_Finset, mem_setOf_eq, add_sub_cancel] at fh1 fh2
  obtain ⟨v',v'h1,v'f⟩ := fh1
  rw [v'f] at fh2
  unfold q at fh2
  have : v'.card + 1 ≤ r.card := by
    suffices g : (↑v'.card : ℝ) < ↑r.card
    · simp only [Nat.cast_lt] at g
      exact g
    exact (div_lt_div_iff_of_pos_right ucard).mp fh2
  have fs : f < sInf T := by
    calc
      f = (↑v'.card : ℝ) / ↑u.card := by assumption
        _≤ ((↑r.card : ℝ) - 1) / ↑u.card := by
          refine div_le_div₀ ?_ ?_ ucard ?_
          · simp only [sub_nonneg, Nat.one_le_cast, Finset.one_le_card]
            unfold Closureset at rc
            simp only [Finset.coe_subset, mem_setOf_eq] at rc
            have ue' : u.Nonempty := by exact Finset.nonempty_iff_ne_empty.mpr ue
            obtain ⟨s,sh⟩ := ue'
            use s
            tauto
          · have : (↑(v'.card + 1) : ℝ) ≤ (↑r.card : ℝ) := by norm_cast
            push_cast at this
            linarith
          · rfl
        _= q - 1 / ↑(↑u : Set S.X).ncard := by
          unfold q
          have : (↑u : Set S.X).ncard = u.card := by simp only [ncard_coe_Finset]
          rw [this]
          ring
        _ < sInf T := by linarith
  contrapose fs
  simp only [not_lt]
  refine (Real.sInf_le_iff ?_ se).mpr ?_
  · exact bddbelow_closureset_quot (↑u : Set S.X)
  intros
  use f
  simp_all

theorem sinf_lemma {S : Set ℝ} {L : ℝ} (h : ∃ (x : ℝ), x ∈ S ∧ x ≤ L): sInf S ≤ max L 0 := by
  have Se : S.Nonempty := by
    obtain ⟨x,xh⟩ := h
    use x
    exact xh.1
  by_cases c : BddBelow S
  · apply le_sup_of_le_left
    apply (@Real.sInf_le_iff S L c Se).2
    intro _ _
    obtain ⟨x,xh⟩ := h
    use x
    simp only [true_and, xh]
    linarith
  rw [Real.sInf_def, Real.sSup_def]
  simp only [nonempty_neg, bddAbove_neg, and_false, ↓reduceDIte, neg_zero, le_sup_right, Se, c]

theorem closurefactor_set_bound' (S : FinclosedSpace): ∃ L : ℝ, ∀ (u : Finset S.X), ClosureFactorSet (↑u : Set S.X) ≤ L := by
  obtain ⟨_,L,Lh⟩ := S.3
  use max L 0
  intro u
  by_cases ue : u = ∅
  · rw [ue]
    simp only [Finset.coe_empty, closurefactor_set_emptyset, le_sup_right]
  by_cases us : IsSemiclosed u
  swap
  · rw [closurefactor_set_notsemiclosed us]
    simp only [le_sup_right]
  obtain ⟨v,uv,vh⟩ := semiclosed_def us
  unfold ClosureFactorSet
  apply sinf_lemma
  simp only [ncard_coe_Finset, mem_setOf_eq]
  have ve : v ≠ ∅ := Finset.Nonempty.ne_empty (Finset.Nonempty.mono uv (Finset.nonempty_iff_ne_empty.mpr ue))
  have : ∃ v ∈ S.F, u ⊆ v := by
    use v
    unfold IsClosed sIsClosed at vh
    simp only [and_self, vh, uv]
  obtain ⟨r,rc,ur,rs⟩ := Lh u this
  use (↑r.card : ℝ)/ (↑u.card : ℝ)
  constructor
  · use r
    unfold Closureset IsClosed sIsClosed at *
    simp_all
  have : 0 < (↑u.card : ℝ) := by
    simp only [Nat.cast_pos, Finset.card_pos]
    exact Finset.nonempty_iff_ne_empty.mpr ue
  exact (div_le_iff₀ this).mpr rs

def ClosureFactorOf {S : FinclosedSpace} (s : Set S.X): ℝ :=
  sSup {x : ℝ| ∃ (u : Set S.X), x = ClosureFactorSet u ∧ u ⊆ s}

def ClosureFactor (S : FinclosedSpace): ℝ :=
  sSup {x : ℝ | ∃ (u : Finset S.X), x = ClosureFactorSet (↑u : Set S.X)}

theorem closurefactor_nonneg (S : FinclosedSpace): 0 ≤ ClosureFactor S := by
  unfold ClosureFactor
  apply Real.sSup_nonneg
  intro x xh
  obtain ⟨v,vh⟩ := xh
  rw [vh]
  exact closurefactor_set_nonneg (↑v : Set S.X)

theorem closurefactorset_le_closurefactor {S : FinclosedSpace} (s : Finset S.X): ClosureFactorSet (↑s : Set S.X) ≤ ClosureFactor S := by
  unfold ClosureFactor
  set T := {x : ℝ | ∃ u : Finset S.X, x = ClosureFactorSet (↑u : Set S.X)}
  have bd : BddAbove T := by
    obtain ⟨L,Lh⟩ := closurefactor_set_bound' S
    use L
    unfold T upperBounds
    simp_all
  have ne : T.Nonempty := by
    unfold T
    use 0
    simp only [mem_setOf_eq]
    use ∅
    simp only [Finset.coe_empty, closurefactor_set_emptyset]
  apply (@Real.le_sSup_iff T (ClosureFactorSet (↑s : Set S.X)) bd ne).2
  intro ε εh
  use (ClosureFactorSet (↑s : Set S.X))
  constructor
  · unfold T
    simp only [mem_setOf_eq]
    use s
  linarith

theorem closurefactorset_notfinite {S : FinclosedSpace} {s : Set S.X} (hs : ¬ Finite s): ClosureFactorSet s = 0 := by
  unfold ClosureFactorSet
  have : {x : ℝ | ∃ v ∈ Closureset s, x = ↑v.card / ↑s.ncard} = ∅ := by
    by_contra h0
    obtain ⟨t,th⟩ := nonempty_iff_ne_empty.mpr h0
    simp only [mem_setOf_eq] at th
    obtain ⟨_,uc,_⟩ := th
    rw [closureset_notfinite hs] at uc
    contradiction
  rw [this, Real.sInf_empty]

theorem closurefactorset_le_closurefactor' {S : FinclosedSpace} (s : Set S.X): ClosureFactorSet (↑s : Set S.X) ≤ ClosureFactor S := by
  by_cases h : Finite s
  · obtain ⟨v,vh⟩ := Set.Finite.exists_finset_coe h
    rw [← vh]
    exact closurefactorset_le_closurefactor v
  rw [closurefactorset_notfinite h]
  exact closurefactor_nonneg S

theorem closurefactor_zero (S : FinclosedSpace): 0 = ClosureFactor S ↔ S.F = {∅} := by
  constructor
  · intro h
    have fa : ∀ (u : Set S.X), ClosureFactorSet u = 0 := by
      intro u
      apply le_antisymm
      · rw [h]
        exact closurefactorset_le_closurefactor' u
      exact closurefactor_set_nonneg u
    ext U
    constructor
    swap
    · intro Ue
      simp only [mem_singleton_iff] at Ue
      rw [Ue]
      exact empty_mem_finclosedspace S
    intro Uh
    simp only [mem_singleton_iff]
    by_contra h0
    have := closurefactorset_le_closurefactor' (↑U : Set S.X)
    have := one_le_closurefactor_set_semiclosed (closed_semiclosed Uh) h0
    linarith
  intro h
  apply le_antisymm
  · exact closurefactor_nonneg S
  unfold ClosureFactor
  apply Real.sSup_nonpos
  intro x xh
  obtain ⟨u,uh⟩ := xh
  suffices : x = 0
  · linarith
  rw [uh]
  apply (@closurefactor_set_zero S u).2
  by_cases ue : u = ∅
  · left
    assumption
  right
  contrapose ue
  simp_all
  obtain ⟨v,vh1,vh2⟩ := semiclosed_def ue
  unfold IsClosed sIsClosed at vh2
  simp_all

theorem closurefactor_def {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u):
  ∃ (u' : Finset S.X), u' ∈ Closureset u ∧ u'.card ≤ (ClosureFactor S)*(u.card) := by
  obtain ⟨v,vh1,vh2⟩ := closurefactor_set_def h
  use v
  simp only [vh1, true_and]
  have : 0 ≤ (↑u.card : ℝ) := by simp only [Nat.cast_nonneg]
  have := closurefactorset_le_closurefactor u
  rw [vh2]
  nlinarith

def Closure {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u): Finset S.X :=
  Exists.choose (closurefactor_def h)

theorem closure_mem {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u): u ⊆ Closure h := by
  suffices : Closure h ∈ Closureset u
  · apply closureset_mem this
  exact (Exists.choose_spec (closurefactor_def h)).1

theorem closure_is_closed {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u):
  IsClosed (Closure h) := by
  unfold Closure
  apply closureset_closed
  exact (Exists.choose_spec (closurefactor_def h)).1

theorem closure_closurefactor {S : FinclosedSpace} {u : Finset S.X} (h : IsSemiclosed u):
  (Closure h).card ≤ (ClosureFactor S)*(u.card) := by
  unfold Closure
  exact (Exists.choose_spec (closurefactor_def h)).2

def fun_closed {S : FinclosedSpace} (t : ℝ) (f : S.X → NNReal): Prop :=
  ∃ (C : ℝ), ∀ (u : Finset S.X), IsClosed u → ∑ i ∈ u, f i ≤ C*(u.card)^t

theorem fun_closed_nonneg {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f):
  ∃ (C : ℝ), (∀ (u : Finset S.X), IsClosed u → ∑ i ∈ u, f i  ≤ C*(u.card)^t) ∧ 0 ≤ C := by
  obtain ⟨C',hC'⟩ := h
  use max 0 C'
  simp_all
  intro u uh
  specialize hC' u uh
  apply le_trans hC'
  apply mul_le_mul_of_nonneg_right
  · simp only [le_sup_right]
  refine Real.rpow_nonneg ?_ t
  simp only [Nat.cast_nonneg]

def fun_closed_const {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f): ℝ :=
  Exists.choose (fun_closed_nonneg h)

theorem fun_closed_const_nonneg {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f):
  0 ≤ fun_closed_const h := (Exists.choose_spec (fun_closed_nonneg h)).2

theorem fun_closed_const_is_bound {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f):
 (∀ (u : Finset S.X), IsClosed u → ∑ i ∈ u, f i  ≤ (fun_closed_const h)*(u.card)^t) := (Exists.choose_spec (fun_closed_nonneg h)).1

/-the exponent t can get bigger:-/
theorem fun_closed_up {S : FinclosedSpace} {t u : ℝ} {f : S.X → NNReal} (h : fun_closed t f) (tu : t ≤ u): fun_closed u f := by
  use fun_closed_const h
  intro U Uh
  by_cases h' : U.card = 0
  · rw [Finset.card_eq_zero.mp h']
    simp only [Finset.sum_empty, NNReal.coe_zero, Finset.card_empty, CharP.cast_eq_zero]
    apply mul_nonneg
    · exact fun_closed_const_nonneg h
    exact Real.zero_rpow_nonneg u
  calc
    ↑(∑ i ∈ U, f i) ≤ fun_closed_const h * ↑U.card ^ t := by exact fun_closed_const_is_bound h U Uh
                  _ ≤ fun_closed_const h * ↑U.card ^ u := by
                    apply mul_le_mul
                    · rfl
                    · refine Real.rpow_le_rpow_of_exponent_le ?_ tu
                      simp only [Nat.one_le_cast, Finset.one_le_card]
                      exact Finset.card_ne_zero.mp h'
                    · apply Real.rpow_nonneg
                      simp only [Nat.cast_nonneg]
                    exact fun_closed_const_nonneg h

/-Negative exponent means that f^r is also fun closed for any 1 ≤ r-/
--theorem fun_closed_neg {t r: ℝ} {f : S.X → NNReal} (h : fun_closed t f) (ht : t ≤ 0) (hr : 1 ≤ r): fun_closed

/-note : fun closed implies that we dont need semiclosed-/

/-note : make ring instance here maybe-/
def UpBounded_on {X : Type u} (U : Set X) (f : X → NNReal):=
  ∃ (C : ℝ), ∀ (x : X), (x ∈ U) → f x ≤ C

def up_bounded_bound {X : Type u} {U : Set X} {f : X → NNReal} (h : UpBounded_on U f): ℝ :=
  Exists.choose h

theorem up_bounded_bound_is_bound {X : Type u} {U : Set X} {f : X → NNReal} (h : UpBounded_on U f):
    ∀ (x : X), (x ∈ U) → f x ≤ up_bounded_bound h := Exists.choose_spec h

theorem fun_bounded_carrier {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f): UpBounded_on (carrier S) f := by
  obtain ⟨C,Ch⟩ := h
  by_cases ht: 0 ≤ t
  · use C*(ClosureFactor S)^t
    intro x xh
    obtain ⟨u,xu,uh⟩ := closurefactor_def (carrier_semiclosed xh)
    obtain ⟨uh',uh''⟩ := xu
    have Cnonneg : 0 ≤ C := by
      specialize Ch u uh''
      have : 0 ≤ C * ↑u.card ^ t := by
        suffices : 0 ≤ (↑(∑ i ∈ u, f i) : ℝ)
        · linarith
        simp only [NNReal.coe_sum]
        apply Finset.sum_nonneg
        intro i iu
        simp only [NNReal.zero_le_coe]
      suffices goal : 0 < (↑u.card ^ t : ℝ)
      · nlinarith
      refine Real.rpow_pos_of_pos ?_ t
      simp_all
      use x
    calc
      ↑(f x : ℝ) = (↑(∑ i ∈ {x}, f i) : ℝ) := by simp only [Finset.sum_singleton]
        _ ≤ ∑ i ∈ u, f i := by
          simp only [NNReal.coe_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg uh'
          simp
        _ ≤ C*(u.card)^t := Ch u uh''
        _ ≤ C*(ClosureFactor S)^t := by
          simp_all
          refine mul_le_mul_of_nonneg ?_ ?_ Cnonneg ?_
          · rfl
          · refine Real.rpow_le_rpow ?_ uh ht
            simp only [Nat.cast_nonneg]
          refine Real.rpow_nonneg (closurefactor_nonneg S) t
  use C
  intro x xh
  obtain ⟨u,xu,uh⟩ := closurefactor_def (carrier_semiclosed xh)
  obtain ⟨uh',uh''⟩ := xu
  have Cnonneg : 0 ≤ C := by
    specialize Ch u uh''
    have : 0 ≤ C * ↑u.card ^ t := by
      suffices : 0 ≤ (↑(∑ i ∈ u, f i) : ℝ)
      · linarith
      simp only [NNReal.coe_sum]
      apply Finset.sum_nonneg
      intro i iu
      simp only [NNReal.zero_le_coe]
    suffices goal : 0 < (↑u.card ^ t : ℝ)
    · nlinarith
    refine Real.rpow_pos_of_pos ?_ t
    simp_all
    use x
  calc
    ↑(f x : ℝ) = (↑(∑ i ∈ {x}, f i) : ℝ) := by simp only [Finset.sum_singleton]
      _ ≤ ∑ i ∈ u, f i := by
        simp only [NNReal.coe_sum]
        apply Finset.sum_le_sum_of_subset_of_nonneg uh'
        simp only [Finset.mem_singleton, NNReal.zero_le_coe, implies_true]
      _ ≤ C*(u.card)^t := Ch u uh''
      _ ≤ C := by
        nth_rw 2[← mul_one C]
        apply mul_le_mul
        · rfl
        · simp_all
          refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
          · simp only [Nat.one_le_cast, Finset.one_le_card]
            use x
          exact le_of_lt ht
        · apply Real.rpow_nonneg
          simp only [Nat.cast_nonneg]
        assumption

def bound_fun {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f): ℝ :=
  max 0 (up_bounded_bound (fun_bounded_carrier h))

theorem bound_fun_is_bound {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f):
  ∀ (x : S.X), x ∈ (carrier S) → f x ≤ bound_fun h := by
  unfold bound_fun
  intro x xh
  calc
    (↑(f x) : ℝ) ≤ (up_bounded_bound (fun_bounded_carrier h)) := by
        exact up_bounded_bound_is_bound (fun_bounded_carrier h) x xh
    _≤ max 0 (up_bounded_bound (fun_bounded_carrier h)) := by exact le_max_right 0 (up_bounded_bound (fun_bounded_carrier h))


theorem bound_fun_nonneg {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (h : fun_closed t f) : 0 ≤ bound_fun h := by
  unfold bound_fun
  exact le_max_left 0 (up_bounded_bound (fun_bounded_carrier h))

section
variable {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (ht : t < 1) (hf : fun_closed t f) {s : Finset S.X} (hs : IsClosed s) (l : NNReal) (hl : l > 0)


variable (a : (Set { x : S.X // x ∈ s })) (b : {x : S.X // x ∈ s}) (c : Set ℤ)

end

theorem fun_closed_add {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} {g : S.X → NNReal} (hf : fun_closed t f) (hg : fun_closed t g): fun_closed t (f+g) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  use C + D
  intro u uc
  simp only [Pi.add_apply, NNReal.coe_sum, NNReal.coe_add]
  calc
    ∑ x ∈ u, ((↑(f x) : ℝ) + ↑(g x)) = ∑ x ∈ u, (↑(f x): ℝ) + (∑ x ∈ u, (↑(g x) : ℝ)) := by rw [Finset.sum_add_distrib]
    _≤ C * (u.card)^t + D * (u.card)^t := by
        specialize hC u
        specialize hD u
        apply add_le_add
        all_goals simp_all
    _= (C + D) * (u.card)^t := by ring

lemma nnreal_sum_mono {α : Type*} {u v : Finset α} (f : α → NNReal) (uv : u ⊆ v): ∑ i ∈ u, f i ≤ ∑ i ∈ v, f i := by
  exact Finset.sum_le_sum_of_ne_zero fun x a a_1 ↦ uv a

lemma nnreal_sum_mono' {α : Type*} {u v : Finset α} (f : α → NNReal) (uv : u ⊆ v): ∑ i ∈ u, (↑(f i) : ℝ) ≤ ∑ i ∈ v, (↑(f i) : ℝ) := by
  calc
    ∑ i ∈ u, (↑(f i) : ℝ)  = ↑(∑ i ∈ u, (f i)) := by simp only [NNReal.coe_sum]
      _≤ ↑(∑ i ∈ v, (f i)) := by refine NNReal.GCongr.toReal_le_toReal (nnreal_sum_mono f uv)
      _ = ∑ i ∈ v, (↑(f i) : ℝ) := by simp only [NNReal.coe_sum]


theorem preimage_bounded {S : FinclosedSpace} {t : ℝ} {f : S.X → NNReal} (ht : t < 1) (ht' : 0 ≤ t) (hf : fun_closed t f) {s : Finset S.X} (hs : IsClosed s) (l : NNReal) (hl : 0 < l):
  ↑(↑s ∩ f ⁻¹' Ioi l).ncard ≤ fun_closed_const hf ^ (1 - t)⁻¹ * ClosureFactor S ^ (t / (1 - t)) * ↑l ^ (-(1 - t)⁻¹) := by
    set d := ClosureFactor S
    set C := fun_closed_const hf
    set k := ((↑s : Set S.X) ∩ (f⁻¹' (Set.Ioi l))).ncard
    suffices : ((↑s : Set S.X) ∩ (f⁻¹' (Set.Ioi l))).ncard * l ≤ C* (d * k)^t
    have Cnonneg : 0 ≤ C := (Exists.choose_spec (fun_closed_nonneg hf)).2
    have dnonneg : 0 ≤ d := by exact closurefactor_nonneg S
    have knonneg : 0 ≤ k := by unfold k; simp only [zero_le]
    rw [Real.mul_rpow dnonneg, ←mul_assoc] at this
    swap
    · simp only [Nat.cast_nonneg]
    field_simp
    by_cases z: k=0
    rw [z]
    simp only [CharP.cast_eq_zero, one_div]
    apply mul_nonneg
    apply mul_nonneg
    apply Real.rpow_nonneg Cnonneg
    exact Real.rpow_nonneg dnonneg (t / (1 - t))
    apply Real.rpow_nonneg
    exact NNReal.zero_le_coe
    have onesubtpos : 1 - t > 0 := by linarith

    have kpos : 0 < k := by exact lt_of_le_of_ne knonneg fun a ↦ z (id (Eq.symm a))
    have klpos : 0 < k*l := by apply mul_pos; simp_all; exact hl
    calc
        (↑k : ℝ) = l^(-(↑1:ℝ))*((k * l)^(1-(1/(1-t))) * (k* l)^(1/(1-t))) := by
          rw [← Real.rpow_add]; simp; rw [mul_comm, mul_assoc]
          field_simp
          nth_rw 1[← Real.rpow_one (↑l : ℝ), ← Real.rpow_add]
          simp only [add_neg_cancel, Real.rpow_zero]
          repeat exact hl
          simp_all
        _ ≤ l^(-(↑1:ℝ))*((k* l)^(1-(1/(1-t))) * (C * d ^ t * k ^ t)^(1/(1-t))) := by
            apply mul_le_mul_of_nonneg_left
            apply mul_le_mul_of_nonneg_left
            refine Real.rpow_le_rpow ?_ this ?_
            simp_all
            apply one_div_nonneg.mpr
            linarith

            apply Real.rpow_nonneg
            simp_all
            refine Real.rpow_nonneg ?_ (-1)
            apply le_of_lt
            exact hl
        _ = C ^ (1 / (1 - t)) * d ^ (t / (1 - t)) * ↑l ^ (-1 / (1 - t)) := by
            repeat rw [Real.mul_rpow]
            repeat rw [← Real.rpow_mul]
            have : t * (1 / (1 - t)) = t / (1-t) := by field_simp
            rw [this]
            set c := C^(1 / (1-t))*(d ^ (t / (1 - t)))
            rw [← mul_assoc, mul_comm ((↑k : ℝ) ^ (1 - 1 / (1 - t))), ← mul_assoc ((↑l : ℝ) ^ (-1))]
            rw [← Real.rpow_add]
            swap
            exact hl
            simp only [one_div]
            have : -1 + (1 - (1 - t)⁻¹) = -1 / (1-t) := by field_simp; ring
            rw [this]
            set l := (↑l : ℝ) ^ (-1 / (1 - t))
            rw [mul_assoc, ← mul_assoc ((↑k :ℝ) ^ (1 - (1 - t)⁻¹)), mul_comm ((↑k :ℝ)^ (1 - (1 - t)⁻¹)), mul_assoc]
            rw [← Real.rpow_add]
            field_simp
            rw [mul_comm]
            all_goals try simp_all
            apply Real.rpow_nonneg dnonneg
            apply mul_nonneg Cnonneg
            apply Real.rpow_nonneg dnonneg
            apply Real.rpow_nonneg
            simp_all
    have fin : Set.Finite ((↑s : Set S.X) ∩ f ⁻¹' Ioi l) := by
      apply Finite.Set.subset (↑s : Set S.X)
      simp only [inter_subset_left]
    have semclosed : IsSemiclosed ((↑s : Set S.X) ∩ f ⁻¹' Ioi l).toFinset := by
      apply @issemiclosed_mono S s (((↑s : Set S.X) ∩ f ⁻¹' Ioi l).toFinset) (closed_semiclosed hs)
      simp only [toFinset_subset, inter_subset_left]
    calc
     ↑((↑s : Set S.X) ∩ f ⁻¹' Ioi l).ncard * (↑l : ℝ) = ∑ i ∈ ((↑s : Set S.X) ∩ f ⁻¹' Ioi l).toFinset, (↑l : ℝ) := by
        simp [- Fintype.card_ofFinset]
        left
        rw [← Finite.card_toFinset fin]
        calc
          (↑s ∩ f ⁻¹' Ioi l).ncard = (↑fin.toFinset : Set S.X).ncard := by simp only [toFinite_toFinset,
            coe_toFinset]
            _= fin.toFinset.card := ncard_coe_Finset fin.toFinset
      _≤ ∑ i ∈ ((↑s : Set S.X) ∩ f ⁻¹' Ioi l).toFinset, (↑(f i) : ℝ) := by
        apply Finset.sum_le_sum
        intro i ih
        simp_all
        exact le_of_lt ih.2
      _≤ ∑ i ∈ Closure semclosed, (↑(f i) : ℝ) := by
        apply nnreal_sum_mono'
        exact closure_mem semclosed
      _≤ C * (Closure semclosed).card^t := by
        unfold C fun_closed_const
        have := (Exists.choose_spec (fun_closed_nonneg hf)).1 (Closure semclosed) (closure_is_closed semclosed)
        simp_all
      _≤ C * (d * ↑k) ^ t := by
        apply mul_le_mul_of_nonneg_left
        swap
        · unfold C
          exact (Exists.choose_spec (fun_closed_nonneg hf)).2
        apply Real.rpow_le_rpow
        simp only [Nat.cast_nonneg]
        unfold d k at *
        apply le_trans (closure_closurefactor semclosed)
        suffices : (↑s ∩ f ⁻¹' Ioi l).toFinset.card = (↑s ∩ f ⁻¹' Ioi l).ncard
        · rw [this]
        exact Eq.symm (ncard_eq_toFinset_card' (↑s ∩ f ⁻¹' Ioi l))
        exact ht'

instance nnatt.instMeasurableSpace : MeasurableSpace ℕ := ⊤



--lemma int_lemma {f : ℝ → ℝ} {A B : Set ℝ}: ∫ x in A, (0:ℝ) = 0 := by sorry

lemma int_lemma {f g : ℝ → ℝ} {A : Set ℝ} (hA : MeasurableSet A) (hg : MeasureTheory.IntegrableOn g A) (mon : ∀ x ∈ A, f x ≤ g x) (fnonneg : ∀ x ∈ A, 0 ≤ f x): ∫ x in A, f x ≤ ∫ x in A, g x := by
  by_cases hf : MeasureTheory.IntegrableOn f A
  exact MeasureTheory.setIntegral_mono_on hf hg hA mon
  rw [MeasureTheory.integral_undef hf]
  apply MeasureTheory.setIntegral_nonneg hA
  intro x xh
  specialize mon x xh
  specialize fnonneg x xh
  linarith

variable {S : FinclosedSpace} {p : S.X → Prop}

def scoe (s : Set {x : S.X // p x}) : Set S.X := {x : S.X | ∃ (y : {x : S.X // p x}), y ∈ s ∧ x = ↑y}

lemma scoe_coe (s : Set {x : S.X // p x}) (a : {x : S.X // p x}) (ha : a ∈ s): ↑a ∈ scoe s := by
  unfold scoe
  simp only [mem_setOf_eq]
  use a

def scoe_map (s : Set {x : S.X // p x}): s → scoe s :=
  fun ⟨a,ah⟩ ↦ ⟨a, by apply scoe_coe; exact ah⟩

def scoe_map' (s : Set {x : S.X // p x}) (h : Inhabited S.X): {x : S.X // p x} → S.X :=
 fun a ↦ if ah : a ∈ s then (↑(scoe_map s ⟨a, ah⟩) : S.X) else default

lemma scoe_map'_mapsto (s : Set {x : S.X // p x}) (h : Inhabited S.X): MapsTo (scoe_map' s h) s (scoe s) := by
  intro x xs
  unfold scoe_map'
  simp only [xs, ↓reduceDIte, Subtype.coe_prop]

lemma scoe_map'_injon (s : Set {x : S.X // p x}) (h : Inhabited S.X): InjOn (scoe_map' s h) s := by
  intro ⟨a,ah'⟩ ah ⟨b,bh'⟩ bh ab
  unfold scoe_map' scoe_map at ab
  simp_all


lemma scoe_map'_surjon (s : Set {x : S.X // p x}) (h : Inhabited S.X): SurjOn (scoe_map' s h) s (scoe s):= by
  intro a ah
  unfold scoe at ah
  obtain ⟨⟨b,bh'⟩,bh⟩ := ah
  unfold scoe_map' scoe_map
  simp only [dite_eq_ite, mem_image, Subtype.exists]
  use b
  use bh'
  simp_all


lemma scoe_map'_bijon (s : Set {x : S.X // p x}) (h : Inhabited S.X): BijOn (scoe_map' s h) s (scoe s) := by
  unfold BijOn
  exact ⟨scoe_map'_mapsto s h, scoe_map'_injon s h, scoe_map'_surjon s h⟩

lemma scoe_ncard {s : Set {x : S.X // p x}}: s.ncard = (scoe s).ncard := by
  by_cases h : Nonempty S.X
  · have := inhabited_of_nonempty h
    unfold ncard encard ENat.card
    suffices : Cardinal.mk ↑s = Cardinal.mk ↑(scoe s)
    · rw [this]
    refine Cardinal.mk_congr ?_
    exact BijOn.equiv (scoe_map' s this) (scoe_map'_bijon s this)
  simp only [not_nonempty_iff] at h
  have se : s = ∅ := by exact eq_empty_of_isEmpty s
  have scoe : scoe s = ∅ := by exact eq_empty_of_isEmpty (scoe s)
  rw [scoe,se]
  simp only [ncard_empty]

lemma finint_rpow (L t: ℝ) (ht : -1 < t): ∫⁻ (a : ℝ) in Ioc 0 L, ‖a ^ t‖ₑ < ⊤ := by
  by_cases hL: L ≤ 0
  · have : Ioc 0 L = ∅ := by
      unfold Ioc
      ext
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intros
      linarith
    rw [this]
    simp only [MeasureTheory.Measure.restrict_empty, MeasureTheory.lintegral_zero_measure, ENNReal.zero_lt_top]
  refine (MeasureTheory.hasFiniteIntegral_def (fun a ↦ a ^ t) (MeasureTheory.volume.restrict (Ioc 0 L))).mp ?_
  refine (MeasureTheory.hasFiniteIntegral_iff_ofReal ?_).mpr ?_
  · unfold Filter.EventuallyLE Filter.Eventually
    simp only [Pi.zero_apply] --man kann {x|0 ≤ x^t} vereinfachen, ist aber nicht ganz easy, mit Real.rpow_def_of_neg
    --suffices : {(x : ℝ)| 0 ≤ x^t} =
    by_cases s0: 0 ≤ Real.cos (t * Real.pi)
    · have : {(x:ℝ) | 0 ≤ x ^ t} = Set.univ := by
        ext x
        simp only [mem_setOf_eq, mem_univ, iff_true]
        by_cases hx: 0 ≤ x
        · exact Real.rpow_nonneg hx t
        simp only [not_le] at hx
        rw [Real.rpow_def_of_neg hx]
        apply mul_nonneg
        · exact Real.exp_nonneg (Real.log x * t)
        exact s0
      rw [this]
      suffices : ∀ᵐ (x : ℝ) ∂MeasureTheory.volume.restrict (Ioc 0 L), ⊤
      · unfold Filter.Eventually at this
        simp [-MeasureTheory.ae_restrict_eq, -Filter.univ_mem] at this
        exact this
      apply MeasureTheory.ae_of_all
      simp only [«Prop».top_eq_true, implies_true]
    have : {(x:ℝ) | 0 ≤ x ^ t} = Ici 0 := by
      ext x
      simp only [mem_setOf_eq, mem_Ici]
      constructor
      · intro hx
        contrapose hx
        simp_all
        rw [Real.rpow_def_of_neg hx]
        apply mul_neg_of_pos_of_neg
        · exact Real.exp_pos (Real.log x * t)
        exact s0
      intro hx
      exact Real.rpow_nonneg hx t
    rw [this]
    simp only [measurableSet_Ioc, MeasureTheory.ae_restrict_eq]
    refine Filter.mem_inf_principal.mpr ?_
    have : {x | x ∈ Ioc 0 L → x ∈ Ici 0} = Set.univ := by
      ext x
      simp only [mem_Ioc, mem_Ici, and_imp, mem_setOf_eq, mem_univ, iff_true]
      intros
      linarith
    rw [this]
    exact Filter.univ_mem
  rw [← MeasureTheory.lintegral_indicator]
  swap
  · measurability
  by_contra h0
  simp only [not_lt, top_le_iff] at h0
  have rw0: ∫⁻ (a : ℝ), (Ioc 0 L).indicator (fun a ↦ ENNReal.ofReal (a ^ t)) a = ∫⁻ (a : ℝ), ENNReal.ofReal ((Ioc 0 L).indicator (fun a ↦ (a ^ t)) a) := by
    refine MeasureTheory.lintegral_congr ?_
    intro a
    by_cases ha : a ∈ Ioc 0 L
    · simp only [ha, indicator_of_mem]
    simp only [ha, not_false_eq_true, indicator_of_notMem, ENNReal.ofReal_zero]
  rw [rw0] at h0
  clear rw0
  have p0: (∫⁻ (a : ℝ), ENNReal.ofReal ((Ioc 0 L).indicator (fun a ↦ (a ^ t)) a)).toReal = 0 := by
    rw [h0]
    rfl
  rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae] at p0
  suffices : ∫ (a : ℝ), (Ioc 0 L).indicator (fun a ↦ a ^ t) a = (1+t)⁻¹ *L^(1+t)
  · rw [this] at p0
    simp only [mul_eq_zero, inv_eq_zero, not_le] at p0 hL
    obtain p0|p0 := p0
    · linarith
    have := (Real.rpow_eq_zero (x := L) (y := 1+t) (le_of_lt hL) (by linarith)).1 p0
    linarith
  calc
    ∫ (a : ℝ), (Ioc 0 L).indicator (fun a ↦ a ^ t) a = ∫ (a : ℝ) in (Ioc 0 L), (fun a ↦ a ^ t) a := by
      refine MeasureTheory.integral_indicator ?_
      measurability
        _ = ∫ (a : ℝ) in (Ioc 0 L), a ^ t := rfl
        _ = ∫ (a : ℝ) in (0 : ℝ)..L, a ^ t := by
          refine Eq.symm (intervalIntegral.integral_of_le ?_)
          linarith
        _ = (L ^ (t + 1) - 0 ^ (t + 1)) / (t + 1) := by
          rw [integral_rpow]
          left
          exact ht
        _= (1 + t)⁻¹ * L ^ (1 + t) := by
          have t0: t + 1 ≠ 0 := by linarith
          rw [add_comm 1]
          simp only [ne_eq, t0, not_false_eq_true, Real.zero_rpow, sub_zero]
          exact div_eq_inv_mul (L ^ (t + 1)) (t + 1)
  · unfold Filter.EventuallyLE
    apply MeasureTheory.ae_of_all
    intro a
    by_cases ha : a ∈ Ioc 0 L
    · simp only [Pi.zero_apply, ha, indicator_of_mem]
      refine Real.rpow_nonneg ?_ t
      unfold Ioc at ha
      simp only [mem_setOf_eq] at ha
      linarith
    simp only [Pi.zero_apply, ha, not_false_eq_true, indicator_of_notMem, le_refl]
  measurability

lemma aestronglymeasurable_mono_ioc {f : ℝ → ℝ} {a b : ℝ} (h : ∀ (x y : ℝ), (x ∈ Ioc a b) → (y ∈ Ioc a b) → x ≤ y → f x ≤ f y): MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioc a b)) := by --benütz  ich evtl gar nicht....
  unfold MeasureTheory.AEStronglyMeasurable --ehh
  refine (aestronglyMeasurable_indicator_iff ?_).mp ?_
  · measurability
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  by_cases ab : b ≤ a
  · have : Ioc a b = ∅ := by
      exact Ioc_eq_empty_of_le ab
    rw [this]
    simp only [indicator_empty, measurable_const]
  simp only [not_le] at ab
  apply measurable_of_Ioi
  intro t
  let l := min (max a (sInf (((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t)))) b
  by_cases ne : Ioc a b ∩ ((Ioc a b).indicator f ⁻¹' Ioi t) = ∅
  · by_cases t0:0 ≤ t
    · have : (Ioc a b).indicator f ⁻¹' Ioi t = ∅ := by
        ext s
        simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
        by_cases sh : s ∈ Ioc a b
        · simp only [sh, indicator_of_mem]
          by_contra h0
          have : s ∈ Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t := by --simp_all doesnt solve this LOL
            simp only [mem_Ioc, not_le] at sh h0
            simp only [mem_inter_iff, mem_Ioc, sh, and_self, mem_preimage, indicator_of_mem,
              mem_Ioi, h0]
          rw [ne] at this
          contradiction
        simp only [sh, not_false_eq_true, Set.indicator_of_notMem]
        exact t0
      rw [this]
      simp only [MeasurableSet.empty]
    suffices : (Ioc a b).indicator f ⁻¹' Ioi t = Set.univ \ (Ioc a b)
    · rw [this]
      measurability
    ext s
    simp only [mem_preimage, mem_Ioi, mem_diff, mem_univ, true_and]
    constructor
    · intro sh as
      suffices : s ∈ Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t
      · rw [ne] at this
        contradiction
      simp only [mem_inter_iff, mem_Ioc, mem_preimage, mem_Ioi]
      simp only [mem_Ioc] at sh as
      tauto
    intro sh
    have : (Ioc a b).indicator f s = 0 := by simp only [sh, not_false_eq_true, Set.indicator_of_notMem]
    rw [this]
    exact lt_of_not_ge t0
  have : Ioc a b ∩ ((Ioc a b).indicator f ⁻¹' Ioi t) = Ioc l b ∨ Ioc a b ∩ ((Ioc a b).indicator f ⁻¹' Ioi t) = Icc l b := by
    have s1: Ioc l b ⊆ Ioc a b ∩ ((Ioc a b).indicator f ⁻¹' Ioi t) := by
      unfold Ioc Ioi
      simp only [preimage_setOf_eq, subset_inter_iff, setOf_subset_setOf, and_imp]
      constructor
      · intro s ls sb
        constructor
        · calc
            a ≤ l := by
              apply le_min
              · simp only [le_sup_left]
              exact le_of_lt ab
            _< s := ls
        exact sb
      intro s ls sb
      have : s ∈ {x | a < x ∧ x ≤ b} := by
        constructor
        · calc
            a ≤ l := by
              apply le_min
              · simp
              exact le_of_lt ab
            _< s := ls
        exact sb
      have : {x | a < x ∧ x ≤ b}.indicator f s = f s := by
        simp [this]
      rw [this]
      clear this

      by_contra h0
      simp at h0
      by_cases la : l=a
      · unfold l at la
        obtain hl|hl := min_choice (a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) b
        swap
        · rw [hl] at la
          linarith
        rw [la] at hl
        simp at hl this
        have ah : a = sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t) := by
          refine le_antisymm ?_ hl
          apply le_csInf
          · exact nonempty_iff_ne_empty.mpr ne
          intro w wh
          simp at wh
          linarith
        have cop := this
        obtain ⟨hh,trash⟩ := this
        clear trash
        rw [ah] at hh
        have : ∀ (ε : ℝ), 0 < ε → ∃ x ∈ Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t, x < a + ε := by
          refine (Real.sInf_le_iff ?_ ?_).1 ?_
          use a
          unfold lowerBounds
          simp only [mem_inter_iff, mem_Ioc, mem_preimage, and_imp, mem_setOf_eq]
          intros
          linarith
          exact nonempty_iff_ne_empty.mpr ne
          linarith
        have as : 0 < s-a := by linarith
        obtain ⟨e,⟨eh11,e12⟩,eh2⟩ := this (s-a) as
        simp [eh11] at eh2 e12

        specialize h e s eh11 cop (le_of_lt eh2)
        linarith
      have lab : l ∈ Ioc a b := by
        simp
        constructor
        · contrapose la
          simp_all
          apply le_antisymm la
          by_cases lb : l = b
          · linarith
          have : l = (a ⊔ sInf ((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) := by
            have : l = (a ⊔ sInf ((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) ∨ l = b := by exact min_choice (a ⊔ sInf ((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) b
            tauto
          rw [this]
          simp
        exact min_le_right (a ⊔ sInf ((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) b
      have fls := h l s lab this (le_of_lt ls)
      have flt : f l ≤ t := by linarith
      have infb : (a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) ≤ b := by
        simp [le_of_lt ab]
        refine (Real.sInf_le_iff ?_ ?_).mpr ?_
        use a
        unfold lowerBounds
        intro s ⟨⟨hs,_⟩,_⟩
        exact le_of_lt hs
        exact nonempty_iff_ne_empty.mpr ne
        intro e eh
        obtain ⟨u,uh⟩ := nonempty_iff_ne_empty.mpr ne
        use u
        constructor
        · exact uh
        simp_all
        linarith

      have hl' : l = (a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) := by exact min_eq_left infb
      have hl'' : l = sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t) := by
        rw [hl']
        have : a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t) = a ∨ a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)= sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t) := max_choice a (sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t))
        obtain this|this := this
        · rw [hl'] at la
          rw [this] at la
          contradiction
        exact this
      rw [hl''] at ls
      have tt: ∀ (ε : ℝ), 0 < ε → ∃ x ∈ Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t, x < l + ε := by
        refine (Real.sInf_le_iff ?_ ?_).1 ?_
        use a
        unfold lowerBounds
        simp only [mem_inter_iff, mem_Ioc, mem_preimage, and_imp, mem_setOf_eq]
        intro w wa wb hw
        linarith
        exact nonempty_iff_ne_empty.mpr ne
        rw [hl'']
      have sl : 0 < s - l := by linarith
      obtain ⟨p,⟨ph11,ph12⟩,ph2⟩ := tt (s-l) sl
      simp [ph11] at ph12
      simp at ph11 ph2
      specialize h p s ph11 this (le_of_lt ph2)
      linarith

    have s2: Ioc a b ∩ ((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t) ⊆ Icc l b := by
      unfold Ioi Ioc Icc
      intro s
      simp
      intro as sb th
      constructor
      swap
      · exact sb
      calc
        l ≤ (a ⊔ sInf ((Ioc a b) ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) := by unfold l; exact min_le_left (a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) b
        _≤ s := by
          apply max_le
          · exact le_of_lt as
          refine (Real.sInf_le_iff ?_ ?_).mpr ?_
          use a
          unfold lowerBounds
          simp only [mem_inter_iff, mem_Ioc, mem_preimage, and_imp, mem_setOf_eq]
          intros
          linarith
          exact nonempty_iff_ne_empty.mpr ne
          intro e eh
          use s
          have : {x | a < x ∧ x ≤ b}.indicator f s = f s := by
            suffices : s ∈ {x | a < x ∧ x ≤ b}
            · simp [this]
            simp_all
          constructor
          · simp_all
          linarith
    have : Ioc a b ∩ (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t) = (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t) := by simp
    rw [this] at s2
    clear this
    have temp: Icc l b = Ioc l b ∪ {l} := by
        ext s
        simp_all
        constructor
        intro hh
        by_cases sl : s = l
        left
        exact sl
        right
        constructor
        · contrapose sl
          simp_all
          linarith
        exact hh.2
        intro hh
        obtain hh|hh := hh
        · simp [hh]
          exact min_le_right (a ⊔ sInf (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)) b
        simp [hh]
        linarith
    by_cases ss : l ∈ Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t
    right
    ext s
    constructor
    · intro sh
      have : s ∈ Icc l b := s2 sh
      rw [temp] at this
      tauto
    intro sh
    rw [temp] at sh
    obtain sh|sh := sh
    · exact s1 sh
    simp at sh
    rw [sh]
    exact ss

    left
    ext s
    constructor
    · intro sh
      have : s ∈ Icc l b := s2 sh
      rw [temp] at this
      obtain this|this := this
      · exact this
      simp at this
      rw [this] at sh
      contradiction
    intro sh
    tauto
  by_cases ht: t < 0
  · suffices goal : (Ioc a b).indicator f ⁻¹' Ioi t = (Set.univ : Set ℝ)\ (Ioc a b) ∪ (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)
    · rw [goal]
      obtain this|this := this
      · rw [this]
        refine MeasurableSet.union ?_ ?_
        · simp
        exact measurableSet_Ioc
      rw [this]
      apply MeasurableSet.union
      · simp
      exact measurableSet_Icc
    set S := (Ioc a b).indicator f ⁻¹' Ioi t
    calc
      S = ((Set.univ : Set ℝ)\ (Ioc a b) ∩ S) ∪ ((Ioc a b) ∩ S) := by
          rw [← @union_inter_distrib_right]
          simp
      _ = ((Set.univ : Set ℝ)\ (Ioc a b)) ∪ (Ioc a b ∩ S) := by
        suffices : ((Set.univ : Set ℝ)\ (Ioc a b) ∩ S) = (Set.univ : Set ℝ)\ (Ioc a b)
        · rw [this]
        ext x
        unfold S
        simp [-mem_Ioc]
        intro xh
        simp [xh]
        exact ht

  simp at ht
  suffices goal : (Ioc a b).indicator f ⁻¹' Ioi t = (Ioc a b ∩ (Ioc a b).indicator f ⁻¹' Ioi t)
  · rw [goal]
    obtain this|this := this
    · rw [this]
      simp
    rw [this]
    simp
  set S := (Ioc a b).indicator f ⁻¹' Ioi t
  calc
    S = ((Set.univ : Set ℝ)\ (Ioc a b) ∩ S) ∪ ((Ioc a b) ∩ S) := by
        rw [← @union_inter_distrib_right]
        simp
    _ = (Ioc a b ∩ S) := by
      simp
      intro s ⟨sh1,sh2⟩
      exfalso
      unfold S at sh2
      simp [-mem_Ioc] at sh2 sh1
      simp [sh1] at sh2
      linarith



lemma aestronglymeasurable_mono_down {f : ℝ → ℝ} {a b : ℝ} (h : ∀ (x y : ℝ), (x ∈ Ioc a b) → (y ∈ Ioc a b) → x ≤ y → f y ≤ f x): MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioc a b)) := by
  have neg : MeasureTheory.AEStronglyMeasurable (-f) (MeasureTheory.volume.restrict (Ioc a b)) := by
    apply aestronglymeasurable_mono_ioc
    simp_all
  have negone : MeasureTheory.AEStronglyMeasurable (fun a ↦ (-1 : ℝ)) (MeasureTheory.volume.restrict (Ioc a b)) := by
    simp_all only [mem_Ioc, and_imp]
    apply MeasureTheory.aestronglyMeasurable_const
  have g : f = fun a ↦ -1 * (-f a) := by simp
  rw [g]
  apply MeasureTheory.AEStronglyMeasurable.mul
  · exact negone
  exact neg

lemma aestronglymeasurable_zero_set
  {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) (h : ∀ (x : ℝ), x ∈ s → f x = 0):
  MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict s) := by
  apply (aestronglyMeasurable_indicator_iff hs).mp
  suffices : s.indicator f = 0
  · rw [this]
    measurability
  ext x
  simp
  intro xh
  exact h x xh

lemma integrable_on_zero_set {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) (h : EqOn 0 f s):
  MeasureTheory.IntegrableOn f s := by
  refine MeasureTheory.IntegrableOn.congr_fun ?_ h hs
  unfold MeasureTheory.IntegrableOn MeasureTheory.Integrable
  constructor
  · measurability
  refine MeasureTheory.HasFiniteIntegral.restrict ?_
  refine (MeasureTheory.hasFiniteIntegral_def 0 MeasureTheory.volume).mpr ?_
  simp only [Pi.zero_apply, enorm_zero, MeasureTheory.lintegral_const,
    MeasureTheory.measure_univ_of_isAddLeftInvariant, zero_mul, ENNReal.zero_lt_top]

theorem layercake_sum {Y : Type*} (hY : Finite Y) (e : Y → ℝ) (he : 0 ≤ e) {p : ℝ} (hp : 1 ≤ p):
  ∑' x : Y, (e x)^p = p*∫ (t : ℝ) in (Ioi 0), t^(p-1) * (e ⁻¹' ((Ioi t) ∪ (Iio (-t)))).ncard := by
  let inst: MeasurableSpace Y := ⊤
  have allm (s : Set Y): MeasurableSet s := by
    unfold MeasurableSet
    unfold inst
    tauto
  have inst' : MeasurableSingletonClass Y := {
    measurableSet_singleton := by
      intro x
      exact allm {x}
  }
  let μ := @MeasureTheory.Measure.count Y inst
  have allf (f : Y → ℝ): Measurable f := by
    unfold Measurable
    intro s hs
    exact allm (f ⁻¹' s)
  have aem : AEMeasurable (abs e) μ := by
    refine Measurable.aemeasurable ?_
    exact allf |e|
  have posm : 0 ≤ᵐ[μ] |e| := by
    unfold Filter.EventuallyLE
    apply MeasureTheory.ae_of_all
    intro a
    simp only [Pi.zero_apply, Pi.abs_apply, abs_nonneg]
  have lem := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
   (f := abs e) μ (p := p) (p_pos :=
    by linarith) (f_mble := aem) posm
  have rw1: ∫⁻ (t : ℝ) in Ioi 0, μ {a | t < |e| a} * ENNReal.ofReal (t ^ (p - 1)) =
    ∫⁻ (t : ℝ) in Ioi 0, μ (e ⁻¹' (Ioi t ∪ Iio (-t))) * ENNReal.ofReal (t ^ (p - 1)) := by
    apply MeasureTheory.lintegral_congr
    intro t
    suffices : {a | t < |e| a} = e ⁻¹' (Ioi t ∪ Iio (-t))
    · rw [this]
    ext a
    simp only [Pi.abs_apply, mem_setOf_eq, preimage_union, mem_union, mem_preimage, mem_Ioi,
      mem_Iio]
    have := lt_abs (a := t) (b := e a)
    have : t < -e a ↔ e a < - t := by constructor; intro; linarith; intro; linarith
    tauto
  rw [rw1] at lem
  clear rw1
  unfold μ at lem
  rw [MeasureTheory.lintegral_count] at lem
  have rw2: ∑' (x : Y), e x ^ p = (∑' (a : Y), ENNReal.ofReal (|e| a ^ p)).toReal  := by
    calc
      ∑' (x : Y), e x ^ p = ∑' (a : Y), |e| a ^ p := by
          simp
          suffices : (fun x ↦ e x ^ p) = (fun a ↦ |e a| ^ p)
          · rw [this]
          ext x
          rw [Eq.symm (abs_of_nonneg he)]
          simp
        _ = (ENNReal.ofReal (∑' (a : Y), |e| a ^ p)).toReal := by
          refine Eq.symm (ENNReal.toReal_ofReal ?_)
          apply tsum_nonneg
          intro i
          simp
          refine Real.rpow_nonneg ?_ p
          simp
        _ = (∑' (a : Y), ENNReal.ofReal (|e| a ^ p)).toReal := by
            simp
            suffices :
            ENNReal.ofReal (∑' (a : Y), |e a| ^ p) = ∑' (a : Y), ENNReal.ofReal (|e a| ^ p)
            · rw [this]
            refine ENNReal.ofReal_tsum_of_nonneg ?_ ?_
            · intro i
              refine Real.rpow_nonneg ?_ p
              simp
            apply Summable.of_finite
  rw [rw2]
  clear rw2
  rw [lem]
  clear lem
  simp
  have rw3: (ENNReal.ofReal p).toReal = p := by simp; linarith
  rw [rw3]
  clear rw3
  simp
  left
  have rw4: ∫⁻ (t : ℝ) in Ioi 0,
    MeasureTheory.Measure.count (e ⁻¹' Ioi t ∪ e ⁻¹' Iio (-t)) * ENNReal.ofReal (t ^ (p - 1)) = ∫⁻ (t : ℝ) in Ioi 0,
    ENNReal.ofReal (t ^ (p - 1))  * (e ⁻¹' Ioi t ∪ e ⁻¹' Iio (-t)).ncard := by
    apply MeasureTheory.lintegral_congr
    intro a
    suffices : MeasureTheory.Measure.count (e ⁻¹' Ioi a ∪ e ⁻¹' Iio (-a)) = ↑(e ⁻¹' Ioi a ∪ e ⁻¹' Iio (-a)).ncard
    · rw [this]
      rw [mul_comm]
    set S := e ⁻¹' Ioi a ∪ e ⁻¹' Iio (-a)
    have : Finite S := by
      exact Finite.Set.finite_union (e ⁻¹' Ioi a) (e ⁻¹' Iio (-a))
    rw [MeasureTheory.Measure.count_apply (allm S)]
    suffices : S.encard = S.ncard
    · rw [this]
      simp
    exact Eq.symm (Finite.cast_ncard_eq this)
  rw [rw4]
  clear rw4
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · suffices : ∫⁻ (t : ℝ) in Ioi 0, ENNReal.ofReal (t ^ (p - 1)) * ↑(e ⁻¹' Ioi t ∪ e ⁻¹' Iio (-t)).ncard = ∫⁻ (a : ℝ) in Ioi 0, ENNReal.ofReal (a ^ (p - 1) * ↑(e ⁻¹' Ioi a ∪ e ⁻¹' Iio (-a)).ncard)
    · rw [this]
    apply MeasureTheory.lintegral_congr
    intro a
    set c := (e ⁻¹' Ioi a ∪ e ⁻¹' Iio (-a)).ncard
    set d := a ^ (p - 1)
    calc
      ENNReal.ofReal d * ↑c = ENNReal.ofReal d *  ENNReal.ofReal (↑c : ℝ) := by simp
        _ = ENNReal.ofReal (d * ↑c) := by refine Eq.symm (ENNReal.ofReal_mul' ?_); unfold c; simp
  · unfold Filter.EventuallyLE Filter.Eventually
    simp
    refine Filter.mem_inf_principal.mpr ?_
    simp
    have : {(x:ℝ) | 0 < x → 0 ≤ x ^ (p - 1) * (↑((e ⁻¹' Ioi x ∪ e ⁻¹' Iio (-x)) : Set Y).ncard : ℝ)} = Set.univ := by
      ext x
      simp
      intro xh
      apply mul_nonneg
      · exact Real.rpow_nonneg (le_of_lt xh) (p - 1)
      exact Nat.cast_nonneg' (e ⁻¹' Ioi x ∪ e ⁻¹' Iio (-x)).ncard
    rw [this]
    exact Filter.univ_mem
  refine (aestronglyMeasurable_indicator_iff ?_).mp ?_
  · measurability
  rw [indicator_mul]
  apply MeasureTheory.AEStronglyMeasurable.mul
  · measurability
  --we can bound again, as Y is finite
  let L := sSup (e '' Set.univ)
  suffices : ((Ioi 0).indicator fun t ↦ (↑(e ⁻¹' Ioi t ∪ e ⁻¹' Iio (-t)).ncard : ℝ)) = (Ioc 0 L).indicator fun t ↦ ↑(e ⁻¹' Ioi t ∪ e ⁻¹' Iio (-t)).ncard
  · rw [this]
    refine (aestronglyMeasurable_indicator_iff ?_).mpr ?_
    · measurability
    apply aestronglymeasurable_mono_down
    intro x y xh yh xy
    simp
    apply ncard_mono
    intro t ht
    simp_all
    obtain ht|ht := ht
    · left
      linarith
    right
    linarith
  ext t
  by_cases ht: t ∈ (Ioc 0 L)
  · have : t ∈ Ioi 0 := by
      simp_all
    simp [this, ht]
  simp [ht]
  intro ht'
  simp [ht'] at ht
  suffices : e ⁻¹' Ioi t ∪ e ⁻¹' Iio (-t) = ∅
  · rw [this]
    exact ncard_empty Y
  ext s
  simp
  constructor
  · calc
      e s ≤ L := by
        unfold L
        simp
        have hs : e s ∈ range e := by use s
        refine (Real.le_sSup_iff ?_ ?_).mpr ?_
        · exact Finite.bddAbove_range e
        · use e s
        intros
        use e s
        constructor
        · exact hs
        linarith
      _ ≤ t := by linarith
  calc
    -t ≤ 0 := by linarith
      _≤ e s := he s


set_option maxHeartbeats 400000 in
--Long calculations (TBD)
theorem layercake_overkill
    {S : FinclosedSpace} {b r : ℝ} (hb : b < 1) (hb2 : 0 ≤ b) {f : S.X → NNReal}
    (hf : fun_closed b f) (hr : 1 / (1 - b) < r): fun_closed 0 (f^r) := by
  have hr' : 1 < r := by
    calc
      1 ≤ 1/(1-b) := by
        apply one_le_one_div
        all_goals simp_all
      _ < r := by assumption
  set L := bound_fun hf
  set C := fun_closed_const hf
  set k := ClosureFactor S
  use r * C^(1/(1-b)) * k^(b/(1-b)) * ∫ (s : ℝ) in Ioc 0 L, s^(r-1-1/(1-b))
  intro U Uh
  simp only [Pi.pow_apply, NNReal.coe_sum, NNReal.coe_rpow, one_div, Real.rpow_zero, mul_one]
  set g : (S.X → ℝ):= fun x ↦ abs (f x)
  calc
    ∑ x ∈ U, ↑(f x) ^ r ≤ ∑ x ∈ U, (g x) ^ r := by unfold g; simp only [NNReal.abs_eq, le_refl]
      _= ∑' x : U, (g x) ^ r := by rw [← @Finset.tsum_subtype]
      _= r * ∫ (s : ℝ) in Ioi 0, s ^ (r - 1) * ↑((fun x ↦ g (↑x : U)) ⁻¹' (Ioi s ∪ Iio (-s))).ncard := by
        rw [layercake_sum]
        exact Finite.of_fintype { x // x ∈ U }
        unfold g
        intro x
        simp only [Pi.zero_apply, NNReal.abs_eq, NNReal.zero_le_coe]
        linarith
      _≤ r * ∫ (s : ℝ) in Ioi 0, s ^ (r - 1) * ↑(↑U ∩ g⁻¹' (Ioi s ∪ Iio (-s))).ncard := by
        --unfold g
        refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
        simp only [le_refl]
        swap
        linarith
        swap
        refine MeasureTheory.setIntegral_nonneg ?_ ?_
        intros
        simp only [measurableSet_Ioi]
        intros
        simp only [preimage_union]
        apply mul_nonneg
        refine Real.rpow_nonneg ?_ (r - 1)
        apply le_of_lt
        assumption
        simp only [Nat.cast_nonneg]
        apply int_lemma
        · measurability
        · have : (fun (x : ℝ) ↦ x ^ (r - 1) * ↑((↑U : Set S.X) ∩ g ⁻¹' (Ioi x ∪ Iio (-x))).ncard) = (Iic L).indicator (fun (x : ℝ) ↦ x ^ (r - 1) * ↑((↑U  : Set S.X) ∩ g ⁻¹' (Ioi x ∪ Iio (-x))).ncard) := by
            ext a
            simp only [preimage_union]
            by_cases ha : a ∈ Iic L
            · simp [ha]
            simp [ha]
            right
            suffices : (↑U ∩ (g ⁻¹' Ioi a ∪ g ⁻¹' Iio (-a))) = ∅
            · rw [this]
              simp only [ncard_empty]
            ext s
            simp only [mem_inter_iff, Finset.mem_coe, mem_union, mem_preimage, mem_Ioi, mem_Iio,
              mem_empty_iff_false, iff_false, not_and, not_or, not_lt]
            intro sU
            unfold g
            simp at ha
            simp
            constructor
            · calc
                ↑(f s) ≤ L := by unfold L; apply bound_fun_is_bound; unfold carrier; use U
                  _ ≤ a := by linarith
            calc
              -a ≤ -L := by linarith
                _≤ 0 := by simp; exact bound_fun_nonneg hf
                _≤ ↑(f s) := by simp
          rw [this]
          clear this
          refine (MeasureTheory.integrable_indicator_iff ?_).mp ?_
          · measurability
          rw [@indicator_indicator, @Ioi_inter_Iic]
          refine (MeasureTheory.integrable_indicator_iff ?_).mpr ?_
          · measurability
          unfold MeasureTheory.IntegrableOn MeasureTheory.Integrable
          constructor
          · apply MeasureTheory.AEStronglyMeasurable.mul
            · measurability
            apply aestronglymeasurable_mono_down
            unfold Ioc
            simp only [mem_setOf_eq, Nat.cast_le, and_imp]
            intro x y xp xL yp yL xy
            apply ncard_le_ncard
            · unfold Ioi
              intro t
              simp
              intro _ h
              constructor
              · assumption
              obtain h|h := h
              · left
                linarith
              right
              linarith
            exact toFinite (↑U ∩ (g ⁻¹' Ioi x ∪ g ⁻¹' Iio (-x)))
          unfold MeasureTheory.HasFiniteIntegral
          calc
            ∫⁻ (a : ℝ) in Ioc 0 L, ‖(fun o ↦ o ^ (r - 1) * ↑(↑U ∩ (g ⁻¹' Ioi o ∪ g ⁻¹' Iio (-o))).ncard) a‖ₑ ≤ ∫⁻ (a : ℝ) in Ioc 0 L, ‖a ^ (r - 1) * (↑(U.card) : ℝ)‖ₑ := by
                apply MeasureTheory.lintegral_mono
                intro a
                simp
                apply mul_le_mul
                all_goals simp
                refine Finset.le_card_iff_exists_subset_card.mpr ?_
                use (↑U ∩ (g ⁻¹' Ioi a ∪ g ⁻¹' Iio (-a))).toFinset
                constructor
                · simp
                exact Eq.symm (ncard_eq_toFinset_card' (↑U ∩ (g ⁻¹' Ioi a ∪ g ⁻¹' Iio (-a))))
              _= U.card * ∫⁻ (a : ℝ) in Ioc 0 L, ‖a ^ (r - 1)‖ₑ := by
                simp
                rw [mul_comm, ← MeasureTheory.lintegral_mul_const]
                measurability
              _< ⊤ := by
                refine ENNReal.mul_lt_top ?_ ?_
                · simp
                refine finint_rpow L (r - 1) ?_
                linarith
          --apply aestronglymeasurable_zero_set
        simp
        intro x xh
        set B := ↑U ∩ ((fun x ↦ g ↑x) ⁻¹' Ioi x ∪ (fun x ↦ g ↑x) ⁻¹' Iio (-x))
        set A := (fun (x : U) ↦ g ↑x) ⁻¹' Ioi x ∪ (fun (x : U) ↦ g (↑x : (S.X))) ⁻¹' Iio (-x)
        suffices : B = scoe A
        · rw [this, scoe_ncard]
        swap
        intro x xh
        unfold Ioi at xh
        apply mul_nonneg
        all_goals simp_all
        refine Real.rpow_nonneg ?_ (r-1)
        linarith

        unfold scoe A B
        ext t
        constructor
        · intro th
          use ⟨t, th.1⟩
          simp
          simp at th
          tauto
        intro th
        simp_all

      _= r * ∫ (s : ℝ) in Ioc 0 L, s ^ (r - 1) * ↑(↑U ∩ g⁻¹' (Ioi s ∪ Iio (-s))).ncard := by
        simp
        left
        set u : ℝ → ℝ := fun o ↦ o ^ (r - 1) * ↑(↑U ∩ (g ⁻¹' Ioi o ∪ g ⁻¹' Iio (-o))).ncard --das ausbessern
        have : MeasureTheory.integral (MeasureTheory.volume.restrict (Ioi 0)) u = (MeasureTheory.integral (MeasureTheory.volume.restrict (Ioc 0 L)) u) +(MeasureTheory.integral (MeasureTheory.volume.restrict (Ioi L)) u) := by
          have : Ioi 0 = (Ioc 0 L) ∪ (Ioi L) := by refine Eq.symm (Ioc_union_Ioi_eq_Ioi ?_); exact bound_fun_nonneg hf
          rw [this]
          refine MeasureTheory.integral_union_ae ?_ ?_ ?_ ?_
          · refine Disjoint.aedisjoint ?_
            simp
          simp
          unfold MeasureTheory.IntegrableOn MeasureTheory.Integrable
          --apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
          constructor
          · apply MeasureTheory.AEStronglyMeasurable.mul
            · measurability
            apply aestronglymeasurable_mono_down --HDJHDFGSHJG !!!!!!!!!!!
            unfold Ioc
            simp only [mem_setOf_eq, Nat.cast_le, and_imp]
            intro x y xp xL yp yL xy
            apply ncard_le_ncard
            · unfold Ioi
              intro t
              simp
              intro _ h
              constructor
              · assumption
              obtain h|h := h
              · left
                linarith
              right
              linarith
            exact toFinite (↑U ∩ (g ⁻¹' Ioi x ∪ g ⁻¹' Iio (-x)))
          unfold MeasureTheory.HasFiniteIntegral
          calc
            ∫⁻ (a : ℝ) in Ioc 0 L, ‖(fun o ↦ o ^ (r - 1) * ↑(↑U ∩ (g ⁻¹' Ioi o ∪ g ⁻¹' Iio (-o))).ncard) a‖ₑ ≤ ∫⁻ (a : ℝ) in Ioc 0 L, ‖a ^ (r - 1) * (↑(U.card) : ℝ)‖ₑ := by
                apply MeasureTheory.lintegral_mono
                intro a
                simp
                apply mul_le_mul
                all_goals simp
                refine Finset.le_card_iff_exists_subset_card.mpr ?_
                use (↑U ∩ (g ⁻¹' Ioi a ∪ g ⁻¹' Iio (-a))).toFinset
                constructor
                · simp
                exact Eq.symm (ncard_eq_toFinset_card' (↑U ∩ (g ⁻¹' Ioi a ∪ g ⁻¹' Iio (-a))))
              _= U.card * ∫⁻ (a : ℝ) in Ioc 0 L, ‖a ^ (r - 1)‖ₑ := by
                simp
                rw [mul_comm, ← MeasureTheory.lintegral_mul_const]
                measurability
              _< ⊤ := by
                refine ENNReal.mul_lt_top ?_ ?_
                · simp
                refine finint_rpow L (r - 1) ?_
                linarith
          --apply aestronglymeasurable_zero_set
          apply integrable_on_zero_set
          · measurability
          intro t th
          unfold Ioi Iio g
          simp
          right
          suffices : ↑U ∩ ({a | t < ↑(f a)} ∪ {a | ↑(f a) < -t}) = ∅
          · rw [this]
            simp
          ext l
          simp
          intro lU
          constructor
          calc
           f l ≤ L := by unfold L; apply bound_fun_is_bound hf; unfold carrier; use U
            _ ≤ t := le_of_lt th
          calc
            -t ≤ -L := by simp; exact (le_of_lt th)
              _≤ 0 := by simp; exact bound_fun_nonneg hf
              _≤ f l := by simp
        unfold u at *
        rw [this]
        clear this
        simp
        apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
        intro x xh
        simp
        right
        suffices : ↑U ∩ (g ⁻¹' Ioi x ∪ g ⁻¹' Iio (-x)) = ∅
        · rw [this]
          simp
        ext t
        simp
        unfold g
        intro tu
        constructor
        · calc
            abs (↑(f t) : ℝ) = f t := by simp
              _≤ L := by unfold L; apply bound_fun_is_bound hf t; unfold carrier; use U
              _≤ x := by exact le_of_lt xh
        simp
        calc
          -x ≤ -L := by unfold Ioi at *; simp_all; linarith
            _≤ 0 := by simp; exact bound_fun_nonneg hf
            _≤ ↑(f t) := by simp
      _= r * ∫ (s : ℝ) in Ioc 0 L, s ^ (r - 1) * ↑(((↑U : Set S.X) ∩ (g⁻¹' (Set.Ioi s)))).ncard := by
        simp
        left
        apply MeasureTheory.setIntegral_congr_fun
        simp
        unfold EqOn
        intro x xh
        simp
        left --ist falsch; jz nict mehr
        suffices : (↑U ∩ (g ⁻¹' Ioi x ∪ g ⁻¹' Iio (-x))) = (↑U ∩ g ⁻¹' Ioi x)
        · rw [this]
        rw [@inter_union_distrib_left]
        suffices : ↑U ∩ g ⁻¹' Iio (-x) = ∅
        · rw [this]
          simp
        ext t
        simp
        intro tu
        unfold g
        calc
          -x ≤ 0 := by simp; unfold Ioc at xh; simp at xh; linarith
            _≤ abs ↑(f t) := by simp
      _ ≤ r * ∫ (s : ℝ) in Ioc 0 L, ( C ^ (1 - b)⁻¹ * k ^ (b / (1 - b))) * (s ^ (r - 1 - (1 - b)⁻¹)) := by
        apply mul_le_mul
        · rfl
        swap
        · refine MeasureTheory.setIntegral_nonneg ?_ ?_
          simp only [measurableSet_Ioc]
          intro x xh
          apply mul_nonneg
          refine Real.rpow_nonneg ?_ (r - 1)
          exact le_of_lt xh.1
          simp only [Nat.cast_nonneg]
        swap
        · linarith
        apply int_lemma
        · measurability
        · unfold MeasureTheory.IntegrableOn MeasureTheory.Integrable
          constructor
          · simp_all only [one_div, C, k, L]
            apply MeasureTheory.AEStronglyMeasurable.const_mul
            apply AEMeasurable.aestronglyMeasurable
            apply AEMeasurable.pow_const
            apply aemeasurable_id'
          unfold MeasureTheory.HasFiniteIntegral
          simp only [enorm_mul]
          rw [← @enorm_mul]
          have : ∫⁻ (a : ℝ) in Ioc 0 L, ‖C ^ (1 - b)⁻¹ * k ^ (b / (1 - b))‖ₑ * ‖a ^ (r - 1 - (1 - b)⁻¹)‖ₑ ∂MeasureTheory.volume =
            ‖C ^ (1 - b)⁻¹ * k ^ (b / (1 - b))‖ₑ * ∫⁻ (a : ℝ) in Ioc 0 L, ‖a ^ (r - 1 - (1 - b)⁻¹)‖ₑ ∂MeasureTheory.volume := by
              refine MeasureTheory.lintegral_const_mul ‖C ^ (1 - b)⁻¹ * k ^ (b / (1 - b))‖ₑ ?_
              simp_all only [one_div]
              apply Measurable.coe_nnreal_ennreal
              apply Measurable.nnnorm
              apply Measurable.pow_const
              apply measurable_id'
          rw [this]
          clear this
          rw [@ENNReal.mul_lt_top_iff]
          left
          constructor
          · exact enorm_lt_top
          apply finint_rpow
          simp_all
        intro s sh
        suffices : ↑(↑U ∩ g ⁻¹' Ioi s).ncard ≤ C ^ (1 - b)⁻¹ * k ^ (b / (1 - b)) * s^(-(1-b)⁻¹)
        · calc
             s^(r-1) * ↑(↑U ∩ g ⁻¹' Ioi s).ncard ≤ s^(r-1) * (C ^ (1 - b)⁻¹ * k ^ (b / (1 - b)) * s ^ (-(1 - b)⁻¹)) := by
              apply mul_le_mul
              · rfl
              · exact this
              · simp only [Nat.cast_nonneg]
              · refine Real.rpow_nonneg ?_ (r - 1)
                unfold Ioc at sh
                rw [mem_setOf_eq] at sh
                linarith
            _= C ^ (1 - b)⁻¹ * k ^ (b / (1 - b)) * s ^ (r - 1 - (1 - b)⁻¹) := by
                rw [← mul_assoc, mul_comm, ← mul_assoc, mul_comm]
                rw [← Real.rpow_add, add_comm]
                simp
                left
                rw [@Mathlib.Tactic.RingNF.add_neg]
                unfold Ioc at sh
                simp at sh
                exact sh.1

        calc
          ↑(↑U ∩ g ⁻¹' Ioi s).ncard ≤ fun_closed_const hf ^ (1 - b)⁻¹ * ClosureFactor S ^ (b / (1 - b)) * ↑s.toNNReal ^ (-(1 - b)⁻¹) := by
            have spos : 0 < s := by
              unfold Ioc at sh
              simp_all
            have : 0 < s.toNNReal := by simp_all
            --suffices : ↑U ∩ g ⁻¹' Ioi s = ↑U ∩ f
            have := @preimage_bounded S b f hb hb2 hf U Uh s.toNNReal this
            set A := (↑U ∩ f ⁻¹' Ioi s.toNNReal)
            set B := ↑U ∩ g ⁻¹' Ioi s
            suffices g : A = B
            · rw [← g]
              assumption
            unfold A B
            ext t
            unfold g
            constructor
            · intro th
              simp_all
              suffices : ↑(s.toNNReal) = s
              · rw [← this]
                tauto
              simp
              linarith

            intro th
            simp_all
            suffices : (↑(s.toNNReal) : ℝ) < ↑(f t)
            · exact this
            suffices : ↑(s.toNNReal) = s
            · rw [this]
              tauto
            simp
            linarith

          _ = C ^ (1 - b)⁻¹ * k ^ (b / (1 - b)) * s ^ (-(1 - b)⁻¹) := by
            unfold C k
            have : max s 0 = s := by unfold Ioc at sh; simp_all; linarith
            simp
            rw [this]
            simp
        simp
        intro x xp xL
        apply mul_nonneg
        refine Real.rpow_nonneg ?_ (r - 1)
        linarith
        simp only [Nat.cast_nonneg]
      _= r *  ( C ^ (1 - b)⁻¹ * k ^ (b / (1 - b))) * ∫ (s : ℝ) in Ioc 0 L, (s ^ (r - 1 - (1 - b)⁻¹)) := by
        rw [mul_assoc r]
        simp
        left
        rw [← MeasureTheory.integral_const_mul]
      _= r * C^((1-b)⁻¹) * k^(b/(1-b)) * ∫ (s : ℝ) in Ioc 0 L, s^(r-1-(1-b)⁻¹) := by
        rw [← mul_assoc]


lemma get_rid {n : ℕ} (i : Fin n): (↑i : ℕ) < n + 1 := by
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
    by_cases is' : i = s + 1
    · use (fun j ↦ if hj : j = 0 then (f ⟨s, by linarith⟩ 1) else f ⟨s+1, by linarith⟩ 0)
    use f ⟨i-1, subone_fin ih⟩

omit [LinearOrder J] in
lemma fillone_card (h : (BadSet f).Nonempty) : (BadSet f).card = (BadSet (FillOne h)).card + 1 := by
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
    rw [this]
    let g := (Fillk f r)
    use FillOnequick g

omit [LinearOrder J] in
theorem Fillk_badset_card (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k ≤ (BadSet f).card) :
    (BadSet (Fillk f k)).card + k = (BadSet f).card := by
  induction' k with k hk'
  · unfold Fillk
    rw [add_zero]
  specialize hk' (Nat.le_of_succ_le hk)
  rw [← hk']
  have ne : (BadSet (Fillk f k)).Nonempty := by
    refine Finset.card_pos.mp ?_
    contrapose hk
    simp_all only [Finset.card_pos, Finset.not_nonempty_iff_eq_empty, not_le, Finset.card_empty,
      zero_add, lt_add_iff_pos_right, zero_lt_one]
  nth_rw 1 [Fillk]
  simp only [eq_mpr_eq_cast, cast_eq]
  have : (BadSet (FillOnequick (Fillk f k))).card + (k + 1)
      = (BadSet (FillOnequick (Fillk f k))).card + 1 + k := by ring
  rw [this]
  unfold FillOnequick
  simp only [ne, ↓reduceDIte, Nat.add_right_cancel_iff]
  rw [← fillone_card]

omit [LinearOrder J] in
theorem Fillk_badset_card' (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k ≤ (BadSet f).card) :
    (BadSet (Fillk f k)).card= (BadSet f).card - k := by
  refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
  exact Eq.symm (Fillk_badset_card f hk)

omit [LinearOrder J] in
theorem Fillk_badset_nonempty (f : Fin (m + 1) → Fin 2 → J) {k : ℕ} (hk : k < (BadSet f).card) :
    (BadSet (Fillk f k)).Nonempty := by
  refine Finset.one_le_card.mp ?_
  rw [Fillk_badset_card' f (le_of_lt hk)]
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
    by_cases hi' : i ≤ ↑((BadSet f).min' h)
    · simp only [hi', ↓reduceDIte, Fin.isValue]
      apply mon.1
    simp [hi']
    by_cases hi'' : i = ↑((BadSet f).min' h) + 1
    · simp only [hi'', ↓reduceIte, Fin.isValue, one_ne_zero]
      apply le_trans' (mon.2 ⟨(↑((BadSet f).min' h) : ℕ), ((BadSet f).min' h).isLt⟩)
      apply le_of_eq
      congr
    simp only [hi'', ↓reduceIte, Fin.isValue]
    apply mon.1
  intro ⟨i, hi⟩
  unfold FillOne
  by_cases hi' : i < ↑((BadSet f).min' h)
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
  by_cases hi'' : i = ↑((BadSet f).min' h)
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
  by_cases hi''' : i = ↑((BadSet f).min' h) + 1 <;> simp [hi''']
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
  rw [Fillk_badset_fillup]
  · apply fillone_pairmon
    exact hk' (Nat.le_of_succ_le hk)
  exact hk

theorem fillup_pairmon (mon : pairmon f): pairmon (FillUp f) := by
  apply fillk_pairmon
  · exact (Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a ↦ a).mpr rfl
  exact mon


def AllowedSeq :=
  {s : Finset (Fin 2 → J) | s = ∅ ∨ ∃ m, ∃ f : Fin (m + 1) → (Fin 2 → J),
    BijOn f (@Set.univ (Fin (m + 1)))  s ∧
    (∀ i : Fin m, f ⟨↑i, get_rid i⟩ 1 = f i.succ 0) ∧
    pairmon f}

theorem allowseq_is_finclosed (J : Type u) [LinearOrder J]:
    IsFinclosed ((AllowedSeq (J := J))) := by
  unfold IsFinclosed
  constructor
  · unfold AllowedSeq
    simp
  use 2
  intro u ⟨v, vh, uv⟩
  obtain vh|vh := vh
  · rw [vh] at uv
    use ∅
    unfold AllowedSeq
    simp_all

  obtain ⟨m, f, bij, ep, mon⟩ := vh
  sorry

end Finclosed
#min_imports
