import MyProjects.ST.CategoryNotes.StructureTower_CategoryExercises_L4
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

open Set Function

namespace BourbakiGuide

namespace StructureTower

def iic (α : Type*) [Preorder α] : StructureTower α α where
  level x := Set.Iic x
  monotone_level := by
    intro i j hij x hx
    exact le_trans hx hij

def natFiltration : StructureTower ℕ ℕ := iic ℕ

def ofAntitone {ι α : Type*} [Preorder ι] (d : ι → Set α) (hd : Antitone d) :
    StructureTower ιᵒᵈ α where
  level i := d (OrderDual.ofDual i)
  monotone_level := by
    intro i j hij x hx
    exact hd (OrderDual.ofDual_le_ofDual.mpr hij) hx

def inter {ι α : Type*} [Preorder ι] (T₁ T₂ : StructureTower ι α) :
    StructureTower ι α where
  level i := T₁.level i ∩ T₂.level i
  monotone_level := by
    intro i j hij x hx
    exact ⟨T₁.monotone_level hij hx.1, T₂.monotone_level hij hx.2⟩

end StructureTower

open StructureTower

def emptyTower : StructureTower Unit Empty where
  level := fun _ => ∅
  monotone_level := by
    intro i j hij x hx
    cases hx

theorem emptyTower_level_eq (u : Unit) :
    emptyTower.level u = ∅ := rfl

theorem emptyTower_union_eq :
    emptyTower.union = ∅ := by
  ext x
  cases x

def natExhaustive : ExhaustiveTower ℕ ℕ where
  toStructureTower := natFiltration
  exhaustive := by
    intro x
    refine ⟨x, ?_⟩
    change x ≤ x
    exact le_rfl

theorem natExhaustive_hasCharRank :
    HasCharRank natExhaustive id := by
  intro x i
  change x ≤ i ↔ x ≤ i
  exact Iff.rfl

theorem natExhaustive_rank_eq (x : ℕ) :
    natExhaustive.rank x = x := by
  have h := congrFun (rank_unique natExhaustive id natExhaustive_hasCharRank) x
  simpa using h.symm

structure FakeTower (ι α : Type*) [Preorder ι] where
  level : ι → Set α

def fakeExample : FakeTower ℕ ℕ where
  level := fun n =>
    if n = 0 then {x | x = 0 ∨ x = 1} else {x | x = 2}

theorem fake_not_monotone :
    ¬ (∀ i j : ℕ, i ≤ j → fakeExample.level i ⊆ fakeExample.level j) := by
  intro hmono
  have h01 : fakeExample.level 0 ⊆ fakeExample.level 1 := hmono 0 1 (by omega)
  have : 0 ∈ fakeExample.level 1 := h01 (by simp [fakeExample])
  simp [fakeExample] at this

inductive TwoPoint where
  | a
  | b
deriving DecidableEq

instance : Preorder TwoPoint where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  lt_iff_le_not_ge := by
    intro x y
    simp

theorem twoPoint_not_antisymm :
    ¬ (∀ x y : TwoPoint, x ≤ y → y ≤ x → x = y) := by
  intro h
  have : TwoPoint.a = TwoPoint.b := h TwoPoint.a TwoPoint.b trivial trivial
  cases this

def twoPointExhaustive : ExhaustiveTower TwoPoint ℕ where
  toStructureTower := {
    level := fun _ => Set.univ
    monotone_level := by
      intro i j hij x hx
      trivial
  }
  exhaustive := by
    intro x
    exact ⟨TwoPoint.a, by trivial⟩

def twoPointRankA : ℕ → TwoPoint := fun _ => TwoPoint.a

def twoPointRankB : ℕ → TwoPoint := fun _ => TwoPoint.b

theorem twoPointRankA_hasChar :
    HasCharRankPreorder twoPointExhaustive twoPointRankA := by
  intro x i
  constructor <;> intro hx <;> trivial

theorem twoPointRankB_hasChar :
    HasCharRankPreorder twoPointExhaustive twoPointRankB := by
  intro x i
  constructor <;> intro hx <;> trivial

theorem rank_not_unique_preorder :
    ∃ (r₁ r₂ : ℕ → TwoPoint), r₁ ≠ r₂ ∧
      HasCharRankPreorder twoPointExhaustive r₁ ∧
      HasCharRankPreorder twoPointExhaustive r₂ := by
  refine ⟨twoPointRankA, twoPointRankB, ?_, twoPointRankA_hasChar, twoPointRankB_hasChar⟩
  intro h
  have : TwoPoint.a = TwoPoint.b := congrFun h 0
  cases this

def singletonTowerFails : ℕ → Set ℕ := fun n => {x | x = n}

theorem singletonTower_not_monotone :
    ¬ Monotone singletonTowerFails := by
  intro hmono
  have h01 : singletonTowerFails 0 ⊆ singletonTowerFails 1 := hmono (by omega)
  have : 0 ∈ singletonTowerFails 1 := h01 (by simp [singletonTowerFails])
  simp [singletonTowerFails] at this

theorem natFiltration_layer (n : ℕ) (hn : 0 < n) :
    natFiltration.level n \ natFiltration.level (n - 1) = {x | x = n} := by
  ext m
  constructor
  · intro hm
    have hm_le : m ≤ n := hm.1
    have hm_not : ¬ m ≤ n - 1 := by
      intro hle
      exact hm.2 hle
    have : m = n := by omega
    simp [this]
  · intro hm
    have hm_eq : m = n := by simpa using hm
    subst m
    constructor
    · show n ≤ n
      exact le_rfl
    · intro hle
      change n ≤ n - 1 at hle
      omega

def almostFiltered : ℕ → Set ℤ :=
  fun n => {z | z.natAbs ≤ n ∧ Even z}

theorem almostFiltered_monotone :
    Monotone almostFiltered := by
  intro i j hij z hz
  exact ⟨le_trans hz.1 hij, hz.2⟩

theorem almostFiltered_zero_mem (n : ℕ) :
    (0 : ℤ) ∈ almostFiltered n := by
  simp [almostFiltered]

theorem almostFiltered_not_add_closed :
    ¬ (∀ n, ∀ x y : ℤ, x ∈ almostFiltered n → y ∈ almostFiltered n →
      x + y ∈ almostFiltered n) := by
  intro hadd
  have htwo : (2 : ℤ) ∈ almostFiltered 2 := by
    norm_num [almostFiltered]
  have hfour : (4 : ℤ) ∈ almostFiltered 2 := by
    simpa using hadd 2 2 2 htwo htwo
  norm_num [almostFiltered] at hfour

def EventuallyMonotoneSeq {α : Type*} (S : ℕ → Set α) : Prop :=
  ∃ N, ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j

def evMonExample : ℕ → Set ℕ :=
  fun n => if n = 0 then {x | x = 5} else Set.Iic n

theorem evMonExample_eventually_monotone :
    EventuallyMonotoneSeq evMonExample := by
  refine ⟨1, ?_⟩
  intro i j hi hij x hx
  have hi0 : i ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  simp [evMonExample, hi0, hj0] at hx ⊢
  exact le_trans hx hij

theorem evMonExample_not_monotone :
    ¬ Monotone evMonExample := by
  intro hmono
  have h01 : evMonExample 0 ⊆ evMonExample 1 := hmono (by omega)
  have : 5 ∈ evMonExample 1 := h01 (by simp [evMonExample])
  norm_num [evMonExample] at this

def truncateToTower {α : Type*} (S : ℕ → Set α) (N : ℕ)
    (h : ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j) :
    StructureTower ℕ α where
  level i := S (i + N)
  monotone_level := by
    intro i j hij x hx
    have hN : N ≤ i + N := by omega
    have hij' : i + N ≤ j + N := by omega
    exact h (i + N) (j + N) hN hij' hx

def thresholdTower {ι α : Type*} [Preorder ι] (w : α → ι) :
    StructureTower ι α where
  level i := {x | w x ≤ i}
  monotone_level := by
    intro i j hij x hx
    exact le_trans hx hij

theorem thresholdTower_eq_iic (α : Type*) [Preorder α] :
    thresholdTower (id : α → α) = StructureTower.iic α := by
  ext i x
  rfl

theorem thresholdTower_exhaustive {ι α : Type*} [Preorder ι]
    (w : α → ι) :
    ∀ x : α, ∃ i : ι, x ∈ (thresholdTower w).level i := by
  intro x
  exact ⟨w x, le_rfl⟩

theorem thresholdTower_add_closed {ι α : Type*} [LinearOrder ι] [AddCommMonoid α]
    (w : α → ι)
    (hadd : ∀ x y, w (x + y) ≤ max (w x) (w y))
    {i : ι} {x y : α}
    (hx : x ∈ (thresholdTower w).level i)
    (hy : y ∈ (thresholdTower w).level i) :
    x + y ∈ (thresholdTower w).level i := by
  show w (x + y) ≤ i
  exact le_trans (hadd x y) (max_le_iff.mpr ⟨hx, hy⟩)

def finTower1 : StructureTower (Fin 3) (Fin 5) where
  level i := {x | x.1 ≤ 2 * i.1 + 1}
  monotone_level := by
    intro i j hij x hx
    have hij' : i.1 ≤ j.1 := by
      simpa using hij
    have hmul : 2 * i.1 ≤ 2 * j.1 := Nat.mul_le_mul_left 2 hij'
    have hstep : 2 * i.1 + 1 ≤ 2 * j.1 + 1 := Nat.add_le_add_right hmul 1
    exact le_trans hx hstep

def finTower2 : StructureTower (Fin 3) (Fin 5) where
  level i := {x | x.1 ≤ 2 * i.1 ∧ x.1 % 2 = 0}
  monotone_level := by
    intro i j hij x hx
    have hij' : i.1 ≤ j.1 := by
      simpa using hij
    have hmul : 2 * i.1 ≤ 2 * j.1 := Nat.mul_le_mul_left 2 hij'
    exact ⟨le_trans hx.1 hmul, hx.2⟩

theorem finTower1_union :
    finTower1.union = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ?_
  refine ⟨⟨2, by decide⟩, ?_⟩
  change x.1 ≤ 5
  omega

theorem finTower1_global :
    finTower1.global = {x | x.1 ≤ 1} := by
  ext x
  constructor
  · intro hx
    have hx0 : x ∈ finTower1.level ⟨0, by decide⟩ := Set.mem_iInter.mp hx ⟨0, by decide⟩
    simpa [finTower1] using hx0
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro i
    change x.1 ≤ 2 * i.1 + 1
    have hbase : 1 ≤ 2 * i.1 + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact le_trans hx hbase

theorem finTower2_subset_finTower1 (i : Fin 3) :
    finTower2.level i ⊆ finTower1.level i := by
  intro x hx
  have hx' : x.1 ≤ 2 * i.1 ∧ x.1 % 2 = 0 := by
    simpa [finTower2] using hx
  change x.1 ≤ 2 * i.1 + 1
  exact le_trans hx'.1 (Nat.le_succ _)

theorem finTower_inter_eq_right (i : Fin 3) :
    (StructureTower.inter finTower1 finTower2).level i = finTower2.level i := by
  ext x
  constructor
  · intro hx
    change x ∈ finTower1.level i ∩ finTower2.level i at hx
    exact hx.2
  · intro hx
    change x ∈ finTower1.level i ∩ finTower2.level i
    exact ⟨finTower2_subset_finTower1 i hx, hx⟩

theorem finTower_inter_level0 :
    (StructureTower.inter finTower1 finTower2).level ⟨0, by decide⟩ = {x | x.1 = 0} := by
  rw [finTower_inter_eq_right]
  ext x
  fin_cases x <;> simp [finTower2]

theorem finTower_inter_level1 :
    (StructureTower.inter finTower1 finTower2).level ⟨1, by decide⟩ =
      {x | x.1 = 0 ∨ x.1 = 2} := by
  rw [finTower_inter_eq_right]
  ext x
  fin_cases x <;> simp [finTower2]

theorem finTower_inter_level2 :
    (StructureTower.inter finTower1 finTower2).level ⟨2, by decide⟩ =
      {x | x.1 = 0 ∨ x.1 = 2 ∨ x.1 = 4} := by
  rw [finTower_inter_eq_right]
  ext x
  fin_cases x <;> simp [finTower2]

end BourbakiGuide
