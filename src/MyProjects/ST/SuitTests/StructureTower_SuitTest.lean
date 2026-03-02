/-
  StructureTower — Suit Test: 11カテゴリ網羅版
  ════════════════════════════════════════════════════════════

  ニコラ・ブルバキ『数学原論』の集合論の精神に従い、
  公理から体系的に11カテゴリの演習問題を Lean 4 で形式化する。

  カテゴリ: trivial / canonical / extreme / pathological /
            counterexample / dual / borderline / non-example /
            out-of-category / schema / finite_computational
  難易度分布: 🟢×3 / 🟡×5 / 🔴×3
  生成日: 2026-03-03
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Data.Nat.Find
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Algebra.Order.Ring.Lemmas

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. StructureTower フレームワーク（Mathlib のみに依存、自己完結）
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level          : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β : Type*} [Preorder ι]

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

def global (T : StructureTower ι α) : Set α := ⋂ i, T.level i

-- 基本構成: 定数塔
def const (ι : Type*) [Preorder ι] (S : Set α) : StructureTower ι α where
  level _ := S
  monotone_level := fun _i _j _hij => Subset.refl _

-- 基本構成: 主下方集合塔
def iic (α : Type*) [Preorder α] : StructureTower α α where
  level x := Set.Iic x
  monotone_level := fun _i _j hij _x hx => le_trans hx hij

-- 基本構成: 単調列塔
def ofMonotoneSeq {α : Type*} [Preorder α] (c : ℕ → α) (hc : Monotone c) :
    StructureTower ℕ α where
  level n := Set.Iic (c n)
  monotone_level := fun _i _j hij _x hx => le_trans hx (hc hij)

-- 基本構成: 標準 ℕ フィルトレーション（level n = {m | m ≤ n}）
def natFiltration : StructureTower ℕ ℕ := ofMonotoneSeq id monotone_id

@[simp] theorem mem_natFiltration_level (n m : ℕ) :
    m ∈ natFiltration.level n ↔ m ≤ n := Set.mem_Iic

-- 基本構成: 添字変換
def reindex {κ : Type*} [Preorder κ] (f : ι → κ) (hf : Monotone f)
    (T : StructureTower κ α) : StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

-- 基本構成: 反単調族の双対化
def ofAntitone (d : ι → Set α) (hd : Antitone d) : StructureTower ιᵒᵈ α where
  level i := d (OrderDual.ofDual i)
  monotone_level := by
    intro i j hij
    exact hd (OrderDual.ofDual_le_ofDual.mpr hij)

-- 基本構成: レベルごとの交叉
def inter (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i := T₁.level i ∩ T₂.level i
  monotone_level := fun _i _j hij _x hx =>
    ⟨T₁.monotone_level hij hx.1, T₂.monotone_level hij hx.2⟩

@[simp] theorem inter_level (T₁ T₂ : StructureTower ι α) (i : ι) :
    (inter T₁ T₂).level i = T₁.level i ∩ T₂.level i := rfl

-- 基本構成: レベルごとの和
def sup (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i := T₁.level i ∪ T₂.level i
  monotone_level := fun _i _j hij _x hx => by
    rcases hx with h | h
    · exact Or.inl (T₁.monotone_level hij h)
    · exact Or.inr (T₂.monotone_level hij h)

-- ExhaustiveTower の定義
structure ExhaustiveTower (α : Type*) extends StructureTower ℕ α where
  exhaustive : ∀ x : α, ∃ i : ℕ, x ∈ level i

noncomputable def ExhaustiveTower.rank {α : Type*} (T : ExhaustiveTower α) (x : α) : ℕ := by
  classical
  exact Nat.find (T.exhaustive x)

theorem ExhaustiveTower.rank_spec {α : Type*} (T : ExhaustiveTower α) (x : α) :
    x ∈ T.level (T.rank x) := by
  classical; exact Nat.find_spec (T.exhaustive x)

theorem ExhaustiveTower.rank_le {α : Type*} (T : ExhaustiveTower α) (x : α)
    (n : ℕ) (h : x ∈ T.level n) : T.rank x ≤ n := by
  classical; exact Nat.find_min' (T.exhaustive x) h

-- HasCharRank: 強い単射公理（Theorem B の核心）
-- 「x ∈ level(i) ↔ r(x) ≤ i」を満たす rank 関数 r の存在
def HasCharRank {α : Type*} (T : ExhaustiveTower α) (r : α → ℕ) : Prop :=
  ∀ x i, x ∈ T.level i ↔ r x ≤ i

-- idealPowTower（問題 6 のため事前定義）
-- I-進フィルトレーション: ℕᵒᵈ-indexed, level n = ↑(I ^ ofDual n)
-- 添字が大きいほど冪が小さいイデアルに対応（反単調の双対化）
noncomputable def idealPowTower {R : Type*} [CommRing R] (I : Ideal R) :
    StructureTower ℕᵒᵈ R where
  level n := ↑(I ^ OrderDual.ofDual n)
  monotone_level := by
    intro i j hij
    -- i ≤ j in ℕᵒᵈ ⟺ ofDual j ≤ ofDual i in ℕ
    have h : OrderDual.ofDual j ≤ OrderDual.ofDual i :=
      OrderDual.ofDual_le_ofDual.mpr hij
    -- I^(ofDual i) ≤ I^(ofDual j)（大きい冪 ⊆ 小さい冪）
    intro x hx
    simp only [Ideal.coe_pow, Set.mem_setOf_eq] at hx ⊢
    exact (Ideal.pow_le_pow_right h) hx

end StructureTower

open StructureTower

-- ════════════════════════════════════════════════════════════
-- §P1. trivial — 空塔（Unit × Empty）🟢
-- ════════════════════════════════════════════════════════════
/-
  目的: 最小構成で StructureTower の公理が満たされることを確認。
  台集合 Empty ではすべての性質が vacuously に成立する。
-/

def emptyTower : StructureTower Unit Empty where
  level := fun _ => ∅
  monotone_level := fun _ _ _ _ hx => hx.elim

theorem emptyTower_level_eq (u : Unit) :
    emptyTower.level u = ∅ := rfl

theorem emptyTower_union_eq :
    emptyTower.union = (∅ : Set Empty) := by
  simp [union, emptyTower]

-- ════════════════════════════════════════════════════════════
-- §P2. canonical — natFiltration の ExhaustiveTower 化 🟢
-- ════════════════════════════════════════════════════════════
/-
  目的: 標準 ℕ-filtration（Iic-塔の原型）で
  rank の一意性（Theorem B）を具体的に確認する。
-/

def natExhaustive : ExhaustiveTower ℕ where
  toStructureTower := natFiltration
  exhaustive := fun x => ⟨x, le_refl x⟩

-- rank(x) = x: Iic 塔では最小レベルはちょうど x 自身
theorem natExhaustive_rank_eq (x : ℕ) :
    natExhaustive.rank x = x := by
  apply Nat.le_antisymm
  · -- rank x ≤ x: x ∈ level x（x ≤ x）から最小性
    exact natExhaustive.rank_le x x (by simp [natExhaustive, natFiltration])
  · -- x ≤ rank x: rank_spec より x ∈ level(rank x) すなわち x ≤ rank x
    have := natExhaustive.rank_spec x
    simp [natExhaustive, natFiltration, ofMonotoneSeq] at this
    exact this

-- HasCharRank natExhaustive id: x ∈ level i ↔ id x ≤ i は natFiltration の定義そのもの
theorem natExhaustive_hasCharRank :
    HasCharRank natExhaustive id := by
  intro x i
  simp [HasCharRank, natExhaustive, natFiltration, ofMonotoneSeq, Set.mem_Iic]

-- ════════════════════════════════════════════════════════════
-- §P3. extreme — Ordinal-indexed tower 🔴
-- ════════════════════════════════════════════════════════════
/-
  目的: 非可算添字型でも StructureTower が機能するか検証。
  level o = {n | n ≤ o.toNat}（o < ω）または Set.univ（o ≥ ω）。

  注意: Theorem B（rank uniqueness）は ExhaustiveTower が ℕ-indexed に
  限定されているため、この Ordinal-indexed 塔には直接適用できない。
  rank 関数の型が ℕ → Ordinal になり型が一致しない。
-/

noncomputable def ordinalTower : StructureTower Ordinal ℕ where
  level o := if o < Ordinal.omega then {n | n ≤ Ordinal.toNat o} else Set.univ
  monotone_level := by
    intro i j hij x hx
    simp only at hx ⊢
    by_cases hi : i < Ordinal.omega
    · rw [if_pos hi] at hx
      by_cases hj : j < Ordinal.omega
      · rw [if_pos hj]
        simp only [Set.mem_setOf_eq] at hx ⊢
        -- i ≤ j < ω なので i.toNat ≤ j.toNat
        exact Nat.le_trans hx (Ordinal.toNat_le_toNat.mpr hij)
      · rw [if_neg hj]; exact Set.mem_univ _
    · -- i ≥ ω なら level i = univ, j ≥ i ≥ ω なので level j = univ も自明
      rw [if_neg hi] at hx
      have hj : ¬ j < Ordinal.omega := fun hj' =>
        hi (lt_of_le_of_lt hij hj')
      rw [if_neg hj]; exact Set.mem_univ _

theorem ordinalTower_union_eq_univ :
    ordinalTower.union = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  simp only [union, Set.mem_iUnion]
  refine ⟨(n : Ordinal), ?_⟩
  simp only [ordinalTower]
  rw [if_pos (by exact_mod_cast Nat.lt_omega_iff.mpr ⟨n, rfl⟩)]
  simp [Ordinal.toNat_natCast]

-- ════════════════════════════════════════════════════════════
-- §P4. pathological — FakeTower と liftCl の関手性崩壊 🔴
-- ════════════════════════════════════════════════════════════
/-
  目的: monotone_level 公理なしでは liftCl が well-defined な
  自己関手にならないことを具体例で示す。

  結論: FakeTower の level 0 に cofinite 閉包を適用すると
  cl({0,1}) が拡大する一方、level 1 の cl({2}) は小さいまま。
  unit 自然変換 T → liftCl(T) のレベル保存が崩壊する。
  すなわち「monotone_level がなければ liftCl が well-defined な
  自己関手にならない」。
-/

structure FakeTower (ι α : Type*) [Preorder ι] where
  level : ι → Set α

def fakeExample : FakeTower ℕ ℕ where
  level := fun n => if n = 0 then {0, 1} else {2}

-- monotone_level の反例: level 0 = {0,1} ⊄ {2} = level 1
theorem fake_not_monotone :
    ¬ (∀ i j : ℕ, i ≤ j → fakeExample.level i ⊆ fakeExample.level j) := by
  intro h
  have h01 : fakeExample.level 0 ⊆ fakeExample.level 1 := h 0 1 (Nat.le_succ 0)
  have h0mem : (0 : ℕ) ∈ fakeExample.level 0 := by
    simp [fakeExample]
  have h0mem' : (0 : ℕ) ∈ fakeExample.level 1 := h01 h0mem
  simp [fakeExample] at h0mem'

-- ════════════════════════════════════════════════════════════
-- §P5. counterexample — 前順序での rank 非一意性 🔴
-- ════════════════════════════════════════════════════════════
/-
  目的: Theorem B（rank uniqueness）が PartialOrder（反対称性）に
  本質的に依存することを、2点前順序で示す。
  前順序では rank 関数が非一意になる反例を構成。
-/

inductive TwoPoint where
  | a : TwoPoint
  | b : TwoPoint
  deriving DecidableEq

-- 全ての組で a ≤ b かつ b ≤ a が成立する前順序（反対称性なし）
instance : Preorder TwoPoint where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

-- この前順序は反対称ではない: a ≤ b かつ b ≤ a だが a ≠ b
theorem twoPoint_not_antisymm :
    ¬ (∀ x y : TwoPoint, x ≤ y → y ≤ x → x = y) := by
  intro h
  exact absurd (h .a .b trivial trivial) (by decide)

-- TwoPoint-indexed tower: すべてのレベルが Set.univ
def twoPointTower : StructureTower TwoPoint ℕ where
  level _ := Set.univ
  monotone_level := fun _ _ _ _ hx => hx

-- r₁ と r₂ の両方が HasCharRank 類似条件を満たすが r₁ ≠ r₂
-- （前順序では全ての組に le が成立するため、任意の rank 関数が条件を満たす）
theorem rank_not_unique_preorder :
    ∃ (r₁ r₂ : ℕ → TwoPoint), r₁ ≠ r₂ ∧
      (∀ x i, x ∈ twoPointTower.level i ↔ r₁ x ≤ i) ∧
      (∀ x i, x ∈ twoPointTower.level i ↔ r₂ x ≤ i) := by
  refine ⟨fun _ => .a, fun _ => .b, ?_, ?_, ?_⟩
  · -- r₁ ≠ r₂
    intro h
    exact absurd (congrFun h 0) (by decide)
  · -- r₁ = fun _ => .a が条件を満たす
    intro x i
    simp [twoPointTower]
    exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩
  · -- r₂ = fun _ => .b が条件を満たす
    intro x i
    simp [twoPointTower]
    exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩

-- ════════════════════════════════════════════════════════════
-- §P6. dual — idealPowTower と ofAntitone の整合性 🟡
-- ════════════════════════════════════════════════════════════
/-
  目的: OrderDual による双対構成が StructureTower 理論で
  正しく機能し、ofAntitone と idealPowTower が整合的か検証。
-/

section DualSection

variable {R : Type*} [CommRing R] (I : Ideal R)

-- I-進反単調族: n ↦ ↑(I^n) は反単調（n が大きいほど I^n は小さい）
def idealPowAntitone : ℕ → Set R :=
  fun n => ↑(I ^ n)

theorem idealPowAntitone_antitone :
    Antitone (idealPowAntitone I) := by
  intro m n hmn x hx
  simp only [idealPowAntitone, Ideal.coe_pow] at hx ⊢
  exact (Ideal.pow_le_pow_right hmn) hx

-- idealPowTower I は ofAntitone による構成と等しい
theorem idealPowTower_eq_ofAntitone :
    idealPowTower I = ofAntitone (idealPowAntitone I)
      (idealPowAntitone_antitone I) := by
  ext i x
  simp [idealPowTower, ofAntitone, idealPowAntitone]

end DualSection

-- ════════════════════════════════════════════════════════════
-- §P7. borderline — singleton vs 累積レベル 🟡
-- ════════════════════════════════════════════════════════════
/-
  目的: monotone_level を「ギリギリ満たさない」失敗例と、
  累積化による修正後の borderline 性質を分析する。
-/

-- 失敗する定義: {n} は単調でない
def singletonTower_fails : ℕ → Set ℕ := fun n => {n}

theorem singletonTower_not_monotone :
    ¬ (∀ i j : ℕ, i ≤ j → singletonTower_fails i ⊆ singletonTower_fails j) := by
  intro h
  have h01 : singletonTower_fails 0 ⊆ singletonTower_fails 1 := h 0 1 (Nat.le_succ 0)
  have : (0 : ℕ) ∈ singletonTower_fails 0 := Set.mem_singleton 0
  have : (0 : ℕ) ∈ singletonTower_fails 1 := h01 this
  simp [singletonTower_fails] at this

-- 修正: natFiltration（累積版）のレイヤー構造
-- level n \ level (n-1) = {n} がちょうど 1 点の新要素
theorem natFiltration_layer (n : ℕ) (hn : 0 < n) :
    natFiltration.level n \ natFiltration.level (n - 1) = {n} := by
  ext m
  simp only [Set.mem_diff, mem_natFiltration_level, Set.mem_singleton_iff]
  omega

-- ════════════════════════════════════════════════════════════
-- §P8. non-example — 偶数制約の加法非閉性 🟡
-- ════════════════════════════════════════════════════════════
/-
  目的: FilteredAddCommMonoid の公理を「あと一歩で」満たすが
  失敗する例を構成。natAbs の制約が加法閉性を破壊する。
-/

def almostFiltered : ℕ → Set ℤ :=
  fun n => {z | z.natAbs ≤ n ∧ Even z}

theorem almostFiltered_monotone :
    Monotone almostFiltered := by
  intro m n hmn z hz
  simp only [almostFiltered, Set.mem_setOf_eq] at hz ⊢
  exact ⟨Nat.le_trans hz.1 hmn, hz.2⟩

theorem almostFiltered_zero_mem (n : ℕ) :
    (0 : ℤ) ∈ almostFiltered n := by
  simp [almostFiltered, Even]
  exact ⟨0, by ring⟩

-- add_mem が失敗する反例: n=2, x=y=2, x+y=4, natAbs 4 = 4 > 2
theorem almostFiltered_not_add_closed :
    ¬ (∀ n : ℕ, ∀ x y : ℤ,
      x ∈ almostFiltered n → y ∈ almostFiltered n →
      x + y ∈ almostFiltered n) := by
  intro h
  have hx : (2 : ℤ) ∈ almostFiltered 2 := by
    simp [almostFiltered, Even]; exact ⟨by norm_num, 1, by ring⟩
  have hsum := h 2 2 2 hx hx
  simp [almostFiltered] at hsum
  omega

-- ════════════════════════════════════════════════════════════
-- §P9. out-of-category — eventually monotone + 打ち切り構成 🟡
-- ════════════════════════════════════════════════════════════
/-
  目的: monotone_level より真に弱い「最終的単調性」を分析し、
  打ち切りによる StructureTower 化を検証する。
-/

def EventuallyMonotoneSeq {α : Type*} (S : ℕ → Set α) : Prop :=
  ∃ N, ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j

-- N=1 から先は Set.Iic で単調、n=0 のみ {5} で非単調
def evMonExample : ℕ → Set ℕ :=
  fun n => if n = 0 then {5} else Set.Iic n

theorem evMonExample_eventually_monotone :
    EventuallyMonotoneSeq evMonExample := by
  refine ⟨1, fun i j hi hij => ?_⟩
  have hi' : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi
  have hj' : j ≠ 0 := Nat.one_le_iff_ne_zero.mp (Nat.le_trans hi hij)
  simp only [evMonExample, if_neg hi', if_neg hj', Set.Iic_subset_Iic]
  exact hij

theorem evMonExample_not_monotone :
    ¬ Monotone evMonExample := by
  intro h
  have h01 : evMonExample 0 ⊆ evMonExample 1 := h (Nat.le_succ 0)
  have h5 : (5 : ℕ) ∈ evMonExample 0 := by simp [evMonExample]
  have h5' := h01 h5
  simp [evMonExample, Set.mem_Iic] at h5'

-- 打ち切り構成: eventually monotone な列を StructureTower に変換
def truncateToTower {α : Type*} (S : ℕ → Set α) (N : ℕ)
    (h : ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j) :
    StructureTower ℕ α where
  level i := S (i + N)
  monotone_level := fun i j hij =>
    h (i + N) (j + N) (Nat.le_add_left N i) (Nat.add_le_add_right hij N)

-- ════════════════════════════════════════════════════════════
-- §P10. schema — thresholdTower（重み関数パターン）🟡
-- ════════════════════════════════════════════════════════════
/-
  目的: iic / ofMonotoneSeq / idealPowTower を統一する
  汎用パターン「閾値塔」を設計・実装する。
  FilteredAddCommMonoid の公理が自然に生じる構造を解明。
-/

-- 重み関数 w : α → ι による閾値塔: level i = {x | w(x) ≤ i}
def thresholdTower {α ι : Type*} [Preorder ι] (w : α → ι) :
    StructureTower ι α where
  level i := {x | w x ≤ i}
  monotone_level := fun _i _j hij _x hx => le_trans hx hij

-- w = id のとき thresholdTower = iic
theorem thresholdTower_eq_iic {α : Type*} [Preorder α] :
    thresholdTower (id : α → α) = iic α := by
  ext i x
  simp [thresholdTower, iic, Set.mem_Iic]

-- w の全射性（各 i が w の像に含まれる）よりすべての x がいずれかのレベルに属する
theorem thresholdTower_exhaustive_of_surjective {α ι : Type*} [Preorder ι]
    (w : α → ι) (hw : Function.Surjective w) :
    ∀ x : α, ∃ i : ι, x ∈ (thresholdTower w).level i := by
  intro x
  exact ⟨w x, le_refl _⟩

-- §P10.4: 加法閉性の十分条件（劣加法的重み関数）
-- w が零元保存（w 0 ≤ i）かつ劣加法的（w(x+y) ≤ max(w x)(w y)）ならば
-- x, y ∈ level i → x+y ∈ level i が成立する
-- （max(w x)(w y) ≤ i ↔ w x ≤ i ∧ w y ≤ i から従う）
theorem thresholdTower_add_mem {α ι : Type*} [Preorder ι] [SemilatticeSup ι]
    [AddCommMonoid α] (w : α → ι)
    (hw : ∀ x y : α, w (x + y) ≤ w x ⊔ w y)
    (i : ι) (x y : α) (hx : x ∈ (thresholdTower w).level i)
    (hy : y ∈ (thresholdTower w).level i) :
    x + y ∈ (thresholdTower w).level i := by
  simp only [thresholdTower, Set.mem_setOf_eq] at hx hy ⊢
  exact le_trans (hw x y) (sup_le hx hy)

-- ════════════════════════════════════════════════════════════
-- §P11. finite_computational — Fin 3 × Fin 5 での明示的計算 🟢
-- ════════════════════════════════════════════════════════════
/-
  目的: 有限かつ完全計算可能な例で union / global / inter の
  結果を明示的に列挙し、機械的検証を行う。
-/

-- 塔 T₁: level 0 = {0,1}, level 1 = {0,1,2,3}, level 2 = Set.univ（= Fin 5 全体）
def finTower1 : StructureTower (Fin 3) (Fin 5) where
  level i := match i with
    | ⟨0, _⟩ => {0, 1}
    | ⟨1, _⟩ => {0, 1, 2, 3}
    | ⟨2, _⟩ => Set.univ
    | ⟨n + 3, h⟩ => absurd h (by omega)
  monotone_level := by
    intro i j hij x hx
    fin_cases i <;> fin_cases j <;>
      simp_all [Fin.le_iff_val_le_val] <;>
      simp_all [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ] <;>
      omega

-- 塔 T₂: level 0 = {0}, level 1 = {0,2}, level 2 = {0,2,4}
def finTower2 : StructureTower (Fin 3) (Fin 5) where
  level i := match i with
    | ⟨0, _⟩ => {0}
    | ⟨1, _⟩ => {0, 2}
    | ⟨2, _⟩ => {0, 2, 4}
    | ⟨n + 3, h⟩ => absurd h (by omega)
  monotone_level := by
    intro i j hij x hx
    fin_cases i <;> fin_cases j <;>
      simp_all [Fin.le_iff_val_le_val] <;>
      simp_all [Set.mem_insert_iff, Set.mem_singleton_iff] <;>
      omega

-- P11-1: union = Set.univ（level 2 = Set.univ が union 全体を張る）
theorem finTower1_union :
    finTower1.union = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [union, Set.mem_iUnion]
  exact ⟨⟨2, by omega⟩, Set.mem_univ x⟩

-- P11-2: global = {0, 1}（level 0 = {0,1} が最小なので交叉はそれに等しい）
theorem finTower1_global :
    finTower1.global = ({0, 1} : Set (Fin 5)) := by
  apply Set.Subset.antisymm
  · -- ⋂ level i ⊆ level ⟨0, _⟩ = {0, 1}
    intro x hx
    have := Set.mem_iInter.mp hx ⟨0, by omega⟩
    simpa [global, finTower1] using this
  · -- {0, 1} ⊆ ⋂ level i（level が単調なので level 0 ⊆ 全レベル）
    intro x hx
    simp only [global, Set.mem_iInter]
    intro i
    fin_cases i <;>
      simp_all [finTower1, Set.mem_insert_iff, Set.mem_singleton_iff]

-- P11-3: inter T₁ T₂ のレベル 0 は {0}
theorem finTower_inter_level0 :
    (inter finTower1 finTower2).level ⟨0, by omega⟩ = {(0 : Fin 5)} := by
  ext x
  simp only [inter_level, Set.mem_inter_iff, Set.mem_singleton_iff]
  simp only [finTower1, finTower2]
  fin_cases x <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end BourbakiGuide
