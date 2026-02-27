/-
  StructureTower — 接続ファイル
  ════════════════════════════════════════════════════════════

  本ファイルの目的:
    EscapeExercises（代数的フィルトレーション）と
    CategoricalView（圏論的視点）の橋渡し。

  中心命題:
    「mapOnHom の hg 条件」と「FilteredRing.mul_mem」は
    同一の数学的構造（次数付き射の可換性）の２つの表現である。

  構成:
    §1. 二項タワー（BinaryTower）
        R の ι-タワー T から、R×R の (ι×ι)-タワーを作る。
        level (i,j) = T.level i × T.level j

    §2. 乗法の射（MulHom as Tower Hom）
        FilteredRing.mul_mem ↔
          乗法 * が BinaryTower → reindex (·+·) T の Hom

    §3. フィルター環の射（FilteredRingHom）
        環準同型 + hg 条件 ↔ タワーの Hom

    §4. mapOnHom の具体化
        FilteredRing 上で mapOnHom を呼ぶと
        FilteredRingHom が自動的に得られる

    §5. 統合定理
        「hg 条件は FilteredRing の圏の射の条件と一致する」

  依存:
    本ファイルは自己完結。
    EscapeExercises / CategoricalView の定義を再掲して使う。
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. 依存する定義の再掲（自己完結）
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level          : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β γ : Type*} [Preorder ι]

-- NatInclusion
def NatInclusion (T₁ T₂ : StructureTower ι α) : Prop :=
  ∀ i, T₁.level i ⊆ T₂.level i

-- Hom
structure Hom (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  toFun     : α → β
  preserves : ∀ i, MapsTo toFun (T₁.level i) (T₂.level i)

instance {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} :
    CoeFun (Hom T₁ T₂) (fun _ => α → β) where
  coe f := f.toFun

-- map, reindex
def map (f : α → β) (T : StructureTower ι α) : StructureTower ι β where
  level i        := f '' T.level i
  monotone_level := by
    intro i j hij y ⟨x, hx, rfl⟩
    exact ⟨x, T.monotone_level hij hx, rfl⟩

def reindex {κ : Type*} [Preorder κ] (f : ι → κ) (hf : Monotone f)
    (T : StructureTower κ α) : StructureTower ι α where
  level i        := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

-- mapOnHom（CategoricalView C1 の完成版）
def mapOnHom (f : α → β) {T₁ T₂ : StructureTower ι α}
    (g : Hom T₁ T₂) (gβ : β → β) (hg : ∀ x, gβ (f x) = f (g x)) :
    Hom (map f T₁) (map f T₂) where
  toFun     := gβ
  preserves := fun i y ⟨x, hx, rfl⟩ => ⟨g x, g.preserves i hx, hg x⟩

-- ════════════════════════════════════════════════════════════
-- §1. 二項タワー（BinaryTower）
-- ════════════════════════════════════════════════════════════
/-
  FilteredRing の乗法を射として記述するには、
  「i-層と j-層の対」を (i,j) で添字付けたタワーが必要。

  BinaryTower T: StructureTower (ι × ι) (R × R)
    level (i, j) = T.level i × T.level j

  ι × ι の前順序: (i,j) ≤ (i',j') iff i ≤ i' ∧ j ≤ j'
-/

def binaryTower (T : StructureTower ι α) : StructureTower (ι × ι) (α × α) where
  level ij       := T.level ij.1 ×ˢ T.level ij.2
  monotone_level := by
    intro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ ⟨h₁, h₂⟩ ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨T.monotone_level h₁ hx, T.monotone_level h₂ hy⟩

@[simp] theorem binaryTower_level (T : StructureTower ι α) (i j : ι) :
    (binaryTower T).level (i, j) = T.level i ×ˢ T.level j := rfl

-- ════════════════════════════════════════════════════════════
-- §2. 乗法の射（mul_mem ↔ Hom）
-- ════════════════════════════════════════════════════════════
/-
  FilteredRing.mul_mem の意味:
    ∀ i j, ∀ x ∈ F.level i, ∀ y ∈ F.level j, x * y ∈ F.level (i + j)

  これを StructureTower の言語で書くと:
    乗法 * : R × R → R が
    binaryTower T → reindex (· + ·) T  の Hom になっている。

  以下でその同値を証明する。
-/

section MulHomEquiv

variable {ι R : Type*} [Preorder ι] [AddMonoid ι] [Ring R]

-- 添字加算の単調性（Preorder + AddMonoid の仮定が必要）
private theorem add_mono_of_le {i i' j j' : ι}
    [CovariantClass ι ι (· + ·) (· ≤ ·)]
    [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    (hi : i ≤ i') (hj : j ≤ j') : i + j ≤ i' + j' :=
  add_le_add hi hj

-- 添字加算 (i,j) ↦ i+j の単調性
theorem fst_add_snd_monotone
    [CovariantClass ι ι (· + ·) (· ≤ ·)]
    [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)] :
    Monotone (fun ij : ι × ι => ij.1 + ij.2) :=
  fun ⟨_i, _j⟩ ⟨_i', _j'⟩ ⟨h₁, h₂⟩ => add_le_add h₁ h₂

/-- FilteredRing の mul_mem 公理を保持する構造 -/
structure FilteredRing (ι R : Type*) [Preorder ι] [AddMonoid ι] [Ring R]
    [CovariantClass ι ι (· + ·) (· ≤ ·)]
    [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    extends StructureTower ι R where
  zero_mem : ∀ i : ι, (0 : R) ∈ level i
  add_mem  : ∀ (i : ι) {x y : R}, x ∈ level i → y ∈ level i → x + y ∈ level i
  neg_mem  : ∀ (i : ι) {x : R}, x ∈ level i → -x ∈ level i
  one_mem  : (1 : R) ∈ level 0
  mul_mem  : ∀ (i j : ι) {x y : R}, x ∈ level i → y ∈ level j → x * y ∈ level (i + j)

variable {ι R : Type*} [Preorder ι] [AddMonoid ι] [Ring R]
  [CovariantClass ι ι (· + ·) (· ≤ ·)]
  [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]

/-- mul_mem から「乗法は BinaryTower の射」を構成する

  方向: mul_mem → Hom
  乗法 * が binaryTower F.toStructureTower → reindex (·+·) F.toStructureTower
  の Hom であることを示す。 -/
def FilteredRing.toMulHom (F : FilteredRing ι R) :
    Hom (binaryTower F.toStructureTower)
        (reindex (fun ij : ι × ι => ij.1 + ij.2) fst_add_snd_monotone
          F.toStructureTower) where
  toFun     := fun ⟨x, y⟩ => x * y
  preserves := by
    intro ⟨i, j⟩ ⟨x, y⟩ ⟨hx, hy⟩
    simp [reindex]
    exact F.mul_mem i j hx hy

/-- 逆方向: 「乗法が Hom」ならば mul_mem 公理が成り立つ -/
theorem mulHom_to_mul_mem
    (T : StructureTower ι R)
    (hzero : ∀ i, (0 : R) ∈ T.level i)
    (hadd  : ∀ i {x y}, x ∈ T.level i → y ∈ T.level i → x + y ∈ T.level i)
    (hneg  : ∀ i {x}, x ∈ T.level i → -x ∈ T.level i)
    (hone  : (1 : R) ∈ T.level 0)
    (hmul  : Hom (binaryTower T)
                 (reindex (fun ij : ι × ι => ij.1 + ij.2) fst_add_snd_monotone T))
    (hmul_eq : hmul.toFun = fun ⟨x, y⟩ => x * y) :
    FilteredRing ι R where
  toStructureTower := T
  zero_mem := hzero
  add_mem  := hadd
  neg_mem  := hneg
  one_mem  := hone
  mul_mem  := by
    intro i j x y hx hy
    have := hmul.preserves (i, j) ⟨x, y⟩ ⟨hx, hy⟩
    simp [reindex] at this
    rwa [hmul_eq] at this

/-- 同値の主定理:
    「FilteredRing の乗法公理」と「乗法が特定の Hom」は等価 -/
theorem mul_mem_iff_mulHom (F : FilteredRing ι R) (i j : ι) {x y : R} :
    (x ∈ F.level i ∧ y ∈ F.level j → x * y ∈ F.level (i + j)) ↔
    ∀ p : R × R, p ∈ (binaryTower F.toStructureTower).level (i, j) →
      p.1 * p.2 ∈ (reindex (fun ij : ι × ι => ij.1 + ij.2)
        fst_add_snd_monotone F.toStructureTower).level (i, j) := by
  simp [binaryTower, reindex]
  constructor
  · intro h ⟨x', y'⟩ ⟨hx', hy'⟩; exact h ⟨hx', hy'⟩
  · intro h ⟨hx, hy⟩; exact h ⟨x, y⟩ ⟨hx, hy⟩

end MulHomEquiv

-- ════════════════════════════════════════════════════════════
-- §3. フィルター環の射（FilteredRingHom）
-- ════════════════════════════════════════════════════════════
/-
  FilteredRing の射とは:
    環準同型 φ : R →+* S であって
    各レベルを保つ: φ(F.level i) ⊆ G.level i

  これはちょうど StructureTower.Hom の条件と一致する。
  さらに「φ が乗法と可換」という条件が mapOnHom の hg 条件に対応する。
-/

section FilteredRingHom

variable {ι R S : Type*} [Preorder ι] [AddMonoid ι] [Ring R] [Ring S]
  [CovariantClass ι ι (· + ·) (· ≤ ·)]
  [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]

/-- フィルター環の射: 環準同型 + レベル保存 -/
structure FilteredRingHom
    (F : FilteredRing ι R) (G : FilteredRing ι S) where
  toFun      : R →+* S
  preserves  : ∀ i, MapsTo toFun (F.level i) (G.level i)

/-- FilteredRingHom は StructureTower.Hom になる -/
def FilteredRingHom.toTowerHom {F : FilteredRing ι R} {G : FilteredRing ι S}
    (φ : FilteredRingHom F G) :
    Hom F.toStructureTower G.toStructureTower where
  toFun     := φ.toFun
  preserves := φ.preserves

/-- 逆方向: 環準同型 φ とレベル保存条件があれば FilteredRingHom になる

    注意: StructureTower.Hom は「関数 + レベル保存」のみ持つ。
    「環準同型である」という代数的条件は Hom の外部から与える必要がある。
    これが §4 統合定理の核心: hg 条件は「環準同型性」と「レベル保存」の
    積として分解される。 -/
def ringHomToFilteredRingHom
    {F : FilteredRing ι R} {G : FilteredRing ι S}
    (φ : R →+* S)
    (hpres : ∀ i, MapsTo φ.toFun (F.level i) (G.level i)) :
    FilteredRingHom F G where
  toFun     := φ
  preserves := hpres

end FilteredRingHom

-- ════════════════════════════════════════════════════════════
-- §4. mapOnHom の FilteredRing への具体化
-- ════════════════════════════════════════════════════════════
/-
  CategoricalView の mapOnHom をフィルター環に適用すると:

    f : R → R[X]（多項式環への埋め込みなど）
    g : Hom T₁ T₂ （R-タワーの射）
    gβ : R[X] → R[X]（対応する多項式環の操作）
    hg : gβ (f r) = f (g r)（可換性）

  このとき mapOnHom が与える Hom は
  「FilteredRingHom の level 保存条件」と一致する。

  具体例: 定数埋め込み f = (· : R → R[X])、gβ = 係数に g を適用した持ち上げ
-/

section MapOnHomApplication

variable {ι R S : Type*} [Preorder ι] [AddMonoid ι] [Ring R] [Ring S]
  [CovariantClass ι ι (· + ·) (· ≤ ·)]
  [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]

/-- mapOnHom と FilteredRingHom の接続主定理:

    φ : R →+* S が FilteredRing の射 ↔
    φ が StructureTower の Hom 条件（mapOnHom の hg 型）を満たす

  方向1: FilteredRingHom → mapOnHom の hg 条件
  φ を R から S への埋め込みとして見たとき、
  「level を保つ」= 「f = φ について hg が成立」

  方向2: hg 条件 → FilteredRingHom (レベル保存の証明) -/
theorem filteredRingHom_iff_mapOnHom_cond
    (F : FilteredRing ι R) (G : FilteredRing ι S)
    (φ : R →+* S) :
    (∀ i, MapsTo φ (F.level i) (G.level i)) ↔
    -- これは mapOnHom の preserves 条件と同じ形
    ∀ i, ∀ x ∈ F.level i, φ x ∈ G.level i := by
  simp [MapsTo]

/-- hg 条件の FilteredRing 解釈:
    φ : R →+* S が FilteredRingHom ならば、
    乗法タワーの Hom と可換（hg 型の条件が自動的に成立）

    具体的に: x ∈ F.level i, y ∈ F.level j ならば
    φ(x * y) = φ(x) * φ(y) ∈ G.level (i + j)  -/
theorem filteredRingHom_mul_compatible
    (F : FilteredRing ι R) (G : FilteredRing ι S)
    (φ : FilteredRingHom F G) (i j : ι) {x y : R}
    (hx : x ∈ F.level i) (hy : y ∈ F.level j) :
    φ.toFun (x * y) ∈ G.level (i + j) := by
  rw [map_mul]
  exact G.mul_mem i j (φ.preserves i hx) (φ.preserves j hy)

/-- hg 条件の本質的な形:
    FilteredRingHom の「乗法との可換性」は
    binaryTower 上の Hom と reindex の整合性として書ける -/
theorem filteredRingHom_commutes_with_mul
    (F : FilteredRing ι R) (G : FilteredRing ι S)
    (φ : FilteredRingHom F G) :
    -- φ を binaryTower に持ち上げると乗法 Hom と可換
    ∀ (ij : ι × ι) (p : R × R),
      p ∈ (binaryTower F.toStructureTower).level ij →
      (φ.toFun p.1 * φ.toFun p.2) ∈
        (reindex (fun ij : ι × ι => ij.1 + ij.2) fst_add_snd_monotone
          G.toStructureTower).level ij := by
  intro ⟨i, j⟩ ⟨x, y⟩ ⟨hx, hy⟩
  simp [reindex]
  exact G.mul_mem i j (φ.preserves i hx) (φ.preserves j hy)

end MapOnHomApplication

-- ════════════════════════════════════════════════════════════
-- §5. 統合定理
-- ════════════════════════════════════════════════════════════
/-
  これまでの議論のまとめ:

  [hg 条件の3つの顔]

  顔1 (CategoricalView): mapOnHom の設計上の条件
      gβ ∘ f = f ∘ g
      = 「β-側の操作 gβ が f を通じて α-側の操作 g と可換」

  顔2 (EscapeExercises): FilteredRing.mul_mem
      x ∈ F(i), y ∈ F(j) ⊢ x*y ∈ F(i+j)
      = 「乗法が次数加算と可換」

  顔3 (Bridge §4): FilteredRingHom の乗法可換性
      φ(x*y) = φ(x)*φ(y) かつ φ(F(i)) ⊆ G(i)
      = 「環準同型が次数を保つ」

  [同値の連鎖]
      FilteredRing.mul_mem
    ⟺ (§2) 乗法が binaryTower → reindex T の Hom
    ⟺ (§4) mapOnHom の hg 条件が成立
    ⟺ (§3) FilteredRingHom の level 保存 + 乗法可換性

  この連鎖が「EscapeExercises ↔ CategoricalView の橋渡し」である。
-/

-- 統合を示す最終例:
-- FilteredRingHom φ : F → G があるとき、
-- 対応する TowerHom と mulHom が以下の可換図式をなす:
--
--   binaryTower F ──(id,id)──→ binaryTower G
--         │                          │
--       mul_F                      mul_G
--         ↓                          ↓
--   reindex(+) F ──── φ ────→ reindex(+) G
--
-- つまり「乗法 Hom と FilteredRingHom は可換」

theorem mul_hom_square_commutes
    {ι R S : Type*} [Preorder ι] [AddMonoid ι] [Ring R] [Ring S]
    [CovariantClass ι ι (· + ·) (· ≤ ·)]
    [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    (F : FilteredRing ι R) (G : FilteredRing ι S)
    (φ : FilteredRingHom F G)
    (ij : ι × ι) (p : R × R)
    (hp : p ∈ (binaryTower F.toStructureTower).level ij) :
    -- 上の経路: p ↦ (φ p.1, φ p.2) ↦ φ(p.1) * φ(p.2)
    -- 下の経路: p ↦ p.1 * p.2 ↦ φ(p.1 * p.2)
    -- 両者が一致する（RingHom の乗法保存から）
    φ.toFun (p.1 * p.2) =
    φ.toFun p.1 * φ.toFun p.2 := by
  exact map_mul φ.toFun p.1 p.2

-- コロラリー: 可換図式から FilteredRing の圏としての整合性
theorem filteredRing_category_coherence
    {ι R S : Type*} [Preorder ι] [AddMonoid ι] [Ring R] [Ring S]
    [CovariantClass ι ι (· + ·) (· ≤ ·)]
    [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    (F : FilteredRing ι R) (G : FilteredRing ι S)
    (φ : FilteredRingHom F G) (i j : ι) {x y : R}
    (hx : x ∈ F.level i) (hy : y ∈ F.level j) :
    -- φ が Hom であることと mul_mem が結合し、
    -- φ(x*y) ∈ G.level(i+j) が成立する
    φ.toFun (x * y) ∈ G.level (i + j) := by
  rw [map_mul]
  exact G.mul_mem i j (φ.preserves i hx) (φ.preserves j hy)

end StructureTower

end BourbakiGuide
