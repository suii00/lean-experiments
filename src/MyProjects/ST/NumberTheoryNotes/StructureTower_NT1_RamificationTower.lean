/-
  StructureTower 数論シリーズ（NT1）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル8相当（数論への第一歩）
  前提: Level 1-7 を完了していること（特に L4 subgroupClosure, L5 idealPowTower）

  動機:
    L5-L7 で可換環上の I-adic フィルトレーションを StructureTower の言語で
    記述し、乗法互換性・ClosedTower・分離条件・Rees 代数との双対性を確立した。
    これらは可換環論の「加法側」の構造である。

    数論シリーズ NT1 では **群の減少フィルトレーション** を StructureTower に導入する。
    動機は **分岐フィルトレーション** — 局所体のガロア拡大に付随する
    ガロア群の正規部分群列:

      G = G₋₁ ⊇ G₀（惰性群）⊇ G₁（暴分岐群）⊇ G₂ ⊇ ...

    ここで G_i = {σ ∈ G | v_L(σ(π) − π) ≥ i + 1} である。
    これは idealPowTower の **群側の双対**:
    - idealPowTower: 環の中のイデアルが縮小していく
    - ramificationTower: 群の中の部分群が縮小していく
    両者は「ガロア対応」を通じて結ばれる。

  ZEN大学 IUT カリキュラムとの対応:
    IUT1: 数論入門（基礎概念）           → §NT1-1 の動機付け
    IUT2: 可換代数・代数幾何・楕円曲線   → L5 idealPowTower が既に対応
    IUT3: ガロア理論・代数的整数論        → §NT1-2, NT1-3 の中核
    IUT4: 類体論・遠アーベル幾何・IUT     → §NT1-5 の展望

  核心的洞察:
    部分群のフィルトレーションは StructureTower ℕᵒᵈ (Set G) として自然に書ける。
    idealPowTower と同じ ℕᵒᵈ 添字を使い、同じ形の分離条件を持つ。
    しかし群には環にない構造がある:

    1. **正規性**: 各 G_i ◁ G（正規部分群）→ 商群 G/G_i が定義できる
    2. **次数付き商**: G_i / G_{i+1} の構造 → Graded Tower Theory の自然な動機
    3. **共役作用**: G が各 G_i に共役で作用 → Hom の非自明な例
    4. **有限性**: 有限拡大 ⟹ ⋂ G_i = {1} → Separated 条件の自然な成立

    ClosedTower の観点: L4 の subgroupClosure を使うと、各 G_i が部分群であることは
    ClosedTower 条件と同値になる。idealPowTower の ClosedTower (idealClosure) と完全に並行。

  学習の流れ:
    §NT1-1. 部分群フィルトレーション塔   — SubgroupFiltration → StructureTower ℕᵒᵈ
    §NT1-2. 正規鎖と閉包性             — Normal chain, ClosedTower under subgroupClosure
    §NT1-3. 分岐塔の抽象定義            — RamificationTower の公理的構成
    §NT1-4. 分離条件と脱出              — Separated ↔ global = {1}, escape theorem
    §NT1-5. idealPowTower への橋        — 環と群の二重フィルトレーション

  ヒントの読み方:
    Hint-1: 大まかな方針
    Hint-2: 使うべき補題やタクティク
    Hint-3: ほぼ答え
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Nat.Find

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definitions（自己完結のため再掲）
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β γ : Type*} [Preorder ι]

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

def global (T : StructureTower ι α) : Set α := ⋂ i, T.level i

structure Hom (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  toFun : α → β
  preserves : ∀ i, MapsTo toFun (T₁.level i) (T₂.level i)

instance (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    CoeFun (Hom T₁ T₂) (fun _ => α → β) where
  coe f := f.toFun

theorem Hom.ext {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {f g : Hom T₁ T₂} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; simp

def Hom.id (T : StructureTower ι α) : Hom T T where
  toFun := _root_.id
  preserves := by intro i x hx; exact hx

def Hom.comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) : Hom T₁ T₃ where
  toFun := g.toFun ∘ f.toFun
  preserves := by intro i x hx; exact g.preserves i (f.preserves i hx)

-- NatInclusion
def NatInclusion (T₁ T₂ : StructureTower ι α) : Prop :=
  ∀ i, T₁.level i ⊆ T₂.level i

-- L3: liftCl, ClosedTower
variable (cl : ClosureOperator (Set α))

def liftCl (T : StructureTower ι α) : StructureTower ι α where
  level i := cl (T.level i)
  monotone_level := by
    intro i j hij x hx
    exact cl.monotone (T.monotone_level hij) hx

structure ClosedTower (cl : ClosureOperator (Set α)) (ι : Type*) [Preorder ι]
    extends StructureTower ι α where
  level_closed : ∀ i, cl (level i) = level i

-- L5: idealPowTower（比較用に再掲）
variable {R : Type*} [CommRing R]

def idealPowTower (I : Ideal R) : StructureTower ℕᵒᵈ R where
  level n := ↑(I ^ OrderDual.ofDual n)
  monotone_level := by
    intro i j hij x hx
    exact
      (Ideal.pow_le_pow_right (I := I)
        (m := OrderDual.ofDual j) (n := OrderDual.ofDual i)
        (OrderDual.ofDual_le_ofDual.mpr hij)) hx

-- ════════════════════════════════════════════════════════════
-- §NT1-1. 部分群フィルトレーション塔  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  数論への第一歩: 群のフィルトレーションを StructureTower として構成する。

  **部分群フィルトレーション**とは、群 G の部分群の減少列:
    G = H₀ ⊇ H₁ ⊇ H₂ ⊇ ...

  これは idealPowTower I: R ⊇ I ⊇ I² ⊇ ... の群側の対応物。
  添字は ℕᵒᵈ（順序双対）— L5 と同じ方式。

  数論的例:
  - 分岐フィルトレーション: G₋₁ ⊇ G₀ ⊇ G₁ ⊇ ...
  - 下中心列: G ⊇ [G,G] ⊇ [[G,G],G] ⊇ ...
  - p-フィルトレーション: G ⊇ Gᵖ[G,G] ⊇ ...

  設計判断:
    入力は `f : ℕ → Subgroup G` で `Antitone f`（i ≤ j → f j ≤ f i）。
    StructureTower は増加族を要求するので、ℕᵒᵈ で添字する。
    level n = ↑(f (OrderDual.ofDual n)) で、L5 の idealPowTower と完全に並行。
-/

section SubgroupFiltration

variable {G : Type*} [Group G]

/-- 🟢 Exercise NT1-1a: 部分群フィルトレーション塔の構成。
    反単調な部分群列 f : ℕ → Subgroup G（i ≤ j → f j ≤ f i）から
    StructureTower ℕᵒᵈ G を構成する。

    L5 の idealPowTower I と完全に並行:
    - idealPowTower: level n = ↑(I ^ ofDual n)  （イデアルの台集合）
    - subgroupTower: level n = ↑(f (ofDual n))    （部分群の台集合）

    単調性: i ≤ j in ℕᵒᵈ ↔ ofDual j ≤ ofDual i in ℕ
                           → f (ofDual i) ≤ f (ofDual j)  （反単調）
                           → ↑(f (ofDual i)) ⊆ ↑(f (ofDual j))
    — ん？逆だ。ℕᵒᵈ で i ≤ j は自然数では ofDual i ≥ ofDual j。
    反単調なので f (ofDual i) ≤ f (ofDual j) → 台集合も ⊆。 ✓

    Hint-1: idealPowTower と同じ構造。
    Hint-2: OrderDual.ofDual_le_ofDual と反単調性を使う。
    Hint-3: `f.monotone (OrderDual.ofDual_le_ofDual.mpr hij)` -/
def subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) : StructureTower ℕᵒᵈ G where
  level n := ↑(OrderDual.ofDual (f (OrderDual.ofDual n)))
  monotone_level := by
    intro i j hij x hx
    have h := f.monotone (OrderDual.ofDual_le_ofDual.mpr hij)
    exact h hx

@[simp] theorem subgroupFiltrationTower_level (f : ℕ →o (Subgroup G)ᵒᵈ) (n : ℕᵒᵈ) :
    (subgroupFiltrationTower f).level n =
      ↑(OrderDual.ofDual (f (OrderDual.ofDual n))) := rfl

/-- 🟢 Exercise NT1-1b: 単位元は全レベルに属する。
    部分群は必ず単位元を含むため、1 ∈ level n for all n。
    これは idealPowTower で 0 ∈ level n（零元は全冪に属する）に対応。

    Hint-1: 部分群は one_mem を持つ。
    Hint-2: Subgroup.one_mem。 -/
theorem one_mem_subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) (n : ℕᵒᵈ) :
    (1 : G) ∈ (subgroupFiltrationTower f).level n := by
  show (1 : G) ∈ (OrderDual.ofDual (f (OrderDual.ofDual n)) : Subgroup G)
  exact one_mem _

/-- 🟢 Exercise NT1-1c: 逆元による閉性。
    g ∈ level n → g⁻¹ ∈ level n。
    部分群は逆元で閉じるため自明。

    Hint-1: Subgroup.inv_mem。 -/
theorem inv_mem_subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) (n : ℕᵒᵈ) {g : G}
    (hg : g ∈ (subgroupFiltrationTower f).level n) :
    g⁻¹ ∈ (subgroupFiltrationTower f).level n := by
  show g⁻¹ ∈ (OrderDual.ofDual (f (OrderDual.ofDual n)) : Subgroup G)
  exact inv_mem hg

/-- 🟡 Exercise NT1-1d: 乗法閉性。
    g, h ∈ level n → g * h ∈ level n。
    部分群は乗法で閉じるため。

    idealPowTower の乗法互換性（L5-1c）が
      x ∈ I^m, y ∈ I^n → xy ∈ I^{m+n}（**異なるレベル間**の乗法）
    であったのに対し、部分群塔の乗法閉性は **同一レベル内** の乗法。
    この差異は環と群の構造的違いを反映している:
    - 環: イデアル冪 I^m · I^n ⊆ I^{m+n}（次数が加算される）
    - 群: 部分群 H_n · H_n ⊆ H_n（次数は変わらない）

    ただし正規鎖の場合、**交換子**が次数を加算する:
      [G_i, G_j] ⊆ G_{i+j}
    これは §NT1-3 で扱う分岐塔の本質的な性質。

    Hint-1: Subgroup.mul_mem。 -/
theorem mul_mem_subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) (n : ℕᵒᵈ) {g h : G}
    (hg : g ∈ (subgroupFiltrationTower f).level n)
    (hh : h ∈ (subgroupFiltrationTower f).level n) :
    g * h ∈ (subgroupFiltrationTower f).level n := by
  show g * h ∈ (OrderDual.ofDual (f (OrderDual.ofDual n)) : Subgroup G)
  exact mul_mem hg hh

/-- 🟡 Exercise NT1-1e: global の特徴づけ。
    global = ⋂ₙ ↑(f n) — 全レベルの共通部分。
    これは idealPowTower の global = ⋂ₙ ↑(I^n)（L5-4a）と並行。

    数論的意味:
    - 分岐フィルトレーションで global = ⋂ G_i = {1}（有限拡大の場合）
    - 下中心列で global = ⋂ γ_i(G)（冪零群の場合 {1}）

    Hint-1: 定義展開。global = ⋂ (n : ℕᵒᵈ), level n。
    Hint-2: ℕᵒᵈ 上の全称と ℕ 上の全称は同値。 -/
theorem subgroupFiltrationTower_global (f : ℕ →o (Subgroup G)ᵒᵈ) :
    (subgroupFiltrationTower f).global =
      ⋂ (n : ℕ), ↑(OrderDual.ofDual (f n)) := by
  simp [StructureTower.global, subgroupFiltrationTower_level]
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro h n
    exact h (OrderDual.toDual n)
  · intro h n
    exact h (OrderDual.ofDual n)

end SubgroupFiltration

-- ════════════════════════════════════════════════════════════
-- §NT1-2. 正規鎖と閉包性  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  部分群フィルトレーション塔が ClosedTower であるための条件を調べる。

  L4 では subgroupClosure : ClosureOperator (Set G) を構成し、
  部分群の台集合が ClosedTower の不動点であることを示した。
  ここでは同じパターンを部分群フィルトレーション塔に適用する。

  subgroupClosure(S) = ⟨S⟩（S で生成される部分群の台集合）

  ClosedTower 条件: ∀ n, subgroupClosure (level n) = level n
  これは「level n が部分群の台集合である」ことと同値。

  部分群フィルトレーション塔は **定義から** 各レベルが Subgroup.carrier なので、
  ClosedTower 条件は自動的に成立する。これは idealPowTower の
  ClosedTower idealClosure（L5-2c）と完全に並行。

  さらに、正規性（Normal）は追加の構造を与える:
  - 各 G_i ◁ G → 共役作用が StructureTower Hom を誘導
  - 商群 G/G_i が well-defined → 塔の「段差」が代数的に記述可能
-/

section NormalChain

variable {G : Type*} [Group G]

/-- subgroupClosure: 部分集合 S から生成される部分群の台集合を返す閉包演算子。
    L4 で定義したものの再掲。Subgroup.closure が Mathlib の生成部分群。

    性質:
    - S ⊆ subgroupClosure S         （包含）
    - subgroupClosure (subgroupClosure S) = subgroupClosure S  （冪等）
    - S ⊆ T → subgroupClosure S ⊆ subgroupClosure T          （単調）
    - ↑H = subgroupClosure ↑H（部分群の台集合は不動点）        -/
noncomputable def subgroupClosure : ClosureOperator (Set G) :=
  {
    toFun := fun S => ↑(Subgroup.closure S)
    monotone' := by
      intro S T hST
      exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono hST)
    le_closure' := by
      intro S
      exact Subgroup.subset_closure
    idempotent' := by
      intro S
      exact congrArg SetLike.coe (Subgroup.closure_eq (Subgroup.closure S))
  }

/-- 🟡 Exercise NT1-2a: 部分群の台集合は subgroupClosure の不動点。
    H : Subgroup G に対し、subgroupClosure ↑H = ↑H。
    これは ClosedTower 条件の核心。

    Hint-1: Subgroup.closure_eq で H.closure = H。
    Hint-2: subgroupClosure の定義を展開して Subgroup.closure_eq を使う。 -/
theorem subgroupClosure_carrier_eq (H : Subgroup G) :
    subgroupClosure (↑H : Set G) = ↑H := by
  change ↑(Subgroup.closure (↑H : Set G)) = (↑H : Set G)
  exact congrArg SetLike.coe (Subgroup.closure_eq H)

/-- 🟡 Exercise NT1-2b: 部分群フィルトレーション塔は ClosedTower。
    各 level n が Subgroup の carrier なので、subgroupClosure で閉じている。
    idealPowTower が ClosedTower idealClosure（L5-2c）であることと並行。

    意義: これにより L3 のモナド理論（liftCl, unit, EM 代数）が
    部分群フィルトレーションにも適用される。

    Hint-1: 各レベルが Subgroup.carrier であることを使う。
    Hint-2: subgroupClosure_carrier_eq を適用。
    Hint-3: `fun n => subgroupClosure_carrier_eq _` -/
def subgroupFiltrationClosedTower (f : ℕ →o (Subgroup G)ᵒᵈ) :
    ClosedTower subgroupClosure ℕᵒᵈ (α := G) where
  level n := ↑(OrderDual.ofDual (f (OrderDual.ofDual n)))
  monotone_level := (subgroupFiltrationTower f).monotone_level
  level_closed n := by
    simpa using
      (subgroupClosure_carrier_eq
        (H := OrderDual.ofDual (f (OrderDual.ofDual n))))

/-- 正規部分群フィルトレーションの条件。
    各 f n が G の正規部分群であること。
    数論的には分岐群 G_i ◁ G が典型。 -/
def IsNormalFiltration (f : ℕ →o (Subgroup G)ᵒᵈ) : Prop :=
  ∀ n, (OrderDual.ofDual (f n)).Normal

/-- 🟡 Exercise NT1-2c: 共役作用は塔の自己射を誘導する。
    g ∈ G に対し、共役 x ↦ g * x * g⁻¹ は
    正規部分群フィルトレーション塔の自己射 (Hom T T) を与える。

    正規性が本質的: h ∈ H_n, H_n ◁ G → g h g⁻¹ ∈ H_n。

    注: idealPowTower では環の可換性により共役が自明（恒等射と一致）。
    群の場合は非自明な Hom を生む — StructureTower で群論固有の現象。

    Hint-1: 正規部分群の定義: g * h * g⁻¹ ∈ H。
    Hint-2: Subgroup.Normal.conj_mem。 -/
def conjugationHom (f : ℕ →o (Subgroup G)ᵒᵈ) (hN : IsNormalFiltration f) (g : G) :
    Hom (subgroupFiltrationTower f) (subgroupFiltrationTower f) where
  toFun x := g * x * g⁻¹
  preserves := by
    intro n x hx
    show g * x * g⁻¹ ∈ (OrderDual.ofDual (f (OrderDual.ofDual n)) : Subgroup G)
    exact (hN (OrderDual.ofDual n)).conj_mem x hx g

end NormalChain

-- ════════════════════════════════════════════════════════════
-- §NT1-3. 分岐塔の抽象定義  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  分岐フィルトレーションの公理的定義。

  古典的な分岐フィルトレーション（局所体のガロア拡大 L/K）:
    G = Gal(L/K)
    G_i = {σ ∈ G | v_L(σ(π) - π) ≥ i + 1}  （i ≥ 0）
    G₋₁ = G（全体群）

  ℕ で添字すると G₀ ⊇ G₁ ⊇ G₂ ⊇ ...（G₋₁ = G は別途管理）。

  公理的に捉えると、分岐フィルトレーションは以下を満たす部分群列:
  (RF1) 反単調: i ≤ j → G_j ≤ G_i
  (RF2) 正規: 各 G_i ◁ G
  (RF3) 分離: ⋂ G_i = {1}（有限拡大の場合）
  (RF4) 交換子条件: [G_i, G_j] ≤ G_{i+j}（より深い分岐の制御）

  (RF4) は数論的に本質的: 交換子が「次数を加算する」。
  これは idealPowTower の乗法互換性 I^m · I^n ⊆ I^{m+n} の群側の対応物。
  ただし群の「乗法」は交換子 [g, h] = g h g⁻¹ h⁻¹ に置き換わる。

  StructureTower の視点:
  - idealPowTower: x ∈ I^m, y ∈ I^n → xy ∈ I^{m+n}      （積が次数を加算）
  - ramificationTower: g ∈ G_i, h ∈ G_j → [g,h] ∈ G_{i+j} （交換子が次数を加算）

  両者は「フィルトレーション付き代数」の概念で統一される。
  これは StructureTower の OrderHom 以上の構造:
  単なる包含関係だけでなく、**演算と添字の算術的関係**を捉えている。
-/

section RamificationTower

variable {G : Type*} [Group G]

/-- 分岐フィルトレーションのデータ。
    部分群列 f に正規性・分離性・交換子条件を付加。

    設計方針:
    - f : ℕ → Subgroup G は反単調（i ≤ j → f j ≤ f i）
    - ℕ で添字（0 が惰性群 G₀, 1 が暴分岐群 G₁, ...）
    - 全体群 G₋₁ = ⊤ は別途 whole フィールドで管理
    - 交換子条件はオプショナル（hasCommutatorBound） -/
structure RamificationData (G : Type*) [Group G] where
  /-- 部分群列: i ↦ G_i（i = 0 は惰性群, i = 1 は暴分岐群）-/
  groups : ℕ → Subgroup G
  /-- 反単調性: i ≤ j → G_j ≤ G_i -/
  antitone : Antitone groups
  /-- 全体群を含む: G₀ ≤ G = ⊤（全ガロア群）-/
  whole : groups 0 ≤ ⊤
  /-- 正規性: 各 G_i は G の正規部分群 -/
  normal : ∀ n, (groups n).Normal

/-- RamificationData から ℕ →o (Subgroup G)ᵒᵈ を構成。
    §NT1-1 の subgroupFiltrationTower に接続するための橋。 -/
def RamificationData.toOrderHom (rd : RamificationData G) :
    ℕ →o (Subgroup G)ᵒᵈ where
  toFun n := OrderDual.toDual (rd.groups n)
  monotone' := by
    intro i j hij
    show rd.groups j ≤ rd.groups i
    exact rd.antitone hij

/-- 🟡 Exercise NT1-3a: 分岐塔の構成。
    RamificationData から StructureTower ℕᵒᵈ G を構成。

    これは §NT1-1 の subgroupFiltrationTower を
    分岐フィルトレーション特有のデータで特殊化したもの。

    Hint-1: subgroupFiltrationTower を rd.toOrderHom に適用。 -/
def ramificationTower (rd : RamificationData G) : StructureTower ℕᵒᵈ G :=
  subgroupFiltrationTower rd.toOrderHom

@[simp] theorem ramificationTower_level (rd : RamificationData G) (n : ℕᵒᵈ) :
    (ramificationTower rd).level n = ↑(rd.groups (OrderDual.ofDual n)) := rfl

/-- 🟡 Exercise NT1-3b: 分岐塔は ClosedTower。
    §NT1-2b の特殊化。

    Hint-1: subgroupFiltrationClosedTower を適用。 -/
def ramificationClosedTower (rd : RamificationData G) :
    ClosedTower subgroupClosure ℕᵒᵈ (α := G) :=
  subgroupFiltrationClosedTower rd.toOrderHom

/-- 🟡 Exercise NT1-3c: 分岐塔の共役自己射。
    §NT1-2c の特殊化。正規性は RamificationData.normal から自動。

    Hint-1: conjugationHom を rd.toOrderHom に適用。 -/
def ramificationConjugation (rd : RamificationData G) (g : G) :
    Hom (ramificationTower rd) (ramificationTower rd) := by
  apply conjugationHom rd.toOrderHom
  · intro n; exact rd.normal n
  · exact g

/-- 交換子条件: [G_i, G_j] ≤ G_{i+j}。
    分岐フィルトレーションの深い性質。

    数論的意味:
    - G_i の元 σ は「i+1 次の精度で恒等写像に近い」
    - G_j の元 τ は「j+1 次の精度で恒等写像に近い」
    - 交換子 [σ, τ] = σ τ σ⁻¹ τ⁻¹ は「(i+j)+1 次の精度で恒等写像に近い」
    - 精度が加算される！

    StructureTower への影響:
    - これは「交換子が次数を加算するフィルトレーション」を公理化する
    - idealPowTower の I^m · I^n ⊆ I^{m+n} と同型のパターン
    - OrderHom だけでは捉えられない **演算構造** -/
def HasCommutatorBound (rd : RamificationData G) : Prop :=
  ∀ i j : ℕ, ∀ g h : G,
    g ∈ rd.groups i → h ∈ rd.groups j →
      g * h * g⁻¹ * h⁻¹ ∈ rd.groups (i + j)

/-- 🔴 Exercise NT1-3d: 交換子条件から「2倍の深さ」。
    HasCommutatorBound → [G_n, G_n] ≤ G_{2n}。
    i = j = n の特殊化。

    これは 群が「急速に冪零に近づく」ことを意味する:
    分岐群列の各段の交換子は2段下に落ちる。

    Hint-1: HasCommutatorBound の i = j = n の場合。
    Hint-2: 定義の展開のみ。 -/
theorem commutator_double_depth (rd : RamificationData G) (hC : HasCommutatorBound rd)
    (n : ℕ) {g h : G} (hg : g ∈ rd.groups n) (hh : h ∈ rd.groups n) :
    g * h * g⁻¹ * h⁻¹ ∈ rd.groups (n + n) :=
  hC n n g h hg hh

end RamificationTower

-- ════════════════════════════════════════════════════════════
-- §NT1-4. 分離条件と脱出  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  L5 の分離条件 IsSeparated を群のフィルトレーションに翻訳する。

  環: IsSeparated I := ⨅ₙ I^n = ⊥ ↔ global idealPowTower = {0}
  群: IsSeparatedGroup f := ⨅ₙ f(n) = ⊥ ↔ global subgroupFiltrationTower = {1}

  数論的意味:
  - 有限ガロア拡大 → 分岐群列は有限段で ⊥ に到達 → 分離的
  - ⋂ G_i = {1} は「十分深くフィルターすると恒等写像だけが残る」
  - これは p-adic 完備化の分離性（⋂ pⁿℤ_p = {0}）の群側の対応物

  L5-4c の escape 定理の群版:
  分離的 → σ ≠ 1 → ∃ n, σ ∉ G_n（非自明な元はどこかで脱出する）
-/

section SeparationGroup

variable {G : Type*} [Group G]

/-- 部分群フィルトレーションの分離条件。
    ⋂ₙ f(n) = ⊥（自明部分群）。

    L5 の IsSeparated I := ⨅ₙ I^n = ⊥ と並行。 -/
def IsSeparatedFiltration (f : ℕ → Subgroup G) : Prop :=
  ⨅ n, f n = ⊥

/-- 🟡 Exercise NT1-4a: 分離条件と global の同値性。
    IsSeparatedFiltration f ↔ global (subgroupFiltrationTower f) = {1}。

    L5-4b の isSeparated_iff_global_eq と並行。

    Hint-1: global = ⋂ₙ ↑(f n) = ↑(⨅ₙ f n)。
    Hint-2: ⊥ の台集合は {1} (Subgroup.coe_bot)。
    Hint-3: Subgroup.coe_iInf と Subgroup.coe_bot の組み合わせ。 -/
theorem isSeparatedFiltration_iff_global (f : ℕ →o (Subgroup G)ᵒᵈ) :
    IsSeparatedFiltration (fun n => OrderDual.ofDual (f n)) ↔
      (subgroupFiltrationTower f).global = {(1 : G)} := by
  have hglobal : (subgroupFiltrationTower f).global =
      ↑(⨅ n : ℕ, OrderDual.ofDual (f n)) := by
    ext x
    simp [StructureTower.global, subgroupFiltrationTower_level]
  constructor
  · intro h
    rw [hglobal, h]
    simp [Subgroup.coe_bot]
  · intro h
    rw [hglobal] at h
    exact SetLike.coe_injective (by simpa [Subgroup.coe_bot] using h)

/-- 🟡 Exercise NT1-4b: 分離条件のもとでの脱出。
    IsSeparatedFiltration f で σ ≠ 1 なら ∃ n, σ ∉ f(n)。

    L5-4c の escape_of_isSeparated と並行。

    数論的意味:
    「非自明なガロア作用素 σ ≠ 1 は、十分深い分岐レベルから脱出する」
    すなわち σ の「分岐の深さ」は有限。これが分岐指標の有限性を保証する。

    Hint-1: IsSeparatedFiltration → global = {1}。σ ≠ 1 なら σ ∉ global。
    Hint-2: global = ⋂ₙ ↑(f n) の否定。
    Hint-3: push_neg で ∃ n を取り出す。 -/
theorem escape_of_isSeparatedFiltration
    (f : ℕ →o (Subgroup G)ᵒᵈ)
    (hSep : IsSeparatedFiltration (fun n => OrderDual.ofDual (f n)))
    {σ : G} (hσ : σ ≠ 1) :
    ∃ n : ℕ, σ ∉ (OrderDual.ofDual (f n) : Subgroup G) := by
  classical
  have hglob := (isSeparatedFiltration_iff_global f).mp hSep
  have hσ_not_global : σ ∉ (subgroupFiltrationTower f).global := by
    rw [hglob]
    simp [hσ]
  rw [subgroupFiltrationTower_global] at hσ_not_global
  simp only [Set.mem_iInter, not_forall] at hσ_not_global
  exact hσ_not_global

/-- 分岐指標（break）の定義。
    分離条件のもとで、σ ≠ 1 なる元の「最大の分岐深さ」。
    b(σ) = sup {i | σ ∈ G_i}。

    有限群の場合は最大値が存在し、これが分岐指標になる。
    Hasse-Arf 定理: 上付番号への変換後、分岐指標は整数値をとる。
    → 将来の NT2 で StructureTower の reindex として定式化予定。 -/
noncomputable def ramificationBreak
    (rd : RamificationData G)
    (hSep : IsSeparatedFiltration rd.groups)
    {σ : G} (hσ : σ ≠ 1) : ℕ := by
  classical
  exact Nat.find (escape_of_isSeparatedFiltration rd.toOrderHom hSep hσ)

/-- 🔴 Exercise NT1-4c: 分岐指標の特徴づけ。
    b(σ) = n ↔ σ ∈ G_n かつ σ ∉ G_{n+1}。

    ただし、b(σ) は「σ ∉ G_n となる最小の n」なので、
    σ ∈ G_{b(σ)-1} かつ σ ∉ G_{b(σ)} が正確。
    ここでは b(σ) > 0 の場合の σ ∈ G_{b(σ)-1} を示す。

    Hint-1: Nat.find_spec で σ ∉ G_{b(σ)} を得る。
    Hint-2: b(σ) > 0 なら b(σ) - 1 < b(σ) で Nat.find_min。
    Hint-3: Nat.find_min の否定から σ ∈ G_{b(σ)-1}。 -/
theorem ramificationBreak_spec
    (rd : RamificationData G)
    (hSep : IsSeparatedFiltration rd.groups)
    {σ : G} (hσ : σ ≠ 1) :
    σ ∉ (rd.groups (ramificationBreak rd hSep hσ) : Subgroup G) := by
  classical
  simpa [ramificationBreak] using
    (Nat.find_spec (escape_of_isSeparatedFiltration rd.toOrderHom hSep hσ))

theorem mem_of_lt_ramificationBreak
    (rd : RamificationData G)
    (hSep : IsSeparatedFiltration rd.groups)
    {σ : G} (hσ : σ ≠ 1) {n : ℕ}
    (hn : n < ramificationBreak rd hSep hσ) :
    σ ∈ (rd.groups n : Subgroup G) := by
  classical
  by_contra h
  exact
    (Nat.find_min (escape_of_isSeparatedFiltration rd.toOrderHom hSep hσ)
      (by simpa [ramificationBreak] using hn)) h

end SeparationGroup

-- ════════════════════════════════════════════════════════════
-- §NT1-5. idealPowTower への橋  🔴
-- ════════════════════════════════════════════════════════════

/-!
  StructureTower が捉える「二重フィルトレーション」:
  同じ算術的現象を環側と群側の2つの塔で同時に記述する。

  設定: 可換環 R のイデアル I と、R の自己同型群 G = Aut(R) の部分群。
  - 環側: idealPowTower I : StructureTower ℕᵒᵈ R
  - 群側: subgroupFiltrationTower f : StructureTower ℕᵒᵈ G

  橋渡し: 「σ ∈ G_n ↔ σ が I^n 上で恒等的に作用」
  すなわち、分岐群 G_n は「I^n を保存する自己同型」の集合。

  StructureTower の視点からの意義:
  - 2つの異なる塔（環上と群上）が **同じ添字集合 ℕᵒᵈ** を共有
  - 塔間の対応は単なる Hom ではなく、「レベルの一致」
  - これは Tower Comparison Theory の数論的動機

  具体例（p-adic 世界）:
  - R = O_L（整数環）, I = 𝔭（素イデアル）
  - G = Gal(L/K), G_n = {σ | ∀ x ∈ O_L, σ(x) - x ∈ 𝔭^{n+1}}
  - idealPowTower 𝔭 と ramificationTower は同じ算術を異なる視点から記述

  ここでは抽象的な設定で、「群作用が塔を保存する」条件を定式化する。
-/

section RingGroupBridge

variable {R : Type*} [CommRing R] {G : Type*}

/-- 群作用による塔の保存。
    G が R に作用し、各 σ ∈ G が idealPowTower I の Hom を誘導する。

    この条件は「σ(I^n) ⊆ I^n for all n」と同値。
    数論的には「ガロア作用がイデアルのべき乗を保存する」。 -/
structure TowerPreservingAction (I : Ideal R) (action : G → R →+* R) where
  /-- 各 σ が I^n を保存する -/
  preserves_pow : ∀ (σ : G) (n : ℕ) (x : R),
    x ∈ I ^ n → action σ x ∈ I ^ n

/-- 🔴 Exercise NT1-5a: 塔保存作用から StructureTower Hom を構成。
    各 σ ∈ G が idealPowTower I の自己射を誘導する。

    Hint-1: Hom の toFun は action σ。
    Hint-2: preserves は TowerPreservingAction.preserves_pow から。 -/
def actionToTowerHom (I : Ideal R) (action : G → R →+* R)
    (hTP : TowerPreservingAction I action) (σ : G) :
    Hom (idealPowTower I) (idealPowTower I) where
  toFun := action σ
  preserves := by
    intro n x hx
    exact hTP.preserves_pow σ (OrderDual.ofDual n) x hx

/-- 🔴 Exercise NT1-5b: 分岐深さの抽象的定義。
    「σ が I^n のレベルで恒等的に作用する」条件:
    ∀ x ∈ R, action σ x - x ∈ I^n。

    これは分岐群 G_n の定義の抽象化:
    G_n = {σ | ∀ x, v(σ(x) - x) ≥ n+1}
    = {σ | ∀ x, σ(x) - x ∈ 𝔭^{n+1}}

    この条件を使って、群 G の部分群列を **環の塔から誘導** できる。 -/
def ramificationSubgroup (I : Ideal R) (action : G → R →+* R) (n : ℕ) : Set G :=
  {σ : G | ∀ x : R, action σ x - x ∈ I ^ n}

/-- 🔴 Exercise NT1-5c: ramificationSubgroup は反単調。
    n ≤ m → ramificationSubgroup I action m ⊆ ramificationSubgroup I action n。
    I^m ⊆ I^n（m ≥ n）だから。

    Hint-1: I^m ≤ I^n を Ideal.pow_le_pow_right で。
    Hint-2: intro して Ideal.pow_le_pow_right を適用。 -/
theorem ramificationSubgroup_antitone (I : Ideal R) (action : G → R →+* R) :
    Antitone (ramificationSubgroup I action) := by
  intro m n hmn σ hσ x
  exact Ideal.pow_le_pow_right hmn (hσ x)

/-- 🔴 Exercise NT1-5d: 恒等自己同型は全レベルに属する。
    id ∈ ramificationSubgroup I action n for all n。
    action 1 = id → id(x) - x = 0 ∈ I^n。

    Hint-1: action of identity is RingHom.id。
    Hint-2: sub_self, Ideal.zero_mem。 -/
theorem id_mem_ramificationSubgroup (I : Ideal R) (action : G → R →+* R)
    [Group G]
    (hId : action 1 = RingHom.id R) (n : ℕ) :
    (1 : G) ∈ ramificationSubgroup I action n := by
  intro x
  simp [hId]

end RingGroupBridge

-- ════════════════════════════════════════════════════════════
-- §Summary. NT1 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  NT1 で構築したこと:

  §NT1-1 **部分群フィルトレーション塔**:
    subgroupFiltrationTower f : StructureTower ℕᵒᵈ G。
    反単調な部分群列から StructureTower を構成。
    idealPowTower と完全に並行する構造。
    各レベルで 1 の帰属、逆元閉性、乗法閉性を確認。

  §NT1-2 **正規鎖と閉包性**:
    subgroupFiltrationClosedTower: ClosedTower subgroupClosure ℕᵒᵈ。
    L4 の subgroupClosure による ClosedTower が自動成立。
    正規部分群列のとき conjugationHom: 共役が塔の自己射を誘導。
    → StructureTower で群論固有の非自明な Hom が出現。

  §NT1-3 **分岐塔の抽象定義**:
    RamificationData: 反単調 + 正規 + 全体群条件。
    ramificationTower: RamificationData → StructureTower ℕᵒᵈ G。
    HasCommutatorBound: [G_i, G_j] ≤ G_{i+j}
      — idealPow_mul_mem の群側の対応物。
      — OrderHom では捉えられない **演算と添字の算術的関係**。

  §NT1-4 **分離条件と脱出**:
    IsSeparatedFiltration f := ⨅ₙ f(n) = ⊥。
    L5 の IsSeparated I と並行。
    escape 定理: σ ≠ 1 → ∃ n, σ ∉ G_n。
    ramificationBreak: 分岐指標 b(σ) = min{n | σ ∉ G_n}。

  §NT1-5 **idealPowTower への橋**:
    TowerPreservingAction: 群作用が塔を保存する条件。
    actionToTowerHom: σ ↦ (idealPowTower の自己射)。
    ramificationSubgroup: 環のイデアル冪から群の分岐部分群を **誘導**。
    → 「環の塔と群の塔が同じ算術を異なる視点で記述する」ことの形式化。

  ──────────────────────────────────────────────
  L5 (idealPowTower) との対比表:

    概念              L5 (環)                    NT1 (群)
    ─────────────────────────────────────────────────────────
    基本構造          idealPowTower I            subgroupFiltrationTower f
    添字              ℕᵒᵈ                        ℕᵒᵈ
    零/単位元帰属     0 ∈ I^n ∀n                 1 ∈ G_n ∀n
    閉性              I^n はイデアル              G_n は部分群
    ClosedTower      idealClosure               subgroupClosure
    乗法互換性        I^m · I^n ⊆ I^{m+n}       [G_i, G_j] ≤ G_{i+j}
    分離条件          ⨅ I^n = ⊥                  ⨅ G_n = ⊥
    脱出定理          x ≠ 0 → ∃n, x ∉ I^n       σ ≠ 1 → ∃n, σ ∉ G_n
    非自明射          環準同型 → Hom              共役 → Hom
    ─────────────────────────────────────────────────────────

  ──────────────────────────────────────────────
  NT2 以降の展望:

    NT2: **Hasse-Arf 定理と reindex**
      分岐フィルトレーションの「上付番号」への変換:
        φ(t) = ∫₀ᵗ [G₀ : G_s]⁻¹ ds
      これは StructureTower の reindex 操作!
      reindex φ (ramificationTower rd) が上付番号分岐塔を与える。
      Hasse-Arf: 上付番号の分岐ジャンプは整数値
        → reindex 後の塔が「整数格子上に集中する」ことの定式化。

    NT3: **局所類体論と Tower Comparison**
      Artin 写像: G^ab ≅ K×/N_{L/K}(L×)
      環側の塔（イデアル冪）と群側の塔（分岐群）を **Artin 写像** で結ぶ。
      2つの異なる StructureTower 間の Hom として定式化。

    NT4: **遠アーベル幾何への接続**（IUT4 対応）
      副有限群のフィルトレーション:
        π₁(X) の開正規部分群列 → StructureTower
      望月の Hodge 劇場: 複数の塔の「リンク」の形式化。
      Θ-リンクと log-リンクは異なる StructureTower 間の射？
  ──────────────────────────────────────────────
-/

end StructureTower

end BourbakiGuide
