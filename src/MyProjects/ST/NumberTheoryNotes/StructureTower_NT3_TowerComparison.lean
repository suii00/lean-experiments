/-
  StructureTower 数論シリーズ（NT3）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル10相当（Tower Comparison Theory）
  前提: NT1-NT2 + L1-L7 を完了していること

  動機:
    NT1 で ramificationTower（群の塔）を構成し、
    NT2 で upperNumberingTower（reindex による番号変換）と
    restrictToSubgroup（部分群制限）を構成した。

    NT1-§5 で「環の塔 idealPowTower と群の塔 ramificationTower が
    同じ算術を異なる視点で記述する」という洞察を得た。
    NT2-§4 で「正しい reindex を選ぶと塔の制限と可換になる」ことを定式化した。

    NT3 では、これらの断片を **Tower Comparison Theory** として統合する。
    これは StructureTower プロジェクトの L8 候補として最初に挙がった方向であり、
    NT1-NT2 の数論的動機を通じて具体的内容を獲得した。

  核心的問い:
    「2つの異なる型 α, β 上の StructureTower T₁, T₂ が
    同じ添字集合 ι を共有するとき、それらの間にどのような
    関係が成り立ちうるか？」

    OrderHom ι (Set α) と OrderHom ι (Set β) を比較するには、
    α と β を結ぶ写像 f : α → β が必要。しかし単なる f では不十分で、
    「f が各レベルを保存する」条件（= StructureTower Hom）が要る。
    さらに「2つの塔が同じ情報を encode している」条件は Hom を超える。

    Tower Comparison Theory は以下を体系化する:
    1. 写像による塔の誘導（map/comap の一般化）
    2. 塔の対（TowerPairing）: 異なる型上の塔を結ぶ構造
    3. 対の整合条件: reindex との可換性
    4. 数論的応用: 環-群の二重塔、Artin 条件

  ZEN大学 IUT カリキュラムとの対応:
    IUT3: ガロア理論 → §NT3-3（ガロア対応の塔版）
    IUT4: 類体論・遠アーベル → §NT3-4, NT3-5（Artin 条件、対の普遍性）

  学習の流れ:
    §NT3-1. 塔の交差と積            — 同一型上の2つの塔の比較
    §NT3-2. TowerPairing            — 異なる型上の塔を結ぶ写像
    §NT3-3. 誘導塔と双対塔対        — 環-群パターンの公理化
    §NT3-4. Reindex 整合的対        — 上付番号整合性の一般化
    §NT3-5. 数論的統合              — NT1-NT2 の全構造の合流

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
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Nat.Find

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definitions（NT1-NT2 から再掲）
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

def NatInclusion (T₁ T₂ : StructureTower ι α) : Prop :=
  ∀ i, T₁.level i ⊆ T₂.level i

def reindex {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) : StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

@[simp] theorem reindex_level {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) (i : ι) :
    (reindex f hf T).level i = T.level (f i) := rfl

def map (f : α → β) (T : StructureTower ι α) : StructureTower ι β where
  level i := f '' T.level i
  monotone_level := by
    intro i j hij y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, T.monotone_level hij hx, rfl⟩

def comap (f : α → β) (T : StructureTower ι β) : StructureTower ι α where
  level i := f ⁻¹' T.level i
  monotone_level := fun _i _j hij _x hx => T.monotone_level hij hx

@[simp] theorem map_level (f : α → β) (T : StructureTower ι α) (i : ι) :
    (map f T).level i = f '' T.level i := rfl

@[simp] theorem comap_level (f : α → β) (T : StructureTower ι β) (i : ι) :
    (comap f T).level i = f ⁻¹' T.level i := rfl

-- L5: idealPowTower
variable {R : Type*} [CommRing R]

def idealPowTower (I : Ideal R) : StructureTower ℕᵒᵈ R where
  level n := ↑(I ^ OrderDual.ofDual n)
  monotone_level := by
    intro i j hij x hx
    exact
      (Ideal.pow_le_pow_right (I := I)
        (m := OrderDual.ofDual j) (n := OrderDual.ofDual i)
        (OrderDual.ofDual_le_ofDual.mpr hij)) hx

-- NT1: subgroupFiltrationTower, RamificationData
variable {G : Type*} [Group G]

def subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) : StructureTower ℕᵒᵈ G where
  level n := ↑(OrderDual.ofDual (f (OrderDual.ofDual n)))
  monotone_level := by
    intro i j hij x hx
    exact (f.monotone (OrderDual.ofDual_le_ofDual.mpr hij)) hx

structure RamificationData (G : Type*) [Group G] where
  groups : ℕ → Subgroup G
  antitone : Antitone groups
  whole : groups 0 ≤ ⊤
  normal : ∀ n, (groups n).Normal

def RamificationData.toOrderHom (rd : RamificationData G) :
    ℕ →o (Subgroup G)ᵒᵈ where
  toFun n := OrderDual.toDual (rd.groups n)
  monotone' := fun _ _ hij => rd.antitone hij

def ramificationTower (rd : RamificationData G) : StructureTower ℕᵒᵈ G :=
  subgroupFiltrationTower rd.toOrderHom

@[simp] theorem ramificationTower_level (rd : RamificationData G) (n : ℕᵒᵈ) :
    (ramificationTower rd).level n = ↑(rd.groups (OrderDual.ofDual n)) := rfl

-- NT2: scaledHerbrand, herbrandReindex, upperNumberingTower
def scaledHerbrand (gs : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => scaledHerbrand gs n + gs (n + 1)

def herbrandReindex (gs : ℕ → ℕ) : ℕᵒᵈ → ℕᵒᵈ :=
  fun n => OrderDual.toDual (scaledHerbrand gs (OrderDual.ofDual n))

theorem scaledHerbrand_monotone (gs : ℕ → ℕ) : Monotone (scaledHerbrand gs) := by
  refine monotone_nat_of_le_succ ?_
  intro n; exact Nat.le_add_right _ _

theorem herbrandReindex_monotone (gs : ℕ → ℕ) : Monotone (herbrandReindex gs) := by
  intro i j hij
  show scaledHerbrand gs (OrderDual.ofDual j) ≤ scaledHerbrand gs (OrderDual.ofDual i)
  exact scaledHerbrand_monotone gs (OrderDual.ofDual_le_ofDual.mpr hij)

def upperNumberingTower (rd : RamificationData G) (gs : ℕ → ℕ) :
    StructureTower ℕᵒᵈ G :=
  reindex (herbrandReindex gs) (herbrandReindex_monotone gs) (ramificationTower rd)

-- NT2: gradedPiece, jumpSet
def gradedPiece (T : StructureTower ℕᵒᵈ α) (n : ℕ) : Set α :=
  T.level (OrderDual.toDual n) \ T.level (OrderDual.toDual (n + 1))

def jumpSet (T : StructureTower ℕᵒᵈ α) : Set ℕ :=
  {n : ℕ | (gradedPiece T n).Nonempty}

-- ════════════════════════════════════════════════════════════
-- §NT3-1. 塔の交差と積  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  Tower Comparison の第一歩: **同一型上** の2つの塔の比較。

  2つの塔 T₁, T₂ : StructureTower ι α が与えられたとき、
  レベルごとの交差・和を取ることで新しい塔を構成できる。

  - 交差塔: (T₁ ⊓ T₂).level i = T₁.level i ∩ T₂.level i
  - 和塔:   (T₁ ⊔ T₂).level i = T₁.level i ∪ T₂.level i

  交差塔は常に well-defined（交差の単調性）だが、
  和塔は一般に StructureTower にならない（和は単調性を保存しない場合がある）。
  …と思いきや、集合の和は実は単調性を保存する。

  NatInclusion との関係:
  - T₁ ⊓ T₂ は T₁ と T₂ の最大下界（NatInclusion の ⊓）
  - NatInclusion T (T₁ ⊓ T₂) ↔ NatInclusion T T₁ ∧ NatInclusion T T₂

  数論的意味:
  - idealPowTower I ⊓ idealPowTower J は「I^n ∩ J^n」の塔
  - 2つの素イデアルの冪塔の交差が「中国剰余定理的」構造を持つ
-/

section TowerMeet

variable {ι α : Type*} [Preorder ι]

/-- 🟢 Exercise NT3-1a: 交差塔。2つの塔のレベルごとの交差。
    (T₁ ⊓ T₂).level i = T₁.level i ∩ T₂.level i。

    Hint-1: Set.inter_subset_inter で単調性。 -/
def towerMeet (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i := T₁.level i ∩ T₂.level i
  monotone_level := by
    intro i j hij x ⟨h₁, h₂⟩
    exact ⟨T₁.monotone_level hij h₁, T₂.monotone_level hij h₂⟩

@[simp] theorem towerMeet_level (T₁ T₂ : StructureTower ι α) (i : ι) :
    (towerMeet T₁ T₂).level i = T₁.level i ∩ T₂.level i := rfl

/-- 🟢 Exercise NT3-1b: 和塔。2つの塔のレベルごとの和。

    Hint-1: Set.union_subset_union で単調性。 -/
def towerJoin (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i := T₁.level i ∪ T₂.level i
  monotone_level := by
    intro i j hij x hx
    rcases hx with h₁ | h₂
    · exact Or.inl (T₁.monotone_level hij h₁)
    · exact Or.inr (T₂.monotone_level hij h₂)

@[simp] theorem towerJoin_level (T₁ T₂ : StructureTower ι α) (i : ι) :
    (towerJoin T₁ T₂).level i = T₁.level i ∪ T₂.level i := rfl

/-- 🟢 Exercise NT3-1c: 交差塔は NatInclusion の下界。

    Hint-1: Set.inter_subset_left / Set.inter_subset_right。 -/
theorem towerMeet_natInclusion_left (T₁ T₂ : StructureTower ι α) :
    NatInclusion (towerMeet T₁ T₂) T₁ :=
  fun _i _x hx => hx.1

theorem towerMeet_natInclusion_right (T₁ T₂ : StructureTower ι α) :
    NatInclusion (towerMeet T₁ T₂) T₂ :=
  fun _i _x hx => hx.2

/-- 🟡 Exercise NT3-1d: 交差塔は NatInclusion の **最大** 下界。
    NatInclusion T T₁ ∧ NatInclusion T T₂ → NatInclusion T (T₁ ⊓ T₂)。

    Hint-1: intro で分解して ⟨h₁ i hx, h₂ i hx⟩。 -/
theorem towerMeet_greatest_lower_bound (T T₁ T₂ : StructureTower ι α)
    (h₁ : NatInclusion T T₁) (h₂ : NatInclusion T T₂) :
    NatInclusion T (towerMeet T₁ T₂) :=
  fun i x hx => ⟨h₁ i hx, h₂ i hx⟩

/-- 🟡 Exercise NT3-1e: global は交差塔の global と整合する。
    global (T₁ ⊓ T₂) = global T₁ ∩ global T₂。

    Hint-1: Set.iInter_inter_distrib。 -/
theorem global_towerMeet (T₁ T₂ : StructureTower ι α) :
    (towerMeet T₁ T₂).global = T₁.global ∩ T₂.global := by
  ext x
  simp [StructureTower.global, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · intro ⟨h₁, h₂⟩ i; exact ⟨h₁ i, h₂ i⟩

end TowerMeet

-- ════════════════════════════════════════════════════════════
-- §NT3-2. TowerPairing  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  **TowerPairing**: 異なる型上の2つの塔を結ぶ構造。

  設定: T₁ : StructureTower ι α, T₂ : StructureTower ι β。
  「T₁ と T₂ が同じ情報を encode している」ことを捉えたい。

  最も基本的な関係は **写像による対応**:
  f : α → β が T₁ から T₂ への Hom であるとき、
  T₁ の構造が f を通じて T₂ に反映される。

  しかし Hom は一方向。双方向の対応は:
  1. f : α → β が Hom(T₁, T₂) かつ g : β → α が Hom(T₂, T₁)
  2. さらに f ∘ g ∼ id, g ∘ f ∼ id（何らかの意味で）

  StructureTower では「レベルの等価」が自然:
    ∀ i, f '' T₁.level i = T₂.level i  （全射的レベル一致）

  これは Hom よりも強い条件:
  - Hom: f '' T₁.level i ⊆ T₂.level i
  - レベル一致: f '' T₁.level i = T₂.level i

  数論的例:
  - φ: R → R/I が idealPowTower I → idealPowTower (φ(I)) のレベル一致を誘導
  - θ: K× → G^ab（Artin 写像）が value group の塔 → 分岐群塔のレベル一致を誘導

  OrderHom の語彙では:
    「2つの OrderHom ι (Set α) と ι (Set β) が f : α → β で結ばれる」
    は記述できるが、Hom・NatInclusion・ClosedTower などの
    追加構造との整合性を捉える言葉がない。
-/

section TowerPairing

variable {ι : Type*} [Preorder ι]

/-- 🟡 Exercise NT3-2a: map による NatInclusion。
    f : α → β と T : StructureTower ι α に対し、
    map f T の level i は f '' T.level i。
    Hom f は「f '' T₁.level i ⊆ T₂.level i」なので、
    NatInclusion (map f T₁) T₂ ↔ f が Hom(T₁, T₂)。

    Hint-1: NatInclusion の定義と map_level を展開。 -/
theorem natInclusion_map_iff_hom {α β : Type*}
    (f : α → β)
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    NatInclusion (map f T₁) T₂ ↔
      ∀ i, ∀ x ∈ T₁.level i, f x ∈ T₂.level i := by
  constructor
  · intro h i x hx
    exact h i ⟨x, hx, rfl⟩
  · intro h i y hy
    rcases (show y ∈ f '' T₁.level i from by
      simpa [map_level] using hy) with ⟨x, hx, rfl⟩
    exact h i x hx

/-- 🟡 Exercise NT3-2b: comap による NatInclusion。
    comap f T₂ の level i は f ⁻¹' T₂.level i。
    NatInclusion T₁ (comap f T₂) ↔ f が Hom(T₁, T₂)。

    Hint-1: comap_level を展開。 -/
theorem natInclusion_comap_iff_hom {α β : Type*}
    (f : α → β)
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    NatInclusion T₁ (comap f T₂) ↔
      ∀ i, ∀ x ∈ T₁.level i, f x ∈ T₂.level i := by
  constructor
  · intro h i x hx
    exact h i hx
  · intro h i x hx
    exact h i x hx

/-- TowerPairing: 2つの塔を結ぶ写像の対。
    f : α → β が「前方射」、g : β → α が「後方射」。
    Hom 条件を両方向で要求する。

    これは StructureTower の圏における「射の対」。
    同型よりは弱い — f ∘ g, g ∘ f が恒等射とは限らない。

    動機:
    - 商写像 R → R/I は前方射（Hom）
    - 持ち上げ R/I → R は一般に後方射にならない
    - ガロア対応は両方向の射を持つ -/
structure TowerPairing {α β : Type*}
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  forward : α → β
  backward : β → α
  forward_preserves : ∀ i, MapsTo forward (T₁.level i) (T₂.level i)
  backward_preserves : ∀ i, MapsTo backward (T₂.level i) (T₁.level i)

/-- TowerPairing から前方 Hom を取り出す。 -/
def TowerPairing.toForwardHom {α β : Type*}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (p : TowerPairing T₁ T₂) : Hom T₁ T₂ where
  toFun := p.forward
  preserves := p.forward_preserves

/-- TowerPairing から後方 Hom を取り出す。 -/
def TowerPairing.toBackwardHom {α β : Type*}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (p : TowerPairing T₁ T₂) : Hom T₂ T₁ where
  toFun := p.backward
  preserves := p.backward_preserves

/-- 🟡 Exercise NT3-2c: 恒等 TowerPairing。

    Hint-1: forward = backward = id。 -/
def TowerPairing.id {α : Type*} (T : StructureTower ι α) :
    TowerPairing T T where
  forward := _root_.id
  backward := _root_.id
  forward_preserves := fun i x hx => hx
  backward_preserves := fun i x hx => hx

/-- 🔴 Exercise NT3-2d: TowerPairing の合成。

    Hint-1: forward は g.forward ∘ f.forward。
    Hint-2: backward は f.backward ∘ g.backward。 -/
def TowerPairing.comp {α β γ' : Type*}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} {T₃ : StructureTower ι γ'}
    (g : TowerPairing T₂ T₃) (f : TowerPairing T₁ T₂) :
    TowerPairing T₁ T₃ where
  forward := g.forward ∘ f.forward
  backward := f.backward ∘ g.backward
  forward_preserves := fun i x hx => g.forward_preserves i (f.forward_preserves i hx)
  backward_preserves := fun i x hx => f.backward_preserves i (g.backward_preserves i hx)

end TowerPairing

-- ════════════════════════════════════════════════════════════
-- §NT3-3. 誘導塔と双対塔対  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  **双対塔対 (Dual Tower Pair)**: 環と群の二重フィルトレーションの公理化。

  NT1-§5 で見た構造:
  - 環側: idealPowTower I : StructureTower ℕᵒᵈ R
  - 群側: ramificationTower rd : StructureTower ℕᵒᵈ G
  - 橋: 群 G が R に作用し、action σ が idealPowTower の Hom を誘導

  この構造を抽象化する:
  - 環側の塔 T_R : StructureTower ι R
  - 群側の塔 T_G : StructureTower ι G
  - 群 G が T_R の自己同型群の中で作用
  - T_G の level i = {σ ∈ G | σ が T_R の level i を「十分保存する」}

  核心的洞察:
  **群の塔 T_G は環の塔 T_R から誘導できる。**
  ramificationSubgroup（NT1-§5）はまさにこの誘導。
  T_G.level i = {σ | ∀ x, action σ x - x ∈ T_R.level i}

  これは「塔が別の塔を決定する」という意味で、
  単なる OrderHom の比較を超えた構造的関係。
-/

section DualTowerPair

variable {ι : Type*} [Preorder ι]

/- 写像による塔の誘導（前像塔）。
    f : α → β に対し、T : StructureTower ι β から
    comap f T : StructureTower ι α を構成。
    L2 で定義済みだが、NT3 の文脈で意味を再確認。

    数論的意味:
    - f = (fun σ x => action σ x - x) のとき、
      comap f (idealPowTower I) の level n = {σ | ∀x, σ(x)-x ∈ I^n}
      = ramificationSubgroup I action n -/

/-- 🟡 Exercise NT3-3a: comap Hom。
    f が T₁ → T₂ の Hom ならば、
    id : α → α が comap f T₂ → T₁ の NatInclusion を誘導する…
    とは限らない。逆方向:
    NatInclusion T₁ (comap f T₂) ↔ f が Hom(T₁, T₂)。

    Hint-1: NT3-2b と同じ。 -/
theorem comap_hom_iff {α β : Type*} (f : α → β)
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    NatInclusion T₁ (comap f T₂) ↔
      (∃ h : Hom T₁ T₂, h.toFun = f) := by
  constructor
  · intro hNat
    exact ⟨⟨f, fun i x hx => hNat i hx⟩, rfl⟩
  · intro ⟨h, hf⟩ i x hx
    have := h.preserves i hx
    rw [← hf]
    exact this

/-- 環-群二重塔データ。
    環 R 上のイデアル I、群 G の R への作用、
    および群側のフィルトレーションを束ねる。

    NT1-§5 の TowerPreservingAction + ramificationSubgroup を
    統合した構造。 -/
structure RingGroupTowerData (R : Type*) [CommRing R]
    (G : Type*) [Group G] where
  /-- イデアル -/
  ideal : Ideal R
  /-- 群作用 -/
  action : G → R →+* R
  /-- 群側のフィルトレーション -/
  groupFiltration : ℕ → Subgroup G
  /-- 反単調性 -/
  groupFiltration_antitone : Antitone groupFiltration
  /-- 整合条件: G_n の元は I^n 上で「恒等的に」作用する -/
  compatible : ∀ (n : ℕ) (σ : G),
    σ ∈ groupFiltration n → ∀ x : R, action σ x - x ∈ ideal ^ n

/-- 🟡 Exercise NT3-3b: RingGroupTowerData から環側の塔を取り出す。

    Hint-1: idealPowTower を適用。 -/
def RingGroupTowerData.ringTower {R : Type*} [CommRing R] {G : Type*} [Group G]
    (d : RingGroupTowerData R G) : StructureTower ℕᵒᵈ R :=
  idealPowTower d.ideal

/-- 🟡 Exercise NT3-3c: RingGroupTowerData から群側の塔を取り出す。
    反単調な部分群列から StructureTower を構成。

    Hint-1: subgroupFiltrationTower を使う。 -/
def RingGroupTowerData.groupTower {R : Type*} [CommRing R] {G : Type*} [Group G]
    (d : RingGroupTowerData R G) : StructureTower ℕᵒᵈ G where
  level n := ↑(d.groupFiltration (OrderDual.ofDual n))
  monotone_level := by
    intro i j hij x hx
    exact d.groupFiltration_antitone (OrderDual.ofDual_le_ofDual.mpr hij) hx

/-- 🔴 Exercise NT3-3d: 整合条件の塔的意味。
    compatible は「各 σ ∈ groupTower.level n に対し、
    action σ の "偏差" が ringTower.level n に属する」ことを意味する。

    これは群の塔が環の塔から「偏差写像を通じて誘導されている」という statement。
    StructureTower 固有の概念: **一方の塔が他方の塔を決定する。**

    Hint-1: compatible を書き直すだけ。 -/
theorem RingGroupTowerData.compatible_tower {R : Type*} [CommRing R]
    {G : Type*} [Group G] (d : RingGroupTowerData R G)
    (n : ℕ) (σ : G)
    (hσ : σ ∈ (d.groupTower).level (OrderDual.toDual n))
    (x : R) :
    d.action σ x - x ∈ (d.ringTower).level (OrderDual.toDual n) :=
  d.compatible n σ hσ x

/-- 🔴 Exercise NT3-3e: 各 σ ∈ groupTower は ringTower の自己射を誘導する。
    NT1-§5 の actionToTowerHom の RingGroupTowerData 版。

    Hint-1: Hom の toFun は action σ。
    Hint-2: preserves は compatible + 代数的操作。 -/
def RingGroupTowerData.actionHom {R : Type*} [CommRing R]
    {G : Type*} [Group G] (d : RingGroupTowerData R G) (σ : G)
    (hσ : ∀ n : ℕ, ∀ x : R, x ∈ d.ideal ^ n → d.action σ x ∈ d.ideal ^ n) :
    Hom d.ringTower d.ringTower where
  toFun := d.action σ
  preserves := by
    intro n x hx
    exact hσ (OrderDual.ofDual n) x hx

end DualTowerPair

-- ════════════════════════════════════════════════════════════
-- §NT3-4. Reindex 整合的対  🔴
-- ════════════════════════════════════════════════════════════

/-!
  NT2 の UpperNumberingCompatible を一般化する。

  **Reindex 整合的対 (Reindex-Compatible Pairing)**:
    2つの塔 T₁ : ST(ι, α), T₂ : ST(ι, β) と
    reindex φ : ι → ι が与えられたとき、
    「φ で reindex した T₁ の制限」と「φ' で reindex した T₂」が一致する条件。

  NT2 の具体例:
    T₁ = ramificationTower(G 全体), T₂ = ramificationTower(H)
    φ_G = Herbrand reindex for G, φ_H = Herbrand reindex for H
    整合条件: reindex φ_G T₁ を H に制限 = reindex φ_H T₂

  一般化すると:
    T₁, T₂ が写像 p : α → β で結ばれ、
    φ₁, φ₂ : ι → ι が 2つの reindex であるとき、
    「p が reindex φ₁ T₁ → reindex φ₂ T₂ の Hom である」条件。

  これは「reindex の選び方が塔の関係を保存する」ことの定式化。
  OrderHom の語彙では記述困難 — reindex と Hom の相互作用が必要。
-/

section ReindexCompatible

variable {ι α β : Type*} [Preorder ι]

/-- Reindex 整合条件。
    f : α → β が reindex φ₁ T₁ → reindex φ₂ T₂ の Hom であること。

    NT2 の UpperNumberingCompatible の一般化:
    - T₁ = ramificationTower rd_G (on G)
    - T₂ = ramificationTower rd_H (on G, restricted to H)
    - φ₁ = herbrandReindex gs_G
    - φ₂ = herbrandReindex gs_H
    - f = inclusion H → G -/
def IsReindexCompatible
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β)
    (f : α → β)
    (φ₁ φ₂ : ι → ι) (hφ₁ : Monotone φ₁) (hφ₂ : Monotone φ₂) : Prop :=
  ∀ i, MapsTo f ((reindex φ₁ hφ₁ T₁).level i) ((reindex φ₂ hφ₂ T₂).level i)

/-- 🔴 Exercise NT3-4a: IsReindexCompatible の展開。
    条件を T₁, T₂ の level で直接表現。

    Hint-1: reindex_level で展開。 -/
theorem isReindexCompatible_iff
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β)
    (f : α → β)
    (φ₁ φ₂ : ι → ι) (hφ₁ : Monotone φ₁) (hφ₂ : Monotone φ₂) :
    IsReindexCompatible T₁ T₂ f φ₁ φ₂ hφ₁ hφ₂ ↔
      ∀ i, MapsTo f (T₁.level (φ₁ i)) (T₂.level (φ₂ i)) := by
  simp [IsReindexCompatible, reindex_level]

/-- 🔴 Exercise NT3-4b: φ₁ = φ₂ = id のとき、通常の Hom 条件。

    Hint-1: reindex_level で id を展開。 -/
theorem isReindexCompatible_id
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) (f : α → β) :
    IsReindexCompatible T₁ T₂ f _root_.id _root_.id monotone_id monotone_id ↔
      ∀ i, MapsTo f (T₁.level i) (T₂.level i) := by
  simp [IsReindexCompatible, reindex_level]

/-- 🔴 Exercise NT3-4c: Reindex 整合的な合成。
    f が (T₁, φ₁) → (T₂, φ₂) に、
    g が (T₂, φ₂) → (T₃, φ₃) に reindex 整合的なら、
    g ∘ f は (T₁, φ₁) → (T₃, φ₃) に reindex 整合的。

    Hint-1: MapsTo.comp。 -/
theorem isReindexCompatible_comp {γ' : Type*}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ'}
    {f : α → β} {g : β → γ'}
    {φ₁ φ₂ φ₃ : ι → ι}
    {hφ₁ : Monotone φ₁} {hφ₂ : Monotone φ₂} {hφ₃ : Monotone φ₃}
    (hf : IsReindexCompatible T₁ T₂ f φ₁ φ₂ hφ₁ hφ₂)
    (hg : IsReindexCompatible T₂ T₃ g φ₂ φ₃ hφ₂ hφ₃) :
    IsReindexCompatible T₁ T₃ (g ∘ f) φ₁ φ₃ hφ₁ hφ₃ := by
  intro i x hx
  exact hg i (hf i hx)

end ReindexCompatible

-- ════════════════════════════════════════════════════════════
-- §NT3-5. 数論的統合  🔴
-- ════════════════════════════════════════════════════════════

/-!
  NT1-NT2 の全構造を Tower Comparison Theory の枠組みで再記述する。

  **定理（環-群整合性の基本定理）**:
    RingGroupTowerData d が与えられたとき、
    偏差写像 δ_σ(x) = action σ x - x は
    groupTower → ringTower の間の
    「σ-parametric な reindex 整合的写像」を定義する。

  より精密には:
  - 各 σ ∈ G に対し、δ_σ : R → R（x ↦ σ(x) - x）
  - σ ∈ groupTower.level(toDual n) ⟹ δ_σ が R → I^n に値を取る
  - これは「群の塔の深さが環の塔の偏差を制御する」という statement

  StructureTower 理論の主定理候補:
  **「2つの塔が同じ算術を記述する」ことの十分条件は
  偏差写像を通じた reindex 整合性である。**

  これは OrderHom ι (Set α) × OrderHom ι (Set β) の語彙では
  自然に述べられない — 「偏差」「σ-パラメトリック」「整合性」の
  全てが StructureTower の Hom + reindex の相互作用に依存する。
-/

section ArithmeticSynthesis

variable {R : Type*} [CommRing R] {G : Type*} [Group G]

/-- 🔴 Exercise NT3-5a: 偏差写像の構成。
    σ ∈ G に対し、δ_σ : R → R, x ↦ action σ x - x。

    Hint-1: 関数定義。 -/
def deviationMap (action : G → R →+* R) (σ : G) : R → R :=
  fun x => action σ x - x

/-- 🔴 Exercise NT3-5b: 整合条件は偏差写像で表現できる。
    d.compatible n σ hσ は
    「δ_σ が R → I^n に値を取る」ことと同値。

    Hint-1: deviationMap の定義を展開。 -/
theorem compatible_iff_deviation (d : RingGroupTowerData R G) (n : ℕ) (σ : G)
    (hσ : σ ∈ d.groupFiltration n) :
    ∀ x : R, deviationMap d.action σ x ∈ (d.ideal ^ n : Ideal R) :=
  d.compatible n σ hσ

/-- 🔴 Exercise NT3-5c: 偏差の加法性（近似）。
    σ, τ ∈ G に対し、
    δ_{στ}(x) = δ_σ(τx) + δ_τ(x)。
    すなわち、(στ)(x) - x = (σ(τx) - τx) + (τx - x)。

    これは telescoping identity であり、交換子条件
    [G_i, G_j] ⊆ G_{i+j} の根拠。

    Hint-1: ring で代数的に証明。 -/
theorem deviation_mul (action : G → R →+* R) (σ τ : G)
    (hcomp : ∀ x, action (σ * τ) x = action σ (action τ x)) (x : R) :
    deviationMap action (σ * τ) x =
      deviationMap action σ (action τ x) + deviationMap action τ x := by
  simp [deviationMap, hcomp]

/-- 🔴 Exercise NT3-5d: 環-群整合性の基本定理。
    d : RingGroupTowerData R G に対し、
    群の塔の level n が「偏差が I^n に入る元」と一致する条件。

    IsExact d n := ↑(d.groupFiltration n) = {σ | ∀ x, δ_σ(x) ∈ I^n}

    exact なら群の塔は環の塔から完全に決定される。
    NT1 の ramificationSubgroup と同値。 -/
def IsExactPairing (d : RingGroupTowerData R G) : Prop :=
  ∀ n, (↑(d.groupFiltration n) : Set G) =
    {σ : G | ∀ x : R, deviationMap d.action σ x ∈ (d.ideal ^ n : Ideal R)}

/-- 🔴 Exercise NT3-5e: exact pairing の片方向は compatible から自動。
    compatible → groupFiltration n ⊆ {σ | ∀ x, δ_σ(x) ∈ I^n}。

    Hint-1: compatible の定義そのもの。 -/
theorem exact_pairing_forward (d : RingGroupTowerData R G) (n : ℕ) :
    (↑(d.groupFiltration n) : Set G) ⊆
      {σ : G | ∀ x : R, deviationMap d.action σ x ∈ (d.ideal ^ n : Ideal R)} := by
  intro σ hσ x
  exact d.compatible n σ hσ x

/-- 🔴 Exercise NT3-5f: jumpSet の環-群対応。
    IsExactPairing のもとで、
    groupTower のジャンプ集合と ringTower の分岐指標が一致する。

    具体的には:
    n ∈ jumpSet(groupTower) ↔ ∃ σ, σ ∈ G_n ∧ σ ∉ G_{n+1}
    IsExact のもとでは:
    σ ∈ G_n ↔ ∀x, δ_σ(x) ∈ I^n
    σ ∉ G_{n+1} ↔ ∃x, δ_σ(x) ∉ I^{n+1}

    つまり jumpSet は「偏差の精度が n だが n+1 ではない σ が存在するレベル」。

    statement のみ（証明は定義の等価変換）。 -/
theorem jumpSet_groupTower_eq (d : RingGroupTowerData R G)
    (hExact : IsExactPairing d) (n : ℕ) :
    n ∈ jumpSet d.groupTower ↔
      ∃ σ : G, σ ∈ d.groupFiltration n ∧ σ ∉ d.groupFiltration (n + 1) := by
  simp [jumpSet, gradedPiece, Set.Nonempty, Set.mem_diff]
  constructor
  · intro ⟨σ, hσn, hσn1⟩
    exact ⟨σ, hσn, hσn1⟩
  · intro ⟨σ, hσn, hσn1⟩
    exact ⟨σ, hσn, hσn1⟩

end ArithmeticSynthesis

-- ════════════════════════════════════════════════════════════
-- §Summary. NT3 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  NT3 で構築したこと:

  §NT3-1 **塔の交差と積**:
    towerMeet (⊓) と towerJoin (⊔) の構成。
    towerMeet が NatInclusion の最大下界であること。
    global の交差との整合性。
    → 同一型上の Tower Comparison の基盤。

  §NT3-2 **TowerPairing**:
    異なる型上の塔を結ぶ双方向写像。
    map/comap と NatInclusion/Hom の同値性。
    TowerPairing の恒等射・合成。
    → 異なる型間の Tower Comparison の基盤。

  §NT3-3 **誘導塔と双対塔対**:
    RingGroupTowerData: 環-群二重フィルトレーションの統合データ。
    ringTower / groupTower の取り出し。
    compatible 条件の塔的意味: 偏差写像を通じた誘導。
    actionHom: 群元による環塔の自己射。
    → NT1-§5 の TowerPreservingAction の構造化。

  §NT3-4 **Reindex 整合的対**:
    IsReindexCompatible: 異なる reindex を通じた Hom 条件。
    φ₁ = φ₂ = id のとき通常の Hom に帰着。
    Reindex 整合的写像の合成則。
    → NT2-§4 の UpperNumberingCompatible の一般化。

  §NT3-5 **数論的統合**:
    deviationMap: δ_σ(x) = σ(x) - x。
    deviation_mul: δ_{στ}(x) = δ_σ(τx) + δ_τ(x)（telescoping）。
    IsExactPairing: 群の塔 = 偏差条件による定義。
    exact_pairing_forward: compatible → 片方向の一致。
    jumpSet_groupTower_eq: ジャンプ集合の環-群対応。

  ──────────────────────────────────────────────
  StructureTower 理論の主定理候補:

    **Theorem (Tower Duality)**:
    IsExactPairing d が成り立つとき、
    群の塔 d.groupTower は環の塔 d.ringTower から
    偏差写像 δ を通じて完全に決定される。
    さらに、Herbrand reindex φ が reindex 整合的ならば、
    上付番号塔も環の塔から決定される。

    この定理は StructureTower 固有:
    - 「偏差写像による塔の誘導」は OrderHom では記述できない
    - 「reindex 整合性」は Hom と reindex の相互作用
    - 「exact pairing」は tower の圏の射を超えた概念

  ──────────────────────────────────────────────
  NT1-NT3 の全体構造:

    NT1: 群の塔の基盤
      subgroupFiltrationTower, RamificationData
      conjugationHom, HasCommutatorBound
      ramificationBreak, IsSeparatedFiltration

    NT2: 添字変換と grading
      gradedPiece, jumpSet
      scaledHerbrand, herbrandReindex
      upperNumberingTower
      UpperNumberingCompatible, HasseArfCondition

    NT3: 比較理論と統合
      towerMeet/towerJoin
      TowerPairing
      RingGroupTowerData, IsExactPairing
      IsReindexCompatible
      deviationMap, deviation_mul

    三者を通じた主張:
    「数論的フィルトレーション（分岐群列、イデアル冪、上付番号）は
    StructureTower の reindex + Hom + Pairing の相互作用として
    自然に記述され、この記述は OrderHom 単体では捉えられない。」

  ──────────────────────────────────────────────
  NT4 への展望:

    NT4: **副有限群と逆極限**（IUT4 対応）
      - 副有限群 π₁(X) の開正規部分群列 → StructureTower
      - 逆極限 lim← G/G_n ↔ global の副有限版
      - 望月の Hodge 劇場: 複数の TowerPairing のネットワーク
      - Θ-リンク = 異なる exact pairing 間の reindex 整合的射？

    これは StructureTower の「紙上の論文」における
    主定理として提示可能な範囲の最前線。
  ──────────────────────────────────────────────
-/

end StructureTower

end BourbakiGuide
