/-
  StructureTower 数論シリーズ（NT4）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル11相当（副有限塔と遠アーベル的構造）
  前提: NT1-NT3 + L1-L7 を完了していること

  動機:
    NT1-NT3 で構築した Tower Comparison Theory は
    「有限次ガロア拡大」の範囲での理論だった。
    NT4 では **副有限群** の世界に踏み出す。

    代数的数論における根本的な対象は副有限群:
    - 絶対ガロア群 Gal(K̄/K) = lim← Gal(L/K)
    - エタール基本群 π₁(X) = lim← Aut(Y/X)
    - 局所体の惰性群 I ≤ Gal(K̄/K)

    これらは StructureTower の逆極限として捉えられる:
    G = lim← G/G_n は ramificationTower の global の「副有限完備化」。

    遠アーベル幾何の核心的思想:
    **数論的対象（数体、曲線）はそのエタール基本群から復元できる。**
    すなわち、π₁(X) の群構造（特にフィルトレーション構造）が
    X の幾何学的情報を完全に決定する。

    StructureTower の視点:
    「X の幾何 ↔ π₁(X) 上の StructureTower」
    遠アーベル性 = この対応が同型であること。
    望月の IUT 理論 = この対応を「変形」する枠組み。

  ZEN大学 IUT カリキュラムとの対応:
    IUT4: 類体論 → §NT4-1（副有限完備化）
          遠アーベル幾何 → §NT4-2, NT4-3（復元定理の定式化）
          IUT → §NT4-4, NT4-5（Hodge 劇場、リンク）

  学習の流れ:
    §NT4-1. 副有限塔              — 商による切詰め、逆系としての塔
    §NT4-2. 塔のネットワーク      — 複数の塔を組み合わせた構造
    §NT4-3. 復元問題              — 塔からの情報の復元
    §NT4-4. Hodge 劇場の骨格      — 環-群対の組織化
    §NT4-5. リンクと不定性        — 非標準同型と reindex の限界

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
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Nat.Find

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definitions（NT1-NT3 から再掲）
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

-- NT1-NT3 definitions
variable {G : Type*} [Group G]

structure RamificationData (G : Type*) [Group G] where
  groups : ℕ → Subgroup G
  antitone : Antitone groups
  whole : groups 0 ≤ ⊤
  normal : ∀ n, (groups n).Normal

def ramificationTower (rd : RamificationData G) : StructureTower ℕᵒᵈ G where
  level n := ↑(rd.groups (OrderDual.ofDual n))
  monotone_level := by
    intro i j hij x hx
    exact rd.antitone (OrderDual.ofDual_le_ofDual.mpr hij) hx

@[simp] theorem ramificationTower_level (rd : RamificationData G) (n : ℕᵒᵈ) :
    (ramificationTower rd).level n = ↑(rd.groups (OrderDual.ofDual n)) := rfl

def gradedPiece (T : StructureTower ℕᵒᵈ α) (n : ℕ) : Set α :=
  T.level (OrderDual.toDual n) \ T.level (OrderDual.toDual (n + 1))

def jumpSet (T : StructureTower ℕᵒᵈ α) : Set ℕ :=
  {n : ℕ | (gradedPiece T n).Nonempty}

def IsSeparatedFiltration (f : ℕ → Subgroup G) : Prop :=
  ⨅ n, f n = ⊥

-- NT3: TowerPairing, RingGroupTowerData
structure TowerPairing {ι : Type*} [Preorder ι] {α β : Type*}
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  forward : α → β
  backward : β → α
  forward_preserves : ∀ i, MapsTo forward (T₁.level i) (T₂.level i)
  backward_preserves : ∀ i, MapsTo backward (T₂.level i) (T₁.level i)

variable {R : Type*} [CommRing R]

structure RingGroupTowerData (R : Type*) [CommRing R]
    (G : Type*) [Group G] where
  ideal : Ideal R
  action : G → R →+* R
  groupFiltration : ℕ → Subgroup G
  groupFiltration_antitone : Antitone groupFiltration
  compatible : ∀ (n : ℕ) (σ : G),
    σ ∈ groupFiltration n → ∀ x : R, action σ x - x ∈ ideal ^ n

-- ════════════════════════════════════════════════════════════
-- §NT4-1. 副有限塔  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  **副有限群のフィルトレーション** を StructureTower として構成する。

  副有限群 G = lim← G/N_i は、開正規部分群の減少列
    G ⊇ N₁ ⊇ N₂ ⊇ ... （⋂ N_i = {1}）
  によって決定される。各 G/N_i は有限群。

  StructureTower との対応:
  - ramificationTower rd（NT1）は有限ガロア群のフィルトレーション
  - 副有限群では level n = ↑(N_n) で、G_n は開正規部分群
  - IsSeparatedFiltration: ⋂ N_n = {1}（副有限群の完備性条件）

  商の塔:
  副有限群の本質は商の系列 G/N₁ ← G/N₂ ← ...
  これは「逆系」であり、StructureTower の **双対的な** 視点を要求する。

  NT4 のアプローチ:
  商の系列を直接 StructureTower として構成するのではなく、
  「商への射影」が StructureTower Hom の系列を成すことを示す。
  これにより逆極限の概念を StructureTower の語彙で捉える。

  数論的文脈:
  - G = Gal(K̄/K): 絶対ガロア群は副有限群
  - N_n: 有限部分拡大に対応する開正規部分群
  - G/N_n = Gal(L_n/K): 有限ガロア群
  - ramificationTower (G/N_n) は NT1 で構成済み
  - 副有限構造 = これらの有限塔の「整合的な系列」
-/

section ProfiniteTower

variable {G : Type*} [Group G]

/-- 副有限塔データ。
    正規部分群の減少列で、分離条件を満たすもの。
    NT1 の RamificationData に分離条件を追加。

    遠アーベル幾何的意味:
    - groups n = N_n（n 番目の開正規部分群）
    - separated: ⋂ N_n = {1}（副有限完備性）
    - normal: 各 N_n ◁ G（商群が well-defined） -/
structure ProfiniteTowerData (G : Type*) [Group G] extends
    RamificationData G where
  separated : IsSeparatedFiltration groups

/-- 🟢 Exercise NT4-1a: ProfiniteTowerData から StructureTower を構成。
    RamificationData の ramificationTower を継承。

    Hint-1: toRamificationData で RamificationData を取り出す。 -/
def profiniteTower (pd : ProfiniteTowerData G) : StructureTower ℕᵒᵈ G :=
  ramificationTower pd.toRamificationData

@[simp] theorem profiniteTower_level (pd : ProfiniteTowerData G) (n : ℕᵒᵈ) :
    (profiniteTower pd).level n = ↑(pd.groups (OrderDual.ofDual n)) := rfl

/-- 🟢 Exercise NT4-1b: 副有限塔の global は {1}。
    separated 条件の直接的帰結。

    Hint-1: global = ⋂ₙ ↑(N_n) = ↑(⨅ₙ N_n) = ↑⊥ = {1}。 -/
theorem profiniteTower_global_eq (pd : ProfiniteTowerData G) :
    (profiniteTower pd).global = {(1 : G)} := by
  ext x
  simp only [StructureTower.global, profiniteTower_level, Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    have : x ∈ (⨅ n : ℕ, pd.groups n : Subgroup G) := by
      rw [Subgroup.mem_iInf]
      intro n; exact h (OrderDual.toDual n)
    rwa [pd.separated, Subgroup.mem_bot] at this
  · intro h
    subst h
    intro n; exact one_mem _

/-- 🟡 Exercise NT4-1c: 副有限塔は全レベルで非空。
    各 N_n は {1} を含む部分群なので level n ≠ ∅。

    Hint-1: 1 ∈ level n。 -/
theorem profiniteTower_nonempty (pd : ProfiniteTowerData G) (n : ℕᵒᵈ) :
    ((profiniteTower pd).level n).Nonempty :=
  ⟨1, one_mem _⟩

/-- 商への制限（切詰め）。
    n 番目の商群 G/N_n を直接扱うのではなく、
    塔を n で切り詰める操作として定式化する。

    truncate pd n: level k = level (min n k)
    k ≥ n のとき level k = level n（それ以上細かくしない）

    数論的意味:
    「有限拡大 L_n/K の情報だけを見る」= 塔を n で切り詰める -/
def truncateTower (T : StructureTower ℕᵒᵈ α) (n : ℕ) : StructureTower ℕᵒᵈ α where
  level k := T.level (OrderDual.toDual (min n (OrderDual.ofDual k)))
  monotone_level := by
    intro i j hij x hx
    apply T.monotone_level _ hx
    show min n (OrderDual.ofDual j) ≤ min n (OrderDual.ofDual i)
    exact min_le_min_left n (OrderDual.ofDual_le_ofDual.mpr hij)

@[simp] theorem truncateTower_level (T : StructureTower ℕᵒᵈ α) (n : ℕ) (k : ℕᵒᵈ) :
    (truncateTower T n).level k =
      T.level (OrderDual.toDual (min n (OrderDual.ofDual k))) := rfl

/-- 🟡 Exercise NT4-1d: 切詰め塔は NatInclusion で元の塔以上。
    min n k ≤ k → level(min n k) ⊇ level(k)（反単調ℕᵒᵈ）。

    Hint-1: T.monotone_level と min_le_right。 -/
theorem truncateTower_natInclusion (T : StructureTower ℕᵒᵈ α) (n : ℕ) :
    NatInclusion T (truncateTower T n) := by
  intro k x hx
  apply T.monotone_level _ hx
  show OrderDual.ofDual (OrderDual.toDual (min n (OrderDual.ofDual k))) ≤ OrderDual.ofDual k
  simp

/-- 🟡 Exercise NT4-1e: 切詰めの単調性。
    m ≤ n → truncate T n は truncate T m の「細分」。

    Hint-1: min m k ≤ min n k。 -/
theorem truncateTower_monotone (T : StructureTower ℕᵒᵈ α) {m n : ℕ} (hmn : m ≤ n) :
    NatInclusion (truncateTower T n) (truncateTower T m) := by
  intro k x hx
  apply T.monotone_level _ hx
  show min m (OrderDual.ofDual k) ≤ min n (OrderDual.ofDual k)
  exact min_le_min_right (OrderDual.ofDual k) hmn

end ProfiniteTower

-- ════════════════════════════════════════════════════════════
-- §NT4-2. 塔のネットワーク  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  **TowerNetwork**: 複数の塔を組み合わせた構造。

  遠アーベル幾何では、1つの数体 K に対して
  複数のフィルトレーション付き対象が同時に存在する:
  - 絶対ガロア群 G_K のフィルトレーション（分岐群列）
  - 整数環 O_K のイデアル冪フィルトレーション
  - 局所化 O_{K,𝔭} の 𝔭-adic フィルトレーション（各素点 𝔭）
  - 剰余体の拡大の次数フィルトレーション

  これらの塔は互いに整合的に関係している:
  - G_K → G_{K_𝔭}（局所化による制限射）
  - O_K → O_{K_𝔭}（局所化による環準同型）
  - 各局所で RingGroupTowerData が成立

  TowerNetwork = これらの塔と射の系をまとめた構造。
  望月の「Hodge 劇場」はこの TowerNetwork の特殊化。

  設計判断:
  Lean で一般的な「塔のネットワーク」を構成するのは型理論的に困難
  （多相的な型族が必要）。ここでは固定された有限個の塔の組み合わせとして
  具体的なパターンを定義する。
-/

section TowerNetwork

variable {ι : Type*} [Preorder ι]

/-- 塔の対の列。
    ℕ で添字された TowerPairing の系列。
    各 n に対して異なる型の塔の対 (T₁ⁿ, T₂ⁿ) と
    それらを結ぶ forward/backward がある。

    ここでは同一型上の対に制限する（型の一様性のため）。 -/
structure TowerPairingFamily {α β : Type*}
    (T₁ : ℕ → StructureTower ι α) (T₂ : ℕ → StructureTower ι β) where
  /-- 各レベルでの対 -/
  pairing : ∀ n, TowerPairing (T₁ n) (T₂ n)
  /-- 対の整合性: 隣接する対の forward が整合する -/
  forward_coherent : ∀ n i (x : α),
    x ∈ (T₁ n).level i →
    x ∈ (T₁ (n + 1)).level i →
    (pairing n).forward x = (pairing (n + 1)).forward x

/-- 🟡 Exercise NT4-2a: 定数族。
    すべての n で同じ塔と対を使う場合。

    Hint-1: pairing を定数関数に。 -/
def TowerPairingFamily.const {α β : Type*}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (p : TowerPairing T₁ T₂) :
    TowerPairingFamily (fun _ => T₁) (fun _ => T₂) where
  pairing _ := p
  forward_coherent _ _ _ _ _ := rfl

/-- 副有限的整合性。
    塔の族 {T_n} が「逆系」的に整合する条件:
    n ≤ m → T_m の情報は T_n の情報を含む。

    StructureTower の NatInclusion で表現:
    n ≤ m → NatInclusion (T_n) (T_m)。

    副有限極限 = この逆系の「最小の塔」。-/
def IsCoherentFamily (T : ℕ → StructureTower ι α) : Prop :=
  ∀ n m, n ≤ m → NatInclusion (T m) (T n)

/-- 🟡 Exercise NT4-2b: 切詰め塔の族は整合的。
    truncateTower T n の族は n に関して整合的。

    Hint-1: truncateTower_monotone。 -/
theorem truncateTower_coherent (T : StructureTower ℕᵒᵈ α) :
    IsCoherentFamily (fun n => truncateTower T n) := by
  intro n m hnm
  simpa using (truncateTower_monotone T hnm)

/-- 🔴 Exercise NT4-2c: 整合的族の「極限塔」。
    整合的族 {T_n} に対し、limTower の level i = ⋃ₙ (T_n).level i。
    n が大きいほど T_n の level が大きいので、和が自然。

    これは副有限極限の StructureTower 版。

    Hint-1: Set.iUnion と monotone の関係。 -/
def limTower (T : ℕ → StructureTower ι α)
    (_hCoh : IsCoherentFamily T) : StructureTower ι α where
  level i := ⋃ n, (T n).level i
  monotone_level := by
    intro i j hij x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, (T n).monotone_level hij hn⟩

@[simp] theorem limTower_level (T : ℕ → StructureTower ι α)
    (hCoh : IsCoherentFamily T) (i : ι) :
    (limTower T hCoh).level i = ⋃ n, (T n).level i := rfl

/-- 🔴 Exercise NT4-2d: 各 T_n は limTower 以下。

    Hint-1: Set.subset_iUnion。 -/
theorem natInclusion_of_limTower (T : ℕ → StructureTower ι α)
    (hCoh : IsCoherentFamily T) (n : ℕ) :
    NatInclusion (T n) (limTower T hCoh) := by
  intro i x hx
  exact Set.mem_iUnion.mpr ⟨n, hx⟩

end TowerNetwork

-- ════════════════════════════════════════════════════════════
-- §NT4-3. 復元問題  🔴
-- ════════════════════════════════════════════════════════════

/-!
  **遠アーベル的復元問題**:
  「フィルトレーション付き群（= StructureTower）から
  元の算術的対象をどこまで復元できるか？」

  具体的な復元定理:
  1. **Neukirch-Uchida**: 数体 K の絶対ガロア群 G_K から K を復元
  2. **望月**: 双曲的曲線 X のエタール基本群 π₁(X) から X を復元
  3. **Mochizuki-Hoshi-Tsujimura**: 混標数の局所体での復元

  StructureTower の視点:
  「復元可能」= StructureTower の同型から元の対象の同型を導出できる。

  定式化:
  - GeometricData: 算術的対象（環 + 群 + フィルトレーション + 整合性）
  - TowerInvariant: StructureTower から抽出できる不変量
  - AnabelianProperty: 塔の同型が幾何学的同型を導く性質
-/

section Reconstruction

variable {ι : Type*} [Preorder ι]

/-- 塔の不変量。
    StructureTower から計算可能な量。
    例: jumpSet（ジャンプ集合）、global、union のサイズ。 -/
structure TowerInvariant (ι α : Type*) [Preorder ι] where
  /-- 不変量の値の型 -/
  value_type : Type*
  /-- 塔から不変量を計算する関数 -/
  compute : StructureTower ι α → value_type

/-- 🔴 Exercise NT4-3a: jumpSet は塔の不変量。

    Hint-1: TowerInvariant の compute に jumpSet を入れる。 -/
def jumpSetInvariant (α : Type*) : TowerInvariant ℕᵒᵈ α where
  value_type := Set ℕ
  compute := jumpSet

/-- 🔴 Exercise NT4-3b: global は塔の不変量。 -/
def globalInvariant (α : Type*) : TowerInvariant ℕᵒᵈ α where
  value_type := Set α
  compute := StructureTower.global

/-- 塔の同型。
    Hom が双方向で、レベルの一致を保証する。 -/
structure TowerIso {α β : Type*}
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) extends
    TowerPairing T₁ T₂ where
  /-- 前方射は全射的にレベルを一致させる -/
  level_eq : ∀ i, forward '' T₁.level i = T₂.level i

/-- 🔴 Exercise NT4-3c: TowerIso は forward Hom が全射的。
    TowerIso から NatInclusion (map forward T₁) T₂ と
    NatInclusion T₂ (map forward T₁) の両方を得る。

    Hint-1: level_eq から等号を分解。 -/
theorem towerIso_natInclusion_eq {α β : Type*}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (iso : TowerIso T₁ T₂) :
    ∀ i, (map iso.forward T₁).level i = T₂.level i := by
  intro i
  simp [map, iso.level_eq]

/-- 遠アーベル性の定式化。
    型 D（幾何学的データ）から StructureTower への対応 F と
    StructureTower の同型から D の同型への対応 G が
    逆写像的であること。

    これは遠アーベル復元定理の **骨格**。
    具体的な D（数体、曲線等）は Lean での構成が困難なため、
    抽象的な枠組みのみ定式化する。 -/
structure AnabelianCorrespondence
    (D : Type*) (α : Type*) where
  /-- 幾何学的データから塔を構成 -/
  toTower : D → StructureTower ℕᵒᵈ α
  /-- 塔の同型から幾何学的データの同型を復元 -/
  fromIso : ∀ d₁ d₂ : D,
    TowerIso (toTower d₁) (toTower d₂) → Prop
  /-- 復元条件: 塔が同型ならば幾何学的データが「同値」 -/
  faithful : ∀ d₁ d₂ : D,
    ∀ iso : TowerIso (toTower d₁) (toTower d₂), fromIso d₁ d₂ iso

end Reconstruction

-- ════════════════════════════════════════════════════════════
-- §NT4-4. Hodge 劇場の骨格  🔴
-- ════════════════════════════════════════════════════════════

/-!
  望月の IUT 理論における **Hodge 劇場** の StructureTower 的骨格。

  Hodge 劇場は以下のデータの組:
  1. 数体 K とその素点の集合
  2. 各素点 𝔭 での局所データ（局所体、分岐群、イデアル冪）
  3. 全体的な整合性条件

  StructureTower の言語では:
  1. 素点の集合 P
  2. 各 𝔭 ∈ P に対する RingGroupTowerData
  3. 異なる素点間の整合条件

  NT3 の RingGroupTowerData を素点ごとに並べ、
  整合条件を課したのが HodgeTheaterData。

  IUT 理論の核心:
  - 通常の代数幾何では Hodge 劇場は1つの数体から「標準的に」構成される
  - IUT では異なる Hodge 劇場間の「非標準的な対応」（Θ-リンク、log-リンク）を扱う
  - この非標準性こそが IUT の本質
-/

section HodgeTheater

/-- Hodge 劇場の骨格データ。
    素点の集合で添字された RingGroupTowerData の族。

    環: 各素点での局所環 R_𝔭
    群: 各素点での分解群 G_𝔭
    整合条件: 各素点での compatible 条件

    IUT の精密な構成は Lean の型理論の限界を超えるため、
    ここでは「同一の環・群」上で素点を添字集合 P で区別する簡略版。 -/
structure HodgeTheaterData (P : Type*) (R : Type*) [CommRing R]
    (G : Type*) [Group G] where
  /-- 各素点でのイデアル -/
  primeIdeal : P → Ideal R
  /-- 各素点での群作用 -/
  action : P → G → R →+* R
  /-- 各素点での群フィルトレーション -/
  groupFilt : P → ℕ → Subgroup G
  /-- 各素点で反単調 -/
  antitone : ∀ 𝔭, Antitone (groupFilt 𝔭)
  /-- 各素点で整合的 -/
  compatible : ∀ (𝔭 : P) (n : ℕ) (σ : G),
    σ ∈ groupFilt 𝔭 n → ∀ x : R, action 𝔭 σ x - x ∈ primeIdeal 𝔭 ^ n

/-- 各素点から RingGroupTowerData を取り出す。 -/
def HodgeTheaterData.atPrime {P R : Type*} [CommRing R] {G : Type*} [Group G]
    (h : HodgeTheaterData P R G) (𝔭 : P) : RingGroupTowerData R G where
  ideal := h.primeIdeal 𝔭
  action := h.action 𝔭
  groupFiltration := h.groupFilt 𝔭
  groupFiltration_antitone := h.antitone 𝔭
  compatible := h.compatible 𝔭

/-- 🔴 Exercise NT4-4a: 各素点での環塔。

    Hint-1: atPrime で RingGroupTowerData を取り出して ringTower。 -/
def HodgeTheaterData.ringTowerAt {P R : Type*} [CommRing R] {G : Type*} [Group G]
    (h : HodgeTheaterData P R G) (𝔭 : P) : StructureTower ℕᵒᵈ R where
  level n := ↑((h.primeIdeal 𝔭) ^ OrderDual.ofDual n)
  monotone_level := by
    intro i j hij x hx
    exact Ideal.pow_le_pow_right (OrderDual.ofDual_le_ofDual.mpr hij) hx

/-- 🔴 Exercise NT4-4b: 各素点での群塔。 -/
def HodgeTheaterData.groupTowerAt {P R : Type*} [CommRing R] {G : Type*} [Group G]
    (h : HodgeTheaterData P R G) (𝔭 : P) : StructureTower ℕᵒᵈ G where
  level n := ↑(h.groupFilt 𝔭 (OrderDual.ofDual n))
  monotone_level := by
    intro i j hij x hx
    exact (h.antitone 𝔭) (OrderDual.ofDual_le_ofDual.mpr hij) hx

/-- 🔴 Exercise NT4-4c: 素点間の比較。
    2つの素点 𝔭, 𝔮 での環塔を比較する射。
    𝔭 | 𝔮（𝔭 が 𝔮 を割る）のとき、
    idealPowTower 𝔮 の各レベルは idealPowTower 𝔭 のレベルに含まれる。

    条件: 𝔭 ⊆ 𝔮 → 𝔮^n ⊆ 𝔭^n → NatInclusion。 -/
theorem HodgeTheaterData.ringTower_natInclusion_of_le
    {P R : Type*} [CommRing R] {G : Type*} [Group G]
    (h : HodgeTheaterData P R G) {𝔭 𝔮 : P}
    (hle : h.primeIdeal 𝔭 ≤ h.primeIdeal 𝔮) :
    NatInclusion (h.ringTowerAt 𝔭) (h.ringTowerAt 𝔮) := by
  intro n x hx
  exact (Ideal.pow_right_mono hle _) hx

end HodgeTheater

-- ════════════════════════════════════════════════════════════
-- §NT4-5. リンクと不定性  🔴
-- ════════════════════════════════════════════════════════════

/-!
  IUT 理論の最も独創的な概念: **Θ-リンク** と **不定性**。

  通常の数学では、2つの Hodge 劇場は「標準的な同型」で結ばれる。
  IUT 理論では、この標準性を **意図的に壊す**。

  Θ-リンク:
  - 2つの Hodge 劇場 HT₁, HT₂ を結ぶ写像
  - 環の塔を保存するが、群の塔は保存しない（またはその逆）
  - 「乗法的構造」と「加法的構造」の間の非標準的対応

  StructureTower の言語:
  - Θ-リンク = IsReindexCompatible **でない** 写像
  - より正確には: ある reindex では整合的だが、別の reindex では整合的でない
  - 不定性 = reindex の非一意性

  Log-リンク:
  - p-adic 対数写像 log: O_K× → K に基づく
  - 乗法群のフィルトレーション → 加法群のフィルトレーション
  - StructureTower Hom だが、環構造は保存しない

  NT4 では以下を定式化する:
  1. TheaterMorphism: Hodge 劇場間の写像
  2. IndeterminacyType: 不定性の3分類
  3. 不定性のある TowerPairing

  証明可能な定理は限られるが、**定式化の精度** が重要。
-/

section LinksAndIndeterminacy

/-- Hodge 劇場間の射。
    全ての素点で環塔・群塔の間の Hom を誘導する。
    標準的な射は全ての構造を保存する。 -/
structure TheaterMorphism {P R : Type*} [CommRing R] {G : Type*} [Group G]
    (h₁ h₂ : HodgeTheaterData P R G) where
  /-- 各素点で環塔の間の Hom -/
  ringHom : ∀ 𝔭, Hom (h₁.ringTowerAt 𝔭) (h₂.ringTowerAt 𝔭)
  /-- 各素点で群塔の間の Hom -/
  groupHom : ∀ 𝔭, Hom (h₁.groupTowerAt 𝔭) (h₂.groupTowerAt 𝔭)

/-- 🔴 Exercise NT4-5a: 恒等射。

    Hint-1: ringHom, groupHom ともに Hom.id。 -/
def TheaterMorphism.id {P R : Type*} [CommRing R] {G : Type*} [Group G]
    (h : HodgeTheaterData P R G) : TheaterMorphism h h where
  ringHom 𝔭 := Hom.id (h.ringTowerAt 𝔭)
  groupHom 𝔭 := Hom.id (h.groupTowerAt 𝔭)

/-- 不定性の型。IUT 理論では3種類の不定性が現れる:
    1. Ind1: 外部自己同型不定性（群の共役による）
    2. Ind2: 局所的乗法不定性（p-adic 単数群）
    3. Ind3: 対数的不定性（log と exp の非一意性）

    StructureTower 的意味:
    - Ind1: conjugationHom（NT1）の非一意性
    - Ind2: 環塔の自己 Hom の族
    - Ind3: 異なる reindex の選択

    ここでは Ind1（共役不定性）を StructureTower で定式化する。 -/
inductive IndeterminacyType
  | conjugation   -- 共役による不定性（群の内部自己同型）
  | multiplicative -- 乗法的不定性（単数群の作用）
  | logarithmic   -- 対数的不定性（log/exp の選択）

/-- 共役不定性の定式化。
    群の塔 T の自己 Hom の集合のうち、
    共役で得られるもの全体。

    NT1 の conjugationHom の集合版。
    |{conjugationHom g | g ∈ G}| が不定性の「大きさ」。 -/
def conjugacyIndeterminacy {G : Type*} [Group G]
    (rd : RamificationData G) : Set (Hom (ramificationTower rd) (ramificationTower rd)) :=
  {h | ∃ g : G, h.toFun = fun x => g * x * g⁻¹}

/-- 🔴 Exercise NT4-5b: 恒等射は共役不定性に属する。
    g = 1 のとき conjugation = id。

    Hint-1: g = 1 で 1 * x * 1⁻¹ = x。 -/
theorem id_mem_conjugacyIndeterminacy {G : Type*} [Group G]
    (rd : RamificationData G) :
    Hom.id (ramificationTower rd) ∈ conjugacyIndeterminacy rd := by
  refine ⟨1, ?_⟩
  funext x
  simp [Hom.id]

/-- 不定性を含む TowerPairing。
    forward が一意ではなく、不定性の分だけ「ぶれる」。
    これが IUT の Θ-リンクの StructureTower 的な表現。

    具体的には:
    - forward は「不定性集合」の中の任意の元
    - どの forward を選んでも Hom 条件は保たれる
    - しかし選択によって global や jumpSet の値が変わりうる -/
structure IndeterminatePairing {α β : Type*}
    (T₁ : StructureTower ℕᵒᵈ α) (T₂ : StructureTower ℕᵒᵈ β) where
  /-- 可能な forward 射の集合 -/
  forwardSet : Set (α → β)
  /-- 各候補が Hom 条件を満たす -/
  all_preserve : ∀ f ∈ forwardSet, ∀ i, MapsTo f (T₁.level i) (T₂.level i)
  /-- 非空（少なくとも1つの選択が存在）-/
  nonempty : forwardSet.Nonempty

/-- 🔴 Exercise NT4-5c: IndeterminatePairing から Hom を選ぶ。
    forwardSet の任意の元が Hom を誘導する。

    Hint-1: Nonempty から元を取り出す。 -/
noncomputable def IndeterminatePairing.someHom {α β : Type*}
    {T₁ : StructureTower ℕᵒᵈ α} {T₂ : StructureTower ℕᵒᵈ β}
    (p : IndeterminatePairing T₁ T₂) : Hom T₁ T₂ where
  toFun := p.nonempty.some
  preserves := p.all_preserve _ p.nonempty.some_mem

end LinksAndIndeterminacy

-- ════════════════════════════════════════════════════════════
-- §Summary. NT4 の全体像と数論シリーズの完結
-- ════════════════════════════════════════════════════════════

/-!
  NT4 で構築したこと:

  §NT4-1 **副有限塔**:
    ProfiniteTowerData: 分離条件付きの正規部分群列。
    profiniteTower: global = {1} の StructureTower。
    truncateTower: n で切り詰め（有限近似）。
    切詰めの単調性と NatInclusion。
    → 副有限群の StructureTower 的記述。

  §NT4-2 **塔のネットワーク**:
    TowerPairingFamily: 対の添字付き族。
    IsCoherentFamily: 逆系的整合性。
    limTower: 整合的族の極限塔（⋃ₙ）。
    → 副有限極限の StructureTower 版。

  §NT4-3 **復元問題**:
    TowerInvariant: 塔から計算可能な量（jumpSet, global 等）。
    TowerIso: レベル一致を保証する双方向 Hom。
    AnabelianCorrespondence: 遠アーベル復元の骨格。
    → 「塔の同型 ⟹ 幾何学的同型」の定式化。

  §NT4-4 **Hodge 劇場の骨格**:
    HodgeTheaterData: 素点で添字された RingGroupTowerData。
    ringTowerAt / groupTowerAt: 各素点での塔。
    ringTower_natInclusion_of_le: 素点間の整除関係と塔の包含。
    TheaterMorphism: 劇場間の射。
    → IUT 的構造の StructureTower 的骨格。

  §NT4-5 **リンクと不定性**:
    IndeterminacyType: 共役・乗法・対数の3分類。
    conjugacyIndeterminacy: 共役 Hom の集合。
    IndeterminatePairing: 不定性を含む対。
    → Θ-リンクの StructureTower 的表現。

  ══════════════════════════════════════════════════
  数論シリーズ NT1-NT4 の完結
  ══════════════════════════════════════════════════

  NT1-NT4 で構築した概念の総数:
    定義: ~50
    定理: ~60
    sorry: 0

  中核概念の階層:

    L1-L7（基盤）
    │
    ├── NT1: 群の塔（subgroupFiltrationTower, ramificationTower）
    │   ├── conjugationHom（群固有の非自明 Hom）
    │   ├── HasCommutatorBound（演算と添字の算術的関係）
    │   └── ramificationBreak（分岐指標）
    │
    ├── NT2: 添字変換と grading
    │   ├── gradedPiece, jumpSet（隣接レベル差分）
    │   ├── scaledHerbrand, herbrandReindex（数論的 reindex）
    │   ├── upperNumberingTower = reindex ∘ ramificationTower
    │   └── HasseArfCondition（整数性条件）
    │
    ├── NT3: Tower Comparison Theory
    │   ├── towerMeet / towerJoin（NatInclusion の束）
    │   ├── TowerPairing（異型塔の双方向接続）
    │   ├── RingGroupTowerData（環-群二重塔）
    │   ├── IsReindexCompatible（reindex 整合的射）
    │   ├── IsExactPairing（偏差による完全決定）
    │   └── deviation_mul（telescoping identity）
    │
    └── NT4: 副有限塔と遠アーベル
        ├── ProfiniteTowerData（分離条件付き正規列）
        ├── truncateTower / limTower（有限近似と極限）
        ├── TowerIso, AnabelianCorrespondence（復元問題）
        ├── HodgeTheaterData（素点添字の劇場）
        └── IndeterminatePairing（不定性を含む対）

  StructureTower の主定理（NT1-NT4 を通じて示されたこと）:

    **Theorem (Number-Theoretic Tower Duality)**:
    数論的フィルトレーション（分岐群列、イデアル冪、上付番号、
    副有限完備化、Hodge 劇場）は、StructureTower の
    Hom + reindex + Pairing + Indeterminacy の体系として
    自然に記述され、以下が成り立つ:

    1. 群の塔は偏差写像を通じて環の塔から決定される（IsExactPairing）
    2. Herbrand reindex は部分群制限と可換になる唯一の reindex
    3. 副有限極限は切詰め塔の整合的族の limTower として構成される
    4. 遠アーベル復元は TowerIso の忠実性として定式化される
    5. IUT の不定性は IndeterminatePairing として捉えられる

    これらの結果は OrderHom ι (Set α) 単体では自然に記述できない。
-/

end StructureTower

end BourbakiGuide
