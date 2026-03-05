/-
  StructureTower 数論シリーズ（NT2）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル9相当（Herbrand 関数と上付番号）
  前提: NT1（分岐フィルトレーション塔）+ L1-L7 を完了していること

  動機:
    NT1 で ramificationTower rd : StructureTower ℕᵒᵈ G を構成した。
    これは「下付番号（lower numbering）」による分岐フィルトレーション:
      G₀ ⊇ G₁ ⊇ G₂ ⊇ ...
    添字 i は「分岐の深さ」を直接表す。

    下付番号には致命的な欠陥がある:
    **部分群への制限と整合しない**。
    H ≤ G に対して、H の分岐フィルトレーション H_i = H ∩ G_i は
    「H の下付番号」とは一般に一致しない。

    解決策は **Herbrand 関数** φ による添字の変換:
      φ(n) = (1/|G₀|) Σ_{i=1}^{n} |G_i|
    この変換で得られる「上付番号（upper numbering）」は
    部分群への制限と整合する:
      H^u = H ∩ G^u  （上付番号は制限と可換！）

    StructureTower の視点:
    **φ は StructureTower.reindex そのものである。**
    上付番号塔 = reindex φ hφ (ramificationTower rd)

    これは L1 で定義した reindex の数論的具体例であり、
    「reindex の選び方に算術的内容がある」ことを示す最初の例。

  ZEN大学 IUT カリキュラムとの対応:
    IUT3: ガロア理論・代数的整数論 → §NT2-1, NT2-2 の中核
    IUT4: 類体論                    → §NT2-4 の Hasse-Arf

  核心的洞察（StructureTower 理論への貢献）:
    1. **Graded Tower Theory**: 連続レベル間の差分 G_i \ G_{i+1} が
       StructureTower の新しい不変量を与える。
       これは OrderHom では自然に記述できない — 隣接レベルの概念が必要。

    2. **Reindex の非自明性**: L1 の reindex は抽象的な関手操作だったが、
       Herbrand 関数は「reindex の選び方自体が定理を含む」ことを示す。
       φ は群の指数から決まる — 塔の内部構造が reindex を決定する。

    3. **Quotient Compatibility**: 上付番号の本質的性質
       「reindex φ した塔は部分群制限と可換」は、
       Tower Comparison Theory の基本定理の数論的インスタンス。

  学習の流れ:
    §NT2-1. Graded Tower（次数付き塔）    — 連続レベル差分の理論
    §NT2-2. Herbrand 関数                 — 離散版の構成と単調性
    §NT2-3. 上付番号塔                    — reindex による構成
    §NT2-4. 商との整合性                  — 上付番号の本質的性質
    §NT2-5. Hasse-Arf の定式化            — 分岐ジャンプの整数性

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
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Sum

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definitions（NT1 から再掲 + reindex）
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

-- reindex（L1 で定義。NT2 の核心的道具）
def reindex {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) : StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

@[simp] theorem reindex_level {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) (i : ι) :
    (reindex f hf T).level i = T.level (f i) := rfl

theorem reindex_id (T : StructureTower ι α) :
    reindex _root_.id monotone_id T = T := by
  ext i _; simp

theorem reindex_comp {κ μ : Type*} [Preorder κ] [Preorder μ]
    (f : ι → κ) (hf : Monotone f) (g : κ → μ) (hg : Monotone g)
    (T : StructureTower μ α) :
    reindex f hf (reindex g hg T) = reindex (g ∘ f) (hg.comp hf) T := by
  ext i _; simp [reindex]

-- NT1 からの定義: subgroupFiltrationTower, RamificationData, ramificationTower

variable {G : Type*} [Group G]

def subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) : StructureTower ℕᵒᵈ G where
  level n := ↑(OrderDual.ofDual (f (OrderDual.ofDual n)))
  monotone_level := by
    intro i j hij x hx
    have h := f.monotone (OrderDual.ofDual_le_ofDual.mpr hij)
    exact h hx

@[simp] theorem subgroupFiltrationTower_level (f : ℕ →o (Subgroup G)ᵒᵈ) (n : ℕᵒᵈ) :
    (subgroupFiltrationTower f).level n =
      ↑(OrderDual.ofDual (f (OrderDual.ofDual n))) := rfl

structure RamificationData (G : Type*) [Group G] where
  groups : ℕ → Subgroup G
  antitone : Antitone groups
  whole : groups 0 ≤ ⊤
  normal : ∀ n, (groups n).Normal

def RamificationData.toOrderHom (rd : RamificationData G) :
    ℕ →o (Subgroup G)ᵒᵈ where
  toFun n := OrderDual.toDual (rd.groups n)
  monotone' := by
    intro i j hij
    show rd.groups j ≤ rd.groups i
    exact rd.antitone hij

def ramificationTower (rd : RamificationData G) : StructureTower ℕᵒᵈ G :=
  subgroupFiltrationTower rd.toOrderHom

@[simp] theorem ramificationTower_level (rd : RamificationData G) (n : ℕᵒᵈ) :
    (ramificationTower rd).level n = ↑(rd.groups (OrderDual.ofDual n)) := rfl

def IsSeparatedFiltration (f : ℕ → Subgroup G) : Prop :=
  ⨅ n, f n = ⊥

-- NT1 の ramificationBreak（再掲のため必要な補題）
theorem subgroupFiltrationTower_global (f : ℕ →o (Subgroup G)ᵒᵈ) :
    (subgroupFiltrationTower f).global =
      ⋂ (n : ℕ), ↑(OrderDual.ofDual (f n)) := by
  simp [StructureTower.global, subgroupFiltrationTower_level]
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro h n; exact h (OrderDual.toDual n)
  · intro h n; exact h (OrderDual.ofDual n)

-- ════════════════════════════════════════════════════════════
-- §NT2-1. Graded Tower（次数付き塔）  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  **Graded Tower Theory**: 連続レベル間の差分を体系的に扱う。

  ℕᵒᵈ 添字の塔 T に対し、「次数 n のグレード」を定義する:
    gradedPiece T n = level(toDual n) \ level(toDual (n+1))

  直感:
  - level(toDual n) = {深さ ≥ n の元}（G_n, I^n 等）
  - level(toDual (n+1)) = {深さ ≥ n+1 の元}
  - gradedPiece T n = {深さがちょうど n の元}

  分岐フィルトレーションでは:
    gradedPiece (ramificationTower rd) n = G_n \ G_{n+1}
  これは「分岐の深さがちょうど n の自己同型」の集合。

  Graded Tower は以下の点で OrderHom を超える:
  1. 隣接レベルの概念は ℕᵒᵈ の離散構造に依存（一般の前順序にはない）
  2. グレードの直和分解 union = ⊔ₙ gradedPiece は非自明な定理
  3. 分岐指標 b(σ) は「σ が属する gradedPiece のインデックス」

  L8 候補として挙がっていた「Graded Tower Theory」の数論的具体化。
-/

section GradedTower

variable {α : Type*}

/-- 🟢 Exercise NT2-1a: ℕᵒᵈ 塔のグレード（次数片）。
    level n と level (n+1) の差分集合。
    「深さがちょうど n の元」の集合。

    設計判断: ℕᵒᵈ の内部操作を避け、ℕ で直接添字する。
    gradedPiece T n = T.level (toDual n) \ T.level (toDual (n+1))

    Hint-1: Set.diff で差分集合。 -/
def gradedPiece (T : StructureTower ℕᵒᵈ α) (n : ℕ) : Set α :=
  T.level (OrderDual.toDual n) \ T.level (OrderDual.toDual (n + 1))

/-- 🟢 Exercise NT2-1b: gradedPiece の成員条件。
    x ∈ gradedPiece T n ↔ x ∈ level(toDual n) ∧ x ∉ level(toDual (n+1))。

    Hint-1: Set.mem_diff。 -/
theorem mem_gradedPiece_iff (T : StructureTower ℕᵒᵈ α) (n : ℕ) (x : α) :
    x ∈ gradedPiece T n ↔
      x ∈ T.level (OrderDual.toDual n) ∧
      x ∉ T.level (OrderDual.toDual (n + 1)) :=
  Set.mem_diff _

/-- 🟢 Exercise NT2-1c: gradedPiece は互いに素。
    m ≠ n → gradedPiece T m ∩ gradedPiece T n = ∅。

    証明の鍵: m < n のとき、gradedPiece T m の元は level(toDual (m+1)) に属さない。
    しかし n ≥ m+1 なので level(toDual n) ⊆ level(toDual (m+1))。
    よって gradedPiece T n の元は level(toDual (m+1)) に属し、矛盾。

    Hint-1: m < n と m > n の2ケースに分ける。
    Hint-2: T.monotone_level で包含を得る。 -/
theorem gradedPiece_disjoint (T : StructureTower ℕᵒᵈ α) {m n : ℕ} (h : m ≠ n) :
    gradedPiece T m ∩ gradedPiece T n = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, mem_gradedPiece_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro ⟨hm, hm'⟩ ⟨hn, _⟩
  rcases Nat.lt_or_gt_of_ne h with h_lt | h_gt
  · -- m < n → n ≥ m + 1 → level(toDual n) ⊆ level(toDual (m+1))
    exact hm' (T.monotone_level (by exact OrderDual.toDual_le_toDual.mpr h_lt) hn)
  · -- n < m → m ≥ n + 1 → level(toDual m) ⊆ level(toDual (n+1))
    have : x ∈ T.level (OrderDual.toDual (n + 1)) :=
      T.monotone_level (by exact OrderDual.toDual_le_toDual.mpr h_gt) hm
    exact hm' (T.monotone_level (by exact OrderDual.toDual_le_toDual.mpr h_lt) hn)

/-- 🟡 Exercise NT2-1d: グレードの和集合と union の関係（上向き）。
    ⋃ₙ gradedPiece T n ⊆ union T。
    各 gradedPiece は level(toDual n) の部分集合なので union に含まれる。

    Hint-1: gradedPiece T n ⊆ level(toDual n)。
    Hint-2: level(toDual n) ⊆ union T。 -/
theorem iUnion_gradedPiece_subset_union (T : StructureTower ℕᵒᵈ α) :
    ⋃ n, gradedPiece T n ⊆ T.union := by
  intro x hx
  simp only [Set.mem_iUnion, mem_gradedPiece_iff] at hx
  obtain ⟨n, hn, _⟩ := hx
  simp only [StructureTower.union, Set.mem_iUnion]
  exact ⟨OrderDual.toDual n, hn⟩

/-- 🟡 Exercise NT2-1e: 分岐塔のグレードの具体化。
    ramificationTower rd の gradedPiece n = G_n \ G_{n+1}。

    Hint-1: 定義を展開するだけ。 -/
theorem gradedPiece_ramification {G : Type*} [Group G]
    (rd : RamificationData G) (n : ℕ) :
    gradedPiece (ramificationTower rd) n =
      ↑(rd.groups n) \ ↑(rd.groups (n + 1)) := by
  simp [gradedPiece, ramificationTower_level]

end GradedTower

-- ════════════════════════════════════════════════════════════
-- §NT2-2. Herbrand 関数  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  Herbrand 関数 φ は分岐フィルトレーションの下付番号を上付番号に変換する。

  古典的定義（連続版）:
    φ(t) = ∫₀ᵗ [G₀ : G_s]⁻¹ ds

  離散版（ℕ 上）:
    φ(0) = 0
    φ(n) = Σ_{i=1}^{n} |G_i| / |G₀|  （n ≥ 1）

  しかし |G_i|/|G₀| は一般に有理数。Lean で扱いやすい形にするため、
  **スケーリング版**（|G₀| 倍）を定義する:

    Φ(0) = 0
    Φ(n) = Σ_{i=1}^{n} |G_i|  （n ≥ 1）

  Φ(n) は自然数（有限群の場合）。
  実際の Herbrand 関数は φ(n) = Φ(n) / |G₀|。

  設計判断:
  - 有限群の場合のみ扱う（[Fintype G]）
  - Nat.card を使って |G_i| を取得
  - 単調性は |G_{n+1}| ≥ 1（部分群は非空）から

  StructureTower への影響:
  - Φ : ℕ → ℕ が単調 → reindex Φ が well-defined
  - Φ の具体的な値が群の指数から決まる → **塔の内部構造が reindex を決定する**
  - これは L1 の抽象的 reindex にはなかった算術的内容
-/

section HerbrandFunction

variable {G : Type*} [Group G]

/-- Herbrand 関数の離散・スケーリング版。
    Φ(n) = Σ_{i=1}^{n} |G_i|。|G₀| で割る前のスケール。

    設計: groupSize : ℕ → ℕ を外部から受け取る（|G_i| の抽象化）。
    これにより Fintype 仮定を必要最小限にできる。 -/
def scaledHerbrand (groupSize : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => scaledHerbrand groupSize n + groupSize (n + 1)

/-- 🟢 Exercise NT2-2a: scaledHerbrand の漸化式。
    Φ(n+1) = Φ(n) + groupSize(n+1)。

    Hint-1: 定義の展開。 -/
@[simp] theorem scaledHerbrand_zero (gs : ℕ → ℕ) :
    scaledHerbrand gs 0 = 0 := rfl

@[simp] theorem scaledHerbrand_succ (gs : ℕ → ℕ) (n : ℕ) :
    scaledHerbrand gs (n + 1) = scaledHerbrand gs n + gs (n + 1) := rfl

/-- 🟡 Exercise NT2-2b: scaledHerbrand は単調。
    groupSize が非負（常に成立）なので Φ は単調。

    Hint-1: 帰納法または Nat.le_add_right。
    Hint-2: Φ(n+1) = Φ(n) + gs(n+1) ≥ Φ(n)。 -/
theorem scaledHerbrand_monotone (gs : ℕ → ℕ) :
    Monotone (scaledHerbrand gs) := by
  intro m n hmn
  induction hmn with
  | refl => le_refl _
  | step h ih => exact le_trans ih (Nat.le_add_right _ _)

/-- 🟡 Exercise NT2-2c: scaledHerbrand は Finset.sum で表現できる。
    Φ(n) = Σ_{i ∈ Finset.range n} gs(i + 1)。
    Finset.range n = {0, 1, ..., n-1} なので
    Σ_{i ∈ range n} gs(i+1) = gs(1) + gs(2) + ... + gs(n) = Φ(n)。

    Hint-1: n に関する帰納法。
    Hint-2: Finset.sum_range_succ で漸化式に帰着。 -/
theorem scaledHerbrand_eq_sum (gs : ℕ → ℕ) (n : ℕ) :
    scaledHerbrand gs n = (Finset.range n).sum (fun i => gs (i + 1)) := by
  induction n with
  | zero => simp
  | succ k ih => simp [Finset.sum_range_succ, ih]

/-- 🟡 Exercise NT2-2d: groupSize が全て正なら scaledHerbrand は狭義単調。
    gs(i) ≥ 1 for all i > 0 → Φ は狭義単調。

    数論的意味: |G_i| ≥ 1（G_i は {1} を含む）は常に成立。
    よって Herbrand 関数は狭義単調 → 単射 → 逆関数 ψ が存在。

    Hint-1: m < n ⟹ Φ(n) ≥ Φ(m) + 1。
    Hint-2: m + 1 ≤ n で Φ(m+1) = Φ(m) + gs(m+1) ≥ Φ(m) + 1。 -/
theorem scaledHerbrand_strictMono (gs : ℕ → ℕ) (hgs : ∀ i, 0 < i → 0 < gs i) :
    StrictMono (scaledHerbrand gs) := by
  intro m n hmn
  induction hmn with
  | refl => exact absurd (lt_irrefl m) (fun h => h)
  | @step k _ ih =>
    simp only [scaledHerbrand_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_of_lt_of_le hmn (le_refl _)) with heq | hlt
    · omega
    · exact lt_of_lt_of_le ih (Nat.le_add_right _ _)

/-- Herbrand 関数から ℕᵒᵈ → ℕᵒᵈ の単調写像を構成。
    ℕᵒᵈ の順序では Φ が単調 ⟹ toDual ∘ Φ ∘ ofDual は反単調だが、
    ℕᵒᵈ → ℕᵒᵈ としては単調になる。

    注意: ℕᵒᵈ で i ≤ j ↔ ofDual i ≥ ofDual j。
    Φ が ℕ で単調 ⟹ ofDual i ≥ ofDual j ⟹ Φ(ofDual i) ≥ Φ(ofDual j)
    ⟹ toDual (Φ(ofDual i)) ≤ toDual (Φ(ofDual j)) in ℕᵒᵈ。 ✓ -/
def herbrandReindex (gs : ℕ → ℕ) : ℕᵒᵈ → ℕᵒᵈ :=
  fun n => OrderDual.toDual (scaledHerbrand gs (OrderDual.ofDual n))

theorem herbrandReindex_monotone (gs : ℕ → ℕ) :
    Monotone (herbrandReindex gs) := by
  intro i j hij
  show scaledHerbrand gs (OrderDual.ofDual j) ≤ scaledHerbrand gs (OrderDual.ofDual i)
  exact scaledHerbrand_monotone gs (OrderDual.ofDual_le_ofDual.mpr hij)

end HerbrandFunction

-- ════════════════════════════════════════════════════════════
-- §NT2-3. 上付番号塔  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  上付番号塔 = reindex (herbrandReindex gs) (ramificationTower rd)。

  古典的対応:
    G^u = G_{ψ(u)}   （ψ = φ⁻¹ は Herbrand 関数の逆関数）

  StructureTower の言語:
    upperTower rd gs = reindex (herbrandReindex gs) (herbrandReindex_monotone gs) (ramificationTower rd)
    level n = (ramificationTower rd).level (herbrandReindex gs n)
            = ↑(rd.groups (Φ(ofDual n)))

  意味:
  - 下付番号: level(toDual i) = ↑(G_i)
  - 上付番号: level(toDual u) = ↑(G_{Φ(u)})
    （Φ が ψ = φ⁻¹ のスケーリング版に対応）

  ここでの Φ は「|G₀| 倍された逆 Herbrand」の離散近似。
  厳密な数論的意味は NT3 以降で扱う。
  NT2 では「reindex が数論的内容を持つ」ことの形式化に集中する。
-/

section UpperNumbering

variable {G : Type*} [Group G]

/-- 🟡 Exercise NT2-3a: 上付番号塔の構成。
    ramificationTower を herbrandReindex で reindex する。

    これは L1 の reindex の **最初の数論的インスタンス**。

    Hint-1: reindex を herbrandReindex と ramificationTower に適用。 -/
def upperNumberingTower (rd : RamificationData G) (gs : ℕ → ℕ) :
    StructureTower ℕᵒᵈ G :=
  reindex (herbrandReindex gs) (herbrandReindex_monotone gs) (ramificationTower rd)

@[simp] theorem upperNumberingTower_level (rd : RamificationData G) (gs : ℕ → ℕ) (n : ℕᵒᵈ) :
    (upperNumberingTower rd gs).level n =
      ↑(rd.groups (scaledHerbrand gs (OrderDual.ofDual n))) := by
  simp [upperNumberingTower, reindex, herbrandReindex, ramificationTower_level]

/-- 🟡 Exercise NT2-3b: 上付番号のレベル 0 は G₀ と一致。
    Φ(0) = 0 なので level(toDual 0) = ↑(G₀)。

    Hint-1: scaledHerbrand_zero。 -/
theorem upperNumberingTower_level_zero (rd : RamificationData G) (gs : ℕ → ℕ) :
    (upperNumberingTower rd gs).level (OrderDual.toDual 0) =
      ↑(rd.groups 0) := by
  simp

/-- 🟡 Exercise NT2-3c: 上付番号は NatInclusion で下付番号より大きい（一般には）。
    gs(i) ≥ i for all i ⟹ Φ(n) ≥ n ⟹ G_{Φ(n)} ⊆ G_n
    ⟹ upperLevel n ⊆ lowerLevel n。

    すなわち上付番号の方が「細かいフィルタリング」になる（一般に）。
    ただし gs ≥ id が常に成立するとは限らない。

    Hint-1: Φ(n) ≥ n → G_{Φ(n)} ≤ G_n → 台集合の包含。
    Hint-2: rd.antitone で反単調性を使う。 -/
theorem upperNumbering_natInclusion_of_ge (rd : RamificationData G) (gs : ℕ → ℕ)
    (hge : ∀ n, n ≤ scaledHerbrand gs n) :
    NatInclusion (upperNumberingTower rd gs) (ramificationTower rd) := by
  intro n
  simp [upperNumberingTower_level, ramificationTower_level]
  exact SetLike.coe_subset_coe.mpr (rd.antitone (hge (OrderDual.ofDual n)))

/-- 🔴 Exercise NT2-3d: reindex の合成則（二重 reindex）。
    2つの reindex を合成すると、Herbrand 関数の合成に対応する。
    これは「下付番号 → 上付番号 → 別の番号付け」の操作を捉える。

    StructureTower.reindex_comp の直接的インスタンス。

    Hint-1: reindex_comp を適用。 -/
theorem upperNumbering_reindex_comp (rd : RamificationData G)
    (gs₁ gs₂ : ℕ → ℕ) :
    reindex (herbrandReindex gs₁) (herbrandReindex_monotone gs₁)
      (upperNumberingTower rd gs₂) =
    reindex (herbrandReindex gs₂ ∘ herbrandReindex gs₁)
      ((herbrandReindex_monotone gs₂).comp (herbrandReindex_monotone gs₁))
      (ramificationTower rd) := by
  ext n x
  simp [upperNumberingTower, reindex]

end UpperNumbering

-- ════════════════════════════════════════════════════════════
-- §NT2-4. 商との整合性  🔴
-- ════════════════════════════════════════════════════════════

/-!
  上付番号の本質的性質:
  **部分群への制限と可換**（下付番号にはこの性質がない）。

  古典的定式化:
    H ≤ G, H ◁ G のとき、
    H の上付番号分岐群 H^u = H ∩ G^u。

  下付番号では一般に H_i ≠ H ∩ G_i
  （H の分岐フィルトレーションは G のそれとは異なる添字付けを持つ）。

  StructureTower の言語:
    T₁ = ramificationTower(G の分岐データ)
    T₂ = ramificationTower(H の分岐データ)
    φ_G = G の Herbrand reindex
    φ_H = H の Herbrand reindex

    「商との整合性」=
      reindex φ_G T₁ の level n を H に制限 =
      reindex φ_H T₂ の level n

    これは Tower Comparison Theory の基本定理:
    **異なる塔を同じ添字空間で比較するとき、
    正しい reindex を選ぶと比較が自然になる。**

  ここでは抽象的な定式化のみ行い、具体的な証明は NT3 に委ねる。
-/

section QuotientCompatibility

variable {G : Type*} [Group G]

/-- 部分群による塔の制限。
    H ≤ G に対し、T : StructureTower ℕᵒᵈ G を H の台集合に制限する。
    level n ↦ level n ∩ ↑H。

    これは StructureTower の comap/intersect の特殊ケース。 -/
def restrictToSubgroup (T : StructureTower ℕᵒᵈ G) (H : Subgroup G) :
    StructureTower ℕᵒᵈ G where
  level n := T.level n ∩ ↑H
  monotone_level := by
    intro i j hij x ⟨hT, hH⟩
    exact ⟨T.monotone_level hij hT, hH⟩

@[simp] theorem restrictToSubgroup_level (T : StructureTower ℕᵒᵈ G) (H : Subgroup G) (n : ℕᵒᵈ) :
    (restrictToSubgroup T H).level n = T.level n ∩ ↑H := rfl

/-- 上付番号の商整合性の定式化。
    2つの分岐データ（G 全体と部分群 H）に対し、
    上付番号が制限と可換であることの条件。

    UpperNumberingCompatible rd_G rd_H gs_G gs_H H とは:
    ∀ n, (upperTower rd_G gs_G).level n ∩ ↑H = (upperTower rd_H gs_H).level n

    これが成り立つとき、上付番号は「正しい reindex」である。
    下付番号（gs = id に対応）では一般にこれが成立しない。 -/
def UpperNumberingCompatible
    (rd_G : RamificationData G)
    (rd_H : RamificationData G)
    (gs_G gs_H : ℕ → ℕ)
    (H : Subgroup G) : Prop :=
  ∀ n : ℕᵒᵈ,
    (upperNumberingTower rd_G gs_G).level n ∩ ↑H =
    (upperNumberingTower rd_H gs_H).level n

/-- 🔴 Exercise NT2-4a: 下付番号の非整合性。
    恒等 reindex（gs = fun _ => 1, Φ = id に相当）では
    一般に商整合性は成り立たない。

    反例: G₁ ≠ {1} で H が G₁ を含まない部分群の場合、
    H ∩ G₁ ≠ H の第1分岐群。

    ここでは「下付番号 = reindex id」を明示する。 -/
theorem lowerNumbering_is_trivial_reindex (rd : RamificationData G) :
    reindex (_root_.id : ℕᵒᵈ → ℕᵒᵈ) (monotone_id) (ramificationTower rd) =
    ramificationTower rd := by
  exact reindex_id (ramificationTower rd)

/-- 🔴 Exercise NT2-4b: 制限塔の包含関係。
    H ≤ G のとき、T を H に制限すると NatInclusion で T 以下。

    Hint-1: 交差 ⊆ 左辺。
    Hint-2: Set.inter_subset_left。 -/
theorem restrictToSubgroup_natInclusion (T : StructureTower ℕᵒᵈ G) (H : Subgroup G) :
    NatInclusion (restrictToSubgroup T H) T := by
  intro n x ⟨hT, _⟩
  exact hT

end QuotientCompatibility

-- ════════════════════════════════════════════════════════════
-- §NT2-5. Hasse-Arf の定式化  🔴
-- ════════════════════════════════════════════════════════════

/-!
  **Hasse-Arf 定理** (1930, Hasse / 1951, Arf):
    L/K がアーベルガロア拡大のとき、
    上付番号の分岐ジャンプ（break）は全て整数である。

  文脈:
  - 下付番号の分岐ジャンプ b は定義から整数（ℕ の元）。
  - 上付番号のジャンプは φ(b) = Φ(b)/|G₀| であり、一般には有理数。
  - Hasse-Arf: アーベル拡大なら φ(b) ∈ ℤ。

  StructureTower の言語での定式化:
  - 分岐ジャンプ = gradedPiece が非空であるインデックス
  - 下付番号のジャンプ集合: {n | gradedPiece (ramificationTower rd) n ≠ ∅}
  - 上付番号のジャンプ集合: {n | gradedPiece (upperNumberingTower rd gs) n ≠ ∅}

  Hasse-Arf はスケーリング版では:
    |G₀| が Φ(b) を割り切る（b が下付番号のジャンプのとき）。

  NT2 では定式化のみ。証明は類体論の深い結果に依存し、NT3 以降の範囲。
-/

section HasseArf

variable {G : Type*} [Group G]

/-- 塔のジャンプ集合。gradedPiece が非空であるインデックスの集合。

    数論的意味:
    - ramificationTower のジャンプ = 分岐指標の値域
    - upperNumberingTower のジャンプ = 上付番号分岐ジャンプ -/
def jumpSet (T : StructureTower ℕᵒᵈ α) : Set ℕ :=
  {n : ℕ | (gradedPiece T n).Nonempty}

/-- 🟡 Exercise NT2-5a: ジャンプ集合は非空ならそこで塔が「段差」を持つ。
    n ∈ jumpSet T ↔ ∃ x, x ∈ level(toDual n) ∧ x ∉ level(toDual (n+1))。

    Hint-1: 定義の展開。 -/
theorem mem_jumpSet_iff {α : Type*} (T : StructureTower ℕᵒᵈ α) (n : ℕ) :
    n ∈ jumpSet T ↔ ∃ x, x ∈ T.level (OrderDual.toDual n) ∧
      x ∉ T.level (OrderDual.toDual (n + 1)) := by
  simp [jumpSet, Set.Nonempty, gradedPiece, Set.mem_diff]

/-- Hasse-Arf 条件の定式化。
    「下付番号のジャンプ b に対し、|G₀| が Φ(b) を割り切る」

    これは「上付番号のジャンプが整数（＝ Φ(b)/|G₀| ∈ ℤ）」と同値。

    構造塔的意味:
    Herbrand reindex による gradedPiece の「移動先」が
    ℕ の格子点に着地する。
    アーベル拡大でないと、着地点が有理数になり、
    ℕ 上の StructureTower として整合的に定義できない。 -/
def HasseArfCondition (rd : RamificationData G) (gs : ℕ → ℕ) (g0size : ℕ) : Prop :=
  ∀ b ∈ jumpSet (ramificationTower rd), g0size ∣ scaledHerbrand gs b

/-- 🔴 Exercise NT2-5b: ジャンプ 0 では Hasse-Arf 条件が自明。
    Φ(0) = 0 は任意の |G₀| で割り切れる。

    Hint-1: scaledHerbrand_zero。
    Hint-2: dvd_zero。 -/
theorem hasseArf_at_zero (rd : RamificationData G) (gs : ℕ → ℕ) (g0size : ℕ) :
    g0size ∣ scaledHerbrand gs 0 := by
  simp

/-- 🔴 Exercise NT2-5c: 分岐塔のジャンプ集合は分離条件と関係する。
    IsSeparatedFiltration → ∃ N, ∀ n ≥ N, n ∉ jumpSet (ramificationTower rd)。
    すなわち、十分深いレベルではジャンプがなくなる。

    直感: 分離的なら ⋂ G_n = {1}。有限群なら G_n が {1} で安定する。
    安定後は gradedPiece = ∅ → ジャンプなし。

    ここでは有限安定性を仮定として statement のみ。 -/
def HasFiniteJumpSet (rd : RamificationData G) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → n ∉ jumpSet (ramificationTower rd)

theorem hasFiniteJumpSet_of_eventually_bot (rd : RamificationData G)
    (hBot : ∃ N : ℕ, ∀ n, N ≤ n → rd.groups n = ⊥) :
    HasFiniteJumpSet rd := by
  obtain ⟨N, hN⟩ := hBot
  exact ⟨N, fun n hn => by
    simp [jumpSet, gradedPiece, ramificationTower_level, Set.Nonempty]
    intro x hx
    have : rd.groups n = ⊥ := hN n hn
    rw [this] at hx
    simpa [Subgroup.mem_bot] using hx⟩

end HasseArf

-- ════════════════════════════════════════════════════════════
-- §Summary. NT2 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  NT2 で構築したこと:

  §NT2-1 **Graded Tower Theory**:
    gradedPiece T n = level(toDual n) \ level(toDual (n+1))。
    「深さがちょうど n の元」を捉える不変量。
    互いに素性、union との関係、分岐塔での具体化。
    → OrderHom では自然に記述できない「隣接レベルの概念」。

  §NT2-2 **Herbrand 関数**:
    scaledHerbrand gs : ℕ → ℕ（Φ(n) = Σ gs(i+1)）。
    単調性、狭義単調性（gs > 0 のとき）。
    Finset.sum による明示的表現。
    herbrandReindex : ℕᵒᵈ → ℕᵒᵈ（reindex 用の単調写像）。

  §NT2-3 **上付番号塔**:
    upperNumberingTower rd gs = reindex (herbrandReindex gs) (ramificationTower rd)。
    L1 の reindex の **最初の数論的インスタンス**。
    level 0 の整合性、下付番号との NatInclusion 関係。
    二重 reindex の合成則。

  §NT2-4 **商との整合性**:
    restrictToSubgroup: 塔の部分群への制限。
    UpperNumberingCompatible: 上付番号が制限と可換である条件の定式化。
    lowerNumbering_is_trivial_reindex: 下付番号 = reindex id。
    → **Tower Comparison Theory の数論的基本定理**。

  §NT2-5 **Hasse-Arf の定式化**:
    jumpSet T: 塔の「段差」が存在するインデックス集合。
    HasseArfCondition: |G₀| ∣ Φ(b) for all jump b。
    HasFiniteJumpSet: 分岐塔のジャンプ集合は有限。
    → アーベル拡大でのみ上付番号が ℕ 上で整合する。

  ──────────────────────────────────────────────
  StructureTower 理論への貢献（NT1 + NT2）:

    発見               OrderHom で可能か    StructureTower の優位性
    ─────────────────────────────────────────────────────────────
    gradedPiece        △（定義は可能）     隣接概念が添字の離散構造に依存
    jumpSet            △                   gradedPiece から自然に導出
    Herbrand reindex   ○（関数合成）       「塔の内部構造が reindex を決定」
    商との整合性       ×                   restrictToSubgroup + NatInclusion
    二重 reindex       ○                   reindex_comp の直接適用
    ─────────────────────────────────────────────────────────────

    特に §NT2-4 の「商との整合性」は、OrderHom の語彙では
    自然に記述できない: 「異なる対象上の2つの OrderHom を
    共通の添字空間で比較し、部分構造への制限と可換になる
    reindex を見つける」という問題は、StructureTower の
    Hom + reindex + NatInclusion の組み合わせで初めて定式化できる。

  ──────────────────────────────────────────────
  NT3 以降の展望:

    NT3: **局所類体論と Tower Comparison**
      Artin 写像 θ: K× → G^ab を使い、
      idealPowTower (K の素イデアル冪) と
      upperNumberingTower (G の上付番号分岐) を
      θ が StructureTower Hom として結ぶことを形式化。
      → Tower Comparison Theory の完全な数論的インスタンス。

    NT4: **副有限群と逆極限**
      π₁(X) のフィルトレーション → StructureTower。
      逆極限 = global の副有限版。
      望月の「宇宙際」= 異なる副有限塔間のリンク？
  ──────────────────────────────────────────────
-/

end StructureTower

end BourbakiGuide
