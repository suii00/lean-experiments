/-
  StructureTower 発展理論（レベル9）: Interleaving / Tower Metric
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル9（主張ファイル / claim file）
  前提: L1-L7 + NT1-NT3（特に reindex, NatInclusion, TowerPairing,
        IsReindexCompatible, rank uniqueness）

  位置づけ:
    本ファイルは「StructureTower が既存構造の別名を卒業するために
    主張すべき定理」を明示するための骨格である。
    定義はすべて sorry-free。定理は可能な限り証明を付し、
    深い Mathlib 依存または本質的作業を要するもののみ sorry とする。

  先行研究との関係（誠実性のための注記）:
    ε-interleaving は TDA における persistence module の標準的比較手段であり、
    「translation / flow による一般化」の系譜（Bubenik–de Silva–Scott 型の
    一般化 persistence、de Silva らの flow 上の interleaving — 文献名は
    論文執筆時に要確認）が存在する。本ファイルの新規性の所在は:
      (1) Set 値の塔（= persistence のホモロジー適用前の層）での定式化と、
          既存の reindex / NatInclusion 語彙との同値（定理 I-0）
      (2) 変位定理（定理 II）を軸にした「一つの定理・二つの分野」:
          解析（sublevel 安定性, 定理 III）と数論（Herbrand 変位, 定理 IV）
      (3) 添字逆数学の第一定理（定理 V）:
          rank 一意性 ⟺ 添字の反対称性（双条件! 逆向きは新規）
    (1)(3) は statement 自体が枠組みを要求する。これが「別名でない」証拠。

  主張する定理の一覧（ステータス付き）:
    定理 I-0  Interleaving = NatInclusion ∘ reindex        [✓ 証明済（定義的）]
    定理 I    擬距離構造（refl / symm / mono / 三角不等式）  [✓ 証明済]
    定理 II   Reindex 変位定理                              [✓ 証明済]
    定理 III  sublevel 等長定理（⟺ ℓ∞ 距離）               [✓ 証明済]
    定理 IV   ℕᵒᵈ 変位定理（Herbrand 接続の一般形）         [✓ 証明済]
    主張 IV'  NT2 接続（upperNumberingTower との実接続）    [別ファイル課題]
    定理 V    rank 一意性の特徴付け ⟺ 反対称性              [✓ 証明済]
    主張 VI   interleaving 距離の三角不等式（ℝ≥0∞ 値）      [sorry]

  ⚠ 方向の注意（NT ファイル群での既往の修正パターン）:
    ℕᵒᵈ 添字では ≤ が反転するため、shift は「引き算」になる。
    §5 の natODShift と §7 の定理 IV は方向を明示的に検算してあるが、
    NT2 の herbrandReindex と接続する際は必ず ψ の向き
    （上付→下付 か 下付→上付ヴか）を再確認すること。
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Basic

open Set Function OrderDual

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. 基本定義の再掲（自己完結性のため）
-- ════════════════════════════════════════════════════════════

/-- 構造塔: 前順序 ι で添字付けられた単調な集合族。 -/
structure StructureTower (ι α : Type*) [Preorder ι] where
  level : ι → Set α
  monotone_level : ∀ {i j : ι}, i ≤ j → level i ⊆ level j

variable {ι α β : Type*} [Preorder ι]

namespace StructureTower

/-- レベルごとの包含（L1 の NatInclusion）。 -/
def NatInclusion (T₁ T₂ : StructureTower ι α) : Prop :=
  ∀ i, T₁.level i ⊆ T₂.level i

/-- 添字変換（L2/NT2 の reindex）。 -/
def reindex {κ : Type*} [Preorder κ] (φ : κ → ι) (hφ : Monotone φ)
    (T : StructureTower ι α) : StructureTower κ α where
  level k := T.level (φ k)
  monotone_level := fun hij => T.monotone_level (hφ hij)

@[simp] theorem reindex_level {κ : Type*} [Preorder κ]
    (φ : κ → ι) (hφ : Monotone φ) (T : StructureTower ι α) (k : κ) :
    (reindex φ hφ T).level k = T.level (φ k) := rfl

end StructureTower

open StructureTower

-- ════════════════════════════════════════════════════════════
-- §1. ShiftFamily — 添字上の平行移動族
-- ════════════════════════════════════════════════════════════

/-!
  interleaving を語るには「添字を ε だけ緩める」操作が必要。
  ℝ なら (· + ε)、ℕᵒᵈ なら (· - ε)。これを公理化する。

  数学的には (M, +, 0, ≤) の ι への単調・膨張的な作用
  （persistence 理論の translation / flow に対応）。
  StructureTower の観点では「reindex の 1 パラメータ族」であり、
  すべてが既存語彙（Monotone + reindex）の上に乗る点が要点。
-/

/-- 添字集合 ι 上の平行移動族。
    shift ε は「ε だけ粗い位置へ動かす」単調写像で、
    モノイド M の作用として整合的。 -/
structure ShiftFamily (ι : Type*) [Preorder ι]
    (M : Type*) [AddCommMonoid M] [PartialOrder M] where
  shift : M → ι → ι
  monotone_shift : ∀ ε, Monotone (shift ε)
  /-- 膨張性: どの点も shift で「上」へ動く。 -/
  le_shift : ∀ (ε : M) (i : ι), i ≤ shift ε i
  shift_zero : ∀ i : ι, shift 0 i = i
  shift_add : ∀ (ε δ : M) (i : ι), shift (ε + δ) i = shift ε (shift δ i)
  /-- パラメータ単調性: 大きい ε ほど遠くへ動かす。 -/
  shift_mono_param : ∀ {ε δ : M}, ε ≤ δ → ∀ i, shift ε i ≤ shift δ i

variable {M : Type*} [AddCommMonoid M] [PartialOrder M]

-- ════════════════════════════════════════════════════════════
-- §2. Interleaving の定義と基本性質
-- ════════════════════════════════════════════════════════════

/-- ε-interleaving: 互いに ε だけ緩めれば含み合う 2 つの塔。
    Set 値の塔では包含が正準的なので、加群値の場合に必要な
    コヒーレンス条件（三角図式）が自動で満たされる点に注意。 -/
def Interleaving (S : ShiftFamily ι M) (ε : M)
    (T₁ T₂ : StructureTower ι α) : Prop :=
  (∀ i, T₁.level i ⊆ T₂.level (S.shift ε i)) ∧
  (∀ i, T₂.level i ⊆ T₁.level (S.shift ε i))

/-- 定理 I-0: Interleaving は既存語彙 NatInclusion + reindex で
    正確に表現できる。定義的同値（Iff.rfl）であることが要点:
    L9 は新しいプリミティブを一切追加していない。 -/
theorem interleaving_iff_natInclusion_reindex
    (S : ShiftFamily ι M) (ε : M) (T₁ T₂ : StructureTower ι α) :
    Interleaving S ε T₁ T₂ ↔
      NatInclusion T₁ (reindex (S.shift ε) (S.monotone_shift ε) T₂) ∧
      NatInclusion T₂ (reindex (S.shift ε) (S.monotone_shift ε) T₁) :=
  Iff.rfl

theorem Interleaving.symm {S : ShiftFamily ι M} {ε : M}
    {T₁ T₂ : StructureTower ι α}
    (h : Interleaving S ε T₁ T₂) : Interleaving S ε T₂ T₁ :=
  ⟨h.2, h.1⟩

/-- ε = 0 の interleaving はレベルごとの相等。
    NT2 の UpperNumberingCompatible は「ε = 0 の interleaving」
    そのものである（NT2 接続時に定理として明示すること）。 -/
theorem interleaving_zero_iff (S : ShiftFamily ι M)
    (T₁ T₂ : StructureTower ι α) :
    Interleaving S 0 T₁ T₂ ↔ ∀ i, T₁.level i = T₂.level i := by
  constructor
  · rintro ⟨h₁, h₂⟩ i
    apply Set.Subset.antisymm
    · simpa [S.shift_zero] using h₁ i
    · simpa [S.shift_zero] using h₂ i
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [S.shift_zero]; exact (h i).le
    · rw [S.shift_zero]; exact (h i).ge

theorem interleaving_refl (S : ShiftFamily ι M) (T : StructureTower ι α) :
    Interleaving S 0 T T :=
  (interleaving_zero_iff S T T).mpr fun _ => rfl

/-- ε 単調性: ε で interleave されるなら、より大きい δ でも。 -/
theorem Interleaving.mono {S : ShiftFamily ι M} {ε δ : M}
    {T₁ T₂ : StructureTower ι α}
    (h : Interleaving S ε T₁ T₂) (hεδ : ε ≤ δ) :
    Interleaving S δ T₁ T₂ :=
  ⟨fun i => (h.1 i).trans (T₂.monotone_level (S.shift_mono_param hεδ i)),
   fun i => (h.2 i).trans (T₁.monotone_level (S.shift_mono_param hεδ i))⟩

-- ════════════════════════════════════════════════════════════
-- §3. 定理 I: 三角不等式（擬距離構造の核）
-- ════════════════════════════════════════════════════════════

/-- 定理 I（三角不等式）: interleaving は加法的に合成する。
    refl（ε=0, 自己）・symm・本定理により、
    d(T₁,T₂) := inf {ε | Interleaving S ε T₁ T₂}
    が塔の空間上の拡張擬距離をなす（inf 版は §8 の主張 VI）。 -/
theorem Interleaving.trans {S : ShiftFamily ι M} {ε δ : M}
    {T₁ T₂ T₃ : StructureTower ι α}
    (h₁ : Interleaving S ε T₁ T₂) (h₂ : Interleaving S δ T₂ T₃) :
    Interleaving S (ε + δ) T₁ T₃ := by
  constructor
  · intro i x hx
    have hx₃ := h₂.1 (S.shift ε i) (h₁.1 i hx)
    rw [show ε + δ = δ + ε from add_comm ε δ, S.shift_add]
    exact hx₃
  · intro i x hx
    have hx₁ := h₁.2 (S.shift δ i) (h₂.2 i hx)
    rw [S.shift_add]
    exact hx₁

-- ════════════════════════════════════════════════════════════
-- §4. 定理 II: Reindex 変位定理（本ファイルの要）
-- ════════════════════════════════════════════════════════════

/-- 定理 II（変位定理）: 恒等写像から ε 以内しかずれない reindex は、
    塔を ε-interleaving の意味でしか動かさない。

      φ i ≤ shift ε i  かつ  i ≤ φ (shift ε i)
      ⟹  d(reindex φ T, T) ≤ ε

    これが「一つの定理・二つの分野」の親定理:
    - 解析側: sublevel 塔 + 平行移動 → 定理 III（安定性）の片翼
    - 数論側: ℕᵒᵈ + Herbrand 変換 → 定理 IV
    - TDA 側: Čech–Rips の log スケール 1-interleaving も
      乗法的 shift + log-reindex でこの形に落ちる（紙側の注記）。 -/
theorem interleaving_reindex (S : ShiftFamily ι M)
    (T : StructureTower ι α) (φ : ι → ι) (hφ : Monotone φ) (ε : M)
    (hlead : ∀ i, φ i ≤ S.shift ε i)
    (hlag : ∀ i, i ≤ φ (S.shift ε i)) :
    Interleaving S ε (reindex φ hφ T) T := by
  constructor
  · intro i x hx
    simp only [reindex_level] at hx
    exact T.monotone_level (hlead i) hx
  · intro i x hx
    simp only [reindex_level]
    exact T.monotone_level (hlag i) hx

-- ════════════════════════════════════════════════════════════
-- §5. 具体的 ShiftFamily: ℝ と ℕᵒᵈ
-- ════════════════════════════════════════════════════════════

open scoped NNReal ENNReal

/-- ℝ 上の標準 shift: r ↦ r + ε（ε : ℝ≥0）。解析・TDA 側の添字。 -/
def realShift : ShiftFamily ℝ ℝ≥0 where
  shift ε r := r + ε
  monotone_shift := fun _ _ _ h => by dsimp only; gcongr
  le_shift := fun ε r => le_add_of_nonneg_right ε.coe_nonneg
  shift_zero := fun r => by simp
  shift_add := fun ε δ r => by push_cast; ring
  shift_mono_param := fun {ε δ} h r => by gcongr

/-- ℕᵒᵈ 上の標準 shift: n ↦ n - ε（切り捨て引き算）。
    減少フィルトレーション（イデアル冪・分岐群列）の添字。
    ⚠ ᵒᵈ で「上へ動く」= ℕ で「小さくなる」ことに注意。 -/
def natODShift : ShiftFamily ℕᵒᵈ ℕ where
  shift ε n := toDual (ofDual n - ε)
  monotone_shift := fun ε i j hij => by
    have h : ofDual j ≤ ofDual i := hij
    exact toDual_le_toDual.mpr (Nat.sub_le_sub_right h ε)
  le_shift := fun ε i => le_toDual.mpr (Nat.sub_le _ _)
  shift_zero := fun i => by simp
  shift_add := fun ε δ i => by
    simp only [ofDual_toDual]
    exact congrArg toDual (by omega)
  shift_mono_param := fun {ε δ} h i =>
    toDual_le_toDual.mpr (Nat.sub_le_sub_left h _)

-- ════════════════════════════════════════════════════════════
-- §6. 定理 III: sublevel 等長定理（解析側の実体化）
-- ════════════════════════════════════════════════════════════

/-- 関数 f の sublevel 塔: level r = {x | f x ≤ r}。
    persistence 理論のホモロジー適用前の対象そのもの。 -/
def sublevelTower {α : Type*} (f : α → ℝ) : StructureTower ℝ α where
  level r := {x | f x ≤ r}
  monotone_level := fun hij _x hx => le_trans hx hij

/-- 定理 III（sublevel 等長定理）:
    sublevel 塔の ε-interleaving は ℓ∞ 距離 ≤ ε と**同値**。

    片方向（安定性）だけでなく双条件であることが主張の核:
    「塔は関数を ℓ∞ の精度で完全に記憶する」。
    従って sublevel 構成は (関数, ℓ∞) から (塔, interleaving) への
    等長埋め込みであり、d の非退化性の反例（ℓ∞ で離れた関数）と
    退化性の例（異なる塔で d = 0）の両方を系として生む。 -/
theorem sublevel_interleaving_iff {α : Type*} (f g : α → ℝ) (ε : ℝ≥0) :
    Interleaving realShift ε (sublevelTower f) (sublevelTower g) ↔
      ∀ x, |f x - g x| ≤ ε := by
  constructor
  · rintro ⟨h₁, h₂⟩ x
    have hf : x ∈ (sublevelTower f).level (f x) := le_refl (f x)
    have hg : x ∈ (sublevelTower g).level (g x) := le_refl (g x)
    have h₁' : g x ≤ f x + (ε : ℝ) := h₁ (f x) hf
    have h₂' : f x ≤ g x + (ε : ℝ) := h₂ (g x) hg
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · intro h
    constructor
    · intro r x hx
      have hx' : f x ≤ r := hx
      have hgf : g x - f x ≤ (ε : ℝ) := (abs_sub_le_iff.mp (h x)).2
      show g x ≤ r + (ε : ℝ)
      linarith
    · intro r x hx
      have hx' : g x ≤ r := hx
      have hfg : f x - g x ≤ (ε : ℝ) := (abs_sub_le_iff.mp (h x)).1
      show f x ≤ r + (ε : ℝ)
      linarith

-- ════════════════════════════════════════════════════════════
-- §7. 定理 IV: ℕᵒᵈ 変位定理（数論側の実体化・一般形）
-- ════════════════════════════════════════════════════════════

/-- 定理 IV（ℕᵒᵈ 変位定理）: ψ : ℕ → ℕ が単調で
      ∀ n, n - ε ≤ ψ n ≤ n
    を満たすなら、ψ-reindex は塔を ε-interleaving でしか動かさない。

    意図された実体化（主張 IV', NT2 接続 — 別ファイル課題）:
      T := ramificationTower rd,  ψ := scaledHerbrand 由来の reindex,
      ε := Herbrand 変位 sup_n (n - ψ n)（ジャンプ有限性から有限）
    とすると「下付番号塔と上付番号塔の interleaving 距離は
    Herbrand 変位以下」。UpperNumberingCompatible（NT2-§4）は
    interleaving_zero_iff により ε = 0 の場合として回収される。

    ⚠ NT2 接続時の必須検算: herbrandReindex の向き（ψ n ≤ n か
    n ≤ ψ n か）。逆向きなら本定理を ψ⁻¹ 側に適用するか、
    仮定を n ≤ ψ n ≤ n + ε に差し替えた双対版を用意する。 -/
theorem interleaving_reindex_natOD {α : Type*}
    (T : StructureTower ℕᵒᵈ α) (ψ : ℕ → ℕ) (hψ : Monotone ψ) (ε : ℕ)
    (h_le : ∀ n, ψ n ≤ n) (h_ge : ∀ n, n - ε ≤ ψ n) :
    Interleaving natODShift ε
      (reindex (toDual ∘ ψ ∘ ofDual) hψ.dual T) T := by
  apply interleaving_reindex
  · intro i
    -- ᵒᵈ で φ i ≤ shift ε i ⟺ ℕ で ofDual i - ε ≤ ψ (ofDual i)
    exact toDual_le_toDual.mpr (h_ge (ofDual i))
  · intro i
    -- ᵒᵈ で i ≤ φ (shift ε i) ⟺ ℕ で ψ (ofDual i - ε) ≤ ofDual i
    exact le_toDual.mpr ((h_le _).trans (Nat.sub_le _ _))

-- ════════════════════════════════════════════════════════════
-- §8. 定理 V: rank 一意性の特徴付け（添字逆数学の第一定理）
-- ════════════════════════════════════════════════════════════

/-!
  L4 の Theorem B（rank uniqueness, ℕ 上）を「添字順序の性質」として
  読み替え、双条件に昇格させる。

  順方向（反対称 ⟹ 一意）は L4 の証明の一般化。
  **逆方向（一意 ⟹ 反対称）が新しい主張**であり、
  ℕ×ℕ や Bool 前順序での非一意性の発見を、
  「どの ι で成り立つか」という分類定理に変換したもの。

  この定理の statement は「すべての塔について」と量化しており、
  OrderHom ι (Set α) の個別の話としては書けない。
  「添字順序を変数化して定理の成立域を問う」という
  StructureTower 固有の問いの、最初の完全な実例。
-/

/-- 一般添字版の特徴付け rank（L4 の HasCharRank の ι 一般化）。 -/
def IsCharRank {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (r : α → ι) : Prop :=
  ∀ x i, x ∈ T.level i ↔ r x ≤ i

/-- 2 つの特徴付け rank は互いに ≤（前順序なら常に成立）。 -/
theorem IsCharRank.le_of_le {ι α : Type*} [Preorder ι]
    {T : StructureTower ι α} {r₁ r₂ : α → ι}
    (h₁ : IsCharRank T r₁) (h₂ : IsCharRank T r₂) (x : α) :
    r₁ x ≤ r₂ x :=
  (h₁ x (r₂ x)).1 ((h₂ x (r₂ x)).2 le_rfl)

/-- 定理 V（rank 一意性の特徴付け）:
    「ι 上のすべての塔で特徴付け rank が一意」⟺「ι は反対称」。

    逆方向の反例構成: a ≤ b ≤ a, a ≠ b に対し、
    PUnit 上の塔 level i := {u | a ≤ i} は
    定数 a と定数 b の両方を特徴付け rank に持つ。
    これは L4-3f（Bool 反例）と ℕ×ℕ 解析の共通核の抽出であり、
    多重パラメータ persistence における完全離散不変量の不在の
    順序論的な影に相当する。 -/
theorem isCharRank_unique_iff_antisymm (ι : Type*) [Preorder ι] :
    (∀ (α : Type) (T : StructureTower ι α) (r₁ r₂ : α → ι),
        IsCharRank T r₁ → IsCharRank T r₂ → r₁ = r₂)
      ↔ ∀ a b : ι, a ≤ b → b ≤ a → a = b := by
  constructor
  · intro huniq a b hab hba
    -- 反例候補の塔: すべてのレベルが「a ≤ i かどうか」だけで決まる
    set T : StructureTower ι PUnit :=
      { level := fun i => {_u : PUnit | a ≤ i}
        monotone_level := fun hij _u hu => le_trans hu hij } with hT
    have h₁ : IsCharRank T (fun _ => a) := fun _x i => Iff.rfl
    have h₂ : IsCharRank T (fun _ => b) := fun _x i =>
      ⟨fun h => le_trans hba h, fun h => le_trans hab h⟩
    have heq := huniq PUnit T (fun _ => a) (fun _ => b) h₁ h₂
    exact congrFun heq PUnit.unit
  · intro hanti α T r₁ r₂ h₁ h₂
    funext x
    exact hanti _ _ (h₁.le_of_le h₂ x) (h₂.le_of_le h₁ x)

/-- 系: 半順序なら特徴付け rank は一意（L4 Theorem B の一般化）。 -/
theorem isCharRank_unique {ι : Type*} [PartialOrder ι] {α : Type*}
    {T : StructureTower ι α} {r₁ r₂ : α → ι}
    (h₁ : IsCharRank T r₁) (h₂ : IsCharRank T r₂) : r₁ = r₂ :=
  funext fun x => le_antisymm (h₁.le_of_le h₂ x) (h₂.le_of_le h₁ x)

-- ════════════════════════════════════════════════════════════
-- §9. 主張 VI: interleaving 距離（ℝ≥0∞ 値）と三角不等式  [sorry]
-- ════════════════════════════════════════════════════════════

/-!
  述語版（§2-§3）を距離に束ねる。ここが本ファイル唯一の sorry。
  紙側では「(塔全体, d) は拡張擬距離空間」が定理 I の最終形。
-/

/-- 塔の interleaving 距離: interleave できる ε の下限。
    interleave 不能なら ∞（iInf の空規約）。 -/
noncomputable def interleavingDist (S : ShiftFamily ι ℝ≥0)
    (T₁ T₂ : StructureTower ι α) : ℝ≥0∞ :=
  ⨅ ε ∈ {ε : ℝ≥0 | Interleaving S ε T₁ T₂}, (ε : ℝ≥0∞)

theorem interleavingDist_self (S : ShiftFamily ι ℝ≥0)
    (T : StructureTower ι α) :
    interleavingDist S T T = 0 := by
  refine le_antisymm ?_ (zero_le _)
  simpa using iInf₂_le (0 : ℝ≥0) (interleaving_refl S T)

theorem interleavingDist_comm (S : ShiftFamily ι ℝ≥0)
    (T₁ T₂ : StructureTower ι α) :
    interleavingDist S T₁ T₂ = interleavingDist S T₂ T₁ := by
  have hset : {ε : ℝ≥0 | Interleaving S ε T₁ T₂} =
      {ε : ℝ≥0 | Interleaving S ε T₂ T₁} :=
    Set.ext fun ε => ⟨Interleaving.symm, Interleaving.symm⟩
  rw [interleavingDist, interleavingDist, hset]

/-- 主張 VI（距離の三角不等式）。

    証明戦略:
    - ENNReal.le_iInf 系で目標を「任意の ε ∈ S₁₂, δ ∈ S₂₃ について
      d(T₁,T₃) ≤ ε + δ」に還元。
    - 各 (ε, δ) に対し Interleaving.trans で ε + δ ∈ S₁₃、
      iInf₂_le で d(T₁,T₃) ≤ ↑(ε + δ) = ↑ε + ↑δ。
    - 二重 iInf の和への分配は ENNReal.iInf_add / add_iInf
      （または iInf₂ の le_iInf₂_iff 版）で処理。
    - 注意: 下限は達成されるとは限らないが、上の近似論法は
      達成を要求しない。ε = ∞（空集合）の場合は自明。
    深さ: Mathlib の ENNReal iInf API の選定が主作業。
    数学的障害はない（sorry は工数の印であって未解決の印ではない）。 -/
theorem interleavingDist_triangle (S : ShiftFamily ι ℝ≥0)
    (T₁ T₂ T₃ : StructureTower ι α) :
    interleavingDist S T₁ T₃ ≤
      interleavingDist S T₁ T₂ + interleavingDist S T₂ T₃ := by
  sorry

-- ════════════════════════════════════════════════════════════
-- L9 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  紙に書くときの主定理群（本ファイルとの対応）:

  **Theorem A (Tower Pseudometric)**
    (ST(ι,α), d) は拡張擬距離空間をなす。
    d = 0 ⟺ レベルごとの相等（interleaving_zero_iff）。
    [Lean: 定理 I 系 + 主張 VI]

  **Theorem B (Displacement)**
    reindex φ の恒等からの変位が ε 以下なら d(reindex φ T, T) ≤ ε。
    [Lean: interleaving_reindex, interleaving_reindex_natOD]

  **Theorem C (Sublevel Isometry)**
    sublevel : (α → ℝ, ℓ∞) → (ST(ℝ,α), d) は等長埋め込み。
    [Lean: sublevel_interleaving_iff]

  **Theorem D (Herbrand Displacement)** — NT2 接続、次の作業対象
    下付番号塔と上付番号塔の距離は Herbrand 変位以下。
    UpperNumberingCompatible は d = 0 の場合。
    [Lean: 定理 IV + NT2 側の変位評価（未着手）]

  **Theorem E (Index Reverse Mathematics, I)**
    ι 上の全塔で特徴付け rank が一意 ⟺ ι は反対称。
    [Lean: isCharRank_unique_iff_antisymm — 完全証明済]

  「別名批判」への回答の構造:
    - 定理 I-0 が示す通り、L9 は語彙を追加しない（reindex の再利用）。
    - 定理 B が一本の親定理で、C（解析/TDA）と D（数論）が
      その instantiation — 「一つの定理・二つの分野」。
    - 定理 E は statement が塔全体への量化を要求する最初の定理で、
      「添字順序の逆数学」プログラムの existence proof。
      次の候補: gradedPiece の標準性 ⟺ 後続者構造（L8 接続）、
      完備化の存在 ⟺ 可算共終性（L6 接続）。
-/

end BourbakiGuide
