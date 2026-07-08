/-
  StructureTower 発展理論（レベル9・続）: 定理 D と定理 E-2
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル9（L9_Interleaving の続編・主張の完成）
  前提: L9_Interleaving + NT1（RamificationData）+ NT2（scaledHerbrand）

  本ファイルの内容:
    定理 D   : 下付番号塔と上付番号塔の interleaving 距離は
               Herbrand 変位 Φ(N) − N で押さえられる
    定理 E-2 : char-rank の**存在**が全塔で保証される
               ⟺ 添字の非空上方集合がすべて最小元を持つ

  ── 検算記録（herbrandReindex の向き）──────────────────
    NT2 の定義: Φ(n) = scaledHerbrand gs n = Σ_{i=1}^{n} gs(i)。
    gs(i) ≥ 1（群サイズなら常に成立）のとき **n ≤ Φ(n)**。
    これは L9 定理 IV の仮定（ψ n ≤ n）と逆側であり、
    双対版（本ファイル §1 の定理 IV'）が必要。
    さらに切り捨て引き算により ψ(n−ε) ≤ n が n < ε で崩れるため、
    Φ(0) = 0 を仮定に加える（scaledHerbrand_zero で満たされる）。
    NT2 の upperNumbering_natInclusion_of_ge が hge : n ≤ Φ(n) を
    仮定していることが向きの傍証。

  ── 変位 ε* の数論的意味 ──────────────────────────────
    ε* = Φ(N) − N = Σ_{i=1}^{N} (gs(i) − 1)。
    gs(i) = |G_i| のとき、これは different の付値の Hilbert 公式
      v(𝔡) = Σ_{i≥0} (|G_i| − 1)
    の i ≥ 1 部分、すなわち **different の暴分岐（wild）部分**。
    （Hilbert の公式との添字規約の対応は論文執筆時に要確認。
     参考: Serre, Corps Locaux, IV — 要文献確認。）
    したがって定理 D の紙側の言明は:
      「下付番号と上付番号の距離は different の wild 部分以下」

  主張一覧（ステータス付き）:
    定理 IV' 双対版 ℕᵒᵈ 変位定理                    [✓ 証明済]
    補題群   scaledHerbrand の変位評価              [✓ 証明済]
    定理 D   lower_upper_interleaving（different 束縛）[✓ 証明済]
    系 D₀    gs ≡ 1 なら上付 = 下付（ε = 0）        [✓ 証明済]
    定理 E-2 char-rank 存在 ⟺ 非空上方集合が単項     [✓ 証明済]
    実例     ℕ ✓ / ℕ×ℕ ✗ / ℝ ✗ + 塔レベルの反例     [✓ 証明済]

  定理 E との分業（添字逆数学の対）:
    定理 E   一意性 ⟺ 反対称性   （ℕ ✓ / ℕ×ℕ ✓ / ℝ ✓ / 一般前順序 ✗）
    定理 E-2 存在   ⟺ 上方集合単項（ℕ ✓ / ℕ×ℕ ✗ / ℝ ✗）
  多重パラメータ添字で壊れるのは**一意性ではなく存在**である。
  E-2 は HasMinRank（塔ごとの条件）の ι への外在化であり、
  ℝ が落ちることは「TDA が barcode でなく interleaving を距離に
  選ぶ理由」の順序論的説明を与える。
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

open Set Function OrderDual

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. 基本定義の再掲（L9 / NT1 / NT2 から、自己完結性のため）
-- ════════════════════════════════════════════════════════════

structure StructureTower (ι α : Type*) [Preorder ι] where
  level : ι → Set α
  monotone_level : ∀ {i j : ι}, i ≤ j → level i ⊆ level j

variable {ι α β : Type*} [Preorder ι]

namespace StructureTower

def reindex {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) :
    StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun hij => T.monotone_level (hf hij)

@[simp] theorem reindex_level {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) (i : ι) :
    (reindex f hf T).level i = T.level (f i) := rfl

end StructureTower

open StructureTower

/-- 添字上の平行移動族（L9 §1）。 -/
structure ShiftFamily (ι : Type*) [Preorder ι]
    (M : Type*) [AddCommMonoid M] [PartialOrder M] where
  shift : M → ι → ι
  monotone_shift : ∀ ε, Monotone (shift ε)
  le_shift : ∀ (ε : M) (i : ι), i ≤ shift ε i
  shift_zero : ∀ i : ι, shift 0 i = i
  shift_add : ∀ (ε δ : M) (i : ι), shift (ε + δ) i = shift ε (shift δ i)
  shift_mono_param : ∀ {ε δ : M}, ε ≤ δ → ∀ i, shift ε i ≤ shift δ i

variable {M : Type*} [AddCommMonoid M] [PartialOrder M]

/-- ε-interleaving（L9 §2）。 -/
def Interleaving (S : ShiftFamily ι M) (ε : M)
    (T₁ T₂ : StructureTower ι α) : Prop :=
  (∀ i, T₁.level i ⊆ T₂.level (S.shift ε i)) ∧
  (∀ i, T₂.level i ⊆ T₁.level (S.shift ε i))

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

/-- 変位定理（L9 §4, 定理 II）。 -/
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

/-- ℕᵒᵈ 上の標準 shift（L9 §5）: n ↦ n − ε。 -/
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

/-- 特徴付け rank（L9 §8）。 -/
def IsCharRank {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (r : α → ι) : Prop :=
  ∀ x i, x ∈ T.level i ↔ r x ≤ i

-- ── NT1 / NT2 からの再掲 ─────────────────────────────────

variable {G : Type*} [Group G]

def subgroupFiltrationTower (f : ℕ →o (Subgroup G)ᵒᵈ) :
    StructureTower ℕᵒᵈ G where
  level n := ↑(ofDual (f (ofDual n)))
  monotone_level := by
    intro i j hij x hx
    exact (f.monotone (ofDual_le_ofDual.mpr hij)) hx

structure RamificationData (G : Type*) [Group G] where
  groups : ℕ → Subgroup G
  antitone : Antitone groups
  whole : groups 0 ≤ ⊤
  normal : ∀ n, (groups n).Normal

def RamificationData.toOrderHom (rd : RamificationData G) :
    ℕ →o (Subgroup G)ᵒᵈ where
  toFun n := toDual (rd.groups n)
  monotone' := fun _ _ hij => rd.antitone hij

def ramificationTower (rd : RamificationData G) : StructureTower ℕᵒᵈ G :=
  subgroupFiltrationTower rd.toOrderHom

@[simp] theorem ramificationTower_level (rd : RamificationData G) (n : ℕᵒᵈ) :
    (ramificationTower rd).level n = ↑(rd.groups (ofDual n)) := rfl

def scaledHerbrand (gs : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => scaledHerbrand gs n + gs (n + 1)

@[simp] theorem scaledHerbrand_zero (gs : ℕ → ℕ) :
    scaledHerbrand gs 0 = 0 := rfl

@[simp] theorem scaledHerbrand_succ (gs : ℕ → ℕ) (n : ℕ) :
    scaledHerbrand gs (n + 1) = scaledHerbrand gs n + gs (n + 1) := rfl

theorem scaledHerbrand_monotone (gs : ℕ → ℕ) :
    Monotone (scaledHerbrand gs) := by
  refine monotone_nat_of_le_succ ?_
  intro n
  rw [scaledHerbrand_succ]
  exact Nat.le_add_right _ _

def herbrandReindex (gs : ℕ → ℕ) : ℕᵒᵈ → ℕᵒᵈ :=
  fun n => toDual (scaledHerbrand gs (ofDual n))

theorem herbrandReindex_monotone (gs : ℕ → ℕ) :
    Monotone (herbrandReindex gs) := by
  intro i j hij
  show scaledHerbrand gs (ofDual j) ≤ scaledHerbrand gs (ofDual i)
  exact scaledHerbrand_monotone gs (ofDual_le_ofDual.mpr hij)

def upperNumberingTower (rd : RamificationData G) (gs : ℕ → ℕ) :
    StructureTower ℕᵒᵈ G :=
  reindex (herbrandReindex gs) (herbrandReindex_monotone gs)
    (ramificationTower rd)

-- ════════════════════════════════════════════════════════════
-- §1. 定理 IV'（双対版 ℕᵒᵈ 変位定理）
-- ════════════════════════════════════════════════════════════

/-- 定理 IV'（双対版）: φ : ℕᵒᵈ → ℕᵒᵈ が ℕ 側で
      n ≤ φ(n) ≤ n + ε  かつ  φ(0) = 0
    を満たすとき、φ-reindex は塔を ε-interleaving でしか動かさない。

    L9 の定理 IV（ψ n ≤ n 側）の双対。検算により scaledHerbrand は
    こちら側（n ≤ Φ(n)）であることが確定した。

    ⚠ φ(0) = 0 が必要な理由: 切り捨て引き算により
    n < ε のとき (n − ε) + ε = ε > n となり、
    φ(n − ε) ≤ n の評価が h_le だけからは出ない。
    n − ε = 0 に落ちるケースを φ(0) = 0 で処理する。
    これは「ℕᵒᵈ 方向反転」に次ぐ第二の罠として記録しておく。 -/
theorem interleaving_reindex_natOD' {α : Type*}
    (T : StructureTower ℕᵒᵈ α) (φ : ℕᵒᵈ → ℕᵒᵈ) (hφ : Monotone φ) (ε : ℕ)
    (h_ge : ∀ n : ℕ, n ≤ ofDual (φ (toDual n)))
    (h_le : ∀ n : ℕ, ofDual (φ (toDual n)) ≤ n + ε)
    (h₀ : ofDual (φ (toDual 0)) = 0) :
    Interleaving natODShift ε (reindex φ hφ T) T := by
  apply interleaving_reindex
  · -- ᵒᵈ: φ i ≤ shift ε i ⟺ ℕ: ofDual i − ε ≤ ofDual (φ i)
    intro i
    show φ i ≤ toDual (ofDual i - ε)
    refine le_toDual.mpr ?_
    exact (Nat.sub_le _ _).trans (h_ge (ofDual i))
  · -- ᵒᵈ: i ≤ φ (shift ε i) ⟺ ℕ: ofDual (φ (toDual (n − ε))) ≤ n
    intro i
    show i ≤ φ (toDual (ofDual i - ε))
    refine ofDual_le_ofDual.mp ?_
    rcases le_total ε (ofDual i) with h | h
    · exact (h_le _).trans (by omega)
    · have hz : ofDual i - ε = 0 := by omega
      rw [hz, h₀]
      exact Nat.zero_le _

-- ════════════════════════════════════════════════════════════
-- §2. scaledHerbrand の変位評価
-- ════════════════════════════════════════════════════════════

/-- gs ≥ 1（正の添字で）なら Φ は恒等写像以上。向き検算の核。 -/
theorem le_scaledHerbrand (gs : ℕ → ℕ) (hgs : ∀ i, 0 < i → 0 < gs i)
    (n : ℕ) : n ≤ scaledHerbrand gs n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : 0 < gs (k + 1) := hgs (k + 1) (Nat.succ_pos k)
    rw [scaledHerbrand_succ]
    omega

/-- 変位 Φ(n) − n の単調性（加法形）。
    ⚠ 設計注意: 切り捨て引き算を避けるため、
    「Φ(m) − m ≤ Φ(n) − n」ではなく加法形
    「Φ(m) + n ≤ m + Φ(n)」で述べる。omega がケース分割なしで通る。 -/
theorem scaledHerbrand_add_le_of_le (gs : ℕ → ℕ)
    (hgs : ∀ i, 0 < i → 0 < gs i) {m n : ℕ} (hmn : m ≤ n) :
    scaledHerbrand gs m + n ≤ m + scaledHerbrand gs n := by
  induction n, hmn using Nat.le_induction with
  | base => omega
  | succ n hmn ih =>
    have h1 : 0 < gs (n + 1) := hgs (n + 1) (Nat.succ_pos n)
    rw [scaledHerbrand_succ]
    omega

/-- 安定域では変位が一定（加法形の等式）。
    gs が N より先で 1 に安定 ⟹ Φ(n) − n = Φ(N) − N（n ≥ N）。 -/
theorem scaledHerbrand_add_eq_of_stab (gs : ℕ → ℕ) {N : ℕ}
    (hstab : ∀ k, N < k → gs k = 1) {n : ℕ} (hNn : N ≤ n) :
    scaledHerbrand gs n + N = n + scaledHerbrand gs N := by
  induction n, hNn using Nat.le_induction with
  | base => omega
  | succ n hNn ih =>
    have h1 : gs (n + 1) = 1 := hstab (n + 1) (by omega)
    rw [scaledHerbrand_succ]
    omega

-- ════════════════════════════════════════════════════════════
-- §3. 定理 D: different 束縛（Herbrand 変位定理・NT2 実接続）
-- ════════════════════════════════════════════════════════════

/-- **定理 D**: フィルトレーションが N で安定する
    （gs(n) = 1 for n > N）とき、下付番号塔と上付番号塔は
      ε* = Φ(N) − N = Σ_{i=1}^{N} (gs(i) − 1)
    で interleave する。

    数論的意味: gs(i) = |G_i| のとき ε* は different の付値の
    Hilbert 公式 Σ_{i≥0}(|G_i| − 1) の暴分岐部分（i ≥ 1）。
    紙側の言明: **d(下付番号塔, 上付番号塔) ≤ v(𝔡) の wild 部分**。

    これは L9 定理 II（変位定理）の数論的 instantiation であり、
    定理 III（sublevel 安定性）と合わせて
    「一つの定理・二つの分野」の存在証明を完成させる。 -/
theorem lower_upper_interleaving (rd : RamificationData G) (gs : ℕ → ℕ)
    (hgs : ∀ i, 0 < i → 0 < gs i)
    (N : ℕ) (hstab : ∀ n, N < n → gs n = 1) :
    Interleaving natODShift (scaledHerbrand gs N - N)
      (upperNumberingTower rd gs) (ramificationTower rd) := by
  have hNle : N ≤ scaledHerbrand gs N := le_scaledHerbrand gs hgs N
  have h_le : ∀ n, scaledHerbrand gs n ≤ n + (scaledHerbrand gs N - N) := by
    intro n
    rcases le_total n N with h | h
    · have := scaledHerbrand_add_le_of_le gs hgs h
      omega
    · have := scaledHerbrand_add_eq_of_stab gs hstab h
      omega
  unfold upperNumberingTower
  refine interleaving_reindex_natOD' (ramificationTower rd)
    (herbrandReindex gs) (herbrandReindex_monotone gs)
    (scaledHerbrand gs N - N) ?_ ?_ ?_
  · intro n
    show n ≤ scaledHerbrand gs n
    exact le_scaledHerbrand gs hgs n
  · intro n
    show scaledHerbrand gs n ≤ n + (scaledHerbrand gs N - N)
    exact h_le n
  · show scaledHerbrand gs 0 = 0
    rfl

/-- 系 D₀: gs ≡ 1（正の添字で）なら ε* = 0、
    すなわち上付番号塔と下付番号塔はレベルごとに一致する。
    NT2 の UpperNumberingCompatible 的状況の「ε = 0 は距離 0」としての回収。 -/
theorem upperNumbering_level_eq_of_all_one (rd : RamificationData G)
    (gs : ℕ → ℕ) (h1 : ∀ n, 0 < n → gs n = 1) (i : ℕᵒᵈ) :
    (upperNumberingTower rd gs).level i = (ramificationTower rd).level i := by
  have h := lower_upper_interleaving rd gs
    (fun n hn => by rw [h1 n hn]; exact Nat.one_pos) 0 (fun n hn => h1 n hn)
  have hε : scaledHerbrand gs 0 - 0 = 0 := rfl
  rw [hε] at h
  exact (interleaving_zero_iff natODShift _ _).mp h i

-- ════════════════════════════════════════════════════════════
-- §4. 定理 E-2 の装置: 到達集合と最小元
-- ════════════════════════════════════════════════════════════

/-- 到達集合: 元 x が属するレベルの添字全体。
    monotone_level により常に上方集合（upper set）。 -/
def reachSet {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (x : α) : Set ι :=
  {i | x ∈ T.level i}

theorem isUpperSet_reachSet {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (x : α) : IsUpperSet (reachSet T x) :=
  fun _i _j hij hi => T.monotone_level hij hi

/-- 構造補題: r が特徴付け rank ⟺ 各 r x が到達集合の最小元。
    定理 E（一意性）と定理 E-2（存在）の共通基盤。
    「char-rank の存在 = 全到達集合の最小元の存在」という翻訳。 -/
theorem isCharRank_iff_isLeast {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (r : α → ι) :
    IsCharRank T r ↔ ∀ x, IsLeast (reachSet T x) (r x) := by
  constructor
  · intro h x
    exact ⟨(h x (r x)).mpr le_rfl, fun i hi => (h x i).mp hi⟩
  · intro h x i
    constructor
    · intro hx
      exact (h x).2 hx
    · intro hle
      exact T.monotone_level hle (h x).1

-- ════════════════════════════════════════════════════════════
-- §5. 定理 E-2: char-rank 存在の特徴付け（添字逆数学 II）
-- ════════════════════════════════════════════════════════════

/-- **定理 E-2（添字逆数学 II）**:
    「ι 上のすべての網羅的塔が特徴付け rank を**持つ**」
      ⟺ 「ι の非空上方集合がすべて最小元を持つ」。

    定理 E（一意性 ⟺ 反対称性）と対をなす。
    逆方向の反例装置は E と同一パターン: 上方集合 U に対する
    PUnit 塔 level i := {u | i ∈ U}。到達集合 = U となり、
    char-rank の存在は U の最小元の存在に一対一対応する。

    右辺の条件は非常に強い: 比較不能な a, b があれば
    {a, b} の生成する上方集合が最小元を持たないため、
    **全順序性を含意する**（さらに上方閉集合の整礎性も要求）。
    ℕ が例外的に良い添字であることの正体がこの条件である。

    注: 主張は α : Type（第 0 宇宙）で述べるが、
    逆方向の証人は PUnit のみなので宇宙多相化は自明。 -/
theorem charRankExists_iff_upperSet_least (ι : Type*) [Preorder ι] :
    (∀ (α : Type) (T : StructureTower ι α),
        (∀ x, ∃ i, x ∈ T.level i) → ∃ r : α → ι, IsCharRank T r)
      ↔ ∀ s : Set ι, IsUpperSet s → s.Nonempty → ∃ m, IsLeast s m := by
  constructor
  · intro hex s hs hne
    obtain ⟨r, hr⟩ :=
      hex PUnit
        ⟨fun i => {_u : PUnit | i ∈ s}, fun hij _u hu => hs hij hu⟩
        (fun _ => hne)
    refine ⟨r PUnit.unit, ?_⟩
    have hleast := (isCharRank_iff_isLeast _ r).mp hr PUnit.unit
    have hreach :
        reachSet
            (⟨fun i => {_u : PUnit | i ∈ s}, fun hij _u hu => hs hij hu⟩)
            PUnit.unit = s := by
      ext i
      simp [reachSet]
    rwa [hreach] at hleast
  · intro hleast α T hexh
    choose r hr using fun x =>
      hleast (reachSet T x) (isUpperSet_reachSet T x) (hexh x)
    exact ⟨r, (isCharRank_iff_isLeast T r).mpr hr⟩

-- ════════════════════════════════════════════════════════════
-- §6. 実例: ℕ ✓ / ℕ×ℕ ✗ / ℝ ✗
-- ════════════════════════════════════════════════════════════

/-- ℕ は条件を満たす（実際は任意の非空集合が最小元を持つ）。
    系: ℕ 上の網羅的塔は常に char-rank を持つ
    — L4 の rank 構成（Nat.find）の存在部分の抽象化。 -/
theorem charRank_exists_nat (α : Type) (T : StructureTower ℕ α)
    (hexh : ∀ x, ∃ i, x ∈ T.level i) : ∃ r : α → ℕ, IsCharRank T r :=
  (charRankExists_iff_upperSet_least ℕ).mpr
    (fun s _hs hne => ⟨sInf s, Nat.sInf_mem hne, fun _i hi => Nat.sInf_le hi⟩)
    α T hexh

/-- ℕ×ℕ は条件を満たさない: 二つの極小元を持つ上方集合。
    多重パラメータ persistence における
    「完全離散不変量の不在」の順序論的な核。 -/
theorem prodNat_exists_upperSet_no_least :
    ∃ s : Set (ℕ × ℕ), IsUpperSet s ∧ s.Nonempty ∧ ∀ m, ¬ IsLeast s m := by
  refine ⟨Set.Ici (1, 0) ∪ Set.Ici (0, 1),
    (isUpperSet_Ici _).union (isUpperSet_Ici _),
    ⟨(1, 0), Set.mem_union_left _ (Set.mem_Ici.mpr le_rfl)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨hmem, hlb⟩
  have h₁ : ((a, b) : ℕ × ℕ) ≤ (1, 0) :=
    hlb (Set.mem_union_left _ (Set.mem_Ici.mpr le_rfl))
  have h₂ : ((a, b) : ℕ × ℕ) ≤ (0, 1) :=
    hlb (Set.mem_union_right _ (Set.mem_Ici.mpr le_rfl))
  rw [Prod.mk_le_mk] at h₁ h₂
  obtain rfl : a = 0 := Nat.le_zero.mp h₂.1
  obtain rfl : b = 0 := Nat.le_zero.mp h₁.2
  rcases hmem with h | h
  · exact absurd (Prod.mk_le_mk.mp (Set.mem_Ici.mp h)).1 (by omega)
  · exact absurd (Prod.mk_le_mk.mp (Set.mem_Ici.mp h)).2 (by omega)

/-- 塔レベルの反例: ℕ×ℕ 上には char-rank を持たない網羅的塔が存在する。
    定理 E（一意性）は ℕ×ℕ で成立するので、
    多重パラメータで壊れるのは存在の側であることの形式的証明。 -/
theorem exists_prodNat_tower_no_charRank :
    ∃ T : StructureTower (ℕ × ℕ) PUnit,
      (∀ x, ∃ i, x ∈ T.level i) ∧ ∀ r : PUnit → ℕ × ℕ, ¬ IsCharRank T r := by
  obtain ⟨s, hs, hne, hno⟩ := prodNat_exists_upperSet_no_least
  refine ⟨⟨fun i => {_u : PUnit | i ∈ s}, fun hij _u hu => hs hij hu⟩,
    fun _ => hne, ?_⟩
  intro r hr
  have hleast := (isCharRank_iff_isLeast _ r).mp hr PUnit.unit
  have hreach :
      reachSet
        (⟨fun i => {_u : PUnit | i ∈ s}, fun hij _u hu => hs hij hu⟩)
        PUnit.unit = s := by
    ext i
    simp [reachSet]
  rw [hreach] at hleast
  exact hno _ hleast

/-- 主定理経由の同内容（両方向の運用確認を兼ねる）。 -/
theorem not_charRankExists_prodNat :
    ¬ ∀ (α : Type) (T : StructureTower (ℕ × ℕ) α),
        (∀ x, ∃ i, x ∈ T.level i) → ∃ r : α → ℕ × ℕ, IsCharRank T r := by
  intro h
  obtain ⟨s, hs, hne, hno⟩ := prodNat_exists_upperSet_no_least
  obtain ⟨m, hm⟩ := (charRankExists_iff_upperSet_least (ℕ × ℕ)).mp h s hs hne
  exact hno m hm

/-- ℝ も条件を満たさない: 開区間 (0, ∞) は最小元を持たない上方集合。
    ℝ 添字の sublevel 塔が一般に rank 型不変量を持たないこと
    — TDA が interleaving 距離を採用する順序論的理由。 -/
theorem real_exists_upperSet_no_least :
    ∃ s : Set ℝ, IsUpperSet s ∧ s.Nonempty ∧ ∀ m, ¬ IsLeast s m := by
  refine ⟨Set.Ioi 0, isUpperSet_Ioi 0, ⟨1, Set.mem_Ioi.mpr one_pos⟩, ?_⟩
  rintro m ⟨hm, hlb⟩
  have hm' : (0 : ℝ) < m := Set.mem_Ioi.mp hm
  have hhalf_mem : m / 2 ∈ Set.Ioi (0 : ℝ) := by
    exact Set.mem_Ioi.mpr (div_pos hm' (by norm_num))
  have hhalf : m ≤ m / 2 := hlb hhalf_mem
  have hlt : m / 2 < m := by
    exact half_lt_self hm'
  exact not_le_of_gt hlt hhalf

-- ════════════════════════════════════════════════════════════
-- 全体のまとめ
-- ════════════════════════════════════════════════════════════

/-!
  本ファイルで L9 の主張群が完成した:

  **Theorem D (Different Bound)** — 本ファイル §3
    d(upperNumberingTower, ramificationTower) ≤ Φ(N) − N
    = Σ_{i=1}^{N}(gs(i) − 1)（different の wild 部分の離散版）。
    ε = 0 の系として「gs ≡ 1 ⟹ 上付 = 下付」。

  **Theorem E-2 (Index Reverse Mathematics, II)** — 本ファイル §5
    char-rank の存在が全網羅的塔で保証される
    ⟺ ι の非空上方集合がすべて最小元を持つ。

  添字逆数学プログラムの現在地:

    定理    塔の性質      ⟺  添字順序の性質         ℕ   ℕ×ℕ  ℝ
    ──────────────────────────────────────────────────────────
    E       rank 一意性   ⟺  反対称性               ✓    ✓    ✓
    E-2     rank 存在     ⟺  非空上方集合が単項      ✓    ✗    ✗
    ──────────────────────────────────────────────────────────

  読み取れること:
  - 多重パラメータ添字（ℕ×ℕ）で壊れるのは一意性ではなく存在。
    これが「多重パラメータ persistence に完全離散不変量がない」
    現象の、塔理論における正確な位置である。
  - ℝ でも存在が壊れる。ℝ 添字の理論（TDA・付値論の連続版）が
    rank/barcode ではなく interleaving 距離（L9 定理 I）を
    基本装置とせざるを得ない理由の順序論的説明。
  - ℕ の特権性の正体は「非空上方集合が単項」という
    強い条件（全順序性 + 上方閉集合の整礎性）である。

  次の候補（E-3 以降）:
  - gradedPiece の標準性 ⟺ 後続者構造（SuccOrder）— L8 接続
  - 完備化の存在 ⟺ 可算共終性 — L6 接続
  - E-2 の右辺条件の内在的特徴付け
    （全順序 + 上方整礎 との同値の形式化）
-/

end BourbakiGuide
