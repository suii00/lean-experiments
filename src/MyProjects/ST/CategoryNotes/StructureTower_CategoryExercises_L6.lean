/-
  StructureTower 発展演習（レベル6）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル6（完備化・統合）
  前提: Level 1-5 を完了していること

  動機:
    L5 で idealPowTower I : StructureTower ℕᵒᵈ R を構成し、
    L1-L4 の全構造が一つの canonical example に合流することを実証した。
    Level 6 ではその先——**I-adic 完備化**を StructureTower の言語で記述し、
    Cauchy 列 → null 列 → 商 → 完備化の普遍性 → ClosedTower
    という可換環論の中核パイプラインを段階的に構築する。

    I-adic 完備化は Bourbaki の母構造の精神に忠実な例:
      順序構造（ℕᵒᵈ 添字の塔）＋代数構造（環の Cauchy 列）＋
      位相構造（I-adic 位相の完備性）
    が一つの構成に統合される。

  核心的洞察:
    Cauchy 列の「速さ」を StructureTower のレベルとして捉える:
      level k = {x : ℕ → R | ∀ m n, x m - x n ∈ I^(min m n + k)}
    k が大きいほど条件が厳しい → ℕᵒᵈ で添字化すると減少的。
    これにより Cauchy 列の空間自体が StructureTower になり、
    null 列は global に対応し、完備化は分離条件の具現化となる。

  学習の流れ:
    §L6-1. Cauchy 列の塔的定義     — (ℕ → R) 上の StructureTower
    §L6-2. null 列と同値関係        — global と setoid の対応
    §L6-3. 完備化の普遍性           — ι : R →+* R̂ と ringHom_towerHom
    §L6-4. 完備塔と ClosedTower     — idealPowTower (Ideal.map ι I)

  ヒントの読み方:
    Hint-1: 大まかな方針
    Hint-2: 使うべき補題やタクティク
    Hint-3: ほぼ答え
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Algebra
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

def NatInclusion (T₁ T₂ : StructureTower ι α) : Prop :=
  ∀ i, T₁.level i ⊆ T₂.level i

-- ClosedTower (L3)
variable (cl : ClosureOperator (Set α))

def liftCl (T : StructureTower ι α) : StructureTower ι α where
  level i := cl (T.level i)
  monotone_level := by
    intro i j hij x hx
    exact cl.monotone (T.monotone_level hij) hx

structure ClosedTower (cl : ClosureOperator (Set α)) (ι : Type*) [Preorder ι]
    extends StructureTower ι α where
  level_closed : ∀ i, cl (level i) = level i

namespace ClosedTower

variable {cl : ClosureOperator (Set α)}

theorem cl_global_subset (T : ClosedTower cl ι) :
    cl T.global ⊆ T.global := by
  intro x hx
  apply Set.mem_iInter.mpr
  intro i
  have h1 : cl T.global ⊆ cl (T.level i) :=
    cl.monotone (fun y hy => Set.mem_iInter.mp hy i)
  exact T.level_closed i ▸ (h1 hx)

end ClosedTower

-- L5 definitions
variable {R : Type*} [CommRing R]

def idealPowTower (I : Ideal R) : StructureTower ℕᵒᵈ R where
  level n := ↑(I ^ OrderDual.ofDual n)
  monotone_level := by
    intro i j hij x hx
    exact
      (Ideal.pow_le_pow_right (I := I)
        (m := OrderDual.ofDual j) (n := OrderDual.ofDual i)
        (OrderDual.ofDual_le_ofDual.mpr hij)) hx

@[simp] theorem idealPowTower_level (I : Ideal R) (n : ℕᵒᵈ) :
    (idealPowTower I).level n = ↑(I ^ OrderDual.ofDual n) := rfl

noncomputable def idealClosure : ClosureOperator (Set R) where
  toFun := fun S => ↑(Ideal.span S)
  monotone' := by intro S T h; exact Ideal.span_mono h
  le_closure' := by intro S; exact Ideal.subset_span
  idempotent' := by
    intro S
    exact
      congrArg (fun J : Ideal R => (J : Set R)) (Ideal.span_eq (Ideal.span S))

theorem idealClosure_fixed_of_ideal (J : Ideal R) :
    idealClosure (R := R) (↑J : Set R) = ↑J := by
  change (↑(Ideal.span (↑J : Set R)) : Set R) = ↑J
  exact
    congrArg (fun K : Ideal R => (K : Set R)) (Ideal.span_eq J)

def idealPowTower_closedTower (I : Ideal R) :
    ClosedTower (idealClosure (R := R)) ℕᵒᵈ where
  level := (idealPowTower I).level
  monotone_level := (idealPowTower I).monotone_level
  level_closed := by
    intro n
    exact idealClosure_fixed_of_ideal (I ^ OrderDual.ofDual n)

theorem ringHom_idealPow_le {S : Type*} [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : Ideal.map φ I ≤ J) (n : ℕ) :
    Ideal.map φ (I ^ n) ≤ J ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono hIJ n

def ringHom_towerHom {S : Type*} [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : Ideal.map φ I ≤ J) :
    Hom (idealPowTower I) (idealPowTower J) where
  toFun := φ
  preserves := by
    intro n x hx
    have h1 : φ x ∈ Ideal.map φ (I ^ OrderDual.ofDual n) :=
      Ideal.mem_map_of_mem φ hx
    exact ringHom_idealPow_le φ I J hIJ (OrderDual.ofDual n) h1

def IsSeparated (I : Ideal R) : Prop :=
  ⨅ n, I ^ n = ⊥

theorem isSeparated_iff_global_eq (I : Ideal R) :
    IsSeparated I ↔ (idealPowTower I).global = {(0 : R)} := by
  have hglobal :
      (idealPowTower I).global = (↑(⨅ n : ℕ, I ^ n) : Set R) := by
    ext x
    simp [StructureTower.global, idealPowTower, Submodule.coe_iInf]
  constructor
  · intro h
    rw [hglobal, h]
    simp [Submodule.bot_coe]
  · intro h
    rw [hglobal] at h
    exact SetLike.coe_injective (by simpa [Submodule.bot_coe] using h)

theorem isHausdorff_of_isSeparated (I : Ideal R) (hI : IsSeparated I) :
    IsHausdorff I R := by
  rw [isHausdorff_iff]
  intro x hx
  by_contra hne
  have hx' : x ∈ (⨅ n : ℕ, I ^ n : Ideal R) := by
    rw [Submodule.mem_iInf]
    intro n
    simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx n
  rw [hI] at hx'
  exact hne (by simpa using hx')

theorem isSeparated_of_isHausdorff (I : Ideal R) [hI : IsHausdorff I R] :
    IsSeparated I := by
  refine eq_bot_iff.2 ?_
  intro x hx
  change x = 0
  apply IsHausdorff.haus hI x
  intro n
  rw [Submodule.mem_iInf] at hx
  simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx n

theorem escape_of_isSeparated (I : Ideal R) (hI : IsSeparated I)
    {x : R} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∉ (I ^ n : Ideal R) := by
  classical
  by_contra h
  push_neg at h
  have : x ∈ (⨅ n, I ^ n : Ideal R) := by
    rw [Submodule.mem_iInf]; exact h
  rw [hI] at this
  exact hx (by simpa using this)

-- ════════════════════════════════════════════════════════════
-- §L6-1. Cauchy 列の塔的定義  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  I-adic Cauchy 列を StructureTower の言語で記述する。

  古典的定義:
    列 x : ℕ → R が I-adic Cauchy ⟺ ∀ k, ∃ N, ∀ m n ≥ N, x m - x n ∈ I^k

  しかし StructureTower で「速さ」を階層化するには、条件の強さを
  パラメータ化するのが自然:
    level k = {x : ℕ → R | ∀ m n, x m - x n ∈ I^(min m n + k)}

  ℕᵒᵈ 添字の意味:
    - k = 0 → x m - x n ∈ I^(min m n)   （最も緩い）
    - k が大きい → 条件が厳しい（「速い」Cauchy 列）
    - ℕᵒᵈ で添字すると、厳しい条件ほど小さいレベル → 減少族 → 増加族

  これは L5-1a の idealPowTower と同じ ℕᵒᵈ パターン。
  関数空間 (ℕ → R) 上の StructureTower として構成する。
-/

section CauchyTower

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟢 Exercise L6-1a: I-adic Cauchy 列の定義。
    列 x : ℕ → R が I-adic Cauchy であるとは、
    任意の m, n に対して x m - x n ∈ I^(min m n) が成り立つこと。

    注: ここでは「古典的な ∃ N 型」ではなく、「一様型」を採用する。
    これは StructureTower のレベル 0 に対応する。 -/
def IsIAdicCauchy (x : ℕ → R) : Prop :=
  ∀ m n, x m - x n ∈ I ^ (min m n)

/-- 🟢 Exercise L6-1b: Cauchy 列の塔。
    level (toDual k) = {x : ℕ → R | ∀ m n, x m - x n ∈ I^(min m n + k)}。
    k が大きいほど条件が厳しい → ℕᵒᵈ で添字化すると増加的。

    単調性の鍵:
      i ≤ j in ℕᵒᵈ ⟺ ofDual j ≤ ofDual i in ℕ
      ⟹ min m n + ofDual i ≥ min m n + ofDual j
      ⟹ I^(min m n + ofDual i) ≤ I^(min m n + ofDual j)
      ⟹ level i ⊆ level j  ✓

    Hint-1: Ideal.pow_le_pow_right で冪の単調性。
    Hint-2: i ≤ j in ℕᵒᵈ → ofDual j ≤ ofDual i を使う。
    Hint-3: `intro i j hij x hx m n;
             exact Ideal.pow_le_pow_right
               (Nat.add_le_add_left (OrderDual.ofDual_le_ofDual.mpr hij) _) (hx m n)` -/
def cauchySeqTower : StructureTower ℕᵒᵈ (ℕ → R) where
  level k := {x : ℕ → R | ∀ m n, x m - x n ∈ I ^ (min m n + OrderDual.ofDual k)}
  monotone_level := by
    intro i j hij x hx m n
    exact Ideal.pow_le_pow_right
      (Nat.add_le_add_left (OrderDual.ofDual_le_ofDual.mpr hij) _) (hx m n)

@[simp] theorem cauchySeqTower_level (k : ℕᵒᵈ) :
    (cauchySeqTower I).level k =
      {x : ℕ → R | ∀ m n, x m - x n ∈ I ^ (min m n + OrderDual.ofDual k)} := rfl

/-- 🟢 Exercise L6-1c: level 0 と IsIAdicCauchy の一致。
    level (toDual 0) の元は IsIAdicCauchy そのもの。
    min m n + 0 = min m n なので自明。

    Hint-1: simp で min m n + 0 = min m n を処理。
    Hint-2: `ext x; simp [cauchySeqTower, IsIAdicCauchy]`
    Hint-3: そのまま。 -/
theorem cauchySeqTower_level_zero :
    (cauchySeqTower I).level (OrderDual.toDual 0) =
      {x : ℕ → R | IsIAdicCauchy I x} := by
  ext x
  simp [cauchySeqTower, IsIAdicCauchy]

/-- 🟡 Exercise L6-1d: 定数列は Cauchy。
    x = fun _ => r は任意のレベルに属する（x m - x n = 0 ∈ I^k）。
    これは L5-1b（idealPowTower_top_level）の函数空間版。

    Hint-1: fun _ => r の差は 0。
    Hint-2: sub_self + Ideal.zero_mem。
    Hint-3: `intro k m n; simp [Ideal.zero_mem]` -/
theorem const_mem_cauchySeqTower (r : R) (k : ℕᵒᵈ) :
    (fun _ : ℕ => r) ∈ (cauchySeqTower I).level k := by
  intro m n
  simp

/-- 🟡 Exercise L6-1e: Cauchy 列の和は Cauchy。
    x, y ∈ level k ⟹ x + y ∈ level k。
    (x + y) m - (x + y) n = (x m - x n) + (y m - y n)
    で、両方 I^(min m n + k) に属するからその和も。

    これは cauchySeqTower が FilteredAddCommMonoid の構造を
    持つことの第一歩（L5-1c の乗法互換性に対応する加法版）。

    Hint-1: Pi.add_apply で成分ごとに展開。
    Hint-2: Ideal.add_mem で和の帰属。
    Hint-3: `intro m n; show (x + y) m - (x + y) n ∈ _;
             ring_nf; exact Ideal.add_mem _ (hx m n) (hy m n)` -/
theorem cauchySeqTower_add_mem (k : ℕᵒᵈ) {x y : ℕ → R}
    (hx : x ∈ (cauchySeqTower I).level k)
    (hy : y ∈ (cauchySeqTower I).level k) :
    (x + y) ∈ (cauchySeqTower I).level k := by
  intro m n
  show (x + y) m - (x + y) n ∈ _
  have hxy : (x + y) m - (x + y) n = (x m - x n) + (y m - y n) := by
    calc
      (x + y) m - (x + y) n = (x m + y m) - (x n + y n) := by rfl
      _ = (x m - x n) + (y m - y n) := by ring
  rw [hxy]
  exact Ideal.add_mem _ (hx m n) (hy m n)

/-- 🔴 Exercise L6-1f: Cauchy 列に定数を掛けても Cauchy。
    r ∈ R, x ∈ level k ⟹ (r • x) ∈ level k。
    (r * x) m - (r * x) n = r * (x m - x n) で、
    I^k は R-加群なので r * (I^k の元) ∈ I^k。

    これは cauchySeqTower が R-加群フィルトレーションの
    構造を持つことの確認。

    Hint-1: Pi.smul_apply で成分ごとに展開。
    Hint-2: Ideal.mul_mem_left で r * (x m - x n) ∈ I^k。
    Hint-3: `intro m n; show r * x m - r * x n ∈ _;
             rw [← mul_sub]; exact Ideal.mul_mem_left _ r (hx m n)` -/
theorem cauchySeqTower_smul_mem (k : ℕᵒᵈ) (r : R) {x : ℕ → R}
    (hx : x ∈ (cauchySeqTower I).level k) :
    (fun n => r * x n) ∈ (cauchySeqTower I).level k := by
  intro m n
  show r * x m - r * x n ∈ _
  rw [← mul_sub]
  exact Ideal.mul_mem_left _ r (hx m n)

end CauchyTower

-- ════════════════════════════════════════════════════════════
-- §L6-2. null 列と同値関係  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  I-adic null 列: x n → 0 in the I-adic topology。
    IsIAdicNull I x := ∀ k, ∃ N, ∀ n ≥ N, x n ∈ I^k

  null 列は cauchySeqTower I の **global** に密接に関連する。
  StructureTower の語彙では:
    null 列 ≈ 「すべてのレベルに eventually 属する列」
    global  = 「すべてのレベルに属する列」（without "eventually"）

  同値関係: x ~ y ⟺ x - y が null 列。
  これにより完備化 R̂ = {Cauchy 列} / {null 列} が得られる。

  L5-4b の IsSeparated 条件との合流:
    R が I-adic 分離的 ⟺ 定数 null 列は零列のみ
    ⟹ ι : R → R̂ が単射
-/

section NullSequences

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟢 Exercise L6-2a: I-adic null 列の定義。
    列 x が null ⟺ ∀ k, ∃ N, ∀ n ≥ N, x n ∈ I^k。
    直感: x n が I-adic 位相で 0 に収束する。 -/
def IsIAdicNull (x : ℕ → R) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ I ^ k

/-- 🟢 Exercise L6-2b: 零列は null。
    x = 0 のとき、x n = 0 ∈ I^k for all n。

    Hint-1: 0 は任意のイデアルの元。
    Hint-2: `intro k; exact ⟨0, fun n _ => Ideal.zero_mem _⟩`
    Hint-3: そのまま。 -/
theorem isIAdicNull_zero : IsIAdicNull I (0 : ℕ → R) := by
  intro k
  exact ⟨0, fun n _ => Ideal.zero_mem _⟩

/-- 🟡 Exercise L6-2c: null 列の和は null。
    x, y が null ⟹ x + y が null。
    ∀ k, ∃ Nx, ∀ n ≥ Nx, x n ∈ I^k
    ∀ k, ∃ Ny, ∀ n ≥ Ny, y n ∈ I^k
    ⟹ N := max Nx Ny として ∀ n ≥ N, (x + y) n = x n + y n ∈ I^k。

    Hint-1: max Nx Ny を N に取る。
    Hint-2: Ideal.add_mem で和の帰属。
    Hint-3: `intro k; obtain ⟨Nx, hx⟩ := hx k; obtain ⟨Ny, hy⟩ := hy k;
             exact ⟨max Nx Ny, fun n hn => Ideal.add_mem _
               (hx n (le_of_max_le_left hn)) (hy n (le_of_max_le_right hn))⟩` -/
theorem isIAdicNull_add {x y : ℕ → R}
    (hx : IsIAdicNull I x) (hy : IsIAdicNull I y) :
    IsIAdicNull I (x + y) := by
  intro k
  obtain ⟨Nx, hx⟩ := hx k
  obtain ⟨Ny, hy⟩ := hy k
  exact ⟨max Nx Ny, fun n hn => by
    show x n + y n ∈ _
    exact Ideal.add_mem _
      (hx n (le_trans (le_max_left Nx Ny) hn))
      (hy n (le_trans (le_max_right Nx Ny) hn))⟩

/-- 🟡 Exercise L6-2d: null 列の負は null。
    x が null ⟹ -x が null。
    (-x) n = -(x n) で、I^k は加法群なので -a ∈ I^k。

    Hint-1: Ideal.neg_mem_iff で -(x n) ∈ I^k ↔ x n ∈ I^k。
    Hint-2: `intro k; obtain ⟨N, hN⟩ := hx k;
             exact ⟨N, fun n hn => Ideal.neg_mem_iff.mpr (hN n hn)⟩`
    Hint-3: そのまま。 -/
theorem isIAdicNull_neg {x : ℕ → R}
    (hx : IsIAdicNull I x) :
    IsIAdicNull I (-x) := by
  intro k
  obtain ⟨N, hN⟩ := hx k
  exact ⟨N, fun n hn => by
    show -x n ∈ _
    exact (I ^ k).neg_mem (hN n hn)⟩

/-- 🟡 Exercise L6-2e: I-adic Setoid の構成。
    二つの列 x, y が同値 ⟺ x - y が null。
    これは Setoid (ℕ → R) を定義する:
      - 反射性: x - x = 0 は null（L6-2b）
      - 対称性: x - y が null ⟹ y - x = -(x - y) も null（L6-2d）
      - 推移性: x - y, y - z が null ⟹ x - z = (x - y) + (y - z) も null（L6-2c）

    Hint-1: 三条件を IsIAdicNull の補題で確認。
    Hint-2: sub_self, neg_sub, sub_add_sub_cancel。
    Hint-3: 下記実装参照。 -/
def iadicSetoid : Setoid (ℕ → R) where
  r x y := IsIAdicNull I (x - y)
  iseqv := {
    refl := fun x => by
      show IsIAdicNull I (x - x)
      simp [isIAdicNull_zero I]
    symm := fun {x y} hxy => by
      show IsIAdicNull I (y - x)
      have : y - x = -(x - y) := by ring
      rw [this]
      exact isIAdicNull_neg I hxy
    trans := fun {x y z} hxy hyz => by
      show IsIAdicNull I (x - z)
      have : x - z = (x - y) + (y - z) := by ring
      rw [this]
      exact isIAdicNull_add I hxy hyz
  }

/-- 🔴 Exercise L6-2f: 分離条件と null 定数列の対応。
    IsSeparated I のとき、定数列 (fun _ => r) が null ⟺ r = 0。
    これは L5-4b の「global = {0}」の函数空間版。

    直感: 分離的 ⟺ I-adic 位相が T₁ ⟺ 定数列で 0 に収束するのは 0 だけ。
    等価的に: ι : R → R̂ が単射。

    Hint-1: (→) r ∈ I^k for all k → r ∈ ⋂ I^k = {0}。
    Hint-2: (←) r = 0 のとき自明。
    Hint-3: `constructor;
             · intro h; by_contra hr; exact escape_of_isSeparated I hI hr (全k帰属);
             · intro h; subst h; simpa using isIAdicNull_zero I` -/
theorem isIAdicNull_const_iff_of_separated (hI : IsSeparated I) (r : R) :
    IsIAdicNull I (fun _ => r) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    obtain ⟨n, hn⟩ := escape_of_isSeparated I hI hr
    obtain ⟨N, hN⟩ := h n
    have : r ∈ I ^ n := by simpa using hN N le_rfl
    exact hn this
  · intro h
    subst h
    simpa using isIAdicNull_zero I

end NullSequences

-- ════════════════════════════════════════════════════════════
-- §L6-3. 完備化の普遍性  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  Mathlib の I-adic 完備化:
    R̂ := AdicCompletion I R
    ι := algebraMap R R̂ : R →+* R̂

  完備化 R̂ にも idealPowTower を適用できる:
    R̂ 上のイデアル J := Ideal.map ι I に対し、
    idealPowTower J : StructureTower ℕᵒᵈ R̂

  ι は「idealPowTower I → idealPowTower (Ideal.map ι I)」の Hom を誘導する。
  これは L5-3b の ringHom_towerHom パターンの canonical 適用:
    φ = ι, J = Ideal.map ι I, hIJ = le_refl (Ideal.map ι I)。

  普遍性:
    任意の環準同型 φ : R →+* S で I-adic 完備な S への写像が、
    R̂ を経由して一意に分解する。
    StructureTower の言語では: φ が誘導する towerHom は ι を経由する。
-/

section Completion

variable {R : Type*} [CommRing R] (I : Ideal R)

-- 便利な略記
-- noncomputable は AdicCompletion が逆極限構成で定義されるため
noncomputable abbrev completionRing := AdicCompletion I R
noncomputable abbrev completionMap : R →+* completionRing I :=
  algebraMap R (completionRing I)

-- 完備化上のイデアル: I の ι による像
noncomputable abbrev completionIdeal : Ideal (completionRing I) :=
  Ideal.map (completionMap I) I

/-- 🟢 Exercise L6-3a: 完備化塔の構成。
    R̂ 上の idealPowTower (Î) を構成する。
    これは ι(I) = Î による I-adic tower を完備化側で展開したもの。

    L5-1a と同じ定義パターン。型が変わるだけ。 -/
noncomputable def completionPowTower :
    StructureTower ℕᵒᵈ (completionRing I) :=
  idealPowTower (completionIdeal I)

@[simp] theorem completionPowTower_level (n : ℕᵒᵈ) :
    (completionPowTower I).level n =
      ↑((completionIdeal I) ^ OrderDual.ofDual n) := rfl

/-- 🟡 Exercise L6-3b: ι が tower hom を誘導する。
    ι : R →+* R̂ は idealPowTower I → completionPowTower I の Hom。
    これは L5-3b の ringHom_towerHom の直接適用。

    条件: Ideal.map ι I ≤ Î = Ideal.map ι I なので le_refl。

    Hint-1: ringHom_towerHom (completionMap I) I (completionIdeal I) le_rfl。
    Hint-2: そのまま。
    Hint-3: `ringHom_towerHom (completionMap I) I (completionIdeal I) le_rfl` -/
noncomputable def completion_towerHom :
    Hom (idealPowTower I) (completionPowTower I) :=
  ringHom_towerHom (completionMap I) I (completionIdeal I) le_rfl

/-- 🟢 Exercise L6-3c: completion_towerHom の toFun は ι そのもの。
    構成から明らかだが、明示的に確認する。

    Hint-1: 定義の展開のみ。
    Hint-2: rfl。 -/
theorem completion_towerHom_toFun :
    (completion_towerHom I).toFun = completionMap I := rfl

/-- 🟡 Exercise L6-3d: 合成の互換性（L5-3d の拡張）。
    φ : R →+* S, ψ : S →+* R̂ に対して、
    completion_towerHom と ringHom_towerHom の合成が
    (ψ ∘ φ) による towerHom と一致する。

    これは L5-3d の ringHom_towerHom_comp パターンの具体化:
    完備化写像 ι を経由する合成が自然に commute する。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: 両辺の toFun は (completionMap I) ∘ φ。
    Hint-3: `Hom.ext rfl` -/
theorem completion_towerHom_comp {S : Type*} [CommRing S]
    (φ : S →+* R) (J : Ideal S) (hIJ : Ideal.map φ J ≤ I) :
    Hom.comp (completion_towerHom I) (ringHom_towerHom φ J I hIJ) =
    ringHom_towerHom ((completionMap I).comp φ) J (completionIdeal I)
      (by
        calc Ideal.map ((completionMap I).comp φ) J
            = Ideal.map (completionMap I) (Ideal.map φ J) := by rw [Ideal.map_map]
          _ ≤ Ideal.map (completionMap I) I := Ideal.map_mono hIJ) := by
  exact Hom.ext rfl

/-- 🔴 Exercise L6-3e: 分離条件下での ι の単射性（statement）。
    IsSeparated I のとき、ι : R → R̂ は単射。
    StructureTower の言語: completion_towerHom I は
    各レベルで単射的（toFun が全体として単射）。

    これは L5-4c（escape_of_isSeparated）の帰結:
    分離的 ⟺ ker ι = ⋂ Iⁿ = {0} ⟺ ι 単射。

    注: `IsSeparated` から `IsHausdorff` を作り、Mathlib の標準定理を使う。

    Hint-1: `isHausdorff_of_isSeparated`。
    Hint-2: `AdicCompletion.of_injective`。
    Hint-3: `completionMap` と `AdicCompletion.of` は同じ埋め込み。 -/
theorem completion_towerHom_injective_of_separated
    (hI : IsSeparated I) :
    Function.Injective (completionMap I) := by
  let _ : IsHausdorff I R := isHausdorff_of_isSeparated I hI
  intro x y hxy
  have hxy' : AdicCompletion.of I R x = AdicCompletion.of I R y := by
    simpa only [completionMap, completionRing] using hxy
  exact (AdicCompletion.of_inj (I := I) (M := R)).mp hxy'

end Completion

-- ════════════════════════════════════════════════════════════
-- §L6-4. 完備塔と ClosedTower  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  完備化 R̂ 上の idealPowTower (Î) は ClosedTower の構造を持つ。
  これは L5-2c（idealPowTower_closedTower）の完備化版。

  さらに、完備塔は以下を同時に満たす「最良の塔」:
    ✓ StructureTower ℕᵒᵈ R̂
    ✓ ClosedTower idealClosure
    ✓ IsSeparated（完備化は自動的に分離的）
    ✓ I-adic 完備性（Cauchy 列が収束する）

  L5 までの全条件が完備化で「最良の形」で実現される。
  Bourbaki の完備化の普遍性: R̂ は I-adic で分離的かつ完備な、
  R からの環の中で「最小の」もの。
-/

section CompletionClosedTower

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟢 Exercise L6-4a: 完備化塔は ClosedTower。
    completionPowTower I = idealPowTower (Î I) は
    idealClosure (on R̂) の不動点族である。
    これは L5-2c の idealPowTower_closedTower を R̂ に適用したもの。

    Hint-1: idealPowTower_closedTower (Î I) を使う。
    Hint-2: そのまま。 -/
noncomputable def completionPowTower_closedTower :
    ClosedTower (idealClosure (R := completionRing I)) ℕᵒᵈ :=
  idealPowTower_closedTower (completionIdeal I)

/-- 🟡 Exercise L6-4b: 完備化の分離性（statement）。
    R̂ は Î-adic に分離的: ⋂ₙ (Î)ⁿ = ⊥。

    直感: 完備化は「十分に分離している」ことが保証される。
    L5-4b の IsSeparated が完備化側で自動的に成立する。

    注: Mathlib は `AdicCompletion` に対し Hausdorff 性を既に与えている。

    Hint-1: `IsHausdorff.map_algebraMap_iff`。
    Hint-2: `isSeparated_of_isHausdorff`。
    Hint-3: completion ideal にそのまま適用。 -/
theorem completionPowTower_isSeparated :
    IsSeparated (completionIdeal I) := by
  let _ : IsHausdorff (completionIdeal I) (completionRing I) :=
    (IsHausdorff.map_algebraMap_iff (I := I) (S := completionRing I)).2
      (inferInstance : IsHausdorff I (completionRing I))
  exact isSeparated_of_isHausdorff (completionIdeal I)

/-- 🟡 Exercise L6-4c: 完備化の global は {0}。
    completionPowTower_isSeparated から直ちに従う。
    L5-4b の isSeparated_iff_global_eq の完備化版。

    Hint-1: IsSeparated → global = {0} は L5-4b と同じ論理。
    Hint-2: completionPowTower_isSeparated を使う。
    Hint-3: `isSeparated_iff_global_eq` に帰着。 -/
theorem completionPowTower_global_singleton :
    (completionPowTower I).global = {(0 : completionRing I)} := by
  simpa [completionPowTower] using
    (isSeparated_iff_global_eq (completionIdeal I)).mp
      (completionPowTower_isSeparated I)

/-- 🔴 Exercise L6-4d: 非零元の完備化版脱出定理。
    R̂ で x ≠ 0 ⟹ ∃ n, x ∉ (Î)ⁿ。
    これは L5-4c（escape_of_isSeparated）の R̂ 版。

    直感: 完備化が分離的であることの直接的帰結。
    零でない元は有限段で I-adic tower から脱出する。

    Hint-1: completionPowTower_isSeparated + escape_of_isSeparated。
    Hint-2: `escape_of_isSeparated (completionIdeal I) (completionPowTower_isSeparated I) hx`
    Hint-3: 直接適用で終わる。 -/
theorem escape_of_completion {x : completionRing I} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∉ ((completionIdeal I) ^ n : Ideal (completionRing I)) := by
  exact escape_of_isSeparated (completionIdeal I) (completionPowTower_isSeparated I) hx

/-- 🔴 Exercise L6-4e: 完備化の ClosedTower global の閉性。
    completionPowTower が ClosedTower であることから、
    global は idealClosure で閉じている。
    L5-2d の idealPow_global_closed の完備化版。

    これと completionPowTower_global_singleton を合わせると:
    idealClosure {0} ⊆ {0}、つまり {0} が idealClosure の不動点
    であることの確認（自明だが、枠組みの整合性の検証）。

    Hint-1: ClosedTower.cl_global_subset を使う。
    Hint-2: `(completionPowTower_closedTower I).cl_global_subset`
    Hint-3: そのまま。 -/
theorem completionPow_global_closed :
    idealClosure (R := completionRing I) (completionPowTower I).global ⊆
      (completionPowTower I).global :=
  (completionPowTower_closedTower I).cl_global_subset

end CompletionClosedTower

-- ════════════════════════════════════════════════════════════
-- §Summary. Level 6 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  Level 6 で確認したこと:

  §L6-1 **Cauchy 列の塔的定義**:
    cauchySeqTower I : StructureTower ℕᵒᵈ (ℕ → R) として構成。
    level k = {x | ∀ m n, x m - x n ∈ I^(min m n + k)}。
    k = 0 が IsIAdicCauchy。定数列は全レベルに属する。
    加法・スカラー倍の閉性を確認 → FilteredModule の構造。

  §L6-2 **null 列と同値関係**:
    IsIAdicNull I x := ∀ k, ∃ N, ∀ n ≥ N, x n ∈ I^k。
    null 列の加法・負に関する閉性 → iadicSetoid の well-definedness。
    分離条件下で定数 null 列 ⟺ 零列（ι の単射性の根拠）。

  §L6-3 **完備化の普遍性**:
    completionPowTower I = idealPowTower (Ideal.map ι I)。
    ι : R →+* R̂ が completion_towerHom を誘導。
    L5-3b の ringHom_towerHom パターンの canonical 適用。
    合成の互換性、分離条件下での単射性。

  §L6-4 **完備塔と ClosedTower**:
    completionPowTower は idealClosure に関する ClosedTower。
    R̂ は Î-adic に分離的（global = {0}）。
    脱出定理の完備化版。
    global の閉性定理の完備化版。

  ──────────────────────────────────────────────
  L1-L6 を通じた全体の合流:

    条件                    L5 での確認       L6 での発展
    ──────────────────────────────────────────────────────
    StructureTower           L5-1a（R 上）     L6-1b（ℕ→R 上）, L6-3a（R̂ 上）
    乗法互換 (mul_mem)       L5-1c             L6-1e/f（Cauchy 列の加法/スカラー）
    ClosedTower              L5-2c             L6-4a（完備化版）
    cl_global_subset         L5-2d             L6-4e（完備化版）
    環準同型 → Hom           L5-3b             L6-3b（ι による towerHom）
    分離条件                 L5-4b             L6-4b（R̂ は自動分離）
    脱出定理                 L5-4c             L6-4d（完備化版脱出）
    Krull 交叉               L5-4e             L6-4c（global = {0} の直接確認）

  ──────────────────────────────────────────────
  次のステップ候補（Level 7 以降）:

    1. **Cauchy 列の収束と完備性**:
       cauchySeqTower I の元が R̂ 上で収束することを示す。
       逆極限 lim R/Iⁿ との同型を構成し、
       StructureTower としての同値性を確認する。

    2. **Rees 代数と次数付き構造**:
       ⊕ₙ Iⁿtⁿ を StructureTower の直和として記述。
       次数環 (graded ring) と StructureTower の「次数付き射」の関係。

    3. **Mathlib CategoryTheory.Monad との正式接続**:
       idealClosure の ClosedTower が CategoryTheory.Monad.Algebra と
       同型であることを形式的に証明する。
       L3 のモナド法則の Category Theory 版への橋渡し。
  ──────────────────────────────────────────────
-/

-- ════════════════════════════════════════════════════════════
-- 検証コマンド:
--   lake env lean StructureTower_CategoryExercises_L6.lean
--   lake build BourbakiGuide.StructureTower
-- ════════════════════════════════════════════════════════════

end StructureTower

end BourbakiGuide
