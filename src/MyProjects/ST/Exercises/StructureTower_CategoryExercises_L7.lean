/-
  StructureTower 発展演習（レベル7）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル7（Rees 代数・次数付き構造）
  前提: Level 1-6 を完了していること

  動機:
    L5 で idealPowTower I : StructureTower ℕᵒᵈ R を構成し、
    L6 で完備化 R̂ 上に completionPowTower を構成した。
    これらは I-adic filtration の「内部的」な見方である:
    R の中で I⁰ ⊇ I ⊇ I² ⊇ ... と縮小していく族。

    Level 7 では **外部的** な見方を提供する:
    **Rees 代数** R[It] = ⊕ₙ Iⁿtⁿ ⊂ R[t] を StructureTower の言語で記述する。

    idealPowTower は ℕᵒᵈ 添字（減少族）だったが、
    Rees 塔は **ℕ 添字（増加族）** ── 次数が上がるほどレベルが大きくなる。
    これは StructureTower プロジェクトで初めての「自然な ℕ 添字」の例であり、
    idealPowTower との双対性が理論の深みを示す。

  核心的洞察:
    Rees 代数の元は「各次数 k の係数が I^k に属する多項式」:
      R[It] = {p ∈ R[t] | ∀ k, coeff p k ∈ I^k}

    これを StructureTower として構成するには、次数による切断を使う:
      level n = {p ∈ R[t] | ∀ k, coeff p k ∈ I^k, かつ deg p ≤ n}
    n が大きいほど「高次の項まで許容する」→ 増加族 → ℕ 添字。

    乗法互換性: p ∈ level m, q ∈ level n ⟹ p * q ∈ level (m + n)
    これは多項式の積の畳み込み公式と I^a · I^b ⊆ I^(a+b) から従う。
    L5-1c の idealPow_mul_mem の「外部化」である。

  学習の流れ:
    §L7-1. Rees 塔の基盤             — R[X] 上の StructureTower ℕ
    §L7-2. 乗法互換性と次数付き構造   — FilteredRing としての Rees 塔
    §L7-3. idealPowTower との双対性   — 係数抽出と単項式埋め込み
    §L7-4. Mathlib reesAlgebra との接続 — union = reesAlgebra, 安定条件

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
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Find

open Set Function Polynomial

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

theorem idealPow_mul_mem (I : Ideal R) (m n : ℕ) {x y : R}
    (hx : x ∈ I ^ m) (hy : y ∈ I ^ n) :
    x * y ∈ I ^ (m + n) := by
  simpa [pow_add] using Ideal.mul_mem_mul hx hy

-- ════════════════════════════════════════════════════════════
-- §L7-1. Rees 塔の基盤  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  Rees 代数の元を StructureTower の言語で定義する。

  古典的定義:
    R[It] = {p ∈ R[t] | ∀ k, coeff p k ∈ I^k}
  これは R[t] の部分代数（Subalgebra）である。

  StructureTower としての構成:
    次数による切断で増加族を作る:
      level n = {p : R[X] | (∀ k, coeff p k ∈ I^k) ∧ (∀ k, n < k → coeff p k = 0)}

  ℕ 添字の意味:
    - level 0 = {定数多項式 C r | r ∈ I⁰ = R} = C '' R
    - level 1 = {a₀ + a₁X | a₀ ∈ R, a₁ ∈ I}
    - level n = {a₀ + a₁X + ... + aₙXⁿ | aₖ ∈ Iᵏ for all k ≤ n}
    n が大きいほど多くの多項式が含まれる → 増加族 → ℕ 添字。

  L5-1a の idealPowTower が ℕᵒᵈ 添字（内部的・縮小族）だったのに対し、
  Rees 塔は ℕ 添字（外部的・拡大族）── 同じ I-adic 構造の双対的な見方。
-/

section ReesTower

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟢 Exercise L7-1a: Rees 元の定義。
    多項式 p : R[X] が Rees 元であるとは、
    各次数 k の係数が I^k に属すること。

    直感: p = a₀ + a₁t + a₂t² + ... で aₖ ∈ Iᵏ。
    これは「各次数の係数がそのべき乗イデアルに属する」条件。 -/
def IsReesElement (p : R[X]) : Prop :=
  ∀ k : ℕ, p.coeff k ∈ I ^ k

/-- 🟢 Exercise L7-1b: Rees 塔の構成。
    level n = {p : R[X] | IsReesElement かつ 次数 ≤ n}。
    次数条件は「k > n ⟹ coeff p k = 0」で表現する。

    単調性の鍵:
      n ≤ m ⟹ {deg ≤ n} ⊆ {deg ≤ m}
      Rees 条件は n に依存しない → level n ⊆ level m  ✓

    注: これは ℕ 添字（非双対）の StructureTower。
    L5 の idealPowTower (ℕᵒᵈ) との双対関係は §L7-3 で形式化する。

    Hint-1: 二条件の組 (Rees 元, 次数制限) で定義。
    Hint-2: 単調性は次数条件の緩和による。
    Hint-3: `intro i j hij p ⟨hR, hD⟩;
             exact ⟨hR, fun k hk => hD k (lt_of_le_of_lt hij hk)⟩` -/
def reesDegreeTower : StructureTower ℕ (R[X]) where
  level n := {p : R[X] | IsReesElement I p ∧ ∀ k, n < k → p.coeff k = 0}
  monotone_level := by
    intro i j hij p ⟨hR, hD⟩
    exact ⟨hR, fun k hk => hD k (lt_of_le_of_lt hij hk)⟩

@[simp] theorem reesDegreeTower_level (n : ℕ) :
    (reesDegreeTower I).level n =
      {p : R[X] | IsReesElement I p ∧ ∀ k, n < k → p.coeff k = 0} := rfl

/-- 🟢 Exercise L7-1c: level 0 は定数 Rees 元。
    level 0 = {C r | r ∈ R} = {定数多項式}。
    k > 0 ⟹ coeff p k = 0 なので p は定数。
    さらに coeff p 0 ∈ I^0 = R は自明。

    Hint-1: C r は coeff (C r) 0 = r, coeff (C r) k = 0 for k > 0。
    Hint-2: ext で集合の等式を元ごとに。
    Hint-3: 順方向は p を C (coeff p 0) に等しいことを示す。 -/
theorem reesDegreeTower_level_zero :
    (reesDegreeTower I).level 0 =
      {p : R[X] | ∃ r : R, p = C r} := by
  ext p
  simp only [reesDegreeTower_level, Set.mem_setOf_eq]
  constructor
  · intro ⟨_, hD⟩
    exact ⟨p.coeff 0, Polynomial.ext (fun k => by
      simp only [Polynomial.coeff_C]
      split_ifs with hk
      · subst hk; rfl
      · exact hD k (by omega))⟩
  · intro ⟨r, hr⟩
    subst hr
    exact ⟨fun k => by
      simp only [Polynomial.coeff_C]
      split_ifs with hk
      · subst hk; simp [Ideal.one_eq_top]
      · exact Ideal.zero_mem _,
    fun k hk => by simp [Polynomial.coeff_C, show k ≠ 0 by omega]⟩

/-- 🟡 Exercise L7-1d: 単項式の埋め込み。
    r ∈ I^n ⟹ C r * X ^ n ∈ level n。
    Rees 塔の各 level が空でないことの証明にもなる。

    直感: aₙtⁿ（単一項の多項式）は Rees 元で次数 = n。

    Hint-1: coeff (C r * X ^ n) k を計算。k = n のとき r、k ≠ n のとき 0。
    Hint-2: Polynomial.coeff_C_mul_X_pow を使う。
    Hint-3: IsReesElement は k = n で r ∈ I^n、k ≠ n で 0 ∈ I^k。
            次数条件は k > n で k ≠ n → coeff = 0。 -/
theorem monomial_mem_reesDegreeTower {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    Polynomial.C r * X ^ n ∈ (reesDegreeTower I).level n := by
  constructor
  · intro k
    simp only [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hk
    · subst hk; exact hr
    · exact Ideal.zero_mem _
  · intro k hk
    simp only [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hk'
    · omega
    · rfl

/-- 🟡 Exercise L7-1e: Rees 塔の加法閉性。
    p, q ∈ level n ⟹ p + q ∈ level n。
    coeff (p + q) k = coeff p k + coeff q k で、
    I^k は加法で閉じているから。

    Hint-1: Polynomial.coeff_add で成分展開。
    Hint-2: Ideal.add_mem で和の帰属。 -/
theorem reesDegreeTower_add_mem (n : ℕ) {p q : R[X]}
    (hp : p ∈ (reesDegreeTower I).level n)
    (hq : q ∈ (reesDegreeTower I).level n) :
    p + q ∈ (reesDegreeTower I).level n := by
  obtain ⟨hpR, hpD⟩ := hp
  obtain ⟨hqR, hqD⟩ := hq
  exact ⟨fun k => by
    simp only [Polynomial.coeff_add]
    exact Ideal.add_mem _ (hpR k) (hqR k),
  fun k hk => by
    simp only [Polynomial.coeff_add, hpD k hk, hqD k hk, add_zero]⟩

/-- 🟡 Exercise L7-1f: 零多項式は全レベルに属する。
    0 ∈ level n for all n。coeff 0 k = 0 ∈ I^k。

    Hint-1: Polynomial.coeff_zero。
    Hint-2: Ideal.zero_mem。 -/
theorem zero_mem_reesDegreeTower (n : ℕ) :
    (0 : R[X]) ∈ (reesDegreeTower I).level n := by
  exact ⟨fun k => by simp, fun k _ => by simp⟩

end ReesTower

-- ════════════════════════════════════════════════════════════
-- §L7-2. 乗法互換性と次数付き構造  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  Rees 塔の核心的性質: 乗法互換性。
    p ∈ level m, q ∈ level n ⟹ p * q ∈ level (m + n)

  多項式の積の k 次係数は:
    coeff (p * q) k = Σ_{i+j=k} (coeff p i) * (coeff q j)

  p が Rees 元 ⟹ coeff p i ∈ I^i
  q が Rees 元 ⟹ coeff q j ∈ I^j
  ⟹ (coeff p i) * (coeff q j) ∈ I^i · I^j ⊆ I^(i+j) = I^k

  Σ は有限和なので、I^k の加法閉性から coeff (p * q) k ∈ I^k。
  次数条件: deg p ≤ m, deg q ≤ n ⟹ deg (p * q) ≤ m + n。

  これは L5-1c の idealPow_mul_mem（I^m · I^n ⊆ I^{m+n}）の
  「多項式的持ち上げ」であり、FilteredRing の mul_mem 公理に対応する。
  Rees 代数が「I-adic filtration の外部的 encode」たる所以。
-/

section ReesMul

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟡 Exercise L7-2a: Rees 元同士の積は Rees 元。
    coeff (p * q) k = Σ_{i+j=k} (coeff p i) * (coeff q j) ∈ I^k。

    証明の骨格:
    1. Polynomial.coeff_mul で畳み込みに展開
    2. Finset.antidiagonal k の各 (i, j) に対して
       coeff p i ∈ I^i, coeff q j ∈ I^j → (coeff p i)(coeff q j) ∈ I^(i+j) = I^k
    3. I^k は加法で閉じている → 有限和 ∈ I^k

    Hint-1: Polynomial.coeff_mul + Ideal.sum_mem。
    Hint-2: Finset.antidiagonal の各 (i, j) で i + j = k を使う。
    Hint-3: `Finset.mem_antidiagonal.mp` で i + j = k を取得。 -/
theorem isReesElement_mul {p q : R[X]}
    (hp : IsReesElement I p) (hq : IsReesElement I q) :
    IsReesElement I (p * q) := by
  intro k
  rw [Polynomial.coeff_mul]
  apply Submodule.sum_mem
  intro ⟨i, j⟩ hij
  have hij' : i + j = k := Finset.mem_antidiagonal.mp hij
  rw [← hij']
  exact idealPow_mul_mem I i j (hp i) (hq j)

/-- 🔴 Exercise L7-2b: Rees 塔の乗法互換性。
    p ∈ level m, q ∈ level n ⟹ p * q ∈ level (m + n)。
    Rees 元条件は L7-2a で確認済み。
    次数条件: k > m + n のとき coeff (p * q) k = 0 を示す。

    鍵: coeff (p * q) k = Σ_{i+j=k} (coeff p i)(coeff q j)。
    k > m + n ⟹ 各 (i, j) で i > m または j > n
    ⟹ coeff p i = 0 or coeff q j = 0
    ⟹ 各項 = 0 ⟹ 和 = 0。

    Hint-1: isReesElement_mul + 次数条件。
    Hint-2: Finset.sum_eq_zero で全項が 0 であることを示す。
    Hint-3: 各 (i, j) ∈ antidiagonal k で i + j = k > m + n だから
            i > m ∨ j > n（鳩の巣原理）。 -/
theorem reesDegreeTower_mul_mem (m n : ℕ) {p q : R[X]}
    (hp : p ∈ (reesDegreeTower I).level m)
    (hq : q ∈ (reesDegreeTower I).level n) :
    p * q ∈ (reesDegreeTower I).level (m + n) := by
  obtain ⟨hpR, hpD⟩ := hp
  obtain ⟨hqR, hqD⟩ := hq
  refine ⟨isReesElement_mul I hpR hqR, fun k hk => ?_⟩
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  have hij' : i + j = k := Finset.mem_antidiagonal.mp hij
  -- i + j = k > m + n なので i > m ∨ j > n（鳩の巣原理）
  by_cases hi : m < i
  · simp [hpD i hi]
  · have hj : n < j := by omega
    simp [hqD j hj]

/-- 🟡 Exercise L7-2c: 1 = C 1 は level 0 の元。
    coeff (C 1) 0 = 1 ∈ I^0 = R。
    coeff (C 1) k = 0 for k > 0。

    FilteredRing の one_mem 条件に対応。

    Hint-1: C 1 は定数多項式。
    Hint-2: Polynomial.coeff_one で展開。 -/
theorem one_mem_reesDegreeTower_zero :
    (1 : R[X]) ∈ (reesDegreeTower I).level 0 := by
  constructor
  · intro k
    simp only [Polynomial.coeff_one]
    split_ifs with hk
    · subst hk; simp [Ideal.one_eq_top]
    · exact Ideal.zero_mem _
  · intro k hk
    simp only [Polynomial.coeff_one]
    split_ifs with hk'
    · omega
    · rfl

/-- 🟡 Exercise L7-2d: 負元の閉性。
    p ∈ level n ⟹ -p ∈ level n。
    coeff (-p) k = -(coeff p k) ∈ I^k。

    Hint-1: Polynomial.coeff_neg。
    Hint-2: Ideal.neg_mem。 -/
theorem neg_mem_reesDegreeTower (n : ℕ) {p : R[X]}
    (hp : p ∈ (reesDegreeTower I).level n) :
    -p ∈ (reesDegreeTower I).level n := by
  obtain ⟨hpR, hpD⟩ := hp
  exact ⟨fun k => by
    simp only [Polynomial.coeff_neg]
    exact (I ^ k).neg_mem (hpR k),
  fun k hk => by
    simp only [Polynomial.coeff_neg, hpD k hk, neg_zero]⟩

/-- 🔴 Exercise L7-2e: R の元によるスカラー倍。
    r ∈ R, p ∈ level n ⟹ C r * p ∈ level n。
    coeff (C r * p) k = r * coeff p k で、
    r ∈ R = I⁰ かつ coeff p k ∈ I^k ⟹ r * coeff p k ∈ I^(0+k) = I^k。

    注: これは「R-代数としてのスカラー倍」であり、
    L6-1f の cauchySeqTower_smul_mem に対応する。

    Hint-1: Polynomial.coeff_C_mul で展開。
    Hint-2: Ideal.mul_mem_left で r * (I^k の元) ∈ I^k。 -/
theorem C_mul_mem_reesDegreeTower (n : ℕ) (r : R) {p : R[X]}
    (hp : p ∈ (reesDegreeTower I).level n) :
    Polynomial.C r * p ∈ (reesDegreeTower I).level n := by
  obtain ⟨hpR, hpD⟩ := hp
  exact ⟨fun k => by
    simp only [Polynomial.coeff_C_mul]
    exact Ideal.mul_mem_left _ r (hpR k),
  fun k hk => by
    simp only [Polynomial.coeff_C_mul, hpD k hk, mul_zero]⟩

end ReesMul

-- ════════════════════════════════════════════════════════════
-- §L7-3. idealPowTower との双対性  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  idealPowTower I（内部的見方）と reesDegreeTower I（外部的見方）を
  具体的な写像で結ぶ。

  係数抽出写像:
    eval_coeff n : R[X] → R,  p ↦ coeff p n
    これは reesDegreeTower I の level n を idealPowTower I の level (toDual n) に写す。

  単項式埋め込み:
    monomial_embed n : R → R[X],  r ↦ C r * X ^ n
    これは I^n の元を reesDegreeTower I の level n に写す。

  合成:
    eval_coeff n ∘ monomial_embed n = id （on I^n）
    つまり「埋め込んで抽出すると元に戻る」── section-retraction の関係。
-/

section Duality

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟢 Exercise L7-3a: 係数抽出は Rees 元を I^n に写す。
    p が Rees 元 ⟹ coeff p n ∈ I^n。
    IsReesElement の定義そのもの。

    Hint-1: IsReesElement の定義を展開するだけ。
    Hint-2: `hp n` -/
theorem coeff_reesElement_mem {p : R[X]} (hp : IsReesElement I p) (n : ℕ) :
    p.coeff n ∈ I ^ n :=
  hp n

/-- 🟡 Exercise L7-3b: 係数抽出は level 保存的（n 次に注目）。
    p ∈ reesDegreeTower I の level m ⟹ coeff p k ∈ I^k for k ≤ m。

    これは「reesDegreeTower I → idealPowTower I」の射の各成分。
    ただし、添字の方向が逆（ℕ vs ℕᵒᵈ）なので、
    直接的な単一の Hom ではなく「射の族」として定式化する。

    Hint-1: Rees 元条件 hp.1 の k 成分。 -/
theorem coeff_reesDegreeTower_mem {m : ℕ} {p : R[X]}
    (hp : p ∈ (reesDegreeTower I).level m) (k : ℕ) (_hk : k ≤ m) :
    p.coeff k ∈ I ^ k :=
  hp.1 k

/-- 🟡 Exercise L7-3c: 単項式埋め込みの level 保存性。
    r ∈ I^n ⟹ C r * X^n ∈ reesDegreeTower I の level n。
    これは L7-1d の monomial_mem_reesDegreeTower の再掲。

    逆方向の対応: idealPowTower から reesDegreeTower への「成分ごとの射」。

    Hint-1: monomial_mem_reesDegreeTower をそのまま使う。 -/
theorem monomial_embed_preserves {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    Polynomial.C r * X ^ n ∈ (reesDegreeTower I).level n :=
  monomial_mem_reesDegreeTower I hr

/-- 🔴 Exercise L7-3d: Section-Retraction の関係。
    「埋め込んで抽出すると元に戻る」:
    coeff (C r * X^n) n = r。

    これは idealPowTower の level (toDual n) と
    reesDegreeTower の level n の間の「成分ごとの同型」の片方向。

    Hint-1: Polynomial.coeff_C_mul_X_pow で n = n のケース。
    Hint-2: `simp [Polynomial.coeff_C_mul_X_pow]` -/
theorem coeff_monomial_embed (n : ℕ) (r : R) :
    (Polynomial.C r * X ^ n).coeff n = r := by
  simp

/-- 🔴 Exercise L7-3e: 双対性の本質 ── 次数付き分解。
    p ∈ reesDegreeTower I の level n ⟹
    p = Σ_{k=0}^{n} C (coeff p k) * X^k。
    各成分 C (coeff p k) * X^k は level k の元。

    これは Rees 塔が idealPowTower の「直和表示」であることの核心:
    reesDegreeTower level n ≅ ⊕_{k=0}^{n} I^k  （加法群として）。
    idealPowTower の level (toDual k) = I^k が「次数 k 成分」に対応する。

    Hint-1: Polynomial.ext で係数比較。
    Hint-2: Polynomial.finset_sum_coeff + Polynomial.coeff_C_mul_X_pow。
    Hint-3: Finset.sum の中で m 番目の項だけが非零。 -/
theorem rees_graded_decomposition {n : ℕ} {p : R[X]}
    (hp : p ∈ (reesDegreeTower I).level n) :
    p = ∑ k ∈ Finset.range (n + 1), Polynomial.C (p.coeff k) * X ^ k := by
  obtain ⟨_, hD⟩ := hp
  ext m
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m ≤ n
  · -- m ≤ n: 和の中の m 番目の項だけが生き残る
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hkm
      have hmk : m ≠ k := by
        exact fun h => hkm h.symm
      simp [hmk]
    · intro hm'
      simp only [Finset.mem_range] at hm'
      omega
  · -- m > n: p.coeff m = 0 かつ和の全項も 0
    push_neg at hm
    rw [hD m hm]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    by_cases hkm : m = k
    · subst hkm
      omega
    · simp [hkm]

end Duality

-- ════════════════════════════════════════════════════════════
-- §L7-4. Mathlib reesAlgebra との接続  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  Mathlib の reesAlgebra I は R[X] の Subalgebra として定義される:
    reesAlgebra I = {p : R[X] | ∀ k, coeff p k ∈ I^k}

  reesDegreeTower I の union（全レベルの合併）は、
  まさにこの reesAlgebra I の台集合と一致する:
    ⋃ₙ (reesDegreeTower I).level n = ↑(reesAlgebra I)

  この一致は StructureTower が Mathlib の既存構造に自然に接続することを示す。

  さらに、reesDegreeTower の構造的な特徴を確認する:
  - global = level 0（増加族の典型的性質）
  - reesDegreeTower は ClosedTower **ではない**（idealPowTower との対比）
-/

section MathlibConnection

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 🟢 Exercise L7-4a: Rees 塔の union の特徴付け。
    ⋃ₙ level n = {p : R[X] | IsReesElement I p}。
    各 p が有限次多項式なので、十分大きい n で level n に属する。

    直感: union は「次数制限を取り払った」Rees 元の全体。

    Hint-1: (→) level n の元は Rees 元（第一条件を取る）。
    Hint-2: (←) Rees 元 p に対して n = natDegree p とすれば level n の元。
    Hint-3: Polynomial.coeff_eq_zero_of_natDegree_lt で次数条件。 -/
theorem reesDegreeTower_union :
    (reesDegreeTower I).union = {p : R[X] | IsReesElement I p} := by
  ext p
  simp only [StructureTower.union, Set.mem_iUnion, reesDegreeTower_level,
             Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hR, _⟩; exact hR
  · intro hR
    exact ⟨p.natDegree, hR, fun k hk =>
      Polynomial.coeff_eq_zero_of_natDegree_lt hk⟩

/-- 🟡 Exercise L7-4b: union と Mathlib の reesAlgebra の台集合の一致。
    reesAlgebra I = {p : R[X] | ∀ i, coeff p i ∈ I^i} (Mathlib の定義)。
    IsReesElement I p = ∀ k, coeff p k ∈ I^k（我々の定義）。
    これらは同じ条件なので union = ↑(reesAlgebra I)。

    注: Mathlib の reesAlgebra は Subalgebra R R[X] として定義されている。
    mem 条件は `∀ i, coeff p i ∈ I ^ i`。

    Hint-1: reesAlgebra の mem 条件を展開。
    Hint-2: reesDegreeTower_union と合成。
    Hint-3: `rw [reesDegreeTower_union]; ext p; simp [IsReesElement, reesAlgebra]` -/
theorem reesDegreeTower_union_eq_reesAlgebra :
    (reesDegreeTower I).union = ↑(reesAlgebra I) := by
  rw [reesDegreeTower_union]
  ext p
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hp i; exact hp i
  · intro hp k; exact hp k

/-- 🟡 Exercise L7-4c: global の特徴付け。
    global = level 0（増加族の最小レベル）。

    証明:
    - global ⊆ level 0: n = 0 の instance を取る。
    - level 0 ⊆ global: 単調性 level 0 ⊆ level n for all n。

    これは idealPowTower の global = ⋂ Iⁿ（分離条件で {0} になり得る）
    とは本質的に異なる:
    - 減少族の global は「全レベルの共通部分」→ 小さい
    - 増加族の global は「最小レベル」→ 大きい

    Hint-1: global = ⋂ₙ level n ⊇ level 0（単調性）。
    Hint-2: global ⊆ level 0（n = 0 で取る）。 -/
theorem reesDegreeTower_global :
    (reesDegreeTower I).global = (reesDegreeTower I).level 0 := by
  ext p
  simp only [StructureTower.global, Set.mem_iInter, reesDegreeTower_level,
             Set.mem_setOf_eq]
  constructor
  · intro h; exact h 0
  · intro h n
    exact (reesDegreeTower I).monotone_level (Nat.zero_le n) h

/-- 🔴 Exercise L7-4d: reesDegreeTower は ClosedTower ではない。
    idealPowTower の各 level Iⁿ はイデアル（= idealClosure の不動点）だった。
    reesDegreeTower の各 level は R[X] のイデアルではない。

    反例: I = (2) in ℤ として、
    p = C 2 * X ∈ level 1（coeff 0 = 0, coeff 1 = 2 ∈ (2)）。
    p * p = C 4 * X² は degree 2 > 1 なので level 1 に属さない。
    よって level 1 は R[X] 上の乗法で閉じていない。

    これは L5 の idealPowTower_closedTower との重要な構造的対比:

    | 性質              | idealPowTower I     | reesDegreeTower I    |
    |-------------------|---------------------|----------------------|
    | 各 level          | イデアル（閉）      | イデアルでない        |
    | ClosedTower       | ✓                   | ✗                    |
    | 閉性の理由/非理由 | I^n は環の部分構造  | 次数制限が乗法非互換  |

    Hint-1: 具体的な反例を構成する。
    Hint-2: p = C 2 * X ∈ level 1 だが p^2 は次数 2。
    Hint-3: level 1 の次数条件 k > 1 → coeff = 0 が p^2 で破れる。 -/
theorem reesDegreeTower_level_not_mul_closed :
    ∃ (p q : (Polynomial ℤ)),
      p ∈ (reesDegreeTower (Ideal.span {(2 : ℤ)})).level 1 ∧
      q ∈ (reesDegreeTower (Ideal.span {(2 : ℤ)})).level 1 ∧
      p * q ∉ (reesDegreeTower (Ideal.span {(2 : ℤ)})).level 1 := by
  -- p = q = C 2 * X
  refine ⟨Polynomial.C 2 * X, Polynomial.C 2 * X, ?_, ?_, ?_⟩
  · -- C 2 * X ∈ level 1
    constructor
    · intro k
      simp only [Polynomial.coeff_C_mul_X]
      split_ifs with hk
      · subst hk
        simp only [pow_one]
        exact Ideal.subset_span (Set.mem_singleton 2)
      · exact Ideal.zero_mem _
    · intro k hk
      simp only [Polynomial.coeff_C_mul_X]
      split_ifs with hk'
      · omega
      · rfl
  · -- same
    constructor
    · intro k
      simp only [Polynomial.coeff_C_mul_X]
      split_ifs with hk
      · subst hk
        simp only [pow_one]
        exact Ideal.subset_span (Set.mem_singleton 2)
      · exact Ideal.zero_mem _
    · intro k hk
      simp only [Polynomial.coeff_C_mul_X]
      split_ifs with hk'
      · omega
      · rfl
  · -- p * q ∉ level 1
    intro ⟨_, hD⟩
    -- (C 2 * X) * (C 2 * X) = C 4 * X^2, whose coeff 2 = 4 ≠ 0
    -- But degree bound says coeff 2 = 0 (since 2 > 1)
    have h2 : ((Polynomial.C (2 : ℤ) * X) * (Polynomial.C 2 * X)).coeff 2 = 0 :=
      hD 2 (by norm_num)
    have h4 : ((Polynomial.C (2 : ℤ) * X) * (Polynomial.C 2 * X)).coeff 2 = 4 := by
      rw [Polynomial.C_mul_X_eq_monomial, Polynomial.monomial_mul_monomial]
      norm_num
    rw [h4] at h2
    norm_num at h2

/-- 🔴 Exercise L7-4e: Rees 塔の乗法互換性は「level 間」で成立。
    level n 内での乗法閉性は成立しないが（L7-4d）、
    level m × level n → level (m + n) は成立する（L7-2b）。

    これは StructureTower の枠組みで本質的な区別:
    - ClosedTower: 各 level が閉包作用素の不動点（level 内の閉性）
    - FilteredRing: level 間の乗法互換性（level 間の整合性）

    idealPowTower は両方を満たすが、reesDegreeTower は後者のみ。
    この事実を明示的に statement として記録する。

    Hint-1: L7-2b をまとめるだけ。 -/
theorem reesDegreeTower_is_filtered_mul :
    ∀ (m n : ℕ) {p q : R[X]},
      p ∈ (reesDegreeTower I).level m →
      q ∈ (reesDegreeTower I).level n →
      p * q ∈ (reesDegreeTower I).level (m + n) := by
  intro m n p q hp hq
  exact reesDegreeTower_mul_mem I m n hp hq

end MathlibConnection

-- ════════════════════════════════════════════════════════════
-- §Summary. Level 7 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  Level 7 で確認したこと:

  §L7-1 **Rees 塔の基盤**:
    reesDegreeTower I : StructureTower ℕ R[X] として構成。
    level n = {p : R[X] | IsReesElement I p ∧ deg p ≤ n}。
    ℕ 添字（非双対）── L5 の idealPowTower (ℕᵒᵈ) との双対。
    定数多項式、単項式の帰属、加法閉性を確認。

  §L7-2 **乗法互換性と次数付き構造**:
    Rees 元の積は Rees 元（畳み込みと I^a · I^b ⊆ I^{a+b}）。
    level m × level n → level (m + n)（FilteredRing の mul_mem）。
    1 ∈ level 0、負元の閉性、R-スカラー倍の閉性。

  §L7-3 **idealPowTower との双対性**:
    係数抽出: coeff p n は Rees 元を I^n に写す。
    単項式埋め込み: r ∈ I^n を C r * X^n ∈ level n に写す。
    Section-retraction: coeff (C r * X^n) n = r。
    次数付き分解: p = Σ C(coeff p k) * X^k。

  §L7-4 **Mathlib reesAlgebra との接続**:
    union = ↑(reesAlgebra I)（Mathlib の Subalgebra との一致）。
    global = level 0 = {定数多項式}（idealPowTower の global とは対照的）。
    reesDegreeTower は ClosedTower ではない（level が R[X]-イデアルでない）。
    乗法互換性は level 間でのみ成立（FilteredRing 的構造）。

  ──────────────────────────────────────────────
  L5-L7 の双対構造:

    観点            L5: idealPowTower  L7: reesDegreeTower
    ──────────────────────────────────────────────────────
    添字            ℕᵒᵈ（減少族）      ℕ（増加族）
    空間            R                   R[X]
    level n         Iⁿ ⊆ R             {deg ≤ n の Rees 元} ⊆ R[X]
    global          ⋂ Iⁿ（分離→{0}）   level 0 ≅ R
    union           level 0 = R         reesAlgebra I
    ClosedTower     ✓                   ✗
    乗法互換性      I^m · I^n ⊆ I^{m+n} level m · level n ⊆ level (m+n)
    次数 k 成分     I^k                 {C r * X^k | r ∈ I^k}

  この双対性は Bourbaki の精神に忠実:
  同一の代数的対象（I-adic filtration）を
  順序構造（ℕᵒᵈ vs ℕ）と代数構造（R vs R[X]）の
  異なる組み合わせで記述している。

  ──────────────────────────────────────────────
  次のステップ候補（Level 8 以降）:

    1. **Associated graded ring**:
       gr_I(R) = ⊕ₙ I^n/I^{n+1} を StructureTower の商として記述。
       reesDegreeTower の「連続する level の差」が次数付き成分。

    2. **Rees 代数と blow-up**:
       Proj(R[It]) は Spec R の I に沿った blow-up。
       StructureTower の幾何学的応用への橋渡し。

    3. **逆極限同型**:
       completionPowTower I ≅ lim← R/I^n の StructureTower 版。
       L6 の cauchySeqTower と completionPowTower の厳密な同値。
  ──────────────────────────────────────────────
-/

-- ════════════════════════════════════════════════════════════
-- 検証コマンド:
--   lake env lean StructureTower_CategoryExercises_L7.lean
--   lake build BourbakiGuide.StructureTower
-- ════════════════════════════════════════════════════════════

end StructureTower

end BourbakiGuide
