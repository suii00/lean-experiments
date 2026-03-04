# StructureTower Level 7: Rees 代数と次数付き構造

## 概要

Level 7 は **Rees 代数** R\[It\] = ⊕ₙ Iⁿtⁿ を StructureTower の言語で記述する。L5 の `idealPowTower` が I-adic filtration の「内部的」見方（R の中で Iⁿ が縮小する）だったのに対し、`reesDegreeTower` は「外部的」見方（R\[X\] の中で次数付き Rees 元が拡大する）を提供する。

**プロジェクト初の ℕ 添字**（非双対）StructureTower であり、`idealPowTower`（ℕᵒᵈ）との双対性が理論の深みを示す。

## 数学的構造

### 核心的定義

```
IsReesElement I p := ∀ k, p.coeff k ∈ I^k

reesDegreeTower I : StructureTower ℕ R[X]
  level n = {p : R[X] | IsReesElement I p ∧ ∀ k, n < k → p.coeff k = 0}
```

### L5-L7 双対構造表

| 観点 | L5: idealPowTower | L7: reesDegreeTower |
|------|-------------------|---------------------|
| 添字 | ℕᵒᵈ（減少族） | ℕ（増加族） |
| 空間 | R | R\[X\] |
| level n | Iⁿ ⊆ R | {deg ≤ n の Rees 元} ⊆ R\[X\] |
| global | ⋂ Iⁿ（分離→{0}） | level 0 ≅ R |
| union | level 0 = R | reesAlgebra I |
| ClosedTower | ✓ | ✗ |
| 乗法互換性 | I^m · I^n ⊆ I^{m+n} | level m · level n ⊆ level (m+n) |
| 次数 k 成分 | I^k | {C r * X^k ∣ r ∈ I^k} |

## 演習一覧（21 exercises）

### §L7-1: Rees 塔の基盤（6 exercises）

| 演習 | 難易度 | Sorry | 内容 |
|------|--------|-------|------|
| L7-1a | 🟢 | No | `IsReesElement` 定義 |
| L7-1b | 🟢 | No | `reesDegreeTower` 構成 |
| L7-1c | 🟢 | No | level 0 = {定数多項式} |
| L7-1d | 🟡 | No | 単項式 C r * X^n ∈ level n |
| L7-1e | 🟡 | No | 加法閉性 |
| L7-1f | 🟡 | No | 零多項式の帰属 |

### §L7-2: 乗法互換性と次数付き構造（5 exercises）

| 演習 | 難易度 | Sorry | 内容 |
|------|--------|-------|------|
| L7-2a | 🟡 | No | Rees 元の積は Rees 元（畳み込み） |
| L7-2b | 🔴 | No | level m × level n → level (m+n)（鳩の巣原理） |
| L7-2c | 🟡 | No | 1 ∈ level 0 |
| L7-2d | 🟡 | No | 負元の閉性 |
| L7-2e | 🔴 | No | R-スカラー倍の閉性 |

### §L7-3: idealPowTower との双対性（5 exercises）

| 演習 | 難易度 | Sorry | 内容 |
|------|--------|-------|------|
| L7-3a | 🟢 | No | 係数抽出 coeff p n ∈ I^n |
| L7-3b | 🟡 | No | 係数抽出の level 保存性 |
| L7-3c | 🟡 | No | 単項式埋め込みの level 保存性 |
| L7-3d | 🔴 | No | Section-retraction: coeff (C r * X^n) n = r |
| L7-3e | 🔴 | No | 次数付き分解 p = Σ C(coeff p k) * X^k |

### §L7-4: Mathlib reesAlgebra との接続（5 exercises）

| 演習 | 難易度 | Sorry | 内容 |
|------|--------|-------|------|
| L7-4a | 🟢 | No | union = {Rees 元全体} |
| L7-4b | 🟡 | No | union = ↑(reesAlgebra I) |
| L7-4c | 🟡 | No | global = level 0 |
| L7-4d | 🔴 | No | level は R\[X\]-乗法閉でない（反例） |
| L7-4e | 🔴 | No | level 間の乗法互換性（まとめ） |

## Sorry 統計

- **全 21 exercises: sorry なし（目標）**
- 定義（def/abbrev）: 4（全て完全実装）
- 定理（theorem）: 17（全て証明付き）

## 難易度分布

- 🟢: 5 exercises（定義展開・simp）
- 🟡: 10 exercises（補題組み合わせ・標準タクティク）
- 🔴: 6 exercises（設計判断・多段推論・反例構成）

## 主要な証明技法

### L7-2a: 畳み込みと Ideal.sum_mem
```
Polynomial.coeff_mul → Finset.antidiagonal → 
各 (i,j) で idealPow_mul_mem → Ideal.sum_mem
```

### L7-2b: 鳩の巣原理
```
k > m + n, i + j = k ⟹ i > m ∨ j > n
⟹ coeff = 0 in one factor ⟹ product term = 0
⟹ Finset.sum_eq_zero
```

### L7-3e: 多項式の次数付き分解
```
Finset.sum_eq_single m で m 番目の項を抽出
split_ifs でデルタ関数的振る舞いを処理
```

### L7-4d: 反例構成
```
ℤ 上の (2), p = C 2 * X
p² = C 4 * X² の次数 2 > 1 で level 1 からはみ出す
```

## L1-L7 の全体像

```
L1: StructureTower基本定義
L2: Hom・合成・自然性
L3: ClosedTower（閉包作用素）
L4: NatInclusion（自然包含）
L5: idealPowTower I（ℕᵒᵈ, 内部的, R上）        ←─ 双対 ─→  L7: reesDegreeTower I（ℕ, 外部的, R[X]上）
L6: completionPowTower（R̂上の完備化塔）
```

## Import 依存

```
Mathlib.RingTheory.ReesAlgebra     -- reesAlgebra
Mathlib.RingTheory.Filtration      -- Ideal.Filtration
Mathlib.Algebra.Polynomial.Basic   -- Polynomial, coeff, C, X
Mathlib.Algebra.Polynomial.Coeff   -- coeff_mul, coeff_add etc.
Mathlib.RingTheory.Ideal.Operations -- Ideal.pow, mul_mem_mul
```
