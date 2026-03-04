# Structure Tower 発展演習 Level 6

## I-adic 完備化塔（I-adic Completion Tower）

**前提**: Level 1–5 を完了していること  
**Lean ファイル**: `StructureTower_CategoryExercises_L6.lean`

---

## §L6-1. Cauchy 列の塔的定義

### 数学的背景

L5 で構成した `idealPowTower I : StructureTower ℕᵒᵈ R` は *R の元* の階層化であった。L6-1 ではこれを **函数空間 `ℕ → R`** に持ち上げ、I-adic Cauchy 列の「速さ」をレベルで表現する。`level k = {x | ∀ m n, x m - x n ∈ I^(min m n + k)}` とすると、k が大きいほど厳しい条件（＝速い収束）となり、ℕᵒᵈ で添字化すれば L5-1a と同じ双対化パターンで StructureTower が得られる。

### 演習一覧

**🟢 Exercise L6-1a: IsIAdicCauchy の定義**  
列 x : ℕ → R が I-adic Cauchy であるとは、∀ m n, x m - x n ∈ I^(min m n)。cauchySeqTower の level 0 に対応する。

**🟢 Exercise L6-1b: cauchySeqTower の構成**  
`StructureTower ℕᵒᵈ (ℕ → R)` の完全実装。単調性は `Ideal.pow_le_pow_right` + ℕᵒᵈ の順序反転。

- Hint-1: i ≤ j in ℕᵒᵈ → ofDual j ≤ ofDual i → 冪が大きい → イデアルが小さい
- Hint-2: `Nat.add_le_add_left` で min m n + k の単調性
- Hint-3: `Ideal.pow_le_pow_right (Nat.add_le_add_left (OrderDual.ofDual_le_ofDual.mpr hij) _) (hx m n)`

**🟢 Exercise L6-1c: level 0 ↔ IsIAdicCauchy**  
min m n + 0 = min m n なので simp で閉じる。

**🟡 Exercise L6-1d: 定数列は全レベルに属する**  
x = fun _ => r の差は 0 ∈ I^k。L5-1b（top_level = univ）の函数空間版。

**🟡 Exercise L6-1e: Cauchy 列の和は Cauchy**  
(x+y) m - (x+y) n = (x m - x n) + (y m - y n)。`Ideal.add_mem` で閉じる。

**🔴 Exercise L6-1f: スカラー倍の保存**  
r * x m - r * x n = r * (x m - x n)。`Ideal.mul_mem_left` で閉じる。R-加群フィルトレーションの構造確認。

---

## §L6-2. null 列と同値関係

### 数学的背景

I-adic null 列は「I-adic 位相で 0 に収束する列」である。`IsIAdicNull I x := ∀ k, ∃ N, ∀ n ≥ N, x n ∈ I^k`。null 列は cauchySeqTower の global に「eventually」の意味で対応する。差が null なら同値とする setoid を構成し、完備化の商空間 R̂ = {Cauchy列} / {null列} の基盤を作る。L5-4b の IsSeparated との合流: 分離的 ⟺ 定数 null 列は零列のみ ⟺ ι 単射。

### 演習一覧

**🟢 Exercise L6-2a: IsIAdicNull の定義**  
null 列の述語定義。完全実装。

**🟢 Exercise L6-2b: 零列は null**  
0 ∈ I^k は `Ideal.zero_mem` で即座に閉じる。

**🟡 Exercise L6-2c: null 列の加法的閉性**  
N = max Nx Ny として `Ideal.add_mem`。

- Hint-1: max で N を取る
- Hint-2: `le_trans (le_max_left ..) hn` で各成分の帰属
- Hint-3: 下記実装参照

**🟡 Exercise L6-2d: null 列の負は null**  
`Ideal.neg_mem_iff` で -a ∈ I^k ↔ a ∈ I^k。

**🟡 Exercise L6-2e: iadicSetoid の構成**  
x ~ y ⟺ x - y が null。反射性（L6-2b）、対称性（L6-2d）、推移性（L6-2c）。

**🔴 Exercise L6-2f: 分離条件と null 定数列**  
IsSeparated I のとき: (fun _ => r) が null ⟺ r = 0。L5-4c（escape_of_isSeparated）の直接適用。

- Hint-1: (→) null → r ∈ I^k for all k → r ∈ ⋂ Iⁿ = {0}
- Hint-2: escape_of_isSeparated で矛盾を導く
- Hint-3: `by_contra hr; obtain ⟨n, hn⟩ := escape_of_isSeparated I hI hr; obtain ⟨N, hN⟩ := h n; exact hn (by simpa using hN N le_rfl)`

---

## §L6-3. 完備化の普遍性

### 数学的背景

Mathlib の `Ideal.AdicCompletion I R` は逆極限 lim← R/Iⁿ として構成される。正準写像 `ι := Ideal.AdicCompletion.of I R : R →+* R̂` に対し、L5-3b の `ringHom_towerHom` パターンを適用すると ι が `idealPowTower I → idealPowTower (Ideal.map ι I)` の Hom を誘導する。これは L5 で確立した「環準同型 → 塔の射」パイプラインの canonical な適用例であり、完備化の普遍性の StructureTower 的表現である。

### 演習一覧

**🟢 Exercise L6-3a: completionPowTower の構成**  
`idealPowTower (Ideal.map ι I)` を R̂ 上で構成。L5-1a の直接適用。

**🟡 Exercise L6-3b: ι が tower hom を誘導**  
`ringHom_towerHom (ι_map I) I (Î I) le_rfl`。L5-3b の canonical 適用。

- Hint-1: 条件 Ideal.map ι I ≤ Î は le_refl
- Hint-2: ringHom_towerHom をそのまま適用
- Hint-3: `ringHom_towerHom (ι_map I) I (Î I) le_rfl`

**🟢 Exercise L6-3c: toFun = ι の確認**  
定義の展開で rfl。

**🟡 Exercise L6-3d: 合成の互換性**  
L5-3d の ringHom_towerHom_comp の具体化。`Hom.ext rfl`。

**🔴 Exercise L6-3e: 分離条件下での ι の単射性（statement）**  
IsSeparated I ⟹ ι 単射。ker ι = ⋂ Iⁿ = ⊥ の帰結。sorry。

---

## §L6-4. 完備塔と ClosedTower

### 数学的背景

completionPowTower は idealClosure (on R̂) に関する ClosedTower である。これは L5-2c の完備化版。さらに R̂ は Î-adic に自動的に分離的（⋂ₙ Îⁿ = ⊥）であり、脱出定理（L5-4c）の完備化版が成立する。L5 の全条件が完備化で「最良の形」で実現される: StructureTower + ClosedTower + IsSeparated + 完備性。

### 演習一覧

**🟢 Exercise L6-4a: completionPowTower は ClosedTower**  
L5-2c の `idealPowTower_closedTower` を R̂ 上で適用。

**🟡 Exercise L6-4b: 完備化の分離性（statement）**  
⋂ₙ (Î)ⁿ = ⊥。逆極限構成からの帰結。sorry。

**🟡 Exercise L6-4c: global = {0}**  
L6-4b からの直接的帰結。sorry（L6-4b に依存）。

**🔴 Exercise L6-4d: 完備化版脱出定理**  
x ≠ 0 in R̂ ⟹ ∃ n, x ∉ (Î)ⁿ。L5-4c + L6-4b の組合せ。sorry。

**🔴 Exercise L6-4e: global の閉性（完備化版）**  
`(completionPowTower_closedTower I).cl_global_subset`。L5-2d の直接適用。**sorry なし**。

---

## §Summary. Level 6 の全体像

### 各節で確認したこと

- **§L6-1**: Cauchy 列の「速さ」を StructureTower のレベルで表現。(ℕ → R) 上の `cauchySeqTower I` を構成。加法・スカラー倍の閉性により FilteredModule の構造を確認。
- **§L6-2**: null 列の定義、加法・負の閉性、iadicSetoid の構成。分離条件下で定数 null 列 ⟺ 零列。
- **§L6-3**: Mathlib の `AdicCompletion` を使い、ι が `idealPowTower I → completionPowTower I` の Hom を誘導することを確認（L5-3b パターン）。合成の互換性と単射性。
- **§L6-4**: 完備化塔が ClosedTower であること、R̂ が自動分離であること、脱出定理の完備化版、global の閉性。

### L1-L6 の合流点

| 条件 | L5 での確認 | L6 での発展 |
|------|------------|------------|
| StructureTower | L5-1a（R 上） | L6-1b（ℕ→R 上）, L6-3a（R̂ 上） |
| 乗法/加法互換 | L5-1c | L6-1e/f（Cauchy 列の加法/スカラー） |
| ClosedTower | L5-2c | L6-4a（完備化版） |
| cl_global_subset | L5-2d | L6-4e（完備化版） |
| 環準同型 → Hom | L5-3b | L6-3b（ι による towerHom） |
| 分離条件 | L5-4b | L6-4b（R̂ は自動分離） |
| 脱出定理 | L5-4c | L6-4d（完備化版脱出） |
| Krull 交叉 | L5-4e | L6-4c（global = {0} の直接確認） |

### 次のステップ候補（Level 7 以降）

1. **Cauchy 列の収束と完備性**: `cauchySeqTower I` の元が R̂ 上で収束することの形式化。逆極限との同型構成。
2. **Rees 代数**: ⊕ₙ Iⁿtⁿ を StructureTower の直和として記述。次数環との接続。
3. **Mathlib CategoryTheory.Monad 接続**: idealClosure の ClosedTower ↔ CategoryTheory.Monad.Algebra の形式的証明。

---

## 検証コマンド

```bash
lake env lean StructureTower_CategoryExercises_L6.lean
lake build BourbakiGuide.StructureTower
```

---

## 演習の難易度一覧

| 演習 | 難易度 | sorry | 主題 |
|------|--------|-------|------|
| L6-1a | 🟢 | なし | IsIAdicCauchy 定義 |
| L6-1b | 🟢 | なし | cauchySeqTower 構成 |
| L6-1c | 🟢 | なし | level 0 = IsIAdicCauchy |
| L6-1d | 🟡 | なし | 定数列は Cauchy |
| L6-1e | 🟡 | なし | Cauchy の加法閉性 |
| L6-1f | 🔴 | なし | スカラー倍の保存 |
| L6-2a | 🟢 | なし | IsIAdicNull 定義 |
| L6-2b | 🟢 | なし | 零列は null |
| L6-2c | 🟡 | なし | null の加法閉性 |
| L6-2d | 🟡 | なし | null の負 |
| L6-2e | 🟡 | なし | iadicSetoid 構成 |
| L6-2f | 🔴 | なし | 分離条件と null 定数列 |
| L6-3a | 🟢 | なし | completionPowTower |
| L6-3b | 🟡 | なし | ι が towerHom を誘導 |
| L6-3c | 🟢 | なし | toFun = ι |
| L6-3d | 🟡 | なし | 合成の互換性 |
| L6-3e | 🔴 | あり | ι の単射性 |
| L6-4a | 🟢 | なし | ClosedTower（完備化版） |
| L6-4b | 🟡 | あり | 完備化の分離性 |
| L6-4c | 🟡 | あり | global = {0} |
| L6-4d | 🔴 | あり | 完備化版脱出定理 |
| L6-4e | 🔴 | なし | global の閉性 |

**sorry 使用箇所**: 4箇所（L6-3e, L6-4b, L6-4c, L6-4d）  
**sorry なし**: 18箇所（def/structure 全完全実装 + 多数の theorem）
