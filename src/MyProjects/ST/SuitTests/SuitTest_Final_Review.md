# StructureTower SuitTest 最終版レビュー

## 総合評価: ★★★★★

**407行、11カテゴリ完全形式化、sorry ゼロ。**

前回指摘した2つの欠損（P3 extreme / P6 dual）が完全に埋まり、
全カテゴリが実証的な証明を持つ。特に P3 の Ordinal-indexed tower は
`ordinalNatBound` による Classical.choose ベースの構成で、
Ordinal API の制約を巧みに回避している。

---

## 新規追加セクションの詳細レビュー

### §P3. extreme — ordinalTower（L72–115）✅ 完全形式化

前回は `level := fun _ => Set.univ` の簡略版だったが、今回は真の定義を実装:

```lean
noncomputable def ordinalNatBound (o : Ordinal) (h : o < Ordinal.omega0) : ℕ :=
  Classical.choose (Ordinal.lt_omega0.mp h)

noncomputable def ordinalTower : StructureTower Ordinal ℕ where
  level o := if h : o < Ordinal.omega0
    then {n | n ≤ ordinalNatBound o h}
    else Set.univ
```

**設計判断の評価:**

`Ordinal.lt_omega0.mp` は `o < ω ↔ ∃ n : ℕ, o = ↑n` を与える。
`Classical.choose` でその `n` を取り出し、`ordinalNatBound` として命名。
これは Mathlib に `Ordinal.toNat` が安定的に存在しない状況への正しい対応。

**monotone_level の証明構造（L81–99）:**

4ケースの場合分けが明快:

| i < ω | j < ω | 方針 |
|:---:|:---:|:---|
| ✓ | ✓ | ordinalNatBound の ℕ 値比較 → Ordinal キャストの単調性 |
| ✓ | ✗ | j ≥ ω なら level j = univ → 自明 |
| ✗ | ✓ | i ≥ ω, j < ω, i ≤ j は矛盾（False.elim） |
| ✗ | ✗ | 両方 univ → 自明 |

L88–94 の核心部分:
```lean
have hij_ord :
    ((ordinalNatBound i hi : ℕ) : Ordinal) ≤ ((ordinalNatBound j hj : ℕ) : Ordinal) := by
  rw [hi_eq, hj_eq] at hij'; exact hij'
have hij_nat : ordinalNatBound i hi ≤ ordinalNatBound j hj := by
  exact_mod_cast hij_ord
```

`exact_mod_cast` で `Ordinal` の不等式を `ℕ` の不等式に変換するテクニックが的確。
`i = ↑(bound i)` と `j = ↑(bound j)` を `rw` で代入し、
`↑(bound i) ≤ ↑(bound j)` から `bound i ≤ bound j` を `exact_mod_cast` で導出。

**union の証明（L101–115）:**

`x : ℕ` に対して `↑x : Ordinal` を witness に取り、
`Ordinal.nat_lt_omega0 x` で `↑x < ω` を確保してから
`dif_pos` で if 分岐を解消。`ordinalNatBound_spec` の対称性を使って
`ordinalNatBound ↑x = x` を導出し、`x ≤ x` で閉じる。

全体として、Ordinal API の制約（`toNat` の不在）を
Classical.choose + spec パターンで完全に回避しており、模範的。

**潜在的リスク:**
- `Ordinal.lt_omega0` の statement が Mathlib で変更される可能性（低リスク）
- `exact_mod_cast` が Ordinal ↔ ℕ のキャスト推論に依存（中リスク、
  Mathlib の cast simp lemma セット変更で影響を受ける可能性）

---

### §P6. dual — idealPowTower + ofAntitone（L185–211）✅ 完全

```lean
noncomputable def idealPowTower (I : Ideal R) : StructureTower ℕᵒᵈ R where
  level n := ↑(I ^ OrderDual.ofDual n)
  monotone_level := by
    exact (Ideal.pow_le_pow_right (I := I)
      (m := OrderDual.ofDual j) (n := OrderDual.ofDual i)
      (OrderDual.ofDual_le_ofDual.mpr hij)) hx
```

前回のレビューで推奨した **名前付き引数** `(I := I) (m := ...) (n := ...)` を採用。
L5 ファイルとの一貫性が確保されている。

`idealPowTower_eq_ofAntitone` の証明は `ext i x; simp [...]` で完結。
`idealPowAntitone_antitone` も同じ名前付き引数パターンを使用しており統一的。

---

## 全セクション品質サマリー

| § | カテゴリ | 難易度 | 状態 | 特記事項 |
|:---|:---|:---:|:---:|:---|
| P1 | trivial | 🟢 | ✅ | `cases hx` で Empty の absurdity |
| P2 | canonical | 🟢 | ✅✅ | rank_unique 再利用、change + Iff.rfl |
| P3 | extreme | 🔴 | ✅✅ | ordinalNatBound による完全形式化（**新規**） |
| P4 | pathological | 🔴 | ✅ | FakeTower の monotone 破壊 |
| P5 | counterexample | 🔴 | ✅✅ | HasCharRankPreorder + TwoPoint |
| P6 | dual | 🟡 | ✅ | idealPowTower = ofAntitone（**新規**） |
| P7 | borderline | 🟡 | ✅ | singleton 失敗 → layer 定式化 |
| P8 | non-example | 🟡 | ✅ | almostFiltered の add 非閉性 |
| P9 | out-of-category | 🟡 | ✅ | eventually monotone + truncate |
| P10 | schema | 🟡 | ✅✅ | SemilatticeSup、不要仮定削除済 |
| P11 | finite_computational | 🟢 | ✅✅ | 算術設計 + 全3レベル検証 |

---

## 前バージョンからの改善点

1. **P3 の完全形式化**: `Set.univ` 簡略版 → `ordinalNatBound` + 4ケース monotonicity
2. **P6 の追加**: idealPowTower の独自定義 + ofAntitone との等価性
3. **名前付き引数の統一**: `Ideal.pow_le_pow_right (I := I) (m := ...) (n := ...)`

---

## 残る改善候補（優先度低）

### 1. natFiltration_layer の簡潔化

現在14行の手動証明。`omega` 一発で閉じる可能性がある:
```lean
theorem natFiltration_layer (n : ℕ) (hn : 0 < n) :
    natFiltration.level n \ natFiltration.level (n - 1) = {x | x = n} := by
  ext m; constructor
  · intro ⟨h1, h2⟩; simp_all [natFiltration, iic]; omega
  · intro hm; simp_all [natFiltration, iic]; omega
```

ただし `change` ベースの現在の証明は教育的価値が高く、
Suit Test の目的（理解の検証）には適している。

### 2. finTower の global/inter の数学的解釈の追記

`finTower1.global = {x | x.1 ≤ 1}` は「奇数閾値フィルトレーションの
global は最小レベル {0,1}」という解釈を持つ。
`finTower_inter_eq_right` は「偶数塔 ⊆ 奇数塔 なので inter = 偶数塔」
という構造的帰結。コメントでこの解釈を付記するとよい。

### 3. P4 pathological の形式的拡張

現在は FakeTower の monotone 破壊のみ。liftCl の関手性崩壊を
形式的に示す（cofinite ClosureOperator の構成 + 偽塔への適用）ことで
pathological カテゴリの目的をより完全に達成できる。ただしこれは
独立した発展課題として適切。

---

## 統計

| 指標 | 値 |
|:---|:---|
| 総行数 | 407 |
| import | 5（L4 + Mathlib 4モジュール） |
| 定義 (def/structure) | 18 |
| 定理 (theorem) | 22 |
| sorry 使用 | 0 |
| カテゴリ完全形式化 | 11/11 |
| 前バージョンからの改善 | +P3 完全形式化、+P6 追加 |
