# エラー修正ログ: StructureTower_OrderExamples.lean

## 概要

`src/MyProjects/ST/OrderNotes/StructureTower_OrderExamples.lean` を `lake build` でビルドしようとした際に発生したエラーとその修正記録。ブルバキ『数学原論』の精神に則った順序論的塔（StructureTower）の例示ファイル。

---

## エラー1: strict implicit 引数の lambda 束縛ミス

### エラー概要

以下の定義で「Application type mismatch」が多数発生した。

```
error: fun hij _ hy => ...
  The argument hij has type α (sort Type) but is expected to have type ? ≤ ?
```

影響箇所: `const`, `iic`, `ofMonotoneSeq`, `reindex`, `icc`, `prod`, `inter`, `sup`

### 原因

Lean 4 の `⦃i j : ι⦄`（strict implicit, 別名 semi-implicit）引数は、lambda 式の中で **自動的にスキップされない**。したがって `fun _ => ...` と書くと「`_` が `i : ι` を束縛」し、残りの引数が型不整合になる。

`StructureTower.monotone_level` の型は

```lean
∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j
```

である。`⊆` 自体も `∀ ⦃x⦄, x ∈ _ → x ∈ _` という strict implicit 付きの型なので、証明項で全引数を明示しなければならない。

### 修正内容

すべての `monotone_level` 証明で引数を明示的に束縛するように変更した。

| 定義 | 修正前 | 修正後 |
|------|--------|--------|
| `const` | `fun _ => Subset.rfl` | `fun _i _j _hij => Subset.refl _` |
| `iic` | `fun hij _ hy => le_trans hy hij` | `fun _i _j hij _x hx => le_trans hx hij` |
| `ofMonotoneSeq` | `fun hij _ hy => le_trans hy (hc hij)` | `fun _i _j hij _x hx => le_trans hx (hc hij)` |
| `reindex` | `fun hij => T.monotone_level (hf hij)` | `fun _i _j hij => T.monotone_level (hf hij)` |
| `icc` | `fun hij _ hy => ⟨hy.1, le_trans hy.2 hij⟩` | `fun _i _j hij _y hy => ⟨hy.1, le_trans hy.2 hij⟩` |
| `prod` | `fun hij _ hp => ⟨T₁.monotone_level hij hp.1, ...⟩` | `fun _i _j hij _p hp => ⟨...⟩` |
| `inter` | `fun hij _ hx => ⟨T₁.monotone_level hij hx.1, ...⟩` | `fun _i _j hij _x hx => ⟨...⟩` |
| `sup` | `fun hij _ hx => by rcases hx` | `fun _i _j hij _x hx => by rcases hx` |

### 修正が正しい理由

`⦃i j : ι⦄` を持つ型 `∀ ⦃i j : ι⦄, i ≤ j → P i j` に対して:

- `fun _i _j hij => ...` は `i`, `j`, `h : i ≤ j` を順に束縛し、残り `P i j` を証明する
- `⊆` = `∀ ⦃x⦄, x ∈ S → x ∈ T` なので、subset 証明には `fun _x hx =>` も必要

---

## エラー2: `Iff.rfl` の型不整合（定義のコンパイル失敗による連鎖）

### エラー概要

```
error: Type mismatch: Iff.rfl has type ?m ↔ ?m but expected y ∈ (iic α).level x ↔ y ≤ x
```

### 原因

`iic` 自体の `monotone_level` がエラー1で失敗しているため、`iic` の定義が不完全な状態になり、後続の `mem_iic_level` の `(iic α).level x` が展開されなかった。連鎖エラー。

### 修正内容

根本である `iic` を修正した後、`Iff.rfl` の代わりに `Set.mem_Iic` を使用する形に統一した。

```lean
-- Before
y ∈ (iic α).level x ↔ y ≤ x := Iff.rfl

-- After
y ∈ (iic α).level x ↔ y ≤ x := Set.mem_Iic
```

同様に `mem_ofMonotoneSeq_level`, `mem_natFiltration_level` も `Set.mem_Iic` に変更。

### 修正が正しい理由

`Set.Iic x = {y | y ≤ x}` の membership は `Set.mem_Iic : a ∈ Set.Iic b ↔ a ≤ b` として既に Mathlib に登録済み。定義的等号への依存を避け、明示的な補題を使うことで、定義の展開方法に依存しない堅牢な証明になる。

---

## エラー3: `union = Set.univ` の証明構文ミス

### エラー概要

```
error: The argument fun x => trivial has type ∀ (x : ?m), True but expected to have type α
```

### 原因

`ext x; simp [union, Set.mem_iUnion]` の後、`simp` が `↔ True` の部分をさらに簡約し、ゴールが `∃ i : α, x ≤ i` の形になった。それに対して `⟨fun _ => trivial, fun _ => ⟨x, le_refl x⟩⟩` という `Iff.intro` 形式のコンストラクタを適用しようとして型が合わなかった。

### 修正内容

```lean
-- Before
theorem iic_union_eq_univ (α : Type*) [Preorder α] :
    (iic α).union = Set.univ := by
  ext x
  simp [union, Set.mem_iUnion]
  exact ⟨fun _ => trivial, fun _ => ⟨x, le_refl x⟩⟩

-- After
theorem iic_union_eq_univ (α : Type*) [Preorder α] :
    (iic α).union = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [union, Set.mem_iUnion, iic, Set.mem_Iic]
  exact ⟨x, le_refl x⟩
```

`natFiltration_union_eq_univ` も同様に修正。

### 修正が正しい理由

`Set.eq_univ_of_forall : (∀ x, x ∈ s) → s = univ` を使うことで、ゴールを「任意の元がその集合に属する」という単純な形に変換できる。その後 `simp only` で `⋃ i, Set.Iic i` の membership を展開し、`⟨x, le_refl x⟩` で存在証人を与える（`x ∈ Set.Iic x` ↔ `x ≤ x` が `le_refl` で成立）。

---

## エラー4: `ext` タクティクが `StructureTower` に未対応

### エラー概要

```
error: No applicable extensionality theorem found for type StructureTower ι α
Note: Extensionality theorems can be registered with the [ext] attribute
```

`reindex_id`, `reindex_comp`, `ofMonotoneSeq_eq_reindex`, `icc_eq_inter_const_iic` で発生。

### 原因

`StructureTower` 構造体に `@[ext]` 属性が付いていなかった。

### 修正内容

```lean
-- Before
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where

-- After
@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
```

### 修正が正しい理由

Lean 4 の `@[ext]` 属性は、構造体に対して「全フィールドが等しければ全体が等しい」という外延性定理を自動生成する。`StructureTower` の場合：

- `level : ι → Set α` … 証明に関わる唯一の実質的なフィールド
- `monotone_level : Prop` … Prop なので proof irrelevance により自動的に等しい

よって `T₁.level = T₂.level → T₁ = T₂` が生成され、`ext` タクティクが機能するようになる。

副作用として `icc_eq_inter_const_iic` で `simp` がゴールを完全に閉じるようになったため、末尾の `exact Iff.rfl` は削除した。

---

## エラー5: `Function.iterate` の定義的等号と `show` タクティクの失敗

### エラー概要

```
error: 'show' tactic failed, pattern
  f (f^[k] S) ⊆ f (f^[k + 1] S)
is not definitionally equal to target
  f^[k + 1] S ⊆ f^[k + 1 + 1] S
```

### 原因

Lean 4 の `Function.iterate` の **定義的** な展開方向は `f^[n+1] x = f^[n] (f x)`（左再帰・右適用）である。

つまり `f^[k+1] S = f^[k] (f S)` であり、`f (f^[k] S)` **ではない**。

`show f (f^[k] S) ⊆ f (f^[k+1] S)` は **命題的**には正しいが、定義的等号を要求する `show` では失敗する。

```lean
-- Lean 4 の iterate の定義（核心部分）
def Function.iterate (f : α → α) : ℕ → α → α
  | 0,   x => x
  | n+1, x => iterate f n (f x)   -- ← f^[n+1] x = f^[n] (f x)
```

一方、Mathlib には `Function.iterate_succ'` という命題がある：

```lean
theorem Function.iterate_succ' : f^[n + 1] = f ∘ f^[n]
-- すなわち f^[n+1] x = f (f^[n] x)
```

### 修正内容

```lean
-- Before
| succ k ih =>
  show f (f^[k] S) ⊆ f (f^[k + 1] S)
  exact hf ih

-- After
| succ k ih =>
  simp only [Function.iterate_succ', Function.comp] at ih ⊢
  exact hf ih
```

### 修正が正しい理由

`simp only [Function.iterate_succ', Function.comp] at ih ⊢` は：

1. **ゴール** `f^[k+1] S ⊆ f^[k+2] S` を `f (f^[k] S) ⊆ f (f (f^[k] S))` に書き換える
2. **仮定** `ih : f^[k] S ⊆ f^[k+1] S` を `ih : f^[k] S ⊆ f (f^[k] S)` に書き換える

その後 `exact hf ih` で `hf : Monotone f` と `ih` を合わせてゴールを閉じる。

`at ih ⊢` が重要：ゴールだけを書き換えると `ih` の型が旧形のまま残り、型不整合が生じる。

---

## 動作確認

```
✔ [8043/8044] Built MyProjects.ST.OrderNotes.StructureTower_OrderExamples (4.2s)
Build completed successfully (8044 jobs)
```

---

## 実装意図のメモ

このファイルはブルバキ『数学原論』§集合論の「構造の種」の精神を Lean 4 で形式化するための例示集である。`StructureTower ι α` は「添字 `ι` で層別された `α` の部分集合の単調族」という一般構造を抽象化し、以下の哲学的立場を反映している：

1. **一般から特殊へ**（du général au particulier）: 塔という抽象的な構造を先に定め、そこへの各具体例（`iic`, `icc`, `ofIterate` など）を特殊化として位置付ける
2. **函手性**（`reindex`）: 添字変換が函手的である（`reindex_id` は単位法則、`reindex_comp` は合成法則）
3. **普遍的構成**（`prod`, `inter`, `sup`）: 積・共通部分・合併という levelwise 構成が塔の圏における積・積・余積に対応する

`@[ext]` の付加は、集合論的な外延性（集合は元の同一性で決まる）を塔レベルに持ち上げる操作であり、ブルバキが重視した「同型の下での不変性」の形式的表現でもある。
