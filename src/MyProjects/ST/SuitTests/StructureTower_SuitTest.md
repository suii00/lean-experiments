# Suit Test: StructureTower 全般 — 11 カテゴリ網羅版

生成日: 2026-03-02  
対象カテゴリ: trivial, canonical, extreme, pathological, counterexample, dual, borderline, non-example, out-of-category, schema, finite_computational  
難易度分布: 🟢×3 / 🟡×5 / 🔴×3

---

## 問題 1 — trivial | 🟢

**目的**  
最小構成で StructureTower の公理が満たされることを確認し、自明な例が理論の退化ケースとして健全に機能することを検証する。

**問題文**  
添字集合 `ι := Unit`（単点集合）、台集合 `α := Empty` に対する StructureTower を構成せよ。すべてのレベルが `∅` であることを示し、さらに `union` が `∅` に等しいことを証明せよ。

数学的背景: 単点添字 × 空台集合は「情報ゼロ」の塔であり、すべての性質が vacuously に成立する。これは `const Unit (∅ : Set Empty)` の特殊化として理解できる。

**Lean シグネチャ例**
```lean
def emptyTower : StructureTower Unit Empty where
  level := fun _ => ∅
  monotone_level := fun _ _ _ _ hx => hx.elim

theorem emptyTower_level_eq (u : Unit) :
    emptyTower.level u = ∅ := sorry

theorem emptyTower_union_eq :
    emptyTower.union = ∅ := sorry
```

---

## 問題 2 — canonical | 🟢

**目的**  
理論の中核となる標準的な ℕ-filtration を構成し、ExhaustiveTower としての性質（rank の存在と一意性）を具体的に確認する。

**問題文**  
自然数上の標準フィルトレーション `natFiltration`（`level n = Set.Iic n`、すなわち `{m : ℕ | m ≤ n}`）に対して以下を行え:

1. `natFiltration` が ExhaustiveTower であることを示せ（`exhaustive` を構成）。
2. `rank x = x` が成立することを証明せよ（`rank` は `Nat.find` による定義）。
3. `HasCharRank natFiltration id` が成立することを証明せよ。

数学的背景: `natFiltration` は Iic-塔の原型であり、rank uniqueness (Theorem B) の最も自然な検証対象である。

**Lean シグネチャ例**
```lean
def natExhaustive : ExhaustiveTower ℕ where
  toStructureTower := natFiltration
  exhaustive := fun x => ⟨x, le_refl x⟩

theorem natExhaustive_rank_eq (x : ℕ) :
    natExhaustive.rank x = x := sorry

theorem natExhaustive_hasCharRank :
    HasCharRank natExhaustive id := sorry
```

---

## 問題 3 — extreme | 🔴

**目的**  
添字集合が非可算順序型（`Ordinal` や `Cardinal`）の場合にも StructureTower の理論が健全に機能するか、スケーラビリティの限界を検証する。

**問題文**  
添字集合 `ι := Ordinal`（順序数全体、自然に well-order をもつ）に対し、台集合 `α := ℕ` で以下の塔を構成せよ:

```
level o := if o < ω then {n : ℕ | n ≤ Ordinal.toNat o} else Set.univ
```

ここで `ω` は最初の極限順序数である。

1. この定義が `monotone_level` を満たすことを証明せよ（`ω` の手前と `ω` 以降の場合分けが必要）。
2. `union` が `Set.univ` に等しいことを示せ。
3. この塔が ExhaustiveTower としての rank 構造をもつ場合、rank 関数は ℕ 値ではなく Ordinal 値になる。ℕ-indexed な Theorem B（rank uniqueness）がそのままでは適用できないことを、型レベルで説明せよ。

**Lean シグネチャ例**
```lean
-- 注意: Ordinal 上の StructureTower は Mathlib の
-- Ordinal.lt_wf と Order.lt_iff_le_not_le を用いる。
-- 完全な形式化は高度であり、以下は骨格のみ。

noncomputable def ordinalTower : StructureTower Ordinal ℕ where
  level o := if o < Ordinal.omega then {n | n ≤ o.toNat} else Set.univ
  monotone_level := sorry -- 場合分けが必要

theorem ordinalTower_union_eq_univ :
    ordinalTower.union = Set.univ := sorry
```

**ヒント**
- `o < ω` かつ `o' < ω` の場合は `Ordinal.toNat` の単調性を利用。
- `o ≥ ω` の場合は `Set.univ` からの包含で自明。
- Theorem B の適用不可能性は、`ExhaustiveTower` が `ℕ`-indexed に限定されている型定義レベルの制約として述べればよい。

---

## 問題 4 — pathological | 🔴

**目的**  
`monotone_level` 公理を除去した「偽塔」において、liftCl（閉包モナド）の関手性が崩壊する具体例を構成し、単調性公理の必要性を示す。

**問題文**  
以下の構造 `FakeTower`（`monotone_level` を持たない）を定義せよ:

```lean
structure FakeTower (ι α : Type*) [Preorder ι] where
  level : ι → Set α
```

1. 具体的な `FakeTower ℕ ℕ` のインスタンスで `level 0 = {0, 1}` かつ `level 1 = {2}` となるものを構成せよ。
2. 位相空間 `ℕ` に離散位相を入れた場合の `topClosure`（位相的閉包演算子）を用いて、`liftCl topClosure` 相当の操作を `FakeTower` に適用すると、結果が再び FakeTower にはなるが、unit 自然変換 `T → liftCl(T)` のレベル保存が **成立しない** ケースが存在しうることを示せ。
3. 上記から「`monotone_level` がなければ liftCl が well-defined な自己関手にならない」ことを1文で結論せよ。

**Lean シグネチャ例**
```lean
structure FakeTower (ι α : Type*) [Preorder ι] where
  level : ι → Set α

def fakeExample : FakeTower ℕ ℕ where
  level := fun n => if n = 0 then {0, 1} else {2}

-- monotone_level の反例
theorem fake_not_monotone :
    ¬ (∀ i j : ℕ, i ≤ j → fakeExample.level i ⊆ fakeExample.level j) := sorry

-- liftCl の適用後に "unit preserves" が失敗する例を構成
-- （離散位相では cl = id なので、非離散位相を使う方が示しやすい）
```

**ヒント**
- 離散位相では `cl = id` なので反例にならない。代わりに `ℕ` に cofinite 位相を入れると `cl({0,1}) = ℕ` のような拡大が起こり、偽塔で「`level 0` は拡大するが `level 1` は拡大しない」状況が作れる。
- `liftCl` の `monotone_level` 証明は `cl.monotone (T.monotone_level hij)` に依存するため、元の `T.monotone_level` がないと構成不能。
- 核心: 偽塔に閉包を適用すると「レベル 0 の閉包がレベル 1 の閉包を超える」ことが起こりうる。

---

## 問題 5 — counterexample | 🔴

**目的**  
「ExhaustiveTower ⟹ HasCharRank T r がある r に対して成立」の **逆**（すなわち「HasCharRank を持つ =⟹ rank の一意性」が **一般の前順序** では成立しない）ことを具体的反例で示す。

**問題文**  
添字集合を `ι := Bool`（`false ≤ true` かつ `false ≤ false`, `true ≤ true` の離散前順序ではなく、`false ≤ true` の全順序）とする。

1. `Bool`-indexed な StructureTower を `level false = {0}`, `level true = {0, 1}` で構成せよ。
2. これを「Bool-exhaustive」（すべての元がいずれかのレベルに属する）塔として、rank 関数 `r₁(0) = false, r₁(1) = true` を定義せよ。
3. 別の関数 `r₂(0) = false, r₂(1) = true` が同じ HasCharRank 条件を（Bool の反対称性により）**一意に** 定まることを確認せよ。
4. 次に添字集合を `WithBot Bool`（`⊥ ≤ false ≤ true`）に拡大し、`level ⊥ = ∅` として同じ carrier を使った場合、`r(1) = true` と `r(1) = false` の **両方** が HasCharRank 類似の条件を満たしうる前順序的状況（非反対称的添字）を構成して、rank uniqueness の反例とせよ。

数学的背景: Theorem B の証明で `Nat.le_antisymm` を使う箇所は、添字集合が `PartialOrder`（反対称的）でなければ成立しない。前順序では同値クラス内で rank が非一意になる。

**Lean シグネチャ例**
```lean
-- Bool は LinearOrder なので PartialOrder → 一意性は保たれる
-- 反例は非反対称的な前順序が必要

-- 2点だが相互に ≤ が成り立つ前順序（同値だが等しくない）
inductive TwoPoint where | a | b

instance : Preorder TwoPoint where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

-- この前順序は反対称ではない: a ≤ b かつ b ≤ a だが a ≠ b

theorem twoPoint_not_antisymm :
    ¬ (∀ x y : TwoPoint, x ≤ y → y ≤ x → x = y) := sorry

-- TwoPoint-indexed tower で rank が非一意
def twoPointTower : StructureTower TwoPoint ℕ where
  level _ := Set.univ
  monotone_level := fun _ _ _ _ hx => hx

-- r₁ x = TwoPoint.a と r₂ x = TwoPoint.b の両方が
-- ∀ x i, x ∈ level i ↔ r(x) ≤ i を満たす
theorem rank_not_unique_preorder :
    ∃ (r₁ r₂ : ℕ → TwoPoint), r₁ ≠ r₂ ∧
      (∀ x i, x ∈ twoPointTower.level i ↔ r₁ x ≤ i) ∧
      (∀ x i, x ∈ twoPointTower.level i ↔ r₂ x ≤ i) := sorry
```

**ヒント**
- `TwoPoint` の前順序で `∀ x y, x ≤ y` とすれば `le_refl` と `le_trans` は自明に成立するが、`a ≤ b ∧ b ≤ a` かつ `a ≠ b` で反対称性が破れる。
- `level _ := Set.univ` かつ `∀ x y, x ≤ y` の前順序なら、任意の `r : ℕ → TwoPoint` が HasCharRank を満たす。
- `r₁ := fun _ => .a` と `r₂ := fun _ => .b` を取れば `r₁ ≠ r₂` だが両方 HasCharRank。

---

## 問題 6 — dual | 🟡

**目的**  
OrderDual による双対構成が StructureTower の理論で正しく機能し、`ofAntitone` と `reindex` が整合的に振る舞うことを検証する。

**問題文**  
イデアル冪塔 `idealPowTower I`（`ℕᵒᵖ`-indexed、`level n = ↑(I ^ ofDual n)`）に対して以下を行え:

1. `idealPowTower I` を `ℕ`-indexed の **反単調** 族 `d : ℕ → Set R`（`d n = ↑(I ^ n)`）と `ofAntitone` 構成の合成として再構成できることを示せ。すなわち `idealPowTower I = ofAntitone d hd` が（`ext` の意味で）成立することを証明せよ。
2. `ofAntitone` で得た `ℕᵒᵖ`-indexed 塔に対して、`OrderDual.toDual ∘ OrderDual.ofDual = id` を用いた `reindex` が恒等変換を与えることを確認せよ。
3. 双対の双対が元に戻ること（`ofAntitone` を2回適用した結果が元の単調族と `ext` で一致すること）を述べ、証明せよ。

**Lean シグネチャ例**
```lean
variable {R : Type*} [CommRing R] (I : Ideal R)

def idealPowAntitone : ℕ → Set R :=
  fun n => ↑(I ^ n)

theorem idealPowAntitone_antitone :
    Antitone (idealPowAntitone I) := sorry

theorem idealPowTower_eq_ofAntitone :
    idealPowTower I = ofAntitone (idealPowAntitone I)
      (idealPowAntitone_antitone I) := sorry
```

**ヒント**
- `Antitone` の証明には `Ideal.pow_le_pow_right` を使用。
- `ext` で各レベルの集合が一致することを示す際、`OrderDual.ofDual_toDual` の簡約が鍵。
- 双対の双対は `OrderDual.ofDual (OrderDual.toDual x) = x` による。

---

## 問題 7 — borderline | 🟡

**目的**  
ExhaustiveTower の公理をギリギリ満たす境界的な例を構成し、`exhaustive` 条件の tight な成立状況を把握する。

**問題文**  
以下の塔 `borderlineExhaustive` を構成せよ:

- 台集合 `α := ℕ`
- 添字集合 `ι := ℕ`
- `level n := {n}`（各レベルがちょうど1点のみを含む）

1. これが StructureTower の `monotone_level` を満たすことを証明せよ。（ヒント: `i ≤ j` のとき `{i} ⊆ {j}` は一般には偽だが、`i = j` のときのみ真。`i < j` のときは `{i} ⊆ {j}` を示す必要はない—— 待て、`monotone_level` は `i ≤ j → level i ⊆ level j` を要求するので、`i < j` の場合にも成立しなければならない。）
2. したがって、上記の定義は **StructureTower の公理を満たさない** ことを示せ。
3. 公理をギリギリ満たすように修正せよ: `level n := Set.Iic n`（累積的にする）との差を説明し、「各レベルに**新しく**加わる元がちょうど1つ」という意味での borderline を `level n \ level (n-1) = {n}`（`n ≥ 1` のとき）として定式化・証明せよ。

**Lean シグネチャ例**
```lean
-- 失敗する定義
def singletonTower_fails : ℕ → Set ℕ := fun n => {n}

theorem singletonTower_not_monotone :
    ¬ (∀ i j : ℕ, i ≤ j → singletonTower_fails i ⊆ singletonTower_fails j) := sorry

-- 修正: 累積版
-- natFiltration は level n = Set.Iic n

theorem natFiltration_layer (n : ℕ) (hn : 0 < n) :
    natFiltration.level n \ natFiltration.level (n - 1) = {n} := sorry
```

**ヒント**
- `singletonTower_not_monotone`: `i = 0`, `j = 1` で `0 ∈ {0}` だが `0 ∉ {1}` を使う。
- `natFiltration_layer`: `Set.Iic n \ Set.Iic (n-1)` = `{n}` は `Nat.lt_of_lt_pred` 等で場合分け。`ext` して `m ∈ Iic n ∧ m ∉ Iic (n-1) ↔ m = n` を示す。

---

## 問題 8 — non-example | 🟡

**目的**  
FilteredAddCommMonoid の公理を「あと一歩で」満たすが失敗する例を構成し、部分構造の閉性条件の精密さを確認する。

**問題文**  
台集合を `ℤ`（整数）、添字を `ℕ` として、以下の集合族を考える:

```
level n := {z : ℤ | z.natAbs ≤ n ∧ z ≠ 0} ∪ {0}    -- ← 修正前
level n := {z : ℤ | z.natAbs ≤ n ∧ Even z}           -- ← 本問の定義
```

1. `level n := {z : ℤ | z.natAbs ≤ n ∧ Even z}` が `monotone_level` を満たすことを示せ。
2. `zero_mem` が満たされることを確認せよ（`Even 0` は `⟨0, rfl⟩` で成立）。
3. しかし `add_mem` が **失敗する** ことを具体的反例で示せ。すなわち、ある `n` と `x, y ∈ level n` で `x + y ∉ level n` となるケースを構成せよ。

数学的背景: 偶数のみからなる集合は加法に関して閉じているが、`natAbs` の制約が加法の閉性を破壊する。`|x + y|` は `|x| + |y|` 以下であるが `n` 以下とは限らない——いや、`|x| ≤ n` かつ `|y| ≤ n` なら `|x+y| ≤ 2n`。問題は `level n` 内で `|x+y| ≤ n` が保証されないこと。

**Lean シグネチャ例**
```lean
def almostFiltered : ℕ → Set ℤ :=
  fun n => {z | z.natAbs ≤ n ∧ Even z}

theorem almostFiltered_monotone :
    Monotone almostFiltered := sorry

theorem almostFiltered_zero_mem (n : ℕ) :
    (0 : ℤ) ∈ almostFiltered n := sorry

theorem almostFiltered_not_add_closed :
    ¬ (∀ n, ∀ x y : ℤ, x ∈ almostFiltered n → y ∈ almostFiltered n →
      x + y ∈ almostFiltered n) := sorry
```

**ヒント**
- 反例: `n = 1` として `x = 0, y = 0` は自明に閉じるが、これでは反例にならない。`n = 2` として `x = 2, y = 2` なら `x + y = 4`, `natAbs 4 = 4 > 2`。
- `Even` 条件は `2 + 2 = 4` で保たれるが、`natAbs` 条件が破れる。

---

## 問題 9 — out-of-category | 🟡

**目的**  
StructureTower の圏の「外側」に位置するが塔的な風味を持つ構造を分析し、圏の境界を明確にする。

**問題文**  
以下の「擬似塔」構造を考える: 台集合 `α` 上の **部分集合の列** `S : ℕ → Set α` で、単調性ではなく **最終的単調性**（eventually monotone）を満たすもの:

```
∃ N, ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j
```

1. この条件は `monotone_level` より真に弱いことを、具体例（最初の有限個のレベルでのみ非単調な列）で示せ。
2. `eventually_monotone` な列 `S` に対し、`reindex (· + N)` で StructureTower を構成できること（打ち切り構成）を示せ。
3. しかし打ち切り構成は元の列の `level 0, ..., level (N-1)` の情報を失う。「eventually monotone な列をそのまま StructureTower として扱う拡張」が、`union` の一般的性質（例: `union` の結合的分解）をどのように破壊するか考察し、具体例を1つ挙げよ。

**Lean シグネチャ例**
```lean
def EventuallyMonotoneSeq (S : ℕ → Set α) : Prop :=
  ∃ N, ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j

-- eventually monotone だが monotone でない例
def evMonExample : ℕ → Set ℕ :=
  fun n => if n = 0 then {5} else Set.Iic n

theorem evMonExample_eventually_monotone :
    EventuallyMonotoneSeq evMonExample := sorry

theorem evMonExample_not_monotone :
    ¬ Monotone evMonExample := sorry

-- 打ち切りによる StructureTower 化
def truncateToTower (S : ℕ → Set α) (N : ℕ)
    (h : ∀ i j, N ≤ i → i ≤ j → S i ⊆ S j) :
    StructureTower ℕ α where
  level i := S (i + N)
  monotone_level := sorry
```

**ヒント**
- `evMonExample` で `N = 1` とすれば、`n ≥ 1` では `Set.Iic` で単調。`n = 0` で `{5} ⊄ {1} = Set.Iic 1` が非単調性の反例。
- 打ち切りの `monotone_level`: `h (i + N) (j + N) (Nat.le_add_left N i) (Nat.add_le_add_right hij N)` の形。

---

## 問題 10 — schema | 🟡

**目的**  
パラメータ化された塔のテンプレートを設計し、異なる数学的文脈で再利用可能な抽象パターンを提供する。

**問題文**  
以下の **閾値塔スキーマ** `thresholdTower` を定義・実装せよ:

台集合 `α` 上に「重み関数」`w : α → ι` が与えられたとき、
```
level i := {x : α | w x ≤ i}
```
は StructureTower を構成する。

1. `thresholdTower` を定義し、`monotone_level` を証明せよ。
2. `w = id` のとき `thresholdTower = iic α` であることを `ext` で示せ。
3. `w` が全射（`Function.Surjective w`）のとき、塔が ExhaustiveTower-like（全 `x` がいずれかのレベルに属する）ことを示せ。ただし添字が ℕ でない一般の場合なので、ExhaustiveTower の型ではなく `∀ x, ∃ i, x ∈ level i` として直接証明すること。
4. `FilteredAddCommMonoid` のスキーマ版: `α` が `AddCommMonoid` で `w` が加法的劣加法（`w (x + y) ≤ max (w x) (w y)` 型の条件——正確にはどういう条件が必要か？）のとき `add_mem` が成立するための `w` への十分条件を見つけ、定式化せよ。

**Lean シグネチャ例**
```lean
def thresholdTower (w : α → ι) : StructureTower ι α where
  level i := {x | w x ≤ i}
  monotone_level := fun _i _j hij _x hx => le_trans hx hij

theorem thresholdTower_eq_iic :
    thresholdTower (id : α → α) = iic α := sorry

theorem thresholdTower_exhaustive_of_surjective
    (w : α → ι) (hw : Function.Surjective w) :
    ∀ x : α, ∃ i : ι, x ∈ (thresholdTower w).level i := sorry
```

**ヒント**
- `thresholdTower_eq_iic`: `ext i x` で展開し、`Set.mem_Iic` と `Set.mem_setOf_eq` で一致を確認。
- 重み関数の全射性は `hw x` で `⟨w x, le_refl _⟩` を得るのに使う……いや、全射性は不要で `⟨w x, le_refl _⟩` で十分。全射性が必要になるのは「すべてのレベルが非空」を示す場合。
- 加法閉性の十分条件: `w 0 ≤ i`（零元条件）と `w (x + y) ≤ max (w x) (w y)` なら `max (w x) (w y) ≤ i` のとき `w(x+y) ≤ i`。ただし `max ≤ i ↔ w x ≤ i ∧ w y ≤ i` なので `x, y ∈ level i` から従う。

---

## 問題 11 — finite_computational | 🟢

**目的**  
有限かつ完全計算可能な例で、StructureTower の基本操作（`union`, `global`, `inter`, `sup`）の結果を明示的に列挙し、機械的検証を容易にする。

**問題文**  
添字集合 `ι := Fin 3`（`{0, 1, 2}`）、台集合 `α := Fin 5`（`{0, 1, 2, 3, 4}`）に対し、以下の塔を構成せよ:

```
level 0 := {0, 1}
level 1 := {0, 1, 2, 3}
level 2 := {0, 1, 2, 3, 4}
```

1. `monotone_level` を `Fin.le_iff_val_le_val` と `decide` を活用して証明せよ。
2. `union = Set.univ` を証明せよ。
3. `global = {0, 1}` を証明せよ。
4. 別の塔 `T₂` を `level 0 := {0}`, `level 1 := {0, 2}`, `level 2 := {0, 2, 4}` として構成し、`inter T₁ T₂` の各レベルを明示的に計算せよ（`inter` はレベルごとの交叉）。

期待される計算結果:
- `(inter T₁ T₂).level 0 = {0}`
- `(inter T₁ T₂).level 1 = {0, 2}`
- `(inter T₁ T₂).level 2 = {0, 2, 4}`

**Lean シグネチャ例**
```lean
def finTower1 : StructureTower (Fin 3) (Fin 5) where
  level := fun i => match i with
    | ⟨0, _⟩ => {0, 1}
    | ⟨1, _⟩ => {0, 1, 2, 3}
    | ⟨2, _⟩ => {0, 1, 2, 3, 4}
    | ⟨n+3, h⟩ => absurd h (by omega)
  monotone_level := sorry -- decide or omega

theorem finTower1_union :
    finTower1.union = Set.univ := sorry

theorem finTower1_global :
    finTower1.global = {0, 1} := sorry

def finTower2 : StructureTower (Fin 3) (Fin 5) where
  level := fun i => match i with
    | ⟨0, _⟩ => {0}
    | ⟨1, _⟩ => {0, 2}
    | ⟨2, _⟩ => {0, 2, 4}
    | ⟨n+3, h⟩ => absurd h (by omega)
  monotone_level := sorry

theorem finTower_inter_level0 :
    (inter finTower1 finTower2).level ⟨0, by omega⟩ = {0} := sorry
```

---

## まとめ

### 難易度分布

| カテゴリ | 難易度 | 主要テーマ |
|:---|:---:|:---|
| trivial | 🟢 | 空塔（Unit × Empty） |
| canonical | 🟢 | natFiltration の ExhaustiveTower 化と rank = id |
| finite_computational | 🟢 | Fin 3 × Fin 5 での明示的計算 |
| dual | 🟡 | idealPowTower と ofAntitone の整合性 |
| borderline | 🟡 | 単点レベル vs 累積レベル、layer の定式化 |
| non-example | 🟡 | 偶数制約の加法非閉性 |
| out-of-category | 🟡 | eventually monotone 列の打ち切り構成 |
| schema | 🟡 | thresholdTower（重み関数パターン） |
| extreme | 🔴 | Ordinal-indexed tower のスケーラビリティ |
| pathological | 🔴 | FakeTower における liftCl 関手性の崩壊 |
| counterexample | 🔴 | 前順序での rank 非一意性（Theorem B の逆の反例） |

### 特に重要な問題

**問題 5（counterexample）** は理論の核心に最も深く関わる。Theorem B（rank uniqueness）が `PartialOrder`（反対称性）に本質的に依存していることを、たった2点の前順序空間 `TwoPoint` で鮮明に示す。この反例は「なぜ ℕ-indexed に限定するのか」「前順序を半順序に制限する代償は何か」という設計判断の根拠を提供する。

**問題 10（schema）** の `thresholdTower` は、`iic`, `ofMonotoneSeq`, `idealPowTower` を統一する汎用パターンであり、フレームワークの再利用性を直接体現する。特に加法閉性の十分条件（劣加法的重み関数）の定式化は、FilteredAddCommMonoid の公理がどのような重み構造から自然に生じるかを明らかにし、新しい応用領域の発見に直結する。
