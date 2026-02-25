## 数学的背景・方針

ニコラ・ブルバキの集合論（*Theory of Sets*, 1968）は以下の特徴を持ちます：

**主要トピック：**
1. **τ演算子（ヒルベルトのε）** — 「性質Pを満たす何らかの元」を選ぶ選択演算子。Lean4では `Classical.choice` / `Classical.epsilon` に対応。
2. **関係と作用素** — 集合論的な関係を一階述語論理で構成。
3. **順序対の定義** — クラトフスキーの定義 `(a, b) = {{a}, {a, b}}`。
4. **函数（写像）** — 函数的関係として定義し、全射・単射・全単射を導出。
5. **同値関係と商集合** — 分割との対応。
6. **基数・整列順序** — 選択公理を用いた基数比較。

Lean4/Mathlib4 では多くがすでに整備されているため、**ブルバキの構成をどう Mathlib の概念と対応させるか**を学ぶスケルトンとして設計します。

---

```lean
-- ============================================================
-- ブルバキ集合論 学習スケルトン
-- 参考: N. Bourbaki, "Theory of Sets" (1968)
-- ============================================================

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.WellFounded
import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Basic

open Set Function

noncomputable section

namespace Bourbaki

-- ============================================================
-- §1. τ 演算子（ヒルベルトの ε、選択演算子）
-- ============================================================

/-- ブルバキの τ 演算子：性質 P を持つ元が存在するとき、その一つを選ぶ。
    Mathlib の `Classical.epsilon` に対応する。
    ブルバキでは「τ_x(P(x))」と書く。 -/
def tau {α : Type*} (P : α → Prop) : α :=
  Classical.epsilon P

/-- τ 演算子の基本性質：P を満たす元が存在するなら、τ(P) も P を満たす。
    ブルバキの公理 S4（τ 公理）に対応。 -/
lemma tau_spec {α : Type*} (P : α → Prop) (h : ∃ x, P x) : P (tau P) := by
  exact Classical.epsilon_spec h

/-- 排中律は τ 演算子から導出できる（ブルバキ流） -/
lemma bourbaki_lem (P : Prop) : P ∨ ¬P := by
  exact Classical.em P

-- ============================================================
-- §2. 関係（Relations）
-- ============================================================

/-- 二項関係の定義：X × X 上の述語 -/
def Relation (α : Type*) := α → α → Prop

/-- 関係 R の定義域（domain） -/
def relDomain {α : Type*} (R : Relation α) : Set α :=
  { x | ∃ y, R x y }

/-- 関係 R の値域（range） -/
def relRange {α : Type*} (R : Relation α) : Set α :=
  { y | ∃ x, R x y }

/-- 関係の逆（converse）：ブルバキでは「R^{-1}」と表記 -/
def relInverse {α : Type*} (R : Relation α) : Relation α :=
  fun x y => R y x

/-- 関係の合成（composition） -/
def relComp {α : Type*} (R S : Relation α) : Relation α :=
  fun x z => ∃ y, R x y ∧ S y z

-- ============================================================
-- §3. 函数（Fonctions）
-- ============================================================

/-- 函数的関係（functional relation）：各 x に対して y は高々一つ -/
def IsFunctional {α : Type*} (R : Relation α) : Prop :=
  ∀ x y z, R x y → R x z → y = z

/-- 全域的函数的関係（total functional relation）：函数に対応 -/
def IsTotalFunctional {α β : Type*} (R : α → β → Prop) : Prop :=
  (∀ x, ∃ y, R x y) ∧ (∀ x y z, R x y → R x z → y = z)

/-- 全射（surjection）の条件 -/
def IsSurjection {α β : Type*} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- 単射（injection）の条件 -/
def IsInjection {α β : Type*} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- 全単射（bijection）の条件 -/
def IsBijection {α β : Type*} (f : α → β) : Prop :=
  IsSurjection f ∧ IsInjection f

/-- 単射は Mathlib の `Injective` と一致する -/
lemma injection_iff_injective {α β : Type*} (f : α → β) :
    IsInjection f ↔ Injective f := by
  simp [IsInjection, Injective]

/-- 全射は Mathlib の `Surjective` と一致する -/
lemma surjection_iff_surjective {α β : Type*} (f : α → β) :
    IsSurjection f ↔ Surjective f := by
  simp [IsSurjection, Surjective]

/-- 全単射から同値（Equiv）を構成する -/
def bijectionToEquiv {α β : Type*} (f : α → β) (hf : IsBijection f) : α ≃ β := by
  exact {
    toFun := f
    invFun := fun b => tau (fun a => f a = b)
    left_inv := by
      intro a
      sorry
    right_inv := by
      intro b
      sorry
  }

-- ============================================================
-- §4. 同値関係（Relations d'équivalence）
-- ============================================================

/-- 同値関係の公理的定義（ブルバキ流） -/
structure EquivRelation (α : Type*) where
  /-- 関係本体 -/
  rel : α → α → Prop
  /-- 反射律 -/
  refl  : ∀ x, rel x x
  /-- 対称律 -/
  symm  : ∀ x y, rel x y → rel y x
  /-- 推移律 -/
  trans : ∀ x y z, rel x y → rel y z → rel x z

/-- EquivRelation から Setoid を構成する -/
def EquivRelation.toSetoid {α : Type*} (R : EquivRelation α) : Setoid α where
  r     := R.rel
  iseqv := ⟨R.refl, R.symm _ _, R.trans _ _ _⟩

/-- 同値類（equivalence class）：x の同値類 -/
def equivClass {α : Type*} (R : EquivRelation α) (x : α) : Set α :=
  { y | R.rel x y }

/-- 商集合（quotient set）：同値類全体の集族 -/
def quotientSet {α : Type*} (R : EquivRelation α) : Set (Set α) :=
  { C | ∃ x, C = equivClass R x }

/-- 同値類は互いに素（disjoint）または等しい -/
lemma equivClass_disjoint_or_eq {α : Type*} (R : EquivRelation α) (x y : α) :
    equivClass R x ∩ equivClass R y = ∅ ∨ equivClass R x = equivClass R y := by
  sorry

/-- 商集合は α の分割（partition）をなす -/
lemma quotientSet_partition {α : Type*} (R : EquivRelation α) :
    ∀ x : α, ∃ C ∈ quotientSet R, x ∈ C := by
  sorry

-- ============================================================
-- §5. 順序関係（Relations d'ordre）
-- ============================================================

/-- 前順序（préordre）の構造 -/
structure Preorder' (α : Type*) where
  /-- 順序関係 -/
  le    : α → α → Prop
  /-- 反射律 -/
  refl  : ∀ x, le x x
  /-- 推移律 -/
  trans : ∀ x y z, le x y → le y z → le x z

/-- 半順序（ordre partiel）：前順序 + 反対称律 -/
structure PartialOrder' (α : Type*) extends Preorder' α where
  /-- 反対称律 -/
  antisymm : ∀ x y, le x y → le y x → x = y

/-- 全順序（ordre total）：半順序 + 全順序律 -/
structure TotalOrder' (α : Type*) extends PartialOrder' α where
  /-- 全順序律（比較可能性） -/
  total : ∀ x y, le x y ∨ le y x

/-- 最小元（minimum）の定義 -/
def IsMinimum {α : Type*} (O : PartialOrder' α) (S : Set α) (m : α) : Prop :=
  m ∈ S ∧ ∀ x ∈ S, O.le m x

/-- 整列集合（ensemble bien ordonné）：すべての非空部分集合が最小元を持つ -/
def IsWellOrdered {α : Type*} (O : TotalOrder' α) : Prop :=
  ∀ S : Set α, S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, O.le m x

-- ============================================================
-- §6. 基数（Cardinaux）と同等性
-- ============================================================

/-- 集合 A と B が同等（équipotent）：全単射が存在する -/
def Equipotent (α β : Type*) : Prop :=
  Nonempty (α ≃ β)

/-- 同等性は同値関係 -/
lemma equipotent_refl (α : Type*) : Equipotent α α := by
  exact ⟨Equiv.refl α⟩

lemma equipotent_symm {α β : Type*} (h : Equipotent α β) : Equipotent β α := by
  sorry

lemma equipotent_trans {α β γ : Type*} (h₁ : Equipotent α β) (h₂ : Equipotent β γ) :
    Equipotent α γ := by
  sorry

/-- カントール・ベルンシュタインの定理：
    A ↪ B かつ B ↪ A ならば A ≃ B -/
theorem cantorBernstein {α β : Type*}
    (f : α ↪ β) (g : β ↪ α) : Equipotent α β := by
  sorry

/-- A が B に単射的に埋め込めるとき、|A| ≤ |B| とみなす -/
def CardLE (α β : Type*) : Prop :=
  Nonempty (α ↪ β)

/-- 選択公理のもとで、任意の二集合は基数が比較可能 -/
theorem cardinal_comparable (α β : Type*) :
    CardLE α β ∨ CardLE β α := by
  sorry

-- ============================================================
-- §7. 選択公理と同値命題
-- ============================================================

/-- 選択公理（Axiome du choix）：
    各 i に対して非空な集合族 { A_i } から元を選ぶ函数が存在する -/
theorem axiomOfChoice {ι : Type*} {A : ι → Set α} (h : ∀ i, (A i).Nonempty) :
    ∃ f : ι → α, ∀ i, f i ∈ A i := by
  exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec⟩

/-- 整列定理（Théorème de Zermelo）：
    任意の集合は整列可能（選択公理と同値） -/
theorem wellOrderingPrinciple (α : Type*) :
    ∃ (R : α → α → Prop), IsWellOrder α R := by
  sorry

end Bourbaki

end
```

---

**学習のポイント：**

各 `sorry` は独立した証明課題になっています。難易度の目安は次の通りです：

| 補題・定理 | 難易度 | 使うべき Mathlib 補題 |
|---|---|---|
| `equivClass_disjoint_or_eq` | ★★☆ | `Set.disjoint_iff` |
| `equipotent_symm/trans` | ★☆☆ | `Equiv.symm`, `Equiv.trans` |
| `cantorBernstein` | ★★★ | `Function.Embedding.schroederBernstein` |
| `bijectionToEquiv` | ★★☆ | `Classical.epsilon_spec` |
| `cardinal_comparable` | ★★★ | `Cardinal.le_total` |

`§6`・`§7` は選択公理に依存するため `noncomputable` が必須です。