/-
  Bourbaki-inspired P4: Category Theory (圏論)
  Bourbaki の構造主義を圏論的に再解釈する

  難易度: 上級
  推奨学習時間: 6〜10週間
  前提: P1_Extended.lean (§6 普遍性), P1_5_Algebra.lean
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory

namespace BourbakiP4

-- ============================================================
-- Part I: 圏の基礎 (Catégories)
-- ============================================================

section CategoryBasics

variable {C : Type*} [Category C]

/-- 射の結合法則。 -/
theorem comp_assoc {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  exact Category.assoc f g h

/-- 恒等射は左単位元。 -/
theorem id_comp {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  exact Category.id_comp f

/-- 恒等射は右単位元。 -/
theorem comp_id {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  exact Category.comp_id f

/-- 同型の対称性。 -/
def iso_symm {X Y : C} (e : X ≅ Y) : Y ≅ X := by
  exact e.symm

/-- 同型の推移性。 -/
def iso_trans {X Y Z : C} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) : X ≅ Z := by
  exact e₁.trans e₂

end CategoryBasics

-- ============================================================
-- Part II: 関手 (Foncteurs)
-- ============================================================

section Functors

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- 関手は射の合成を保存する。 -/
theorem functor_map_comp (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  exact F.map_comp f g

/-- 関手は恒等射を保存する。 -/
theorem functor_map_id (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  exact F.map_id X

/-- 関手の合成。 -/
theorem functor_comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  rfl

/-- 関手は同型を保存する。 -/
def functor_preserves_iso (F : C ⥤ D) {X Y : C} (e : X ≅ Y) :
    F.obj X ≅ F.obj Y := by
  exact F.mapIso e

end Functors

-- ============================================================
-- Part III: 自然変換 (Transformations naturelles)
-- ============================================================

section NaturalTransformations

variable {C D : Type*} [Category C] [Category D]

/-- 自然変換の naturality 条件。 -/
theorem nat_trans_naturality {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := by
  exact α.naturality f

/-- 自然同型は各成分が同型。 -/
def nat_iso_component_iso {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    F.obj X ≅ G.obj X := by
  exact e.app X

end NaturalTransformations

-- ============================================================
-- Part IV: 米田の補題 (Lemme de Yoneda)
-- Bourbaki 的普遍性の圏論的定式化
-- ============================================================

section YonedaLemma

variable {C : Type*} [Category C]

/-- 米田埋め込みは忠実充満。 -/
-- 演習課題
def yoneda_fully_faithful :
    (yoneda (C := C)).FullyFaithful := by
  exact Yoneda.fullyFaithful

/-
米田の補題:
    Hom(h_X, F) ≅ F(X) (自然同型)。 -/
-- この深い定理は Mathlib の yonedaEquiv として実装されている

-- 演習: 具体的な圏（例えば Set）で米田の補題を確認
-- yonedaEquiv の型を #check で確認してみよう

end YonedaLemma

-- ============================================================
-- Part V: 極限と余極限 (Limites et colimites)
-- ============================================================

section LimitsColimits

variable {C : Type*} [Category C]

/-
積の普遍性（P1_Extended §6 の圏論的一般化）。
    P1_Extended の prodLift を圏論的に再解釈。 -/

-- 演習: 等化子 (equalizer) の普遍性を確認
-- 参考: Limits.Shapes.Equalizers

/- 演習: 引き戻し (pullback) の普遍性。 -/
-- pullback は等化子と積から構成できることを確認
-- 参考: Limits.Shapes.Pullbacks

/- 極限の存在 → 完備圏。 -/
-- 演習課題
-- 有限極限を持つ圏の性質を調べる

end LimitsColimits

-- ============================================================
-- Part VI: 随伴関手 (Foncteurs adjoints)
-- Bourbaki の Galois 接続の圏論的一般化
-- ============================================================

section Adjunctions

variable {C D : Type*} [Category C] [Category D]

/-
随伴は Galois 接続の一般化:
    P1_Extended §1 の GaloisConnection は Preorder 圏の随伴。 -/

/-- 随伴の定義的性質: Hom(Lc, d) ≅ Hom(c, Rd)。 -/
-- 演習課題
def adjunction_hom_equiv (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (X : C) (Y : D) :
    (L.obj X ⟶ Y) ≃ (X ⟶ R.obj Y) := by
  exact adj.homEquiv X Y

/- 左随伴は余極限を保存する。 -/
-- 演習課題 (高度)
-- 参考: Adjunction.leftAdjoint_preservesColimits

/- 右随伴は極限を保存する。 -/
-- 演習課題 (高度)
-- 参考: Adjunction.rightAdjoint_preservesLimits

end Adjunctions

-- ============================================================
-- Part VII: 圏の同値 (Équivalence de catégories)
-- ============================================================

section Equivalences

variable {C D : Type*} [Category C] [Category D]

/-- 圏の同値は関手の同型ペア。 -/
def equivalence_inv_fun_id (e : C ≌ D) :
    e.inverse ⋙ e.functor ≅ 𝟭 D := by
  exact e.counitIso

def equivalence_fun_inv_id (e : C ≌ D) :
    e.functor ⋙ e.inverse ≅ 𝟭 C := by
  exact e.unitIso.symm

/-
同値な圏は「同じ」圏論的性質を持つ。
    演習: 同値が極限の存在を保存することを確認。 -/

end Equivalences

-- ============================================================
-- Part VIII: モナド (Monades)
-- 随伴から生まれる構造
-- ============================================================

section Monads

variable {C : Type*} [Category C]

/-- 随伴からモナドが生まれる。 -/
-- 演習課題
def adjunction_gives_monad {D : Type*} [Category D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) :
    Monad C := by
  exact adj.toMonad

/-
モナドの単位 (η) と乗法 (μ) の性質。
    μ ∘ ηT = id, μ ∘ Tη = id, μ ∘ μT = μ ∘ Tμ -/
-- 演習: Monad.left_unit, Monad.right_unit, Monad.assoc を確認

end Monads

-- ============================================================
-- Part IX: Abel圏入門 (Catégories abéliennes)
-- Bourbaki, Algèbre X (ホモロジー代数)
-- ============================================================

section AbelianCategories

-- Abel 圏は加群の圏の抽象化
-- すべての射が核と余核を持ち、像と余像が同型

-- 演習: 以下の性質を確認
-- 1. Abel圏では短完全列が定義できる
-- 2. 蛇の補題 (snake lemma)
-- 3. 五項補題 (five lemma)

-- 参考: CategoryTheory.Abelian

end AbelianCategories

-- ============================================================
-- Part X: 統合課題 - Bourbaki構造主義の圏論的再解釈
-- ============================================================

section Integration

/-
P1 → P4 の対応表:

  P1 の概念           圏論的対応
  ─────────────────────────────────
  前順序 (Preorder)    薄い圏 (thin category)
  Galois接続           随伴関手
  群準同型の像          射の像 (image)
  商群                  余核 (cokernel)
  直積のコンパクト性    極限の保存
  普遍射 (prodLift)    極限の普遍性

  P1_5 の概念          圏論的対応
  ─────────────────────────────────
  テンソル積           モノイダル圏の ⊗
  局所化               圏の局所化
  自由加群             自由関手 (左随伴)
  商環                 余核

  P2 の概念            圏論的対応
  ─────────────────────────────────
  Lp空間               関手 L^p
  双対空間             反変関手 Hom(−, k)
  Hahn-Banach          部分対象からの拡張
-/

-- 最終演習: 好きな Bourbaki の定理を1つ選び、
-- その圏論的意味を Lean 4 で形式化せよ。

end Integration

end BourbakiP4
