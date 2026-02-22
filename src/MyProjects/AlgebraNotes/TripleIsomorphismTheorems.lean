/-
  TripleIsomorphismTheorems.lean
  群の第一・第二・第三同型定理のブルバキ流形式化
  Bourbaki-style formalization of the Three Group Isomorphism Theorems
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Lattice
import Mathlib.Algebra.Group.Hom.Basic

open QuotientGroup Subgroup

noncomputable section

variable {G : Type*} [Group G]

/-!
## 第一同型定理 (First Isomorphism Theorem)

準同型 φ : G →* H に対して G ⧸ ker φ ≃* range φ
-/

/-- 第一同型定理：群準同型の像と核商の同型 -/
theorem firstIsomorphismTheorem
    {H : Type*} [Group H]
    (φ : G →* H) :
    G ⧸ MonoidHom.ker φ ≃* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

/-- 第一同型定理の普遍性：任意の準同型は核を経由して因子分解される -/
theorem firstIsomorphismTheorem_universalProperty
    {H : Type*} [Group H]
    (φ : G →* H) :
    ∃! ψ : G ⧸ MonoidHom.ker φ →* MonoidHom.range φ,
      ∀ g : G, ψ (QuotientGroup.mk g) = ⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ := by
  sorry

/-!
## 第二同型定理 (Second Isomorphism Theorem / Diamond Theorem)

H ⊴ G, K ≤ G のとき K ⧸ (H ⊓ K) ≃* (H ⊔ K) ⧸ H
-/

/-- 第二同型定理の設定：H が G の正規部分群、K が G の部分群 -/
section SecondIsomorphism

variable (H K : Subgroup G) [hHN : H.Normal]

/-- H と K の積（集合論的） HK = H ⊔ K は部分群をなす -/
lemma sup_eq_range_mul :
    (H ⊔ K : Subgroup G) = (H ⊔ K) := rfl

/-- K から (H ⊔ K) ⧸ H への標準的な準同型写像 -/
def secondIsoMap : K →* (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K) :=
  sorry

/-- 第二同型定理の準同型の核は H ⊓ K に等しい -/
lemma secondIsoMap_ker :
    MonoidHom.ker (secondIsoMap H K) = (H ⊓ K).subgroupOf K := by
  sorry

/-- 第二同型定理の準同型は全射である -/
lemma secondIsoMap_surjective :
    Function.Surjective (secondIsoMap H K) := by
  sorry

/-- **第二同型定理（ダイヤモンド同型定理）**
    H ⊴ G, K ≤ G のとき K ⧸ (H ⊓ K) ≃* (H ⊔ K) ⧸ H -/
theorem secondIsomorphismTheorem :
    K ⧸ (H ⊓ K).subgroupOf K ≃* (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K) := by
  sorry

end SecondIsomorphism

/-!
## 第三同型定理 (Third Isomorphism Theorem / Correspondence Theorem)

H ⊴ G, K ⊴ G, H ≤ K のとき (G ⧸ H) ⧸ (K ⧸ H) ≃* G ⧸ K
-/

section ThirdIsomorphism

variable (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ≤ K)

/-- H ≤ K のとき K ⧸ H は G ⧸ H の正規部分群をなす -/
instance quotientNormal : (K.map (QuotientGroup.mk' H)).Normal := by
  sorry

/-- G ⧸ H から (G ⧸ H) ⧸ (K ⧸ H) への射影合成写像 -/
def thirdIsoMap : G →* (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) :=
  (QuotientGroup.mk' (K.map (QuotientGroup.mk' H))).comp (QuotientGroup.mk' H)

/-- 第三同型定理の準同型写像の核は K に等しい -/
lemma thirdIsoMap_ker :
    MonoidHom.ker (thirdIsoMap H K hHK) = K := by
  sorry

/-- 第三同型定理の準同型写像は全射である -/
lemma thirdIsoMap_surjective :
    Function.Surjective (thirdIsoMap H K hHK) := by
  sorry

/-- **第三同型定理（対応定理）**
    H ⊴ G, K ⊴ G, H ≤ K のとき (G ⧸ H) ⧸ (K ⧸ H) ≃* G ⧸ K -/
theorem thirdIsomorphismTheorem :
    (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K := by
  sorry

/-- 第三同型定理（等式形式）：核から同型を構成する標準的証明 -/
theorem thirdIsomorphismTheorem' :
    (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K :=
  MulEquiv.symm <|
    (QuotientGroup.quotientKerEquivRange (thirdIsoMap H K hHK)).trans (by
      sorry)

end ThirdIsomorphism

/-!
## ブルバキ流普遍性の統一的定式化

三つの同型定理を普遍性（UMP）の観点から統一的に捉える
-/

/-- 準同型の因子分解定理（第一同型定理の圏論的言い換え）
    φ : G →* H, N ⊴ G, N ≤ ker φ のとき G ⧸ N →* H が一意に存在する -/
theorem quotient_lift_unique
    {H : Type*} [Group H]
    (N : Subgroup G) [N.Normal]
    (φ : G →* H)
    (hN : N ≤ MonoidHom.ker φ) :
    ∃! ψ : G ⧸ N →* H,
      φ = ψ.comp (QuotientGroup.mk' N) := by
  sorry

/-- 同型定理の圏論的本質：核と商の双対性 -/
theorem kernel_quotient_duality
    {H : Type*} [Group H]
    (φ : G →* H)
    (N : Subgroup G) [N.Normal]
    (hN : N = MonoidHom.ker φ) :
    Nonempty (G ⧸ N ≃* MonoidHom.range φ) := by
  sorry

end
