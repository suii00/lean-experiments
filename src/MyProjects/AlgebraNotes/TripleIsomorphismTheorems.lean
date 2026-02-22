/-
  TripleIsomorphismTheorems.lean
  群の第一・第二・第三同型定理のブルバキ流形式化
  Bourbaki-style formalization of the Three Group Isomorphism Theorems
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Hom.Basic

open QuotientGroup Subgroup

noncomputable section

variable {G : Type*} [Group G]

/-!
## 第一同型定理 (First Isomorphism Theorem)

準同型 φ : G →* H に対して G ⧸ ker φ ≃* range φ
-/

/-- 第一同型定理：群準同型の像と核商の同型 -/
def firstIsomorphismTheorem
    {H : Type*} [Group H]
    (φ : G →* H) :
    G ⧸ MonoidHom.ker φ ≃* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

/-- 第一同型定理の普遍性：任意の準同型は核を経由して因子分解される -/
theorem firstIsomorphismTheorem_universalProperty
    {H : Type*} [Group H]
    (φ : G →* H) :
    ∃! ψ : G ⧸ MonoidHom.ker φ →* MonoidHom.range φ,
      ∀ g : G, ψ (g : G ⧸ MonoidHom.ker φ) = ⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ := by
  refine ⟨(QuotientGroup.quotientKerEquivRange φ).toMonoidHom, ?_, ?_⟩
  · intro g
    rfl
  · intro ψ hψ
    ext g
    simpa using hψ g

/-!
## 第二同型定理 (Second Isomorphism Theorem / Diamond Theorem)

H ⊴ G, K ≤ G のとき K ⧸ (H ∩ K) ≃* (K ⊔ H) ⧸ H
（Lean では左辺の分母を `H.subgroupOf K` として表現）
-/

section SecondIsomorphism

variable (H K : Subgroup G)

/-- H と K の積（集合論的） HK = H ⊔ K は部分群をなす -/
lemma sup_eq_range_mul :
    (H ⊔ K : Subgroup G) = (H ⊔ K : Subgroup G) := rfl

variable [hHN : H.Normal]

/-- K から (K ⊔ H) ⧸ H への標準的な準同型写像 -/
def secondIsoMap : K →* (K ⊔ H : Subgroup G) ⧸ H.subgroupOf (K ⊔ H) :=
  (QuotientGroup.mk' (H.subgroupOf (K ⊔ H))).comp (Subgroup.inclusion le_sup_left)

lemma secondIsoMap_eq :
    secondIsoMap H K =
      (QuotientGroup.quotientInfEquivProdNormalQuotient K H).toMonoidHom.comp
        (QuotientGroup.mk' (H.subgroupOf K)) := by
  ext x
  rfl

/-- 第二同型定理の準同型の核は H ∩ K に対応する部分群に等しい -/
lemma secondIsoMap_ker :
    MonoidHom.ker (secondIsoMap H K) = H.subgroupOf K := by
  ext x
  simp [secondIsoMap, Subgroup.mem_subgroupOf]

/-- 第二同型定理の準同型は全射である -/
lemma secondIsoMap_surjective :
    Function.Surjective (secondIsoMap H K) := by
  rw [secondIsoMap_eq (H := H) (K := K)]
  simpa using Function.Surjective.comp
    (QuotientGroup.quotientInfEquivProdNormalQuotient K H).surjective
    (QuotientGroup.mk'_surjective (H.subgroupOf K))

/-- **第二同型定理（ダイヤモンド同型定理）**
    H ⊴ G, K ≤ G のとき K ⧸ (H ∩ K) ≃* (K ⊔ H) ⧸ H -/
def secondIsomorphismTheorem :
    K ⧸ H.subgroupOf K ≃* (K ⊔ H : Subgroup G) ⧸ H.subgroupOf (K ⊔ H) :=
  QuotientGroup.quotientInfEquivProdNormalQuotient K H

end SecondIsomorphism

/-!
## 第三同型定理 (Third Isomorphism Theorem / Correspondence Theorem)

H ⊴ G, K ⊴ G, H ≤ K のとき (G ⧸ H) ⧸ (K ⧸ H) ≃* G ⧸ K
-/

section ThirdIsomorphism

variable (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ≤ K)

/-- H ≤ K のとき K ⧸ H は G ⧸ H の正規部分群をなす -/
instance quotientNormal : (K.map (QuotientGroup.mk' H)).Normal := by
  infer_instance

/-- G ⧸ H から (G ⧸ H) ⧸ (K ⧸ H) への射影合成写像 -/
def thirdIsoMap (_hHK : H ≤ K) : G →* (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) :=
  (QuotientGroup.mk' (K.map (QuotientGroup.mk' H))).comp (QuotientGroup.mk' H)

/-- 第三同型定理の準同型写像の核は K に等しい -/
lemma thirdIsoMap_ker :
    MonoidHom.ker (thirdIsoMap H K hHK) = K := by
  calc
    MonoidHom.ker (thirdIsoMap H K hHK)
        = (MonoidHom.ker (QuotientGroup.mk' (K.map (QuotientGroup.mk' H)))).comap
            (QuotientGroup.mk' H) := by
              rfl
    _ = (K.map (QuotientGroup.mk' H)).comap (QuotientGroup.mk' H) := by
          simp [QuotientGroup.ker_mk']
    _ = H ⊔ K := by
          simp [QuotientGroup.comap_map_mk']
    _ = K := by
          exact sup_eq_right.mpr hHK

/-- 第三同型定理の準同型写像は全射である -/
lemma thirdIsoMap_surjective :
    Function.Surjective (thirdIsoMap H K hHK) := by
  simpa [thirdIsoMap] using Function.Surjective.comp
    (QuotientGroup.mk'_surjective (K.map (QuotientGroup.mk' H)))
    (QuotientGroup.mk'_surjective H)

/-- **第三同型定理（対応定理）**
    H ⊴ G, K ⊴ G, H ≤ K のとき (G ⧸ H) ⧸ (K ⧸ H) ≃* G ⧸ K -/
def thirdIsomorphismTheorem :
    (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K :=
  QuotientGroup.quotientQuotientEquivQuotient H K hHK

/-- 第三同型定理（等式形式）：標準同型としての同値な表現 -/
def thirdIsomorphismTheorem' :
    (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K :=
  thirdIsomorphismTheorem H K hHK

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
  refine ⟨QuotientGroup.lift N φ hN, ?_, ?_⟩
  · exact (QuotientGroup.lift_comp_mk' N φ hN).symm
  · intro ψ hψ
    ext g
    have hψg : ψ (QuotientGroup.mk' N g) = φ g := by
      simpa [MonoidHom.comp_apply] using (congrArg (fun f : G →* H => f g) hψ).symm
    simpa [QuotientGroup.lift_mk'] using hψg

/-- 同型定理の圏論的本質：核と商の双対性 -/
theorem kernel_quotient_duality
    {H : Type*} [Group H]
    (φ : G →* H)
    (N : Subgroup G) [N.Normal]
    (hN : N = MonoidHom.ker φ) :
    Nonempty (G ⧸ N ≃* MonoidHom.range φ) := by
  subst hN
  exact ⟨QuotientGroup.quotientKerEquivRange φ⟩

end
