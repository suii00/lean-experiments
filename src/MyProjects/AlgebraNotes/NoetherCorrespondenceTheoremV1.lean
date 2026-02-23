/-
# Noether Correspondence Theorem
## ニコラ・ブルバキの数学原論・ZF集合論に基づく形式化

商環 R/I のイデアル格子と、I を含む R のイデアル格子の
完全な双射対応を確立する。
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

namespace NoetherCorrespondence

open Ideal Ideal.Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

noncomputable section

/-!
## Part I: 基本写像の定義
-/

/-- I を含むイデアルの部分型 -/
abbrev IdealOver := {J : Ideal R // I ≤ J}

/-- 商環への標準的全射 -/
abbrev π : R →+* R ⧸ I := Ideal.Quotient.mk I

/-!
## Part II: 対応写像の定義
-/

/-- 順方向写像：I を含むイデアル J を R/I のイデアル π(J) に送る -/
def forward : IdealOver I → Ideal (R ⧸ I) :=
  fun ⟨J, _⟩ => Ideal.map (π I) J

/-- 逆方向写像：R/I のイデアル K̄ を引き戻し π⁻¹(K̄) に送る -/
def backward : Ideal (R ⧸ I) → IdealOver I :=
  fun K => ⟨Ideal.comap (π I) K, by
    intro r hr
    simp [π, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]⟩

/-!
## Part III: 補助補題
-/

/-- イデアル写像のメンバーシップ特徴付け -/
lemma mem_map_iff (J : Ideal R) (x : R ⧸ I) :
    x ∈ Ideal.map (π I) J ↔ ∃ r ∈ J, (π I) r = x := by
  simpa [and_left_comm, and_assoc] using
    (Ideal.mem_map_iff_of_surjective (π I) Ideal.Quotient.mk_surjective (I := J) (y := x))

/-- イデアル引き戻しのメンバーシップ特徴付け -/
lemma mem_comap_iff (K : Ideal (R ⧸ I)) (r : R) :
    r ∈ Ideal.comap (π I) K ↔ (π I) r ∈ K := by
  rfl

/-- π の全射性：すべての商環の元は持ち上げを持つ -/
lemma π_surjective : Function.Surjective (π I) :=
  Ideal.Quotient.mk_surjective

/-- 引き戻しは I を含む -/
lemma comap_contains_I (K : Ideal (R ⧸ I)) :
    I ≤ Ideal.comap (π I) K := by
  intro r hr
  simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hr]

/-- 像と引き戻しの関係：I ≤ J のとき comap(map(J)) = J -/
lemma comap_map_eq (J : Ideal R) (hIJ : I ≤ J) :
    Ideal.comap (π I) (Ideal.map (π I) J) = J := by
  ext r
  simp only [mem_comap_iff, mem_map_iff]
  constructor
  · intro ⟨s, hs, hrs⟩
    have h : r - s ∈ I := by
      exact Ideal.Quotient.eq.mp hrs.symm
    have : r = s + (r - s) := by ring
    rw [this]
    exact J.add_mem hs (hIJ h)
  · intro hr
    exact ⟨r, hr, rfl⟩

/-- 像と引き戻しの関係：map(comap(K)) = K（π が全射のため） -/
lemma map_comap_eq (K : Ideal (R ⧸ I)) :
    Ideal.map (π I) (Ideal.comap (π I) K) = K := by
  exact Ideal.map_comap_of_surjective (π I) (π_surjective I) K

/-!
## Part IV: 主定理 — 全単射対応
-/

/-- backward は forward の左逆写像 -/
lemma backward_forward_id (J : IdealOver I) :
    backward I (forward I J) = J := by
  exact Subtype.ext (comap_map_eq I J.1 J.2)

/-- forward は backward の左逆写像 -/
lemma forward_backward_id (K : Ideal (R ⧸ I)) :
    forward I (backward I K) = K := by
  simp only [forward, backward]
  exact map_comap_eq I K

/-- **ノーター対応定理（双射部分）**
    I を含む R のイデアル格子と R/I のイデアル格子は全単射対応する -/
def noether_correspondence :
    IdealOver I ≃ Ideal (R ⧸ I) where
  toFun     := forward I
  invFun    := backward I
  left_inv  := backward_forward_id I
  right_inv := forward_backward_id I

/-!
## Part V: 構造保存 — 素イデアル対応
-/

/-- **素イデアル保存（順方向）**
    I ⊆ J かつ J が素イデアルなら π(J) も素イデアル -/
lemma forward_preserves_prime (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsPrime) :
    (Ideal.map (π I) J).IsPrime := by
  letI : J.IsPrime := hJ
  refine Ideal.map_isPrime_of_surjective (f := π I) (π_surjective I) ?_
  intro r hr
  rw [RingHom.mem_ker] at hr
  exact hIJ (Ideal.Quotient.eq_zero_iff_mem.mp hr)

/-- **素イデアル保存（逆方向）**
    π(J) が素イデアルなら J も素イデアル -/
lemma backward_preserves_prime (J : Ideal R) (hIJ : I ≤ J)
    (hK : (Ideal.map (π I) J).IsPrime) : J.IsPrime := by
  letI : (Ideal.map (π I) J).IsPrime := hK
  simpa [comap_map_eq I J hIJ] using
    (Ideal.comap_isPrime (f := π I) (K := Ideal.map (π I) J))

/-- **素イデアル対応定理**
    I ⊆ J のとき J が素イデアル ⟺ π(J) が素イデアル -/
theorem prime_correspondence (J : Ideal R) (hIJ : I ≤ J) :
    J.IsPrime ↔ (Ideal.map (π I) J).IsPrime :=
  ⟨forward_preserves_prime I J hIJ, backward_preserves_prime I J hIJ⟩

/-!
## Part VI: 構造保存 — 最大イデアル対応
-/

/-- **最大イデアル保存（順方向）**
    I ⊆ J かつ J が最大イデアルなら π(J) も最大イデアル -/
lemma forward_preserves_maximal (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
    (Ideal.map (π I) J).IsMaximal := by
  letI : J.IsMaximal := hJ
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le (f := π I) (π_surjective I) <| by
    intro r hr
    rw [RingHom.mem_ker] at hr
    exact hIJ (Ideal.Quotient.eq_zero_iff_mem.mp hr)

/-- **最大イデアル保存（逆方向）**
    π(J) が最大イデアルなら J も最大イデアル -/
lemma backward_preserves_maximal (J : Ideal R) (hIJ : I ≤ J)
    (hK : (Ideal.map (π I) J).IsMaximal) : J.IsMaximal := by
  letI : (Ideal.map (π I) J).IsMaximal := hK
  simpa [comap_map_eq I J hIJ] using
    (Ideal.comap_isMaximal_of_surjective (f := π I) (π_surjective I)
      (K := Ideal.map (π I) J))

/-- **最大イデアル対応定理**
    I ⊆ J のとき J が最大イデアル ⟺ π(J) が最大イデアル -/
theorem maximal_correspondence (J : Ideal R) (hIJ : I ≤ J) :
    J.IsMaximal ↔ (Ideal.map (π I) J).IsMaximal :=
  ⟨forward_preserves_maximal I J hIJ, backward_preserves_maximal I J hIJ⟩

/-!
## Part VII: 完全なノーター対応定理
-/

/-- **ノーター対応定理（完全版）**

    環 R とイデアル I に対して、全単射
      φ : {J : Ideal R | I ≤ J} ≃ Ideal (R ⧸ I)
    が存在し、以下を満たす：
    1. φ(J) = π(J)（像による定義）
    2. φ⁻¹(K̄) = π⁻¹(K̄)（引き戻しによる逆）
    3. J が素イデアル ⟺ φ(J) が素イデアル
    4. J が最大イデアル ⟺ φ(J) が最大イデアル -/
theorem noether_correspondence_complete :
    ∃ (φ : IdealOver I ≃ Ideal (R ⧸ I)),
      (∀ J : IdealOver I, φ J = Ideal.map (π I) J.val) ∧
      (∀ K : Ideal (R ⧸ I), (φ.symm K).val = Ideal.comap (π I) K) ∧
      (∀ J : IdealOver I, J.val.IsPrime ↔ (φ J).IsPrime) ∧
      (∀ J : IdealOver I, J.val.IsMaximal ↔ (φ J).IsMaximal) := by
  use noether_correspondence I
  refine ⟨fun J => rfl, fun K => rfl, ?_, ?_⟩
  · intro J
    exact prime_correspondence I J.val J.property
  · intro J
    exact maximal_correspondence I J.val J.property

end

end NoetherCorrespondence
