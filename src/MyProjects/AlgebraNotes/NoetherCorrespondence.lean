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
import Mathlib.Order.GaloisConnection

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
  exact Submodule.mem_map

/-- イデアル引き戻しのメンバーシップ特徴付け -/
lemma mem_comap_iff (K : Ideal (R ⧸ I)) (r : R) :
    r ∈ Ideal.comap (π I) K ↔ (π I) r ∈ K := by
  exact Submodule.mem_comap

/-- π の全射性：すべての商環の元は持ち上げを持つ -/
lemma π_surjective : Function.Surjective (π I) :=
  Ideal.Quotient.mk_surjective

/-- 引き戻しは I を含む -/
lemma comap_contains_I (K : Ideal (R ⧸ I)) :
    I ≤ Ideal.comap (π I) K := by
  intro r hr
  simp [mem_comap_iff, π, Ideal.Quotient.eq_zero_iff_mem.mpr hr]

/-- 像と引き戻しの関係：I ≤ J のとき comap(map(J)) = J -/
lemma comap_map_eq (J : Ideal R) (hIJ : I ≤ J) :
    Ideal.comap (π I) (Ideal.map (π I) J) = J := by
  ext r
  simp only [mem_comap_iff, mem_map_iff]
  constructor
  · intro ⟨s, hs, hrs⟩
    have h : r - s ∈ I := by
      rwa [← Ideal.Quotient.eq, eq_comm] at hrs
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
  ext r
  simp only [forward, backward, Subtype.mk.injEq]
  exact (comap_map_eq I J.val J.property).symm ▸ Iff.rfl

/-- forward は backward の左逆写像 -/
lemma forward_backward_id (K : Ideal (R ⧸ I)) :
    forward I (backward I K) = K := by
  simp only [forward, backward]
  exact map_comap_eq I K

/-- **ノーター対応定理（双射部分）**
    I を含む R のイデアル格子と R/I のイデアル格子は全単射対応する -/
theorem noether_correspondence :
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
  apply Ideal.map_isPrime_of_surjective (π_surjective I)
  intro r hr
  rw [RingHom.mem_ker] at hr
  exact hIJ (Ideal.Quotient.eq_zero_iff_mem.mp hr)

/-- **素イデアル保存（逆方向）**
    π(J) が素イデアルなら J も素イデアル -/
lemma backward_preserves_prime (J : Ideal R) (hIJ : I ≤ J)
    (hK : (Ideal.map (π I) J).IsPrime) : J.IsPrime := by
  rw [comap_map_eq I J hIJ ▸ show J = Ideal.comap (π I) (Ideal.map (π I) J) from
    (comap_map_eq I J hIJ).symm]
  exact Ideal.comap_isPrime

/-- **素イデアル対応定理**
    I ⊆ J のとき J が素イデアル ⟺ π(J) が素イデアル -/
theorem prime_correspondence (J : Ideal R) (hIJ : I ≤ J) :
    J.IsPrime ↔ (Ideal.map (π I) J).IsPrime :=
  ⟨forward_preserves_prime I J hIJ, backward_preserves_prime I J hIJ⟩

/-!
## Part VI: 構造保存 — 最大イデアル対応

### 修正箇所の数学的解説

`forward_preserves_maximal` の証明で鍵となるのは以下の2点：

1. **L ≠ J の証明**：L = J を仮定すると
     K = π(π⁻¹(K)) = π(L) = π(J) = map π J
   となり K ≠ map π J に矛盾。
   map_comap_eq（π の全射性による）を使えば ext による元ごとの議論は不要。

2. **L = ⊤ から K = ⊤ の導出**：
     K = π(π⁻¹(K)) = π(L) = π(⊤) = ⊤
   全射 π に対して π(⊤) = ⊤ は Ideal.map_top_of_surjective。
-/

/-- **最大イデアル保存（順方向）**
    I ⊆ J かつ J が最大イデアルなら π(J) も最大イデアル -/
lemma forward_preserves_maximal (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
    (Ideal.map (π I) J).IsMaximal := by
  constructor
  · -- map π J ≠ ⊤ を示す
    intro h_top
    have hJ_top : J = ⊤ := by
      have : Ideal.comap (π I) (Ideal.map (π I) J) = Ideal.comap (π I) ⊤ := by
        rw [h_top]
      rw [comap_map_eq I J hIJ] at this
      rw [this]
      exact Ideal.comap_top (π I)
    exact hJ.ne_top hJ_top
  · -- 最大性：map π J ⊆ K かつ K ≠ map π J なら K = ⊤
    intro K hK hKne
    -- L := π⁻¹(K)
    let L := Ideal.comap (π I) K
    -- Step 1: J ≤ L（comap の単調性と comap_map_eq から）
    have hJL : J ≤ L := by
      rw [← comap_map_eq I J hIJ]
      exact Ideal.comap_mono hK
    -- Step 2: L ≠ J（もし L = J なら K = map π J となり矛盾）
    --   K = map π (comap π K) = map π L = map π J
    have hLne : L ≠ J := by
      intro heq
      exact hKne ((map_comap_eq I K).symm.trans (congr_arg (Ideal.map (π I)) heq))
    -- Step 3: J の最大性より L = ⊤
    have hL_top : L = ⊤ := hJ.eq_of_le hJL (Ne.symm hLne)
    -- Step 4: K = π(π⁻¹(K)) = π(L) = π(⊤) = ⊤
    calc Ideal.map (π I) (Ideal.comap (π I) K)
          = K := map_comap_eq I K
      _ = _ := by rw [show Ideal.comap (π I) K = L from rfl] at *
                  rw [← map_comap_eq I K, hL_top]
                  exact Ideal.map_top_of_surjective _ (π_surjective I)

/-- **最大イデアル保存（逆方向）**
    π(J) が最大イデアルなら J も最大イデアル -/
lemma backward_preserves_maximal (J : Ideal R) (hIJ : I ≤ J)
    (hK : (Ideal.map (π I) J).IsMaximal) : J.IsMaximal := by
  rw [comap_map_eq I J hIJ ▸ show J = Ideal.comap (π I) (Ideal.map (π I) J) from
    (comap_map_eq I J hIJ).symm]
  exact Ideal.comap_isMaximal_of_surjective (π I) (π_surjective I)

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
