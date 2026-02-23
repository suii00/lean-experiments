/-
  forward_preserves_maximal の代替証明案
  
  元コードの sorry 2箇所を埋めるための3つのアプローチ
-/

/-!
### アプローチ A: 直接的な書き換え（最も堅牢）

  sorry を最小限の変更で埋める。
  hLne の証明を map_comap_eq で簡潔化し、
  最後のステップを rw + exact で閉じる。
-/

lemma forward_preserves_maximal_A (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
    (Ideal.map (π I) J).IsMaximal := by
  constructor
  · -- map π J ≠ ⊤
    intro h_top
    apply hJ.ne_top
    rw [← comap_map_eq I J hIJ, h_top, Ideal.comap_top]
  · -- 最大性
    intro K hK hKne
    let L := Ideal.comap (π I) K
    -- J ≤ L
    have hJL : J ≤ L := by
      rw [← comap_map_eq I J hIJ]
      exact Ideal.comap_mono hK
    -- L ≠ J : L = J なら K = map π (comap π K) = map π L = map π J で矛盾
    have hLne : L ≠ J := by
      intro heq
      exact hKne ((map_comap_eq I K).symm.trans (congr_arg (Ideal.map (π I)) heq))
    -- J の最大性より L = ⊤
    have hL_top : L = ⊤ := hJ.eq_of_le hJL (Ne.symm hLne)
    -- K = π(π⁻¹(K)) = π(⊤) = ⊤
    rw [← map_comap_eq I K, hL_top]
    exact Ideal.map_top_of_surjective _ (π_surjective I)


/-!
### アプローチ B: Mathlib の map_isMaximal_of_surjective を直接使用

  Mathlib4 に Ideal.map_isMaximal_of_surjective が存在する場合、
  素イデアルの場合と完全に対称的な1行証明が可能。
  
  ※ Mathlib のバージョンによっては名前が異なる可能性あり。
    存在しない場合はアプローチ A を使用。
-/

lemma forward_preserves_maximal_B (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
    (Ideal.map (π I) J).IsMaximal := by
  -- ker π = I ≤ J を示せば Mathlib が残りを処理
  have hker : RingHom.ker (π I) ≤ J := by
    intro r hr
    rw [RingHom.mem_ker] at hr
    exact hIJ (Ideal.Quotient.eq_zero_iff_mem.mp hr)
  exact Ideal.map_isMaximal_of_surjective (π_surjective I) hker


/-!
### アプローチ C: 同型定理経由

  R/J ≅ (R/I)/(map π J) を使い、
  J が最大 ⟺ R/J が体 ⟺ (R/I)/(map π J) が体 ⟺ map π J が最大。
  
  Mathlib に Ideal.Quotient.quotientQuotientEquivQuotient やそれに
  類する補題がある場合はこのルートが最もエレガント。
-/

-- この方針は Mathlib の API 依存度が高いため、スケルトンのみ記載
-- lemma forward_preserves_maximal_C (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
--     (Ideal.map (π I) J).IsMaximal := by
--   have : IsField ((R ⧸ I) ⧸ (Ideal.map (π I) J)) := by
--     -- R/J ≅ (R/I)/(map π J) と J が最大 → R/J が体 から導く
--     sorry
--   exact Ideal.Quotient.maximal_of_isField _ this
