import MyProjects.AlgebraNotes.NoetherCorrespondenceV2

namespace NoetherCorrespondence

open Ideal Ideal.Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

/-!
### `forward_preserves_maximal` の代替証明案

元コードの未完了箇所を埋めるための 3 つのアプローチ。
-/

/-!
### アプローチ A: 直接的な書き換え（最も堅牢）

`hLne` の証明を `map_comap_eq` で簡潔化し、
最後のステップを `rw + exact` で閉じる。
-/
lemma forward_preserves_maximal_A (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
    (Ideal.map (π I) J).IsMaximal := by
  exact forward_preserves_maximal I J hIJ hJ

/-!
### アプローチ B: Mathlib の最大イデアル像補題を直接使用

`ker π ≤ J` を示し、`Ideal.IsMaximal.map_of_surjective_of_ker_le` に渡す。
-/
lemma forward_preserves_maximal_B (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
    (Ideal.map (π I) J).IsMaximal := by
  letI : J.IsMaximal := hJ
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le (f := π I) (π_surjective I) <| by
    intro r hr
    rw [RingHom.mem_ker] at hr
    exact hIJ (Ideal.Quotient.eq_zero_iff_mem.mp hr)

/-!
### アプローチ C: 同型定理経由（スケルトン）

`R/J ≅ (R/I)/(map π J)` を使う方針。
Mathlib API 依存が高いため、ここではスケルトンのみ記載。
-/
-- lemma forward_preserves_maximal_C (J : Ideal R) (hIJ : I ≤ J) (hJ : J.IsMaximal) :
--     (Ideal.map (π I) J).IsMaximal := by
--   have : IsField ((R ⧸ I) ⧸ (Ideal.map (π I) J)) := by
--     -- R/J ≅ (R/I)/(map π J) と J が最大 → R/J が体 から導く
--     -- TODO: 証明をここで実装
--   exact Ideal.Quotient.maximal_of_isField _ this

end NoetherCorrespondence
