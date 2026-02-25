/-
  Bourbaki-inspired P1.5: Commutative Algebra (代数学 II)
  Bridges the gap between P1 (groups) and P2 (analysis).
  Source: Bourbaki, Algèbre I–III, Algèbre Commutative I–II

  難易度: 中級〜上級
  推奨学習時間: 4〜8週間
  前提: P1.lean, P1_Extended.lean 完了
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.FieldTheory.Minpoly.Field

open Ideal

namespace BourbakiP1_5

-- ============================================================
-- Part I: 環と準同型 (Anneaux et morphismes)
-- Bourbaki, Algèbre I, §8
-- ============================================================

section RingBasics

variable {R : Type*} [CommRing R]

/-- 環準同型は乗法を保存する（P1の群版の拡張）。 -/
theorem ring_hom_map_mul {S : Type*} [CommRing S] (f : R →+* S) (x y : R) :
    f (x * y) = f x * f y := by
  exact f.map_mul x y

/-- 環準同型は加法を保存する。 -/
theorem ring_hom_map_add {S : Type*} [CommRing S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := by
  exact f.map_add x y

/-- 環準同型は1を保存する。 -/
theorem ring_hom_map_one {S : Type*} [CommRing S] (f : R →+* S) :
    f 1 = 1 := by
  exact f.map_one

end RingBasics

-- ============================================================
-- Part II: イデアルの基本操作 (Opérations sur les idéaux)
-- Bourbaki, Algèbre Commutative I, §1
-- ============================================================

section IdealOps

variable {R : Type*} [CommRing R]

/-- イデアルの和はイデアル。 -/
theorem ideal_sum_eq (I J : Ideal R) :
    (I ⊔ J : Ideal R) = I + J := by
  rfl

/-- イデアルの積はイデアル。 -/
theorem ideal_mul_le_inf (I J : Ideal R) :
    I * J ≤ I ⊓ J := by
  exact Ideal.mul_le_inf

/-- 素イデアルの定義的性質。 -/
theorem prime_iff_quotient_integral {p : Ideal R} [hp : p.IsPrime] {a b : R}
    (hab : a * b ∈ p) : a ∈ p ∨ b ∈ p := by
  exact hp.mem_or_mem hab

/-- 極大イデアルは素イデアルである。 -/
theorem maximal_is_prime {m : Ideal R} [hm : m.IsMaximal] : m.IsPrime := by
  exact Ideal.IsMaximal.isPrime hm

end IdealOps

-- ============================================================
-- Part III: 商環 (Anneaux quotients)
-- Bourbaki, Algèbre I, §8.7
-- ============================================================

section QuotientRings

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- 商写像の全射性。 -/
theorem quotient_mk_surjective : Function.Surjective (Ideal.Quotient.mk I) := by
  exact Ideal.Quotient.mk_surjective

/-- 商環の核はイデアル自身。 -/
theorem quotient_ker_eq : RingHom.ker (Ideal.Quotient.mk I) = I := by
  exact Ideal.mk_ker

/-- 商環が体 ⟺ イデアルが極大。
    Bourbaki, Algèbre Commutative I, §2.1, Proposition 2 -/
theorem quotient_isField_iff_maximal :
    IsField (R ⧸ I) ↔ I.IsMaximal := by
  constructor
  · intro h
    exact Ideal.Quotient.maximal_of_isField I h
  · intro h
    exact Ideal.Quotient.isField_iff_isMaximal.mpr h

/-- 商環が整域 ⟺ イデアルが素。 -/
theorem quotient_isDomain_iff_prime :
    IsDomain (R ⧸ I) ↔ I.IsPrime := by
  exact Ideal.Quotient.isDomain_iff_prime

end QuotientRings

-- ============================================================
-- Part IV: 環の同型定理 (Théorèmes d'isomorphisme)
-- Bourbaki, Algèbre I, §8.7
-- ============================================================

section IsomorphismTheorems

variable {R S : Type*} [CommRing R] [CommRing S]

/-- 環の第一同型定理: R / ker(f) ≅ im(f)。 -/
theorem first_iso_theorem (f : R →+* S) :
    Nonempty (R ⧸ RingHom.ker f ≃+* f.range) := by
  exact ⟨RingHom.quotientKerEquivRange f⟩

/-- 第三同型定理 (correspondence): I ⊇ J ならば (R/J)/(I/J) ≅ R/I。 -/
theorem third_iso_theorem (I J : Ideal R) (h : J ≤ I) :
    Nonempty ((R ⧸ J) ⧸ (I.map (Ideal.Quotient.mk J)) ≃+* R ⧸ I) := by
  exact ⟨Ideal.quotientQuotientEquivQuotient J I h⟩

end IsomorphismTheorems

-- ============================================================
-- Part V: 局所化 (Localisation)
-- Bourbaki, Algèbre Commutative II, §2
-- ============================================================

section Localization

variable {R : Type*} [CommRing R] (S : Submonoid R)

/-- 局所化写像は単射 ⟺ S に零因子がない。 -/
-- 演習課題: この同値を確認する
theorem localization_map_injective_of_no_zero_divisors
    [NoZeroDivisors R] [Nontrivial R] :
    Function.Injective (algebraMap R (Localization S)) := by
  sorry  -- 課題: IsLocalization.injective を使って証明

/-- 局所化の普遍性: S⁻¹R は S の像が可逆になる「最小の」環。 -/
-- 演習課題
theorem localization_universal {T : Type*} [CommRing T] [Algebra R T]
    [IsLocalization S T] (Q : Type*) [CommRing Q] (f : R →+* Q)
    (hf : ∀ s : S, IsUnit (f s)) :
    ∃! g : T →+* Q, g.comp (algebraMap R T) = f := by
  sorry  -- 課題: IsLocalization.lift を使って構成

end Localization

-- ============================================================
-- Part VI: 加群の基礎 (Modules)
-- Bourbaki, Algèbre II, §1
-- ============================================================

section Modules

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- R-線形写像の像は部分加群。 -/
theorem range_is_submodule (f : M →ₗ[R] N) :
    ∃ p : Submodule R N, (p : Set N) = Set.range f := by
  exact ⟨LinearMap.range f, rfl⟩

/-- 加群の第一同型定理: M / ker(f) ≅ im(f)。 -/
theorem module_first_iso (f : M →ₗ[R] N) :
    Nonempty ((M ⧸ LinearMap.ker f) ≃ₗ[R] ↥(LinearMap.range f)) := by
  exact ⟨f.quotKerEquivRange⟩

/-- 部分加群の商。 -/
theorem submodule_quotient_surjective (p : Submodule R M) :
    Function.Surjective (p.mkQ) := by
  exact p.mkQ_surjective

end Modules

-- ============================================================
-- Part VII: 自由加群と階数 (Modules libres et rang)
-- Bourbaki, Algèbre II, §7
-- ============================================================

section FreeModules

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- 有限次元ベクトル空間では、基底の濃度は一意。
    (自由加群の「階数」が well-defined)。 -/
theorem finrank_eq_of_basis {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} [Fintype ι] (b : Basis ι R V) [StrongRankCondition R] :
    Module.finrank R V = Fintype.card ι := by
  exact Module.finrank_eq_card_basis b

end FreeModules

-- ============================================================
-- Part VIII: テンソル積 (Produit tensoriel)
-- Bourbaki, Algèbre III, §1–§4
-- ============================================================

section TensorProduct

variable {R : Type*} [CommRing R]
variable {M N P : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

open TensorProduct

/-- テンソル積の普遍性:
    双線形写像 M × N → P は M ⊗ N → P を一意に経由する。 -/
theorem tensor_universal (f : M →ₗ[R] N →ₗ[R] P) :
    ∃ g : M ⊗[R] N →ₗ[R] P,
      ∀ (m : M) (n : N), g (m ⊗ₜ n) = f m n := by
  exact ⟨TensorProduct.lift f, fun m n => TensorProduct.lift.tmul m n⟩

/-- テンソル積は右完全（右完全性の一部）:
    演習課題 - テンソル積は右完全関手。 -/
-- 完全列 M' → M → M'' → 0 に対して
-- M' ⊗ N → M ⊗ N → M'' ⊗ N → 0 が完全

-- この性質は Mathlib の lTensor_exact / rTensor_exact で扱える
-- 演習として確認してみよう

end TensorProduct

-- ============================================================
-- Part IX: Noether 環 (Anneaux noethériens)
-- Bourbaki, Algèbre Commutative III, §2
-- ============================================================

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Noether環のすべてのイデアルは有限生成。 -/
theorem ideals_finitely_generated (I : Ideal R) : I.FG := by
  exact IsNoetherian.noetherian I

/-- Noether環ではイデアルの昇鎖条件が成立。 -/
-- 演習課題: ACC を直接確認
theorem ascending_chain_condition :
    WellFoundedGT (Ideal R) := by
  sorry  -- 課題: isNoetherian_iff_wellFounded を活用

end Noetherian

-- ============================================================
-- Part X: UFD と PID (Domaines factoriels et principaux)
-- Bourbaki, Algèbre Commutative VII
-- ============================================================

section FactorizationDomains

variable {R : Type*} [CommRing R] [IsDomain R]

/-- PID は Noether 環。 -/
theorem pid_is_noetherian [IsPrincipalIdealRing R] : IsNoetherianRing R := by
  infer_instance

/-- PID では既約元と素元が一致。 -/
-- 演習課題
theorem irreducible_iff_prime_in_pid [IsPrincipalIdealRing R] {p : R} :
    Irreducible p ↔ Prime p := by
  sorry  -- 課題: PrincipalIdealRing.irreducible_iff_prime を確認

/-- UFD のすべての元は既約元の積に分解される（一意性付き）。 -/
-- 演習課題: UniqueFactorizationMonoid の性質を確認
-- 参考: Mathlib の UniqueFactorizationMonoid

end FactorizationDomains

-- ============================================================
-- Part XI: 最小多項式と体の拡大（入門）
-- Bourbaki, Algèbre V, §1
-- ============================================================

section FieldExtensions

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- 最小多項式は monicである。 -/
theorem minpoly_monic {α : E} (h : IsIntegral F α) :
    (minpoly F α).Monic := by
  exact minpoly.monic h

/-- 最小多項式は α を零化する。 -/
theorem minpoly_aeval_eq_zero {α : E} (h : IsIntegral F α) :
    Polynomial.aeval α (minpoly F α) = 0 := by
  exact minpoly.aeval F α

/-- 演習課題: α を零化する多項式はすべて最小多項式で割り切れる。 -/
theorem minpoly_dvd_of_aeval_zero {α : E} (h : IsIntegral F α)
    {p : F[X]} (hp : Polynomial.aeval α p = 0) :
    minpoly F α ∣ p := by
  sorry  -- 課題: minpoly.dvd を使って証明

end FieldExtensions

end BourbakiP1_5
