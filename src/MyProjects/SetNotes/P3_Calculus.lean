/-
  Bourbaki-inspired P3: Calculus and Differentiation (微積分学)
  Bourbaki, Fonctions d'une variable réelle (FVR)

  難易度: 中級〜上級
  推奨学習時間: 4〜6週間
  前提: P1.lean, P2_Advanced_Analysis.lean (Part I-II)
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.IntermediateValue

open Set Filter MeasureTheory
open scoped BigOperators

noncomputable section

namespace BourbakiP3

-- ============================================================
-- Part I: 微分の基礎 (Dérivées)
-- Bourbaki, FVR I, §1–§2
-- ============================================================

section DerivBasics

/-- 定数関数の導関数は0。 -/
theorem deriv_const (c : ℝ) : deriv (fun _ : ℝ => c) = 0 := by
  ext x
  exact _root_.deriv_const x c

/-- 恒等関数の導関数は1。 -/
theorem deriv_id' : deriv id = fun _ => (1 : ℝ) := by
  exact (_root_.deriv_id' : deriv id = fun _ => (1 : ℝ))

/-- 和の微分法則。 -/
theorem deriv_add_at {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x := by
  exact deriv_add hf hg

/-- 積の微分法則 (Leibniz rule)。 -/
theorem deriv_mul_at {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f * g) x = deriv f x * g x + f x * deriv g x := by
  exact deriv_mul hf hg

/-- 合成関数の微分法則 (chain rule)。 -/
theorem deriv_comp_at {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    deriv (f ∘ g) x = deriv f (g x) * deriv g x := by
  exact deriv_comp x hf hg

end DerivBasics

-- ============================================================
-- Part II: 平均値の定理 (Théorème des accroissements finis)
-- Bourbaki, FVR I, §2
-- ============================================================

section MeanValueTheorem

/-- Rolle の定理:
    f(a) = f(b) かつ f が [a,b] で連続、(a,b) で微分可能ならば、
    f'(c) = 0 なる c ∈ (a,b) が存在。 -/
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (_hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hfab : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  simpa using exists_deriv_eq_zero hab hfc hfab

/-- 平均値の定理 (Lagrange):
    f が [a,b] で連続、(a,b) で微分可能ならば、
    f(b) - f(a) = f'(c)(b - a) なる c が存在。 -/
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  have hfdOn : DifferentiableOn ℝ f (Ioo a b) := by
    intro x hx
    exact (hfd x hx).differentiableWithinAt
  rcases exists_deriv_eq_slope f hab hfc hfdOn with ⟨c, hc, hc'⟩
  refine ⟨c, hc, ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  calc
    f b - f a = ((f b - f a) / (b - a)) * (b - a) := by
      field_simp [hba]
    _ = deriv f c * (b - a) := by
      rw [← hc']

/-- 単調性判定: f' ≥ 0 on (a,b) ⟹ f は [a,b] で単調非減少。 -/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) :
    MonotoneOn f (Icc a b) := by
  let D : Set ℝ := Icc a b
  have hfd' : DifferentiableOn ℝ f (interior D) := by
    intro x hx
    exact (hfd x (by simpa [D, interior_Icc] using hx)).differentiableWithinAt
  have hf'' : ∀ x ∈ interior D, 0 ≤ deriv f x := by
    intro x hx
    exact hf' x (by simpa [D, interior_Icc] using hx)
  simpa [D] using
    (_root_.monotoneOn_of_deriv_nonneg (D := D) (hD := convex_Icc a b) hfc hfd' hf'')

end MeanValueTheorem

-- ============================================================
-- Part III: 中間値の定理 (Théorème des valeurs intermédiaires)
-- Bourbaki, Topologie générale IV, §6
-- ============================================================

section IntermediateValue

/-- 中間値の定理: 連続関数は中間値を取る。 -/
theorem intermediate_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) {v : ℝ}
    (hva : f a ≤ v) (hvb : v ≤ f b) :
    ∃ c ∈ Icc a b, f c = v := by
  exact intermediate_value_Icc hab hf ⟨hva, hvb⟩

/-- 零点定理 (Bolzano): f(a) < 0 < f(b) ならば零点が存在。 -/
-- 演習課題
theorem bolzano {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (ha : f a < 0) (hb : 0 < f b) :
    ∃ c ∈ Icc a b, f c = 0 := by
  exact intermediate_value_theorem hab hf (v := 0) ha.le hb.le

end IntermediateValue

-- ============================================================
-- Part IV: 微積分学の基本定理 (Théorème fondamental du calcul)
-- Bourbaki, FVR II (Intégration)
-- ============================================================

section FTC

variable {f : ℝ → ℝ}

/-- FTC Part 1: 積分の微分。
    f が連続ならば F(x) = ∫ₐˣ f(t) dt は微分可能で F'(x) = f(x)。 -/
theorem ftc_part1 {a : ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable _ _)
    (Continuous.stronglyMeasurableAtFilter hf MeasureTheory.volume (nhds x))
    hf.continuousAt

/-- FTC Part 2: Newton-Leibniz 公式。
    F' = f ならば ∫ₐᵇ f(t) dt = F(b) - F(a)。 -/
theorem ftc_part2 {a b : ℝ} {F : ℝ → ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in a..b, f x = F b - F a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hF hf

end FTC

-- ============================================================
-- Part V: Fréchet 微分 (Dérivée de Fréchet)
-- Bourbaki, Variétés, 準備として
-- ============================================================

section FrechetDerivative

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fréchet 微分の一意性。 -/
theorem fderiv_unique {f : E → F} {x : E} {L₁ L₂ : E →L[ℝ] F}
    (h₁ : HasFDerivAt f L₁ x) (h₂ : HasFDerivAt f L₂ x) :
    L₁ = L₂ := by
  exact h₁.unique h₂

/-- Fréchet 微分の和。 -/
theorem fderiv_add_at {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x := by
  exact fderiv_add hf hg

/-- Fréchet 微分の合成 (chain rule の一般化)。 -/
theorem fderiv_comp_at {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (f ∘ g) x = (fderiv ℝ f (g x)).comp (fderiv ℝ g x) := by
  exact fderiv_comp x hf hg

end FrechetDerivative

-- ============================================================
-- Part VI: Taylor の定理 (Formule de Taylor)
-- Bourbaki, FVR I, §5
-- ============================================================

section TaylorTheorem

/- Taylor の定理 (Lagrange の剰余項):
   演習課題 - n 回微分可能な関数に対する Taylor 展開。 -/

-- Mathlib では taylor_mean_remainder / taylor_mean_remainder_unordered
-- として利用可能。

-- 演習: 具体的な関数で Taylor 展開を確認
-- 例えば exp の Taylor 展開

/-- exp(x) の n 次 Taylor 多項式の収束。 -/
-- 演習課題
theorem exp_taylor_converges (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => Finset.sum (Finset.range n) (fun k => x ^ k / k.factorial))
      Filter.atTop (nhds (Real.exp x)) := by
  simpa [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat

end TaylorTheorem

-- ============================================================
-- Part VII: 陰関数定理への準備 (Théorème des fonctions implicites)
-- Bourbaki, Variétés différentielles
-- ============================================================

section ImplicitFunction

-- 陰関数定理は Mathlib の
-- ImplicitFunctionData / HasStrictFDerivAt.implicitFunctionDataOfComplemented
-- として利用可能

-- 高度な演習: 逆関数定理を陰関数定理の系として導出

/- 逆関数定理: f'(a) が可逆ならば f は a の近傍で局所同相。 -/
-- 演習課題 (高度)
-- 参考: Mathlib の ContDiff.to_localHomeomorph

end ImplicitFunction

-- ============================================================
-- Part VIII: 凸解析入門 (Analyse convexe, introduction)
-- Bourbaki, EVT II 補足
-- ============================================================

section ConvexAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- 凸関数: f(tx + (1-t)y) ≤ tf(x) + (1-t)f(y)。 -/
-- Mathlib の ConvexOn を使って基本性質を確認

/- 演習: 微分可能な凸関数の特徴づけ。
   f が凸 ⟺ f' が単調非減少。 -/

/- 演習: Jensen の不等式。
   f が凸ならば f(E[X]) ≤ E[f(X)]。 -/
-- 参考: MeasureTheory.ConvexOn.integral_le

end ConvexAnalysis

end BourbakiP3
