/-
  Bourbaki-inspired advanced analysis notes for Lean 4 / Mathlib.
  Source: Bourbaki_Lean_Guide.md
-/

import Mathlib

open Set Filter
open scoped Topology

noncomputable section

namespace BourbakiP2

-- ============================================================
-- Part I: Measure theory
-- ============================================================

section MeasureTheoryPart

variable {α ι : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)

theorem measure_empty : μ ∅ = 0 := by
  exact MeasureTheory.measure_empty

theorem measure_mono {s t : Set α} (h : s ⊆ t) : μ s ≤ μ t := by
  exact MeasureTheory.measure_mono h

theorem measure_union_of_disjoint {s t : Set α}
    (hd : Disjoint s t) (ht : MeasurableSet t) :
    μ (s ∪ t) = μ s + μ t := by
  exact MeasureTheory.measure_union hd ht

theorem measure_iUnion {f : ι → Set α} [Countable ι]
    (hpair : Pairwise (Function.onFun Disjoint f))
    (hmeas : ∀ i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) := by
  exact MeasureTheory.measure_iUnion hpair hmeas

end MeasureTheoryPart

-- ============================================================
-- Part II: Integration theory
-- ============================================================

section IntegrationPart

variable {α : Type*} [MeasurableSpace α]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (μ : MeasureTheory.Measure α)

theorem integral_add {f g : α → G}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ) :
    (∫ x, (f x + g x) ∂μ) = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := by
  exact MeasureTheory.integral_add hf hg

theorem integral_sub {f g : α → G}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ) :
    (∫ x, (f x - g x) ∂μ) = (∫ x, f x ∂μ) - (∫ x, g x ∂μ) := by
  exact MeasureTheory.integral_sub hf hg

theorem lintegral_mono {f g : α → ENNReal} (hfg : f ≤ g) :
    (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, g x ∂μ) := by
  exact MeasureTheory.lintegral_mono hfg

end IntegrationPart

-- ============================================================
-- Part III: Lp spaces
-- ============================================================

section LpPart

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable (p : ENNReal) [Fact (1 ≤ p)] (μ : MeasureTheory.Measure α)

theorem lp_norm_triangle (f g : MeasureTheory.Lp E p μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  simpa using norm_add_le f g

omit [Fact (1 ≤ p)] in
theorem lp_norm_formula (f : MeasureTheory.Lp E p μ) :
    ‖f‖ = (MeasureTheory.eLpNorm ((f : MeasureTheory.Lp E p μ) : α →ₘ[μ] E) p μ).toReal := by
  simpa using MeasureTheory.Lp.norm_def f

end LpPart

-- ============================================================
-- Part IV: Topological vector spaces
-- ============================================================

section TVSPart

theorem continuous_add_map {E : Type*} [TopologicalSpace E] [Add E] [ContinuousAdd E] :
    Continuous (fun p : E × E => p.1 + p.2) := by
  exact continuous_add

theorem continuous_smul_map {𝕜 E : Type*}
    [TopologicalSpace 𝕜] [SMul 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E] :
    Continuous (fun p : 𝕜 × E => p.1 • p.2) := by
  exact continuous_smul

end TVSPart

-- ============================================================
-- Part V: Banach spaces and fixed points
-- ============================================================

section BanachPart

variable {α : Type*} [EMetricSpace α] [CompleteSpace α]
variable {K : NNReal} {f : α → α}

theorem contracting_exists_fixedPoint (hf : ContractingWith K f) (x : α)
    (hx : edist x (f x) ≠ ⊤) :
    ∃ y,
      Function.IsFixedPt f y ∧
        Filter.Tendsto (fun n => f^[n] x) Filter.atTop (nhds y) ∧
          ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * ↑K ^ n / (1 - ↑K) := by
  exact ContractingWith.exists_fixedPoint hf x hx

variable {β : Type*} [Preorder β]
variable {u : β → α}

theorem cauchy_tendsto_of_completeSpace (hu : CauchySeq u) :
    ∃ x, Filter.Tendsto u Filter.atTop (nhds x) := by
  exact _root_.cauchySeq_tendsto_of_complete hu

section UniformBoundedness

variable {𝕜 E F ι : Type*}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
variable (g : ι → E →L[𝕜] F)

theorem banach_steinhaus_bound
    (h : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ‖(g i) x‖ ≤ C) :
    ∃ C' : ℝ, ∀ i : ι, ‖g i‖ ≤ C' := by
  exact banach_steinhaus h

end UniformBoundedness

end BanachPart

-- ============================================================
-- Part VI: Dual spaces
-- ============================================================

section DualPart

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Hahn-Banach extension theorem (analytic form). -/
theorem hahn_banach_extension (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  exact exists_extension_norm_eq p f

end DualPart

section DualCompactPart

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Banach-Alaoglu theorem in weak dual form (closed balls are compact in weak-* topology). -/
theorem banach_alaoglu_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsCompact ((WeakDual.toStrongDual : WeakDual 𝕜 E → StrongDual 𝕜 E) ⁻¹' Metric.closedBall x' r) := by
  exact WeakDual.isCompact_closedBall 𝕜 x' r

end DualCompactPart

-- ============================================================
-- Part VII: Spectral theory
-- ============================================================

section SpectrumPart

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem spectrum_isClosed (a : A) : IsClosed (spectrum ℂ a) := by
  exact spectrum.isClosed a

theorem spectrum_isCompact (a : A) : IsCompact (spectrum ℂ a) := by
  letI : ProperSpace ℂ := by infer_instance
  exact spectrum.isCompact a

variable [Nontrivial A]

theorem spectrum_nonempty (a : A) : (spectrum ℂ a).Nonempty := by
  exact spectrum.nonempty a

omit [Nontrivial A] in
theorem gelfand_formula_tendsto (a : A) :
    Filter.Tendsto (fun n : ℕ => (↑‖a ^ n‖₊ : ENNReal) ^ (1 / (n : ℝ))) Filter.atTop
      (nhds (spectralRadius ℂ a)) := by
  simpa using spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

end SpectrumPart

end BourbakiP2
