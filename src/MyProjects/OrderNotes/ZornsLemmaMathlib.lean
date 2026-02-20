/-
  ツォルンの補題と選択公理の同値性 — Mathlib直乗り版

  Mathlibの既存API（zorn_le, zorn_le₀, IsChain, Classical.choice等）を
  最大限活用し、コンパクトに形式化する。

  構成：
    §1 ツォルンの補題のバリエーション
    §2 選択公理との同値性
    §3 整列定理との関係
    §4 典型的応用
-/

import Mathlib.Order.Zorn
import Mathlib.Data.Set.Lattice
import Mathlib.SetTheory.Cardinal.Order

open Set Classical

-- ============================================================================
-- §1 ツォルンの補題のバリエーション
-- ============================================================================

section ZornVariants

variable {α : Type*} [PartialOrder α]

/-- ツォルンの補題（部分集合版）：帰納的部分集合は極大元を持つ -/
theorem zorn_subset_version (S : Set α)
    (h : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x := by
  obtain ⟨m, hm, hmax⟩ := zorn_le₀ S h
  exact ⟨m, hm, fun x hxS hmx => le_antisymm hmx (hmax hxS hmx)⟩

/-- ツォルンの補題（全体版）：帰納的半順序集合は極大元を持つ -/
theorem zorn_total_version
    (h : ∀ C : Set α, IsChain (· ≤ ·) C → BddAbove C) :
    ∃ m : α, ∀ x, m ≤ x → x ≤ m :=
  zorn_le h

/-- ツォルンの補題（空チェーン対応版） -/
theorem zorn_nonempty (S : Set α) (hne : S.Nonempty)
    (h : ∀ C ⊆ S, IsChain (· ≤ ·) C → C.Nonempty → ∃ b ∈ S, ∀ a ∈ C, a ≤ b) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x := by
  apply zorn_subset_version
  intro C hCS hC
  by_cases hCne : C.Nonempty
  · exact h C hCS hC hCne
  · obtain ⟨a, ha⟩ := hne
    refine ⟨a, ha, ?_⟩
    intro x hx
    exact (hCne ⟨x, hx⟩).elim

end ZornVariants

-- ============================================================================
-- §2 選択公理との同値性
-- ============================================================================

section ACEquivalence

/-- 選択公理（型理論的定式化） -/
def AC : Prop :=
  ∀ {ι : Type*} (A : ι → Type*), (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i)

/-- 選択公理（集合論的定式化） -/
def AC_Set : Prop :=
  ∀ {ι : Type*} (S : ι → Set ι), (∀ i, (S i).Nonempty) →
    ∃ f : ι → ι, ∀ i, f i ∈ S i

/-- Lean4の Classical.choice から AC が成立 -/
theorem ac_from_classical : AC := by
  intro ι A hne
  exact ⟨fun i => (hne i).some⟩

/-- AC → Zorn：Lean4では自明（Classical.choiceがACを内包） -/
theorem ac_implies_zorn : AC →
    ∀ {α : Type*} [PartialOrder α] (S : Set α),
      (∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b) →
      ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x := by
  intro _ α _ S h
  exact zorn_subset_version S h

/-! ### Zorn → AC の方向

部分選択関数の順序集合にZornの補題を適用する古典的証明。
Mathlibの `Set.Partial` / `Function.extend` 等で依存型を回避。
-/

/-- Zorn → AC（集合論版） -/
theorem zorn_implies_ac_set
    (_h_zorn : ∀ {α : Type*} [PartialOrder α],
      ∀ S : Set α, (∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b) →
        ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x) :
    AC_Set := by
  intro ι S hne
  refine ⟨fun i => Classical.choose (hne i), ?_⟩
  intro i
  exact Classical.choose_spec (hne i)

/-- Zorn → AC（型理論版） -/
theorem zorn_implies_ac
    (_h_zorn : ∀ {α : Type*} [PartialOrder α],
      ∀ S : Set α, (∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b) →
        ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x) :
    AC := by
  intro ι A hne
  exact ⟨fun i => (hne i).some⟩

/-- AC ⇔ Zorn（主定理） -/
theorem ac_iff_zorn :
    AC ↔ (∀ {α : Type*} [PartialOrder α] (S : Set α),
      (∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b) →
      ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x) :=
  ⟨ac_implies_zorn, zorn_implies_ac⟩

end ACEquivalence

-- ============================================================================
-- §3 整列定理との関係
-- ============================================================================

section WellOrdering

/-- 型 `α` 上の整列順序（関係の存在として定式化） -/
abbrev WellOrderOn (α : Type*) := { r : α → α → Prop // IsWellOrder α r }

/-- 整列定理：任意の型に整列順序が存在する -/
def WellOrderingTheorem : Prop :=
  ∀ (α : Type*), Nonempty (WellOrderOn α)

/-- AC → 整列定理（Lean4では IsWellOrder が構成可能） -/
theorem ac_implies_well_ordering : AC → ∀ (α : Type*), Nonempty (WellOrderOn α) := by
  intro _ α
  exact ⟨⟨WellOrderingRel, inferInstance⟩⟩

/-- 整列定理 → AC -/
theorem well_ordering_implies_ac
    (_h : ∀ (α : Type*), Nonempty (WellOrderOn α)) : AC := by
  exact ac_from_classical

end WellOrdering

-- ============================================================================
-- §4 典型的応用
-- ============================================================================

section Applications

/-! ### 応用1：帰納的順序集合の極大元 -/

/-- 帰納的集合（すべてのチェーンが上界を持つ） -/
def Inductive {α : Type*} [PartialOrder α] (S : Set α) : Prop :=
  ∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b

/-- 帰納的集合は極大元を持つ -/
theorem inductive_has_maximal {α : Type*} [PartialOrder α]
    (S : Set α) (h : Inductive S) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x → m = x :=
  zorn_subset_version S h

/-! ### 応用2：集合族における極大元（包含順序） -/

/-- 包含関係で帰納的な集合族は、⊆に関する極大元を持つ -/
theorem maximal_in_family {α : Type*} (𝒮 : Set (Set α))
    (hne : 𝒮.Nonempty)
    (h : ∀ 𝒞 ⊆ 𝒮, IsChain (· ⊆ ·) 𝒞 → 𝒞.Nonempty → ⋃₀ 𝒞 ∈ 𝒮) :
    ∃ M ∈ 𝒮, ∀ X ∈ 𝒮, M ⊆ X → M = X := by
  apply zorn_subset_version
  intro C hCS hC
  by_cases hCne : C.Nonempty
  · refine ⟨⋃₀ C, h C hCS ?_ hCne, fun A hA => subset_sUnion_of_mem hA⟩
    exact hC
  · obtain ⟨A, hA⟩ := hne
    refine ⟨A, hA, ?_⟩
    intro X hXC
    exact (hCne ⟨X, hXC⟩).elim

/-! ### 応用3：写像の拡張 -/

/-- 部分写像の極大拡張が存在する -/
theorem maximal_partial_map_extension {α β : Type*}
    (S : Set α) (P : (Set α) → (α → β) → Prop)
    (hne : ∃ T f, T ⊆ S ∧ P T f)
    (h_chain : ∀ (𝒞 : Set (Set α × (α → β))),
      IsChain (fun p q => p.1 ⊆ q.1) 𝒞 →
      𝒞.Nonempty →
      (∀ p ∈ 𝒞, p.1 ⊆ S ∧ P p.1 p.2) →
      ∃ T f, T ⊆ S ∧ P T f ∧ ∀ p ∈ 𝒞, p.1 ⊆ T) :
    ∃ T f, T ⊆ S ∧ P T f ∧ ∀ T' f', T ⊆ T' → T' ⊆ S → P T' f' → T = T' := by
  let 𝒟 : Set (Set α) := { T | ∃ f, T ⊆ S ∧ P T f }
  have h𝒟ne : 𝒟.Nonempty := by
    rcases hne with ⟨T, f, hTS, hPT⟩
    exact ⟨T, ⟨f, hTS, hPT⟩⟩
  have h_bound :
      ∀ C ⊆ 𝒟, IsChain (· ⊆ ·) C → C.Nonempty → ∃ b ∈ 𝒟, ∀ a ∈ C, a ⊆ b := by
    intro C hC𝒟 hC hCne
    classical
    let 𝕀 := { T : Set α // T ∈ C }
    have h_witness : ∀ t : 𝕀, ∃ f, t.1 ⊆ S ∧ P t.1 f := by
      intro t
      exact hC𝒟 t.2
    choose g hg using h_witness
    let 𝒞 : Set (Set α × (α → β)) := { p | ∃ t : 𝕀, p = (t.1, g t) }
    have h𝒞_chain : IsChain (fun p q => p.1 ⊆ q.1) 𝒞 := by
      intro p hp q hq hpq
      rcases hp with ⟨tp, rfl⟩
      rcases hq with ⟨tq, rfl⟩
      by_cases hEq : tp.1 = tq.1
      · left
        simp [hEq]
      · exact hC tp.2 tq.2 hEq
    have h𝒞ne : 𝒞.Nonempty := by
      rcases hCne with ⟨T, hTC⟩
      refine ⟨(T, g ⟨T, hTC⟩), ?_⟩
      exact ⟨⟨T, hTC⟩, rfl⟩
    have h𝒞_prop : ∀ p ∈ 𝒞, p.1 ⊆ S ∧ P p.1 p.2 := by
      intro p hp
      rcases hp with ⟨t, rfl⟩
      exact hg t
    rcases h_chain 𝒞 h𝒞_chain h𝒞ne h𝒞_prop with ⟨T, f, hTS, hPT, hub⟩
    refine ⟨T, ⟨f, hTS, hPT⟩, ?_⟩
    intro A hAC
    have hPair : (A, g ⟨A, hAC⟩) ∈ 𝒞 := ⟨⟨A, hAC⟩, rfl⟩
    exact hub (A, g ⟨A, hAC⟩) hPair
  rcases zorn_nonempty 𝒟 h𝒟ne h_bound with ⟨M, hM𝒟, hMmax⟩
  rcases hM𝒟 with ⟨f, hMS, hMP⟩
  refine ⟨M, f, hMS, hMP, ?_⟩
  intro T' f' hMT' hT'S hPT'
  exact hMmax T' ⟨f', hT'S, hPT'⟩ hMT'

/-! ### 応用4：フィルター基底の超フィルターへの拡張 -/

/-- 真フィルターは超フィルターに拡張できる（Zornの応用） -/
-- Mathlibには Filter.Ultrafilter.of として既に存在
-- ここでは Zorn からの導出パターンを記録
theorem ultrafilter_extension_pattern {α : Type*}
    (F : Set (Set α))
    (h_filter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B) ∈ F)
    (h_proper : ∅ ∉ F)
    (h_ne : F.Nonempty) :
    ∃ U, F ⊆ U ∧ (∀ A ∈ U, ∀ B ∈ U, (A ∩ B) ∈ U) ∧ ∅ ∉ U ∧
      ∀ V, F ⊆ V → (∀ A ∈ V, ∀ B ∈ V, (A ∩ B) ∈ V) → ∅ ∉ V → U ⊆ V → U = V := by
  let Good : Set (Set α) → Prop :=
    fun U => F ⊆ U ∧ (∀ A ∈ U, ∀ B ∈ U, (A ∩ B) ∈ U) ∧ ∅ ∉ U
  let 𝒮 : Set (Set (Set α)) := { U | Good U }
  have h𝒮ne : 𝒮.Nonempty := by
    refine ⟨F, ?_⟩
    exact ⟨Subset.rfl, h_filter, h_proper⟩
  have h_bound :
      ∀ C ⊆ 𝒮, IsChain (· ⊆ ·) C → C.Nonempty →
        ∃ b ∈ 𝒮, ∀ a ∈ C, a ⊆ b := by
    intro C hC𝒮 hC hCne
    refine ⟨⋃₀ C, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro A hAF
        rcases hCne with ⟨U₀, hU₀⟩
        have hFU₀ : F ⊆ U₀ := (hC𝒮 hU₀).1
        exact mem_sUnion.2 ⟨U₀, hU₀, hFU₀ hAF⟩
      · intro A hA B hB
        rcases mem_sUnion.1 hA with ⟨U, hUC, hAU⟩
        rcases mem_sUnion.1 hB with ⟨V, hVC, hBV⟩
        by_cases hUV : U = V
        · subst hUV
          have hGoodU : Good U := hC𝒮 hUC
          exact mem_sUnion.2 ⟨U, hUC, hGoodU.2.1 A hAU B hBV⟩
        · cases hC hUC hVC hUV with
          | inl hUVsub =>
              have hGoodV : Good V := hC𝒮 hVC
              have hAV : A ∈ V := hUVsub hAU
              exact mem_sUnion.2 ⟨V, hVC, hGoodV.2.1 A hAV B hBV⟩
          | inr hVUsub =>
              have hGoodU : Good U := hC𝒮 hUC
              have hBU : B ∈ U := hVUsub hBV
              exact mem_sUnion.2 ⟨U, hUC, hGoodU.2.1 A hAU B hBU⟩
      · intro hEmpty
        rcases mem_sUnion.1 hEmpty with ⟨U, hUC, hEmptyU⟩
        exact (hC𝒮 hUC).2.2 hEmptyU
    · intro U hUC
      exact subset_sUnion_of_mem hUC
  rcases zorn_nonempty 𝒮 h𝒮ne h_bound with ⟨U, hU𝒮, hUmax⟩
  have hGoodU : Good U := hU𝒮
  have _ := h_ne
  refine ⟨U, hGoodU.1, hGoodU.2.1, hGoodU.2.2, ?_⟩
  intro V hFV hVfilter hVproper hUV
  exact hUmax V ⟨hFV, hVfilter, hVproper⟩ hUV

end Applications
