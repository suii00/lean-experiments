/-
  Bourbaki-style order notes:
  core definitions + Zorn lemma bridge to mathlib.
-/

import Mathlib.Order.Zorn

namespace Bourbaki

section Definitions

class Ordre (α : Type*) extends LE α where
  refl : ∀ a : α, a ≤ a
  trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  antisym : ∀ {a b : α}, a ≤ b → b ≤ a → a = b

class OrdreTotal (α : Type*) extends Ordre α where
  total : ∀ a b : α, a ≤ b ∨ b ≤ a

variable {α : Type*} [Ordre α]

def EstChaine (C : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ C → b ∈ C → a ≤ b ∨ b ≤ a

def EstMajorant (S : Set α) (x : α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ S → a ≤ x

def EstMaximal (S : Set α) (x : α) : Prop :=
  x ∈ S ∧ ∀ ⦃y : α⦄, y ∈ S → x ≤ y → x = y

def EstInductif (S : Set α) : Prop :=
  ∀ C, C ⊆ S → EstChaine C → ∃ b ∈ S, EstMajorant C b

end Definitions

section Bridge

instance ordreToPartialOrder (α : Type*) [h : Ordre α] : PartialOrder α where
  le := h.le
  le_refl := h.refl
  le_trans := fun _ _ _ => h.trans
  le_antisymm := fun _ _ hab hba => h.antisym hab hba

variable {α : Type*} [Ordre α]

lemma estChaine_iff_isChain (C : Set α) :
    EstChaine C ↔ IsChain (· ≤ ·) C := by
  constructor
  · intro h a ha b hb hab
    exact h ha hb
  · intro h a b ha hb
    by_cases hab : a = b
    · left
      simp [hab]
    · exact h ha hb hab

end Bridge

section Zorn

variable {α : Type*} [Ordre α]

theorem zorn (S : Set α) (hInd : EstInductif S) :
    ∃ m, EstMaximal S m := by
  have hMathlib : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∃ b ∈ S, ∀ a ∈ C, a ≤ b := by
    intro C hCS hC
    exact hInd C hCS ((estChaine_iff_isChain C).2 hC)
  rcases zorn_le₀ S hMathlib with ⟨m, hmS, hmMax⟩
  refine ⟨m, hmS, ?_⟩
  intro y hy hmy
  exact Ordre.antisym hmy (hmMax hy hmy)

theorem zorn_global
    (h : ∀ C : Set α, EstChaine C → ∃ b : α, EstMajorant C b) :
    ∃ m : α, ∀ x : α, m ≤ x → x ≤ m := by
  let S : Set α := Set.univ
  have hInd : EstInductif S := by
    intro C _ hC
    rcases h C hC with ⟨b, hb⟩
    exact ⟨b, Set.mem_univ b, hb⟩
  rcases zorn S hInd with ⟨m, hmS, hmMax⟩
  refine ⟨m, ?_⟩
  intro x hmx
  have hEq : m = x := hmMax (by simp [S]) hmx
  cases hEq
  exact Ordre.refl m

end Zorn

section Choice

def AxiomeDeChoix : Prop :=
  ∀ {ι : Type*} (A : ι → Type*), (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i)

theorem axiomeDeChoix_classical : AxiomeDeChoix := by
  intro ι A hA
  classical
  exact ⟨fun i => Classical.choice (hA i)⟩

theorem choix_implique_zorn :
    AxiomeDeChoix →
    (∀ {α : Type*} [Ordre α] (S : Set α), EstInductif S → ∃ m, EstMaximal S m) := by
  intro _ α _ S hInd
  exact zorn S hInd

theorem zorn_implique_choix
    (_hZorn : ∀ {α : Type*} [Ordre α] (S : Set α), EstInductif S → ∃ m, EstMaximal S m) :
    AxiomeDeChoix := by
  exact axiomeDeChoix_classical

theorem equivalence_choix_zorn :
    AxiomeDeChoix ↔
    (∀ {α : Type*} [Ordre α] (S : Set α), EstInductif S → ∃ m, EstMaximal S m) :=
  ⟨choix_implique_zorn, zorn_implique_choix⟩

end Choice

end Bourbaki
