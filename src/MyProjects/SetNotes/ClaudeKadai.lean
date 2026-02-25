/-
  Bourbaki-style set theory skeleton in Lean 4 / Mathlib.
  Source: Claude-kadai.md
-/

import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Set.Lattice

open Set Function

noncomputable section

namespace Bourbaki

-- ============================================================
-- §1. τ operator (Hilbert's ε)
-- ============================================================

/-- Bourbaki's τ operator: chooses an element satisfying `P` when it exists. -/
def tau {α : Type*} [Nonempty α] (P : α → Prop) : α :=
  Classical.epsilon P

/-- τ-specification axiom (`Classical.epsilon_spec`). -/
lemma tau_spec {α : Type*} [Nonempty α] (P : α → Prop) (h : ∃ x, P x) : P (tau P) := by
  exact Classical.epsilon_spec h

/-- Excluded middle in Bourbaki style. -/
lemma bourbaki_lem (P : Prop) : P ∨ ¬P := by
  exact Classical.em P

-- ============================================================
-- §2. Relations
-- ============================================================

/-- Binary relation on `α`. -/
abbrev Relation (α : Type*) := α → α → Prop

/-- Domain of a relation. -/
def relDomain {α : Type*} (R : Relation α) : Set α :=
  { x | ∃ y, R x y }

/-- Range of a relation. -/
def relRange {α : Type*} (R : Relation α) : Set α :=
  { y | ∃ x, R x y }

/-- Converse relation. -/
def relInverse {α : Type*} (R : Relation α) : Relation α :=
  fun x y => R y x

/-- Composition of relations. -/
def relComp {α : Type*} (R S : Relation α) : Relation α :=
  fun x z => ∃ y, R x y ∧ S y z

-- ============================================================
-- §3. Functions
-- ============================================================

/-- Functional relation: each `x` maps to at most one `y`. -/
def IsFunctional {α β : Type*} (R : α → β → Prop) : Prop :=
  ∀ x y z, R x y → R x z → y = z

/-- Total functional relation. -/
def IsTotalFunctional {α β : Type*} (R : α → β → Prop) : Prop :=
  (∀ x, ∃ y, R x y) ∧ IsFunctional R

/-- Surjectivity (Bourbaki phrasing). -/
def IsSurjection {α β : Type*} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- Injectivity (Bourbaki phrasing). -/
def IsInjection {α β : Type*} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- Bijectivity. -/
def IsBijection {α β : Type*} (f : α → β) : Prop :=
  IsSurjection f ∧ IsInjection f

lemma injection_iff_injective {α β : Type*} (f : α → β) :
    IsInjection f ↔ Injective f := by
  simp [IsInjection, Injective]

lemma surjection_iff_surjective {α β : Type*} (f : α → β) :
    IsSurjection f ↔ Surjective f := by
  simp [IsSurjection, Surjective]

/-- Build an `Equiv` from a bijection. -/
def bijectionToEquiv {α β : Type*} (f : α → β) (hf : IsBijection f) : α ≃ β := by
  rcases hf with ⟨hsurj, hinj⟩
  refine
    { toFun := f
      invFun := fun b => Classical.choose (hsurj b)
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    exact hinj _ _ (Classical.choose_spec (hsurj (f a)))
  · intro b
    exact Classical.choose_spec (hsurj b)

-- ============================================================
-- §4. Equivalence relations and quotient sets
-- ============================================================

/-- Axiomatic equivalence relation. -/
structure EquivRelation (α : Type*) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ x y, rel x y → rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z

/-- Convert to `Setoid`. -/
def EquivRelation.toSetoid {α : Type*} (R : EquivRelation α) : Setoid α where
  r := R.rel
  iseqv := by
    refine ⟨R.refl, ?_, ?_⟩
    · intro x y hxy
      exact R.symm x y hxy
    · intro x y z hxy hyz
      exact R.trans x y z hxy hyz

/-- Equivalence class of `x`. -/
def equivClass {α : Type*} (R : EquivRelation α) (x : α) : Set α :=
  { y | R.rel x y }

/-- Quotient set as a family of classes. -/
def quotientSet {α : Type*} (R : EquivRelation α) : Set (Set α) :=
  { C | ∃ x, C = equivClass R x }

/-- Two equivalence classes are either disjoint or equal. -/
lemma equivClass_disjoint_or_eq {α : Type*} (R : EquivRelation α) (x y : α) :
    equivClass R x ∩ equivClass R y = ∅ ∨ equivClass R x = equivClass R y := by
  by_cases hxy : R.rel x y
  · right
    ext z
    constructor
    · intro hz
      exact R.trans y x z (R.symm x y hxy) hz
    · intro hz
      exact R.trans x y z hxy hz
  · left
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hzx, hzy⟩
      exact False.elim (hxy (R.trans x z y hzx (R.symm y z hzy)))
    · intro hz
      simp at hz

/-- Every element belongs to some quotient class. -/
lemma quotientSet_partition {α : Type*} (R : EquivRelation α) :
    ∀ x : α, ∃ C ∈ quotientSet R, x ∈ C := by
  intro x
  refine ⟨equivClass R x, ?_, ?_⟩
  · exact ⟨x, rfl⟩
  · exact R.refl x

-- ============================================================
-- §5. Order relations
-- ============================================================

/-- Preorder (Bourbaki-style explicit fields). -/
structure Preorder' (α : Type*) where
  le : α → α → Prop
  refl : ∀ x, le x x
  trans : ∀ x y z, le x y → le y z → le x z

/-- Partial order = preorder + antisymmetry. -/
structure PartialOrder' (α : Type*) extends Preorder' α where
  antisymm : ∀ x y, le x y → le y x → x = y

/-- Total order = partial order + totality. -/
structure TotalOrder' (α : Type*) extends PartialOrder' α where
  total : ∀ x y, le x y ∨ le y x

/-- Minimum in a subset. -/
def IsMinimum {α : Type*} (O : PartialOrder' α) (S : Set α) (m : α) : Prop :=
  m ∈ S ∧ ∀ x ∈ S, O.le m x

/-- Well-ordered set in the Bourbaki sense. -/
def IsWellOrdered {α : Type*} (O : TotalOrder' α) : Prop :=
  ∀ S : Set α, S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, O.le m x

-- ============================================================
-- §6. Equipotence and cardinals
-- ============================================================

/-- `α` and `β` are equipotent iff there is an equivalence. -/
def Equipotent (α β : Type*) : Prop :=
  Nonempty (α ≃ β)

lemma equipotent_refl (α : Type*) : Equipotent α α := by
  exact ⟨Equiv.refl α⟩

lemma equipotent_symm {α β : Type*} (h : Equipotent α β) : Equipotent β α := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

lemma equipotent_trans {α β γ : Type*} (h₁ : Equipotent α β) (h₂ : Equipotent β γ) :
    Equipotent α γ := by
  rcases h₁ with ⟨e₁⟩
  rcases h₂ with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

/-- Cantor-Bernstein theorem via Mathlib's embedding antisymmetry. -/
theorem cantorBernstein {α β : Type*}
    (f : α ↪ β) (g : β ↪ α) : Equipotent α β := by
  simpa [Equipotent] using (Function.Embedding.antisymm f g)

/-- Cardinal comparison by existence of an embedding. -/
def CardLE (α β : Type*) : Prop :=
  Nonempty (α ↪ β)

/-- Any two cardinals are comparable (classically). -/
theorem cardinal_comparable (α β : Type*) :
    CardLE α β ∨ CardLE β α := by
  simpa [CardLE] using (Function.Embedding.total α β)

-- ============================================================
-- §7. Axiom of choice and well-ordering
-- ============================================================

/-- Set-indexed choice function. -/
theorem axiomOfChoice {ι α : Type*} {A : ι → Set α} (h : ∀ i, (A i).Nonempty) :
    ∃ f : ι → α, ∀ i, f i ∈ A i := by
  exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec⟩

/-- Zermelo well-ordering principle (via `WellOrderingRel`). -/
theorem wellOrderingPrinciple (α : Type*) :
    ∃ (R : α → α → Prop), IsWellOrder α R := by
  exact ⟨WellOrderingRel, inferInstance⟩

end Bourbaki
