/-
  Order-theoretic examples of StructureTower.

  Each example shows how a standard order-theoretic object
  is an instance of the tower abstraction.

  §5a. const         — trivial / degenerate baseline
  §5b. iic / ici     — principal down/up-set towers
  §5c. ofMonotoneSeq — ℕ-indexed filtration
  §5d. reindex       — change of index (functorial)
  §5e. ofAntitone    — decreasing families via OrderDual
  §5f. ofIterate     — expansive operator iterates
  §5g. icc           — bounded-below intervals
  §5h. prod / inter / sup — levelwise constructions
  §5i. relations     — how examples connect to each other
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure

open Set Function

namespace BourbakiGuide

-- ────────────────────────────────────────────────────
-- Core definition (same as Bourbaki_Lean_Guide.lean §1)
-- ────────────────────────────────────────────────────

structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β : Type*} [Preorder ι]

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

-- ============================================================
-- §5a. Constant tower（定数塔）
-- ============================================================

/-- Every level is the same set S. This is the degenerate case:
    no information is encoded in the stratification. -/
def const (ι : Type*) [Preorder ι] (S : Set α) : StructureTower ι α where
  level _ := S
  monotone_level := fun _ => Subset.rfl

@[simp] theorem const_level (S : Set α) (i : ι) :
    (const ι S).level i = S := rfl

theorem const_union (S : Set α) [Nonempty ι] :
    (const ι S).union = S := by
  simp [union, Set.iUnion_const]

-- ============================================================
-- §5b. Principal downset tower（主下方集合塔）
-- ============================================================

/-- The most fundamental example: `level x = {y | y ≤ x}`.
    The tower *is* the order relation, viewed as a set-valued map.
    Every other Iic-flavored tower factors through this one. -/
def iic (α : Type*) [Preorder α] : StructureTower α α where
  level x := Set.Iic x
  monotone_level := fun hij _ hy => le_trans hy hij

@[simp] theorem mem_iic_level {α : Type*} [Preorder α] (x y : α) :
    y ∈ (iic α).level x ↔ y ≤ x := Iff.rfl

theorem iic_union_eq_univ (α : Type*) [Preorder α] :
    (iic α).union = Set.univ := by
  ext x
  simp [union, Set.mem_iUnion]
  exact ⟨fun _ => trivial, fun _ => ⟨x, le_refl x⟩⟩

/-- Dual: principal upset tower `level x = {y | x ≤ y}`,
    indexed by `αᵒᵈ` so that it becomes increasing. -/
def ici (α : Type*) [Preorder α] : StructureTower αᵒᵈ α where
  level x := Set.Ici (OrderDual.ofDual x)
  monotone_level := by
    intro i j hij y hy
    -- hij : i ≤ j in αᵒᵈ means ofDual j ≤ ofDual i in α
    exact le_trans (OrderDual.ofDual_le_ofDual.mpr hij) hy

@[simp] theorem mem_ici_level {α : Type*} [Preorder α] (x : αᵒᵈ) (y : α) :
    y ∈ (ici α).level x ↔ OrderDual.ofDual x ≤ y := Iff.rfl

-- ============================================================
-- §5c. Monotone sequence tower（単調列塔）
-- ============================================================

/-- An ℕ-indexed chain of principal ideals, from a monotone sequence. -/
def ofMonotoneSeq {α : Type*} [Preorder α] (c : ℕ → α) (hc : Monotone c) :
    StructureTower ℕ α where
  level n := Set.Iic (c n)
  monotone_level := fun hij _ hy => le_trans hy (hc hij)

@[simp] theorem mem_ofMonotoneSeq_level {α : Type*} [Preorder α]
    (c : ℕ → α) (hc : Monotone c) (n : ℕ) (y : α) :
    y ∈ (ofMonotoneSeq c hc).level n ↔ y ≤ c n := Iff.rfl

/-- Standard ℕ-filtration: level n = {m | m ≤ n}. -/
def natFiltration : StructureTower ℕ ℕ := ofMonotoneSeq id monotone_id

@[simp] theorem mem_natFiltration_level (n m : ℕ) :
    m ∈ natFiltration.level n ↔ m ≤ n := Iff.rfl

theorem natFiltration_union_eq_univ : natFiltration.union = Set.univ := by
  ext x
  simp [union, Set.mem_iUnion]
  exact ⟨fun _ => trivial, fun _ => ⟨x, le_refl x⟩⟩

-- ============================================================
-- §5d. Reindex（添字変換）
-- ============================================================

/-- Change of index: precompose a tower with a monotone map.
    This is the contravariant part of the "tower functor". -/
def reindex {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) : StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun hij => T.monotone_level (hf hij)

@[simp] theorem reindex_level {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) (i : ι) :
    (reindex f hf T).level i = T.level (f i) := rfl

/-- Reindex by id is the identity. -/
theorem reindex_id (T : StructureTower ι α) :
    reindex id monotone_id T = T := by
  ext i _; simp

/-- Reindex is functorial. -/
theorem reindex_comp {κ μ : Type*} [Preorder κ] [Preorder μ]
    (f : ι → κ) (hf : Monotone f) (g : κ → μ) (hg : Monotone g)
    (T : StructureTower μ α) :
    reindex f hf (reindex g hg T) = reindex (g ∘ f) (hg.comp hf) T := by
  ext i _; simp

-- ============================================================
-- §5e. Antitone families via OrderDual（反単調族の双対化）
-- ============================================================

/-- A *decreasing* family `d : ι → Set α` becomes an increasing family
    when we view the index through `ιᵒᵈ`. -/
def ofAntitone (d : ι → Set α) (hd : Antitone d) :
    StructureTower ιᵒᵈ α where
  level i := d (OrderDual.ofDual i)
  monotone_level := by
    intro i j hij
    exact hd (OrderDual.ofDual_le_ofDual.mpr hij)

@[simp] theorem ofAntitone_level (d : ι → Set α) (hd : Antitone d) (i : ιᵒᵈ) :
    (ofAntitone d hd).level i = d (OrderDual.ofDual i) := rfl

-- ============================================================
-- §5f. Iterated operator tower（反復作用素塔）
-- ============================================================

/-- Auxiliary: expansive monotone f satisfies f^[n] S ⊆ f^[n+1] S. -/
private theorem iterate_subset_succ (f : Set α → Set α) (hf : Monotone f)
    (S : Set α) (hS : S ⊆ f S) :
    ∀ n : ℕ, f^[n] S ⊆ f^[n + 1] S := by
  intro n
  induction n with
  | zero => exact hS
  | succ k ih =>
    show f (f^[k] S) ⊆ f (f^[k + 1] S)
    exact hf ih

/-- Given monotone `f : Set α → Set α` with `S ⊆ f S`,
    the iterates `n ↦ f^[n] S` form an ℕ-tower.
    Models: generated σ-algebra steps, iterative closure, etc. -/
def ofIterate (f : Set α → Set α) (hf : Monotone f)
    (S : Set α) (hexpand : S ⊆ f S) :
    StructureTower ℕ α where
  level n := f^[n] S
  monotone_level := by
    intro i j hij
    induction hij with
    | refl => exact Subset.rfl
    | step _ ih =>
      exact Subset.trans ih (iterate_subset_succ f hf S hexpand _)

@[simp] theorem ofIterate_level (f : Set α → Set α) (hf : Monotone f)
    (S : Set α) (hexpand : S ⊆ f S) (n : ℕ) :
    (ofIterate f hf S hexpand).level n = f^[n] S := rfl

theorem seed_subset_union_ofIterate (f : Set α → Set α) (hf : Monotone f)
    (S : Set α) (hexpand : S ⊆ f S) :
    S ⊆ (ofIterate f hf S hexpand).union := by
  intro x hx
  simp [union, Set.mem_iUnion]
  exact ⟨0, hx⟩

-- ============================================================
-- §5g. Bounded-below interval tower（下界付き区間塔）
-- ============================================================

/-- `level x = Icc a x = {y | a ≤ y ∧ y ≤ x}`.
    A "truncated" version of the Iic tower, restricting to elements above `a`. -/
def icc {α : Type*} [Preorder α] (a : α) : StructureTower α α where
  level x := Set.Icc a x
  monotone_level := fun hij _ hy => ⟨hy.1, le_trans hy.2 hij⟩

@[simp] theorem mem_icc_level {α : Type*} [Preorder α] (a x y : α) :
    y ∈ (icc a).level x ↔ a ≤ y ∧ y ≤ x := Iff.rfl

theorem icc_level_subset_iic_level {α : Type*} [Preorder α] (a x : α) :
    (icc a).level x ⊆ (iic α).level x :=
  fun _ hy => hy.2

-- ============================================================
-- §5h. Levelwise constructions（レベルごとの構成）
-- ============================================================

/-- Levelwise product: `level i = T₁.level i × T₂.level i`. -/
def prod (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    StructureTower ι (α × β) where
  level i := T₁.level i ×ˢ T₂.level i
  monotone_level := fun hij _ hp =>
    ⟨T₁.monotone_level hij hp.1, T₂.monotone_level hij hp.2⟩

@[simp] theorem mem_prod_level (T₁ : StructureTower ι α) (T₂ : StructureTower ι β)
    (i : ι) (p : α × β) :
    p ∈ (prod T₁ T₂).level i ↔ p.1 ∈ T₁.level i ∧ p.2 ∈ T₂.level i :=
  Set.mem_prod

/-- Levelwise intersection. -/
def inter (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i := T₁.level i ∩ T₂.level i
  monotone_level := fun hij _ hx =>
    ⟨T₁.monotone_level hij hx.1, T₂.monotone_level hij hx.2⟩

@[simp] theorem mem_inter_level (T₁ T₂ : StructureTower ι α) (i : ι) (x : α) :
    x ∈ (inter T₁ T₂).level i ↔ x ∈ T₁.level i ∧ x ∈ T₂.level i := Iff.rfl

/-- Levelwise union. -/
def sup (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i := T₁.level i ∪ T₂.level i
  monotone_level := fun hij _ hx => by
    rcases hx with h | h
    · exact Or.inl (T₁.monotone_level hij h)
    · exact Or.inr (T₂.monotone_level hij h)

-- ============================================================
-- §5i. Inter-example relations（例の間の関係）
-- ============================================================

section Relations

/-- An ℕ-sequence tower is a reindex of the Iic tower. -/
theorem ofMonotoneSeq_eq_reindex {α : Type*} [Preorder α]
    (c : ℕ → α) (hc : Monotone c) :
    ofMonotoneSeq c hc = reindex c hc (iic α) := by
  ext n y; simp

/-- The Icc tower is the intersection of const and Iic. -/
theorem icc_eq_inter_const_iic {α : Type*} [Preorder α] (a : α) :
    icc a = inter (const α (Set.Ici a)) (iic α) := by
  ext x y
  simp [icc, inter, const, iic, Set.Ici, Set.Iic, Set.Icc]
  exact Iff.rfl

end Relations

end StructureTower

end BourbakiGuide
