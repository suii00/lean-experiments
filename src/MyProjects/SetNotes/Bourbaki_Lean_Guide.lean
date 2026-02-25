/-
  Bourbaki-inspired "structure-first" module.
  Source: Bourbaki_Lean_Guide.md

  Goal of this file:
  - keep the spirit of "from general structures to concrete examples"
  - provide a reusable skeleton (not a full exercise set)
  - model one possible formal core of "structures meres" via towers
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure

open Set Function

namespace BourbakiGuide

-- ============================================================
-- §1. Tower of structures (Bourbaki-style abstraction)
-- ============================================================

/--
`StructureTower ι α` records an increasing family of subsets of `α` indexed by `ι`.
This captures the "stratified structure" viewpoint appearing across order, algebra,
and topology in a single interface.
-/
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β γ : Type*} [Preorder ι]

/-- Convenience: every tower gives a monotone map `ι → Set α`. -/
theorem level_monotone (T : StructureTower ι α) : Monotone T.level := by
  intro i j hij
  exact T.monotone_level hij

/-- Membership propagates upward along the index preorder. -/
theorem mem_of_le (T : StructureTower ι α) {i j : ι} (hij : i ≤ j) {x : α}
    (hx : x ∈ T.level i) : x ∈ T.level j :=
  T.monotone_level hij hx

/-- The set covered by all levels of the tower. -/
def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

theorem mem_union_iff (T : StructureTower ι α) {x : α} :
    x ∈ T.union ↔ ∃ i, x ∈ T.level i := by
  simp [union]

/-- If each point appears at some level, the tower covers the whole type. -/
theorem union_eq_univ_of_forall_mem (T : StructureTower ι α)
    (hcover : ∀ x : α, ∃ i : ι, x ∈ T.level i) :
    T.union = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rcases hcover x with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, hi⟩

-- ============================================================
-- §2. Transport and induced towers
-- ============================================================

/-- Pullback of a tower along a map. -/
def comap (f : α → β) (T : StructureTower ι β) : StructureTower ι α where
  level i := f ⁻¹' T.level i
  monotone_level := by
    intro i j hij x hx
    exact T.monotone_level hij hx

/-- Direct image of a tower along a map. -/
def map (f : α → β) (T : StructureTower ι α) : StructureTower ι β where
  level i := f '' T.level i
  monotone_level := by
    intro i j hij y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, T.monotone_level hij hx, rfl⟩

/-- Transport of a tower across an equivalence (Bourbaki transport principle). -/
def transport (e : α ≃ β) (T : StructureTower ι α) : StructureTower ι β :=
  map e T

theorem mem_transport_iff (e : α ≃ β) (T : StructureTower ι α) {i : ι} {y : β} :
    y ∈ (transport e T).level i ↔ e.symm y ∈ T.level i := by
  constructor
  · intro hy
    rcases hy with ⟨x, hx, hxy⟩
    subst hxy
    simpa
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩

-- ============================================================
-- §3. Morphisms of towers
-- ============================================================

/-- Structure-preserving maps between towers with a common index preorder. -/
structure Hom (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  toFun : α → β
  preserves : ∀ i, MapsTo toFun (T₁.level i) (T₂.level i)

instance (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) : CoeFun (Hom T₁ T₂) (fun _ => α → β) where
  coe f := f.toFun

/-- Identity morphism on a tower. -/
def Hom.id (T : StructureTower ι α) : Hom T T where
  toFun := fun x => x
  preserves := by
    intro i x hx
    simpa using hx

/-- Composition of tower morphisms. -/
def Hom.comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) : Hom T₁ T₃ where
  toFun := g ∘ f
  preserves := by
    intro i x hx
    exact g.preserves i (f.preserves i hx)

-- ============================================================
-- §4. Order/Galois/Closure instantiation
-- ============================================================

section OrderSide

variable {α β : Type*} [PartialOrder α] [Preorder β]

/-- A closure operator yields a canonical tower via principal closed upper sets. -/
def towerOfClosure (c : ClosureOperator α) : StructureTower α α where
  level x := {y : α | y ≤ c x}
  monotone_level := by
    intro i j hij y hy
    exact le_trans hy (c.monotone hij)

@[simp] theorem mem_towerOfClosure_iff (c : ClosureOperator α) (x y : α) :
    y ∈ (towerOfClosure c).level x ↔ y ≤ c x := Iff.rfl

/-- Galois connection gives a closure operator, then a structure tower. -/
def towerOfGalois {l : α → β} {u : β → α} (hgc : GaloisConnection l u) :
    StructureTower α α :=
  towerOfClosure hgc.closureOperator

@[simp] theorem mem_towerOfGalois_iff {l : α → β} {u : β → α}
    (hgc : GaloisConnection l u) (x y : α) :
    y ∈ (towerOfGalois hgc).level x ↔ y ≤ u (l x) := Iff.rfl

end OrderSide

end StructureTower

end BourbakiGuide
