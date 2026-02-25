/-
  Bourbaki-inspired P1 notes for Lean 4 / Mathlib.
  Source: Bourbaki_Lean_Guide.md
-/

import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace BourbakiP1

-- ============================================================
-- §1. Preorders and transitivity
-- ============================================================

/-- In a preorder, the relation `≤` is transitive. -/
theorem preorder_trans {α : Type*} [Preorder α] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  exact le_trans hab hbc

-- ============================================================
-- §2. Partial orders and uniqueness of suprema
-- ============================================================

/-- A least upper bound is unique in a partial order. -/
theorem lub_unique {α : Type*} [PartialOrder α] {s : Set α} {a b : α}
    (ha : IsLUB s a) (hb : IsLUB s b) : a = b := by
  exact ha.unique hb

-- ============================================================
-- §3. Lattices and distributive laws
-- ============================================================

/-- Left distributivity in a distributive lattice. -/
theorem inf_sup_distrib_left {α : Type*} [DistribLattice α] (a b c : α) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  simpa using inf_sup_left a b c

/-- Right distributivity in a distributive lattice. -/
theorem sup_inf_distrib_right {α : Type*} [DistribLattice α] (a b c : α) :
    (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) := by
  simpa using sup_inf_right a b c

-- ============================================================
-- §4. Group homomorphisms and images
-- ============================================================

/-- The image of multiplication under a group homomorphism. -/
theorem map_mul_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (x * y) = f x * f y := by
  exact f.map_mul x y

/-- Membership in the image (range) of a group homomorphism. -/
theorem mem_range_iff_exists {G H : Type*} [Group G] [Group H]
    (f : G →* H) (y : H) : y ∈ Set.range f ↔ ∃ x : G, f x = y := by
  rfl

-- ============================================================
-- §5. Compactness and Hausdorffness
-- ============================================================

/-- In a Hausdorff space, every compact set is closed. -/
theorem compact_isClosed {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) : IsClosed K := by
  exact hK.isClosed

/-- Product of two compact sets is compact. -/
theorem compact_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {L : Set Y} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (K ×ˢ L) := by
  exact hK.prod hL

-- ============================================================
-- §6. Finite direct products of compact sets
-- ============================================================

/-- Finite product of compact sets is compact. -/
theorem finite_compact_pi {ι : Type*} [Finite ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] {K : ∀ i, Set (X i)}
    (hK : ∀ i, IsCompact (K i)) : IsCompact (Set.univ.pi K) := by
  simpa using isCompact_univ_pi hK

end BourbakiP1
