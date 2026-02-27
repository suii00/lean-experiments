/-
  StructureTower Escape Exercises
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Goal: Give StructureTower mathematical content beyond OrderHom ι (P(α)).
  Three directions:
    I.   Subobject constraints (filtered objects)
    II.  Inter-level algebra (graded structures)
    III. Limit axioms (continuity / separation / exhaustion)

  Each placeholder below is an exercise to be filled in.
  Exercises marked 🟢 🟡 🔴 by difficulty.
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Find

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definition (reproduced for self-containedness)
-- ════════════════════════════════════════════════════════════

structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β : Type*} [Preorder ι]

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

theorem mem_of_le (T : StructureTower ι α) {i j : ι} (hij : i ≤ j) {x : α}
    (hx : x ∈ T.level i) : x ∈ T.level j :=
  T.monotone_level hij hx

-- ════════════════════════════════════════════════════════════
-- Direction I: Subobject constraints
-- ════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- §I-1. Filtered additive commutative monoid  🟢
-- ────────────────────────────────────────────────────

/-- A filtered additive commutative monoid: each level is an additive submonoid.
    This is the simplest non-trivial departure from bare OrderHom. -/
structure FilteredAddCommMonoid (ι M : Type*) [Preorder ι] [AddCommMonoid M]
    extends StructureTower ι M where
  zero_mem : ∀ i : ι, (0 : M) ∈ level i
  add_mem  : ∀ (i : ι) {x y : M}, x ∈ level i → y ∈ level i → x + y ∈ level i

namespace FilteredAddCommMonoid

variable {ι M : Type*} [Preorder ι] [AddCommMonoid M]

/-- 🟢 Exercise I-1a: The trivial filtration (every level is {0}). -/
def trivial : FilteredAddCommMonoid ι M where
  level _ := {0}
  monotone_level := fun _i _j _hij _x hx => hx
  zero_mem := fun _i => by simp
  add_mem := by
    intro _i x y hx hy
    simp at hx hy
    simp [hx, hy]

/-- 🟢 Exercise I-1b: The universal filtration (every level is univ). -/
def universal : FilteredAddCommMonoid ι M where
  level _ := Set.univ
  monotone_level := fun _i _j _hij _x _hx => by simp
  zero_mem := fun _i => by simp
  add_mem := by
    intro _i x y hx hy
    simp

/-- 🟡 Exercise I-1c: Intersection of two filtered monoids is filtered. -/
def inter (F₁ F₂ : FilteredAddCommMonoid ι M) : FilteredAddCommMonoid ι M where
  level i := F₁.level i ∩ F₂.level i
  monotone_level := by
    intro i j hij x hx
    exact ⟨F₁.monotone_level hij hx.1, F₂.monotone_level hij hx.2⟩
  zero_mem := fun i => ⟨F₁.zero_mem i, F₂.zero_mem i⟩
  add_mem := by
    intro i x y hx hy
    exact ⟨F₁.add_mem i hx.1 hy.1, F₂.add_mem i hx.2 hy.2⟩

/-- 🟡 Exercise I-1d: Pullback along an AddMonoidHom. -/
def comap {N : Type*} [AddCommMonoid N] (φ : M →+ N)
    (F : FilteredAddCommMonoid ι N) : FilteredAddCommMonoid ι M where
  level i := φ ⁻¹' F.level i
  monotone_level := by
    intro i j hij x hx
    exact F.monotone_level hij hx
  zero_mem := by
    intro i
    simpa using F.zero_mem i
  add_mem := by
    intro i x y hx hy
    simpa [map_add] using F.add_mem i hx hy

end FilteredAddCommMonoid

-- ────────────────────────────────────────────────────
-- §I-2. Filtered group  🟡
-- ────────────────────────────────────────────────────

/-- A filtered group: each level is a subgroup of G. -/
structure FilteredGroup (ι G : Type*) [Preorder ι] [Group G]
    extends StructureTower ι G where
  one_mem : ∀ i : ι, (1 : G) ∈ level i
  mul_mem : ∀ (i : ι) {x y : G}, x ∈ level i → y ∈ level i → x * y ∈ level i
  inv_mem : ∀ (i : ι) {x : G}, x ∈ level i → x⁻¹ ∈ level i

namespace FilteredGroup

variable {ι G H : Type*} [Preorder ι] [Group G] [Group H]

/-- 🟢 Exercise I-2a: Each level determines a Subgroup. -/
def levelSubgroup (F : FilteredGroup ι G) (i : ι) : Subgroup G where
  carrier := F.level i
  one_mem' := F.one_mem i
  mul_mem' := by
    intro x y hx hy
    exact F.mul_mem i hx hy
  inv_mem' := by
    intro x hx
    exact F.inv_mem i hx

/-- 🟡 Exercise I-2b: The level subgroups form a monotone map. -/
theorem levelSubgroup_monotone (F : FilteredGroup ι G) :
    Monotone F.levelSubgroup := by
  intro i j hij x hx
  exact F.monotone_level hij hx

/-- 🟡 Exercise I-2c: Pullback along a group homomorphism. -/
def comap (φ : G →* H) (F : FilteredGroup ι H) : FilteredGroup ι G where
  level i := φ ⁻¹' F.level i
  monotone_level := by
    intro i j hij x hx
    exact F.monotone_level hij hx
  one_mem := by
    intro i
    simpa using F.one_mem i
  mul_mem := by
    intro i x y hx hy
    simpa [map_mul] using F.mul_mem i hx hy
  inv_mem := by
    intro i x hx
    simpa using F.inv_mem i hx

/-- 🔴 Exercise I-2d: Image of a filtered group (uses MonoidHom properties). -/
def map (φ : G →* H) (F : FilteredGroup ι G) : FilteredGroup ι H where
  level i := φ '' F.level i
  monotone_level := by
    intro i j hij y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, F.monotone_level hij hx, rfl⟩
  one_mem := by
    intro i
    exact ⟨1, F.one_mem i, by simp⟩
  mul_mem := by
    intro i x y hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    exact ⟨x' * y', F.mul_mem i hx' hy', by simp⟩
  inv_mem := by
    intro i x hx
    rcases hx with ⟨x', hx', rfl⟩
    exact ⟨x'⁻¹, F.inv_mem i hx', by simp⟩

end FilteredGroup

-- ────────────────────────────────────────────────────
-- §I-3. Filtered ring  🔴
-- ────────────────────────────────────────────────────

/-- A filtered ring with the multiplicative compatibility axiom.
    `mul_mem` intertwines the index algebra with the carrier algebra:
    this is exactly where OrderHom equivalence breaks. -/
structure FilteredRing (ι R : Type*) [Preorder ι] [AddMonoid ι] [Ring R]
    extends StructureTower ι R where
  zero_mem : ∀ i : ι, (0 : R) ∈ level i
  add_mem  : ∀ (i : ι) {x y : R}, x ∈ level i → y ∈ level i → x + y ∈ level i
  neg_mem  : ∀ (i : ι) {x : R}, x ∈ level i → -x ∈ level i
  one_mem  : (1 : R) ∈ level 0
  mul_mem  : ∀ (i j : ι) {x y : R},
    x ∈ level i → y ∈ level j → x * y ∈ level (i + j)

namespace FilteredRing

variable {ι R : Type*} [Preorder ι] [AddMonoid ι] [Ring R]

/-- 🟡 Exercise I-3a: level 0 is closed under multiplication. -/
theorem level_zero_mul_closed (F : FilteredRing ι R)
    {x y : R} (hx : x ∈ F.level 0) (hy : y ∈ F.level 0) :
    x * y ∈ F.level 0 := by
  simpa using F.mul_mem 0 0 hx hy
  -- Hint: F.mul_mem 0 0 hx hy gives x * y ∈ F.level (0 + 0), then rewrite

/-- 🔴 Exercise I-3b: Lax multiplicative compatibility. -/
theorem mul_mem_of_le (F : FilteredRing ι R)
    {i j k l : ι} (hij : i ≤ j) (hkl : k ≤ l)
    {x y : R} (hx : x ∈ F.level i) (hy : y ∈ F.level k) :
    x * y ∈ F.level (j + l) := by
  exact F.mul_mem j l (F.monotone_level hij hx) (F.monotone_level hkl hy)

end FilteredRing

-- ════════════════════════════════════════════════════════════
-- Direction III: Limit axioms
-- ════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- §III-1. Exhaustive tower  🟢
-- ────────────────────────────────────────────────────

/-- A tower is exhaustive if every element appears at some level. -/
structure ExhaustiveTower (ι α : Type*) [Preorder ι]
    extends StructureTower ι α where
  exhaustive : ∀ x : α, ∃ i : ι, x ∈ level i

namespace ExhaustiveTower

variable {ι α : Type*} [Preorder ι]

/-- 🟢 Exercise III-1a: An exhaustive tower covers everything. -/
theorem union_eq_univ (T : ExhaustiveTower ι α) :
    T.toStructureTower.union = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases T.exhaustive x with ⟨i, hi⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- 🟢 Exercise III-1b: For ℕ-indexed exhaustive towers, rank exists. -/
noncomputable def rank (T : ExhaustiveTower ℕ α) (x : α) : ℕ :=
  by
    classical
    exact Nat.find (T.exhaustive x)

/-- 🟢 Exercise III-1c: The rank is realized. -/
theorem rank_spec (T : ExhaustiveTower ℕ α) (x : α) :
    x ∈ T.level (T.rank x) := by
  classical
  simpa [rank] using Nat.find_spec (T.exhaustive x)

/-- 🟡 Exercise III-1d: The rank is minimal. -/
theorem rank_le (T : ExhaustiveTower ℕ α) (x : α)
    (n : ℕ) (h : x ∈ T.level n) :
    T.rank x ≤ n := by
  classical
  simpa [rank] using Nat.find_min' (T.exhaustive x) h

/-- 🟡 Exercise III-1e: Finer tower ⟹ higher rank. -/
theorem rank_antitone (T₁ T₂ : ExhaustiveTower ℕ α)
    (h : ∀ i, T₁.level i ⊆ T₂.level i) (x : α) :
    T₂.rank x ≤ T₁.rank x := by
  exact rank_le (T := T₂) (x := x) (n := T₁.rank x) (h _ (rank_spec (T := T₁) x))

end ExhaustiveTower

-- ────────────────────────────────────────────────────
-- §III-2. Separated filtration  🟡
-- ────────────────────────────────────────────────────

/-- A separated (Hausdorff) filtered additive group:
    the intersection of all levels is trivial. -/
structure SeparatedFilteredAddGroup (ι G : Type*) [Preorder ι] [AddCommGroup G]
    extends StructureTower ι G where
  zero_mem  : ∀ i, (0 : G) ∈ level i
  add_mem   : ∀ i {x y : G}, x ∈ level i → y ∈ level i → x + y ∈ level i
  neg_mem   : ∀ i {x : G}, x ∈ level i → -x ∈ level i
  separated : ∀ x : G, (∀ i, x ∈ level i) → x = 0

namespace SeparatedFilteredAddGroup

variable {ι G : Type*} [Preorder ι] [AddCommGroup G]

/-- 🟡 Exercise III-2a: The intersection of all levels is {0}. -/
theorem iInter_level_eq (F : SeparatedFilteredAddGroup ι G) :
    ⋂ i, F.level i = {0} := by
  ext x
  constructor
  · intro hx
    have hxAll : ∀ i, x ∈ F.level i := by
      intro i
      exact Set.mem_iInter.mp hx i
    have hx0 : x = 0 := F.separated x hxAll
    simp [hx0]
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Set.mem_iInter.mpr (fun i => F.zero_mem i)

/-- 🟡 Exercise III-2b: Non-zero elements escape some level. -/
theorem exists_not_mem_of_ne_zero (F : SeparatedFilteredAddGroup ι G)
    {x : G} (hx : x ≠ 0) :
    ∃ i, x ∉ F.level i := by
  by_contra h
  apply hx
  apply F.separated
  intro i
  by_contra hxi
  exact h ⟨i, hxi⟩

end SeparatedFilteredAddGroup

-- ════════════════════════════════════════════════════════════
-- Synthesis: concrete witness that subobject ≠ powerset
-- ════════════════════════════════════════════════════════════

/-- A monotone set family that is NOT a filtered additive monoid.
    This witnesses that FilteredAddCommMonoid ι ℤ ⊊ OrderHom ι (P(ℤ)). -/
example : ∃ (f : ℕ → Set ℤ), Monotone f ∧
    ¬(∀ i, (0 : ℤ) ∈ f i ∧ ∀ x y, x ∈ f i → y ∈ f i → x + y ∈ f i) := by
  refine ⟨fun _ => {1}, fun _i _j _hij x hx => hx, ?_⟩
  intro h
  have h0 : (0 : ℤ) ∈ ({1} : Set ℤ) := (h 0).1
  exact Int.zero_ne_one (Set.mem_singleton_iff.mp h0)

end StructureTower

end BourbakiGuide
