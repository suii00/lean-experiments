/-
  Bourbaki-inspired P1 extended notes for Lean 4 / Mathlib.
  Source: Bourbaki_Lean_Guide.md
-/

import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.MetricSpace.Cauchy

open Set Function

namespace BourbakiP1Extended

-- ============================================================
-- §1. Galois connections and order theory
-- ============================================================

/-- Left adjoint in order-theoretic form. -/
def IsLowerAdjoint {α β : Type*} [Preorder α] [Preorder β] (l : α → β) : Prop :=
  ∃ u : β → α, GaloisConnection l u

/-- Right adjoint in order-theoretic form. -/
def IsUpperAdjoint {α β : Type*} [Preorder α] [Preorder β] (u : β → α) : Prop :=
  ∃ l : α → β, GaloisConnection l u

theorem galois_monotone_left {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α} (hgc : GaloisConnection l u) : Monotone l := by
  exact hgc.monotone_l

theorem galois_monotone_right {α β : Type*} [Preorder α] [Preorder β]
    {l : α → β} {u : β → α} (hgc : GaloisConnection l u) : Monotone u := by
  exact hgc.monotone_u

-- ============================================================
-- §2. Closure operators
-- ============================================================

/-- Closure operator induced by a Galois connection. -/
def gcClosure {α β : Type*} [PartialOrder α] [Preorder β]
    {l : α → β} {u : β → α} (hgc : GaloisConnection l u) : ClosureOperator α :=
  hgc.closureOperator

theorem le_gcClosure {α β : Type*} [PartialOrder α] [Preorder β]
    {l : α → β} {u : β → α} (hgc : GaloisConnection l u) (x : α) :
    x ≤ gcClosure hgc x := by
  exact (gcClosure hgc).le_closure x

theorem gcClosure_monotone {α β : Type*} [PartialOrder α] [Preorder β]
    {l : α → β} {u : β → α} (hgc : GaloisConnection l u) :
    Monotone (gcClosure hgc) := by
  exact (gcClosure hgc).monotone

theorem gcClosure_idempotent {α β : Type*} [PartialOrder α] [Preorder β]
    {l : α → β} {u : β → α} (hgc : GaloisConnection l u) (x : α) :
    gcClosure hgc (gcClosure hgc x) = gcClosure hgc x := by
  exact (gcClosure hgc).idempotent' x

-- ============================================================
-- §2b. Bourbaki-style mother structure
-- ============================================================

/-- A Bourbaki-style mother structure:
order data + a Galois connection + its induced closure behavior. -/
structure OrderClosureMother (α β : Type*) [PartialOrder α] [Preorder β] where
  l : α → β
  u : β → α
  gc : GaloisConnection l u

namespace OrderClosureMother

variable {α β : Type*} [PartialOrder α] [Preorder β]

def closure (M : OrderClosureMother α β) : ClosureOperator α :=
  M.gc.closureOperator

@[simp] theorem closure_apply (M : OrderClosureMother α β) (x : α) :
    M.closure x = M.u (M.l x) := rfl

theorem monotone_l (M : OrderClosureMother α β) : Monotone M.l := by
  exact M.gc.monotone_l

theorem monotone_u (M : OrderClosureMother α β) : Monotone M.u := by
  exact M.gc.monotone_u

theorem le_closure (M : OrderClosureMother α β) (x : α) : x ≤ M.closure x := by
  exact M.closure.le_closure x

theorem closure_idempotent (M : OrderClosureMother α β) (x : α) :
    M.closure (M.closure x) = M.closure x := by
  exact M.closure.idempotent' x

/-- Closed elements determine a canonical Galois insertion. -/
def giToCloseds (M : OrderClosureMother α β) :
    GaloisInsertion M.closure.toCloseds Subtype.val :=
  M.closure.gi

/-- Reconstructing closure from closed elements gives the same operator. -/
@[simp] theorem closure_from_giToCloseds (M : OrderClosureMother α β) :
    M.giToCloseds.gc.closureOperator = M.closure := by
  exact closureOperator_gi_self M.closure

end OrderClosureMother

-- ============================================================
-- §3. Quotient groups and normal subgroups
-- ============================================================

theorem quotient_mk_surjective {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] : Function.Surjective (QuotientGroup.mk' N) := by
  exact QuotientGroup.mk'_surjective N

theorem quotient_eq_one_iff_mem {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (x : G) : QuotientGroup.mk' N x = 1 ↔ x ∈ N := by
  rw [QuotientGroup.mk'_apply]
  exact QuotientGroup.eq_one_iff (N := N) x

theorem ker_is_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (f.ker).Normal := by
  infer_instance

theorem first_iso_nonempty {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ f.ker ≃* ↥f.range) := by
  exact ⟨QuotientGroup.quotientKerEquivRange f⟩

-- ============================================================
-- §4. Topological properties and homeomorphisms
-- ============================================================

theorem homeomorph_preserves_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {K : Set X} : IsCompact K ↔ IsCompact (e '' K) := by
  exact (e.isCompact_image (s := K)).symm

theorem homeomorph_preserves_connected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set X} : IsConnected s ↔ IsConnected (e '' s) := by
  exact (e.isConnected_image (s := s)).symm

theorem connected_univ_of_connectedSpace {X : Type*} [TopologicalSpace X] [ConnectedSpace X] :
    IsConnected (Set.univ : Set X) := by
  exact isConnected_univ

-- ============================================================
-- §5. Urysohn lemma (sketch)
-- ============================================================

theorem urysohn_separation {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), Set.EqOn (fun x => f x) 0 s ∧ Set.EqOn (fun x => f x) 1 t ∧
      ∀ x : X, f x ∈ Set.Icc (0 : ℝ) 1 := by
  simpa using exists_continuous_zero_one_of_isClosed hs ht hd

-- ============================================================
-- §6. Complete spaces and universal properties
-- ============================================================

theorem cauchySeq_has_limit_of_complete {α : Type*} [UniformSpace α] [CompleteSpace α]
    {u : ℕ → α} (h : CauchySeq u) : ∃ x, Filter.Tendsto u Filter.atTop (nhds x) := by
  exact cauchySeq_tendsto_of_complete h

/-- Universal arrow to binary products in `Type`. -/
def prodLift {X Y Z : Type*} (f : X → Y) (g : X → Z) : X → Y × Z :=
  fun x => (f x, g x)

theorem fst_comp_prodLift {X Y Z : Type*} (f : X → Y) (g : X → Z) :
    Prod.fst ∘ prodLift f g = f := by
  funext x
  rfl

theorem snd_comp_prodLift {X Y Z : Type*} (f : X → Y) (g : X → Z) :
    Prod.snd ∘ prodLift f g = g := by
  funext x
  rfl

theorem prodLift_unique {X Y Z : Type*} (f : X → Y) (g : X → Z)
    (h : X → Y × Z)
    (hfst : Prod.fst ∘ h = f)
    (hsnd : Prod.snd ∘ h = g) :
    h = prodLift f g := by
  funext x
  apply Prod.ext
  · have hf := congrArg (fun k => k x) hfst
    simpa [Function.comp] using hf
  · have hg := congrArg (fun k => k x) hsnd
    simpa [Function.comp] using hg

end BourbakiP1Extended
