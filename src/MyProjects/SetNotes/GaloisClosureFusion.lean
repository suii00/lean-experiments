/-
  母なる構造の融合 — ガロア接続 × 順序理論 × 閉包作用素

  Nicolas Bourbaki が提唱した三つの母なる構造（structures mères）
    ■ 代数的構造（Algebraic）
    ■ 順序構造（Order）
    ■ 位相的構造（Topological）
  に共通する **閉包系（système de fermeture）** を統一原理として抽出し、
  ガロア接続がこれら母構造間の「橋」として閉包を誘導する構図を形式化する。

  構成：
    §1  ClosureSystem — 閉包系（母なる構造の共通骨格）
    §2  StructureMère — ブルバキの三母構造の分類
    §3  GaloisClosureSystem — ガロア接続と閉包系の融合
    §4  不動点理論 — 閉元と余閉元
    §5  具体例 — σ-代数への応用
    §6  統一定理 — ガロア接続から閉包系への橋
-/

import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Lattice

open Set Function

noncomputable section

namespace StructuresMeres

-- ============================================================================
-- §1. ClosureSystem — 閉包系（母なる構造の共通骨格）
-- ============================================================================

/-! ### 閉包系

代数的構造の部分代数族、順序構造の完備束、位相的構造の閉集合系 ——
すべてが「全体は閉」かつ「任意の交叉で閉」という公理を満たす。
これは母なる構造の共通骨格である。-/

/-- 閉包系：母なる構造の根底にある共通構造。
    冪集合上の閉集合族が、全体集合を含み、任意の空でない交叉で閉じる。 -/
structure ClosureSystem (α : Type*) where
  /-- 閉集合の族 -/
  Closed : Set (Set α)
  /-- 公理1：全体は閉 -/
  closed_univ : Set.univ ∈ Closed
  /-- 公理2：空でない交叉で閉（閉包作用素の存在を保証） -/
  closed_sInter : ∀ S ⊆ Closed, S.Nonempty → ⋂₀ S ∈ Closed

namespace ClosureSystem

variable {α : Type*} (CS : ClosureSystem α)

/-- 閉包系から閉包作用素を導出する：最小の閉上集合。 -/
def closure (s : Set α) : Set α :=
  ⋂₀ { t ∈ CS.Closed | s ⊆ t }

/-- 閉包は元の集合を含む（膨張性）。 -/
theorem subset_closure (s : Set α) : s ⊆ CS.closure s := by
  intro x hx
  simp only [closure, mem_sInter]
  intro t ⟨_, hst⟩
  exact hst hx

/-- 閉包は閉である。 -/
theorem closure_mem_Closed (s : Set α) : CS.closure s ∈ CS.Closed := by
  apply CS.closed_sInter
  · intro t ht
    exact ht.1
  · exact ⟨Set.univ, ⟨CS.closed_univ, subset_univ s⟩⟩

/-- 閉包は単調である。 -/
theorem closure_mono {s t : Set α} (hst : s ⊆ t) :
    CS.closure s ⊆ CS.closure t := by
  intro x hx
  simp only [closure, mem_sInter] at *
  intro u ⟨hu_closed, hu_sup⟩
  exact hx u ⟨hu_closed, hst.trans hu_sup⟩

/-- 閉包は冪等である。 -/
theorem closure_idempotent (s : Set α) :
    CS.closure (CS.closure s) = CS.closure s := by
  apply le_antisymm
  · intro x hx
    simp only [closure, mem_sInter] at *
    intro t ht
    apply hx t
    exact ⟨ht.1, fun y hy => hy t ht⟩
  · exact CS.subset_closure (CS.closure s)

/-- 集合が閉であるとは、閉包で不動ということ。 -/
theorem closed_iff_closure_eq (s : Set α) :
    s ∈ CS.Closed ↔ CS.closure s = s := by
  constructor
  · intro hs
    apply le_antisymm
    · intro x hx
      simp only [closure, mem_sInter] at hx
      exact hx s ⟨hs, le_refl s⟩
    · exact CS.subset_closure s
  · intro heq
    rw [← heq]
    exact CS.closure_mem_Closed s

end ClosureSystem

-- ============================================================================
-- §2. StructureMère — ブルバキの三母構造の分類
-- ============================================================================

/-! ### 母なる構造

ブルバキは数学の全構造を三つの「母なる構造」に還元した：
  ■ 代数的構造 — 演算の法則（群、環、体…）
  ■ 順序構造   — 順序の法則（束、完備束…）
  ■ 位相的構造 — 近さの法則（位相空間、一様空間…）

各母構造はそれぞれ固有の閉包系を持ち、
ガロア接続を介して互いに閉包を誘導し合う。 -/

/-- ブルバキの三つの母なる構造の分類。 -/
inductive StructureKind where
  /-- 代数的構造：演算の法則 -/
  | Algebraic
  /-- 順序構造：順序の法則 -/
  | Order
  /-- 位相的構造：近さの法則 -/
  | Topological
  deriving DecidableEq, Repr

-- ============================================================================
-- §3. GaloisClosureSystem — ガロア接続と閉包系の融合
-- ============================================================================

/-! ### ガロア接続が誘導する閉包系

ガロア接続 `(l, u)` は母なる構造間の「橋」である。
合成 `u ∘ l` が α 上の閉包作用素を、
合成 `l ∘ u` が β 上の核作用素を誘導する。

この構造体は、ガロア接続を核として
閉包作用素・核作用素・閉元・余閉元を束ねる。 -/

/-- ガロア接続が誘導する閉包系統。
    母なる構造間の橋渡しを行う核構造。

    パラメータ：
    - `α` : 上側の半順序集合（閉包が作用する空間）
    - `β` : 下側の半順序集合（核が作用する空間）
    - `l` : 下側随伴（左随伴）
    - `u` : 上側随伴（右随伴）
    - `gc`: ガロア接続の証明 -/
structure GaloisClosureSystem (α β : Type*) [PartialOrder α] [PartialOrder β] where
  /-- 下側随伴（左随伴） -/
  l : α → β
  /-- 上側随伴（右随伴） -/
  u : β → α
  /-- ガロア接続の証明：l a ≤ b ↔ a ≤ u b -/
  gc : GaloisConnection l u

namespace GaloisClosureSystem

variable {α β : Type*} [PartialOrder α] [PartialOrder β]
  (gcs : GaloisClosureSystem α β)

-- ------- 閉包作用素 -------

/-- 閉包作用素 cl := u ∘ l。Mathlib の ClosureOperator として導出。 -/
def closure : ClosureOperator α := gcs.gc.closureOperator

/-- 閉包の計算：cl x = u (l x)。 -/
@[simp] theorem closure_apply (x : α) : gcs.closure x = gcs.u (gcs.l x) := rfl

/-- 膨張性：x ≤ cl x。 -/
theorem le_closure (x : α) : x ≤ gcs.closure x :=
  gcs.closure.le_closure x

/-- 単調性。 -/
theorem closure_mono : Monotone gcs.closure :=
  gcs.closure.monotone

/-- 冪等性：cl (cl x) = cl x。 -/
theorem closure_idempotent (x : α) :
    gcs.closure (gcs.closure x) = gcs.closure x :=
  gcs.closure.idempotent' x

-- ------- 随伴の基本性質 -------

/-- l は単調。 -/
theorem l_mono : Monotone gcs.l := gcs.gc.monotone_l

/-- u は単調。 -/
theorem u_mono : Monotone gcs.u := gcs.gc.monotone_u

-- ------- 核作用素 -------

/-- 核の計算：ker y := l (u y)。 -/
def kernel (y : β) : β := gcs.l (gcs.u y)

/-- 核は縮小的：ker y ≤ y。 -/
theorem kernel_le (y : β) : gcs.kernel y ≤ y :=
  gcs.gc.l_u_le y

/-- 核は単調。 -/
theorem kernel_mono : Monotone gcs.kernel := by
  intro y₁ y₂ h
  exact gcs.l_mono (gcs.u_mono h)

-- ------- l ∘ u ∘ l = l （重要な随伴恒等式） -------

/-- 随伴恒等式：l ∘ u ∘ l = l。
    この恒等式は、l の像がすべて核の不動点であることを意味する。 -/
theorem l_u_l (x : α) : gcs.l (gcs.u (gcs.l x)) = gcs.l x := by
  apply le_antisymm
  · exact gcs.gc.l_u_le (gcs.l x)
  · exact gcs.gc.monotone_l (gcs.gc.le_u_l x)

/-- 随伴恒等式：u ∘ l ∘ u = u。
    この恒等式は、u の像がすべて閉包の不動点であることを意味する。 -/
theorem u_l_u (y : β) : gcs.u (gcs.l (gcs.u y)) = gcs.u y := by
  apply le_antisymm
  · exact gcs.gc.monotone_u (gcs.gc.l_u_le y)
  · exact gcs.gc.le_u_l (gcs.u y)

end GaloisClosureSystem

-- ============================================================================
-- §4. 不動点理論 — 閉元と余閉元
-- ============================================================================

/-! ### 閉元と余閉元

ガロア接続 `(l, u)` の閉包作用素 `cl = u ∘ l` の不動点が **閉元**、
核作用素 `ker = l ∘ u` の不動点が **余閉元** である。
`l` は閉元と余閉元の間の順序同型を誘導する。 -/

namespace GaloisClosureSystem

variable {α β : Type*} [PartialOrder α] [PartialOrder β]
  (gcs : GaloisClosureSystem α β)

/-- 閉元：閉包で不動な元（u (l x) = x を満たす元）。 -/
def ClosedElements : Set α :=
  { x | gcs.u (gcs.l x) = x }

/-- 余閉元：核で不動な元（l (u y) = y を満たす元）。 -/
def CoclosedElements : Set β :=
  { y | gcs.l (gcs.u y) = y }

/-- u の像はすべて閉元。 -/
theorem u_mem_closed (y : β) : gcs.u y ∈ gcs.ClosedElements := by
  simp only [ClosedElements, mem_setOf_eq]
  exact gcs.u_l_u y

/-- l の像はすべて余閉元。 -/
theorem l_mem_coclosed (x : α) : gcs.l x ∈ gcs.CoclosedElements := by
  simp only [CoclosedElements, mem_setOf_eq]
  exact gcs.l_u_l x

/-- 閉元 x に対し、u (l x) = x がそのまま成り立つ。 -/
theorem closed_iff (x : α) :
    x ∈ gcs.ClosedElements ↔ gcs.u (gcs.l x) = x := by
  simp [ClosedElements]

/-- 余閉元 y に対し、l (u y) = y がそのまま成り立つ。 -/
theorem coclosed_iff (y : β) :
    y ∈ gcs.CoclosedElements ↔ gcs.l (gcs.u y) = y := by
  simp [CoclosedElements]

/-- 閉元は u の像と一致。 -/
theorem closedElements_eq_range_u :
    gcs.ClosedElements = Set.range gcs.u := by
  ext x
  simp only [ClosedElements, mem_setOf_eq, mem_range]
  constructor
  · intro hx
    exact ⟨gcs.l x, hx⟩
  · intro ⟨y, hy⟩
    rw [← hy]
    exact gcs.u_l_u y

/-- 余閉元は l の像と一致。 -/
theorem coclosedElements_eq_range_l :
    gcs.CoclosedElements = Set.range gcs.l := by
  ext y
  simp only [CoclosedElements, mem_setOf_eq, mem_range]
  constructor
  · intro hy
    exact ⟨gcs.u y, hy⟩
  · intro ⟨x, hx⟩
    rw [← hx]
    exact gcs.l_u_l x

end GaloisClosureSystem

-- ============================================================================
-- §5. 具体例 — σ-代数への応用（母なる構造の結節点）
-- ============================================================================

/-! ### σ-代数 — 三母構造が一点に会する結節点

σ-代数は三母構造の交差点である：
  ■ 代数的：Bool代数としての構造（∩, ∪, ᶜ の演算）
  ■ 順序的：包含関係で完備束（σ-代数の束）
  ■ 位相的：Borel σ-代数 = 位相から生成

Mathlib の `MeasurableSpace.giGenerateFrom` は
  `generateFrom : Set (Set α) → MeasurableSpace α` と
  `u m := {s | MeasurableSet[m] s}`
のガロア挿入を与える。これは GaloisClosureSystem のインスタンスである。 -/

/-- σ-代数の母なる構造：集合族から可測空間を生成するガロア接続。
    generateFrom ⊣ measurableSetOf として
    GaloisClosureSystem のインスタンスを構成する。 -/
def sigmaMere (α : Type*) :
    GaloisClosureSystem (Set (Set α)) (MeasurableSpace α) where
  l := MeasurableSpace.generateFrom
  u := fun m => {s | @MeasurableSet α m s}
  gc := MeasurableSpace.giGenerateFrom.gc

namespace SigmaMereExamples

variable {α : Type*}

/-- σ-代数の閉包：集合族 S に対し、σ(S) の可測集合族を返す。 -/
@[simp] theorem sigma_closure_apply (s : Set (Set α)) :
    (sigmaMere α).closure s =
      {t | @MeasurableSet α (MeasurableSpace.generateFrom s) t} := rfl

/-- 任意の集合族は、それが生成する σ-代数に含まれる。 -/
theorem subset_sigma_closure (s : Set (Set α)) :
    s ⊆ (sigmaMere α).closure s :=
  (sigmaMere α).le_closure s

/-- σ-代数の閉包は冪等。 -/
theorem sigma_closure_idempotent (s : Set (Set α)) :
    (sigmaMere α).closure ((sigmaMere α).closure s) =
      (sigmaMere α).closure s :=
  (sigmaMere α).closure_idempotent s

/-- 可測空間はすべて閉元（σ-代数として不動点）。 -/
theorem measurableSpace_is_closed (m : MeasurableSpace α) :
    (sigmaMere α).u m ∈ (sigmaMere α).ClosedElements :=
  (sigmaMere α).u_mem_closed m

end SigmaMereExamples

/-! ### 統一定理

ガロア接続は ClosureSystem を誘導する。
すなわち、`Set α` 上のガロア接続から
`α` の冪集合上の閉包系を自然に構成できる。
これが母なる構造の統一原理である：
どの母構造間のガロア接続も、閉包系という共通の骨格を生む。 -/

/-- ガロア接続から直接 ClosureSystem を構成する。

    `Set α` 上のガロア接続において、
    閉元の族（閉包で不動な部分集合）は閉包系の公理を満たす。

    ここで `GaloisClosureSystem (Set α) β` の `ClosedElements` は
    `Set (Set α)` 型であり、`ClosureSystem α` の `Closed` と一致する。 -/
def GaloisClosureSystem.toClosureSystem
    {α β : Type*} [PartialOrder β]
    (gcs : GaloisClosureSystem (Set α) β) :
    ClosureSystem α where
  Closed := gcs.ClosedElements
  closed_univ := by
    simp only [GaloisClosureSystem.ClosedElements, mem_setOf_eq]
    apply le_antisymm
    · exact subset_univ _
    · exact gcs.le_closure Set.univ
  closed_sInter := by
    intro S hS hSne
    simp only [GaloisClosureSystem.ClosedElements, mem_setOf_eq] at *
    apply le_antisymm
    · intro x hx
      simp only [mem_sInter] at *
      intro t ht
      have ht_closed := hS ht
      rw [← ht_closed]
      exact gcs.closure_mono (sInter_subset_of_mem ht) hx
    · exact gcs.le_closure (⋂₀ S)

end StructuresMeres
