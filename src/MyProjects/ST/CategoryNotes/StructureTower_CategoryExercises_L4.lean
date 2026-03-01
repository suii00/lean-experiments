/-
  StructureTower 発展演習（レベル4）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  難易度: レベル4（発展）
  前提: Level 1-3（圏の公理・構造・閉包モナド）+ 接地（Grounding）を完了していること

  動機:
    L3 + 接地で、ClosureOperator を核とした閉包モナドの理論が完成し、
    位相的閉包（topClosure）と部分群生成（subgroupClosure）の2分野で接地した。

    Level 4 では以下の4方向に発展させる:

    1. **cl-parametric な構造比較**:
       異なる閉包演算子を「同じ塔に適用」した場合の比較。
       cl₁ ≤ cl₂ が ClosedTower の包含を誘導する仕組み。

    2. **σ-代数への第3の接地**:
       MeasurableSpace / MeasurableSet を ClosureOperator に接続し、
       「3分野統合」を完成させる。

    3. **Rank uniqueness**:
       ExhaustiveTower における rank 関数の一意性定理（Theorem B）。
       PartialOrder での一意性と、前順序での非一意性の対比。

    4. **ClosedTower の圏**:
       ClosedTower 間の射が StructureTower 射の制限であること、
       unit : T → liftCl cl T が reflector であること。

  学習の流れ:
    §L4-1. cl-parametric 比較     — 閉包の強弱が塔に誘導する構造
    §L4-2. σ-代数の接地           — 可測集合による第3のケーススタディ
    §L4-3. Rank uniqueness        — 網羅的塔における rank の一意性
    §L4-4. ClosedTower の圏       — reflective subcategory への道

  ヒントの読み方:
    Hint-1: 大まかな方針
    Hint-2: 使うべき補題やタクティク
    Hint-3: ほぼ答え
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Nat.Find

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definitions（自己完結のため再掲）
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β γ : Type*} [Preorder ι]

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

def global (T : StructureTower ι α) : Set α := ⋂ i, T.level i

structure Hom (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  toFun : α → β
  preserves : ∀ i, MapsTo toFun (T₁.level i) (T₂.level i)

instance (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    CoeFun (Hom T₁ T₂) (fun _ => α → β) where
  coe f := f.toFun

theorem Hom.ext {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {f g : Hom T₁ T₂} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; simp

def Hom.id (T : StructureTower ι α) : Hom T T where
  toFun := _root_.id
  preserves := by intro i x hx; exact hx

def Hom.comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) : Hom T₁ T₃ where
  toFun := g.toFun ∘ f.toFun
  preserves := by intro i x hx; exact g.preserves i (f.preserves i hx)

-- L3 からの定義: liftCl, unit, join, ClosedTower

variable (cl : ClosureOperator (Set α))

def liftCl (T : StructureTower ι α) : StructureTower ι α where
  level i := cl (T.level i)
  monotone_level := by
    intro i j hij x hx
    exact cl.monotone (T.monotone_level hij) hx

@[simp] theorem liftCl_level (T : StructureTower ι α) (i : ι) :
    (liftCl cl T).level i = cl (T.level i) := rfl

def unit (T : StructureTower ι α) :
    Hom T (liftCl cl T) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    exact cl.le_closure (T.level i) hx

def liftCl_mapId (T₁ T₂ : StructureTower ι α)
    (h : ∀ i, T₁.level i ⊆ T₂.level i) :
    Hom (liftCl cl T₁) (liftCl cl T₂) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    exact cl.monotone (h i) hx

def join (T : StructureTower ι α) :
    Hom (liftCl cl (liftCl cl T)) (liftCl cl T) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    simpa [cl.idempotent] using hx

structure ClosedTower (cl : ClosureOperator (Set α)) (ι : Type*) [Preorder ι]
    extends StructureTower ι α where
  level_closed : ∀ i, cl (level i) = level i

namespace ClosedTower

variable {cl : ClosureOperator (Set α)}

theorem liftCl_eq_self (T : ClosedTower cl ι) :
    liftCl cl T.toStructureTower = T.toStructureTower := by
  ext i x; simp [liftCl, T.level_closed i]

def ofFixed (T : StructureTower ι α)
    (h : liftCl cl T = T) : ClosedTower cl ι where
  toStructureTower := T
  level_closed := by
    intro i
    exact congr_fun (congr_arg StructureTower.level h) i

def algebra (T : ClosedTower cl ι) :
    Hom (liftCl cl T.toStructureTower) T.toStructureTower where
  toFun := _root_.id
  preserves := by
    intro i x hx; simpa [liftCl, T.level_closed i] using hx

theorem algebra_unit (T : ClosedTower cl ι) :
    Hom.comp (algebra T) (unit cl T.toStructureTower) =
    Hom.id T.toStructureTower := Hom.ext rfl

def ofAlgebra (T : StructureTower ι α)
    (a : Hom (liftCl cl T) T)
    (ha_id : a.toFun = _root_.id)
    (_ha_unit : Hom.comp a (unit cl T) = Hom.id T) :
    ClosedTower cl ι where
  toStructureTower := T
  level_closed := by
    intro i
    apply Set.Subset.antisymm
    · intro x hx
      have hx' := a.preserves i hx
      simpa [ha_id] using hx'
    · intro x hx
      exact cl.le_closure (T.level i) hx

theorem cl_global_subset (T : ClosedTower cl ι) :
    cl T.global ⊆ T.global := by
  intro x hx
  apply Set.mem_iInter.mpr
  intro i
  have h1 : cl T.global ⊆ cl (T.level i) :=
    cl.monotone (fun y hy => Set.mem_iInter.mp hy i)
  exact T.level_closed i ▸ (h1 hx)

end ClosedTower

-- 接地からの定義（再掲）

section TopologyDefs
variable {α : Type*} [TopologicalSpace α]

noncomputable def topClosure : ClosureOperator (Set α) where
  toFun := _root_.closure
  monotone' := fun _S _T h => closure_mono h
  le_closure' := fun _S => subset_closure
  idempotent' := fun _S => isClosed_closure.closure_eq

theorem isClosed_iff_topClosure_fixed (S : Set α) :
    IsClosed S ↔ topClosure S = S := by
  constructor
  · intro h; change _root_.closure S = S; exact h.closure_eq
  · intro h; change _root_.closure S = S at h
    exact (closure_eq_iff_isClosed (s := S)).1 h

end TopologyDefs

section SubgroupDefs
variable {G : Type*} [Group G]

def subgroupClosure : ClosureOperator (Set G) where
  toFun := fun S => ↑(Subgroup.closure S)
  monotone' := by
    intro S T h
    exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono h)
  le_closure' := by intro S; exact Subgroup.subset_closure
  idempotent' := by
    intro S
    exact congr_arg SetLike.coe (Subgroup.closure_eq (Subgroup.closure S))

theorem isSubgroupCarrier_iff_fixed (S : Set G) :
    (∃ H : Subgroup G, (H : Set G) = S) ↔ subgroupClosure S = S := by
  constructor
  · rintro ⟨H, rfl⟩
    change ↑(Subgroup.closure (↑H : Set G)) = (↑H : Set G)
    exact congr_arg SetLike.coe (Subgroup.closure_eq H)
  · intro h
    refine ⟨Subgroup.closure S, ?_⟩
    change (↑(Subgroup.closure S) : Set G) = S at h
    exact h

end SubgroupDefs

-- ExhaustiveTower（EscapeExercises から再掲）

structure ExhaustiveTower (ι α : Type*) [Preorder ι]
    extends StructureTower ι α where
  exhaustive : ∀ x : α, ∃ i : ι, x ∈ level i

namespace ExhaustiveTower

variable {α : Type*}

noncomputable def rank (T : ExhaustiveTower ℕ α) (x : α) : ℕ := by
  classical
  exact Nat.find (T.exhaustive x)

theorem rank_spec (T : ExhaustiveTower ℕ α) (x : α) :
    x ∈ T.level (T.rank x) := by
  classical
  simpa [rank] using Nat.find_spec (T.exhaustive x)

theorem rank_le (T : ExhaustiveTower ℕ α) (x : α)
    (n : ℕ) (h : x ∈ T.level n) :
    T.rank x ≤ n := by
  classical
  simpa [rank] using Nat.find_min' (T.exhaustive x) h

end ExhaustiveTower

-- ════════════════════════════════════════════════════════════
-- §L4-1. cl-parametric な構造比較  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  異なる ClosureOperator cl₁, cl₂ を「同じ塔 T に適用」するとき、
  cl₁ ≤ cl₂（すなわち ∀ S, cl₁ S ⊆ cl₂ S）ならば
  liftCl cl₁ T → liftCl cl₂ T の自然な射が存在する。

  さらに cl₁-ClosedTower ⊇ cl₂-ClosedTower（強い閉包の不動点は少ない）
  となる。閉包演算子の順序が塔の圏に誘導する構造を調べる。
-/

section ClParametric

variable {α : Type*}

/-- 閉包演算子の順序: cl₁ ≤ cl₂ ↔ ∀ S, cl₁ S ⊆ cl₂ S。 -/
def ClLeq (cl₁ cl₂ : ClosureOperator (Set α)) : Prop :=
  ∀ S : Set α, cl₁ S ⊆ cl₂ S

/-- 🟡 Exercise L4-1a: cl₁ ≤ cl₂ が liftCl の間の自然な射を誘導する。
    各レベルで cl₁(T.level i) ⊆ cl₂(T.level i) なので、
    toFun = id の Hom が得られる。

    Hint-1: toFun = id。preserves は hle (T.level i)。
    Hint-2: `intro i x hx; exact hle (T.level i) hx`
    Hint-3: そのまま。 -/
def liftCl_comparison {cl₁ cl₂ : ClosureOperator (Set α)}
    (hle : ClLeq cl₁ cl₂)
    (T : StructureTower ι α) :
    Hom (liftCl cl₁ T) (liftCl cl₂ T) where
  toFun := _root_.id
  preserves := by
    sorry
    /- skeleton:
       intro i x hx
       exact hle (T.level i) hx -/

/-- 🟡 Exercise L4-1b: 射の合成は推移的。
    cl₁ ≤ cl₂ ≤ cl₃ のとき、comparison の合成 = 直接の comparison。

    Hint-1: 両辺 toFun = id ∘ id = id。
    Hint-2: `Hom.ext rfl`
    Hint-3: そのまま。 -/
theorem liftCl_comparison_trans {cl₁ cl₂ cl₃ : ClosureOperator (Set α)}
    (h₁₂ : ClLeq cl₁ cl₂) (h₂₃ : ClLeq cl₂ cl₃)
    (T : StructureTower ι α) :
    Hom.comp (liftCl_comparison h₂₃ T) (liftCl_comparison h₁₂ T) =
    liftCl_comparison (fun S => Subset.trans (h₁₂ S) (h₂₃ S)) T := by
  sorry
  /- skeleton: exact Hom.ext rfl -/

/-- 🔴 Exercise L4-1c: cl₂-ClosedTower は cl₁-ClosedTower（cl₁ ≤ cl₂ のとき）。
    cl₂ S = S ならば cl₁ S ⊆ cl₂ S = S、かつ S ⊆ cl₁ S（拡大性）
    より cl₁ S = S。

    つまり「強い閉包の不動点は弱い閉包の不動点でもある」。

    Hint-1: level_closed i は cl₁(T.level i) = T.level i を示す。
    Hint-2: Set.Subset.antisymm で挟む:
            cl₁ S ⊆ cl₂ S = S（hle + T.level_closed）と S ⊆ cl₁ S（拡大性）。
    Hint-3: `Subset.antisymm (by rw [← T.level_closed i]; exact hle _)
                              (cl₁.le_closure _)` -/
def ClosedTower.weaken {cl₁ cl₂ : ClosureOperator (Set α)}
    (hle : ClLeq cl₁ cl₂)
    (T : ClosedTower cl₂ ι) :
    ClosedTower cl₁ ι where
  toStructureTower := T.toStructureTower
  level_closed := by
    sorry
    /- skeleton:
       intro i
       apply Set.Subset.antisymm
       · -- cl₁(level i) ⊆ cl₂(level i) = level i
         calc cl₁ (T.level i) ⊆ cl₂ (T.level i) := hle (T.level i)
           _ = T.level i := T.level_closed i
       · -- level i ⊆ cl₁(level i) by extensivity
         exact cl₁.le_closure (T.level i) -/

/-- 🔴 Exercise L4-1d: liftCl の合成。
    liftCl cl₂ (liftCl cl₁ T) の各レベルは cl₂(cl₁(T.level i))。
    cl₁ が cl₂ に吸収される（cl₂ ∘ cl₁ = cl₂）条件下で
    liftCl cl₂ (liftCl cl₁ T) = liftCl cl₂ T。

    Hint-1: 塔の ext で各レベルを比較。
    Hint-2: 仮定 habsorb i : cl₂ (cl₁ (T.level i)) = cl₂ (T.level i)。
    Hint-3: `ext i x; simp [liftCl]; rw [habsorb]` -/
theorem liftCl_absorb {cl₁ cl₂ : ClosureOperator (Set α)}
    (habsorb : ∀ S : Set α, cl₂ (cl₁ S) = cl₂ S)
    (T : StructureTower ι α) :
    liftCl cl₂ (liftCl cl₁ T) = liftCl cl₂ T := by
  sorry
  /- skeleton:
     ext i x
     simp [liftCl]
     rw [habsorb] -/

/-- 🔴 Exercise L4-1e: 冪等閉包は自身に吸収される。
    cl (cl S) = cl S（冪等性）より、liftCl cl (liftCl cl T) = liftCl cl T。
    これは L3 の join が同型であることの別表現。

    Hint-1: liftCl_absorb を cl₁ = cl₂ = cl で適用。
    Hint-2: habsorb は cl.idempotent。
    Hint-3: `liftCl_absorb (fun S => cl.idempotent S) T` -/
theorem liftCl_idempotent (cl : ClosureOperator (Set α))
    (T : StructureTower ι α) :
    liftCl cl (liftCl cl T) = liftCl cl T := by
  sorry
  /- skeleton: exact liftCl_absorb (fun S => cl.idempotent S) T -/

end ClParametric

-- ════════════════════════════════════════════════════════════
-- §L4-2. σ-代数への第3の接地  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  MeasurableSpace α が与えられたとき、
  「生成 σ-代数」は ClosureOperator (Set α) のように振る舞う。

  ただし、Mathlib の MeasurableSet は集合 S に対する命題
  （MeasurableSet S : Prop）であり、
  Set α → Set α 型の閉包演算子として直接的には表現されない。

  ここでは「可測集合の不動点条件」を直接的に扱う方法を取る:
  MeasurableSet S ↔ cl_meas S = S
  という形の ClosureOperator を外側から構成するのではなく、
  ClosedTower の条件を MeasurableSet で直接記述する。

  これにより、topClosure / subgroupClosure と **並列的に**
  「可測集合の塔」を ClosedTower の枠組みで捉えられることを確認する。
-/

section MeasurableSection

variable {α : Type*} [MeasurableSpace α]

/-- 可測集合の塔: 各レベルが可測集合である StructureTower。
    topClosure / subgroupClosure と並列の構造。

    注意: ClosureOperator (Set α) を経由せず、
    MeasurableSet を直接条件に使う。これは
    Mathlib の MeasurableSet API が closure 形式でないため。 -/
structure MeasurableTower (ι : Type*) [Preorder ι]
    extends StructureTower ι α where
  level_measurable : ∀ i, MeasurableSet (level i)

namespace MeasurableTower

variable {ι : Type*} [Preorder ι]

/-- 🟢 Exercise L4-2a: 定数可測塔。
    可測集合 S をすべてのレベルに配置した塔は MeasurableTower。

    Hint-1: level _ := S, monotone は自明。
    Hint-2: level_measurable は仮定 h そのもの。
    Hint-3: 構造体リテラルで直接構成。 -/
def const (S : Set α) (h : MeasurableSet S) :
    MeasurableTower (α := α) ι where
  level := fun _ => S
  monotone_level := sorry
  level_measurable := sorry
  /- skeleton:
     level := fun _ => S
     monotone_level := fun _i _j _hij => Subset.rfl
     level_measurable := fun _i => h -/

/-- 🟢 Exercise L4-2b: univ と ∅ の塔。

    Hint-1: MeasurableSet.univ / MeasurableSet.empty。
    Hint-2: const を使う。
    Hint-3: `const Set.univ MeasurableSet.univ` -/
def univTower : MeasurableTower (α := α) ι :=
  sorry
  /- skeleton: const Set.univ MeasurableSet.univ -/

def emptyTower : MeasurableTower (α := α) ι :=
  sorry
  /- skeleton: const ∅ MeasurableSet.empty -/

/-- 🟡 Exercise L4-2c: 可測塔の交叉は可測。
    各レベルで T₁.level i ∩ T₂.level i が可測。

    Hint-1: MeasurableSet.inter を使う。
    Hint-2: `T₁.level_measurable i |>.inter (T₂.level_measurable i)`
    Hint-3: monotone は両方の monotone の And。 -/
def inter (T₁ T₂ : MeasurableTower (α := α) ι) :
    MeasurableTower (α := α) ι where
  level i := T₁.level i ∩ T₂.level i
  monotone_level := by
    sorry
    /- skeleton:
       intro i j hij x hx
       exact ⟨T₁.monotone_level hij hx.1, T₂.monotone_level hij hx.2⟩ -/
  level_measurable := by
    sorry
    /- skeleton:
       intro i
       exact (T₁.level_measurable i).inter (T₂.level_measurable i) -/

/-- 🟡 Exercise L4-2d: 可測塔の補集合。
    各レベルで (T.level i)ᶜ が可測。
    ただし、これは **反単調** な族になるので StructureTower にはならない。
    代わりに、補集合の可測性だけを定理として述べる。

    Hint-1: MeasurableSet.compl を使う。
    Hint-2: `(T.level_measurable i).compl`
    Hint-3: そのまま。 -/
theorem level_compl_measurable (T : MeasurableTower (α := α) ι) (i : ι) :
    MeasurableSet (T.level i)ᶜ := by
  sorry
  /- skeleton: exact (T.level_measurable i).compl -/

/-- 🔴 Exercise L4-2e: 可測塔の global は可測集合。
    global = ⋂ᵢ T.level i。可測集合の可算交叉が可測であるためには
    添字が可算（Countable ι）であることが必要。

    Hint-1: MeasurableSet.iInter を使う（Countable ι が必要）。
    Hint-2: `MeasurableSet.iInter (fun i => T.level_measurable i)`
    Hint-3: そのまま。 -/
theorem global_measurable [Countable ι]
    (T : MeasurableTower (α := α) ι) :
    MeasurableSet T.global := by
  sorry
  /- skeleton:
     change MeasurableSet (⋂ i, T.level i)
     exact MeasurableSet.iInter (fun i => T.level_measurable i) -/

end MeasurableTower

/-- 🔴 Exercise L4-2f: 3分野統合の確認。
    位相・代数・可測の3分野で、以下の共通パターンが成立:
      「各レベルが P であれば、global も P である」
    ここでは P = MeasurableSet 版を、上の global_measurable で確認済み。

    位相版（closedTower_global_isClosed）と代数版（closedTower_global_isSubgroup）
    と合わせて、StructureTower が3分野を統一するインターフェースであることを
    明示的に述べる。

    この演習は statement のみ。証明は global_measurable の直接的適用。

    Hint-1: global_measurable を適用。
    Hint-2: そのまま。
    Hint-3: `T.global_measurable` -/
theorem MeasurableTower.global_measurable_synthesis
    [Countable ι] (T : MeasurableTower (α := α) ι) :
    MeasurableSet T.global := by
  sorry
  /- skeleton: exact T.global_measurable -/

end MeasurableSection

-- ════════════════════════════════════════════════════════════
-- §L4-3. Rank uniqueness  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  ExhaustiveTower ℕ α における rank 関数 r : α → ℕ の一意性。

  rank(x) = min {i | x ∈ level i} は常に存在する（Nat.find）。
  問い: 「level i = {x | r(x) ≤ i} を満たす r は rank に一致するか？」

  これが Theorem B（rank uniqueness）:
    ∀ x i, x ∈ level i ↔ r(x) ≤ i  ⟹  r = rank

  この定理は PartialOrder（ℕ）で成立するが、
  一般の前順序では非一意になりうる。
-/

section RankUniqueness

variable {α : Type*}

/-- 強い単射公理: rank 関数 r が塔を完全に特徴づける条件。
    x ∈ level i ↔ r(x) ≤ i。 -/
def HasCharRank (T : ExhaustiveTower ℕ α) (r : α → ℕ) : Prop :=
  ∀ x i, x ∈ T.level i ↔ r x ≤ i

/-- 🟡 Exercise L4-3a: rank 関数は常に HasCharRank を「半分」満たす。
    x ∈ level i ⟹ rank(x) ≤ i（rank の最小性）。

    Hint-1: これは rank_le そのもの。
    Hint-2: `T.rank_le x i h`
    Hint-3: そのまま。 -/
theorem rank_le_of_mem (T : ExhaustiveTower ℕ α) (x : α) (i : ℕ)
    (h : x ∈ T.level i) :
    T.rank x ≤ i := by
  sorry
  /- skeleton: exact T.rank_le x i h -/

/-- 🟡 Exercise L4-3b: 逆方向: rank(x) ≤ i ⟹ x ∈ level i。
    rank(x) のレベルに x が属し（rank_spec）、単調性で上に運ぶ。

    Hint-1: T.rank_spec x で x ∈ level(rank x)。
    Hint-2: T.monotone_level h で rank x ≤ i → level(rank x) ⊆ level i。
    Hint-3: `T.monotone_level h (T.rank_spec x)` -/
theorem mem_of_rank_le (T : ExhaustiveTower ℕ α) (x : α) (i : ℕ)
    (h : T.rank x ≤ i) :
    x ∈ T.level i := by
  sorry
  /- skeleton: exact T.monotone_level h (T.rank_spec x) -/

/-- 🟡 Exercise L4-3c: rank は HasCharRank を満たす。
    上の2つを合わせる。

    Hint-1: Iff.intro で両方向。
    Hint-2: `⟨rank_le_of_mem T x i, mem_of_rank_le T x i⟩`
    Hint-3: そのまま。 -/
theorem rank_hasCharRank (T : ExhaustiveTower ℕ α) :
    HasCharRank T T.rank := by
  sorry
  /- skeleton:
     intro x i
     exact ⟨rank_le_of_mem T x i, mem_of_rank_le T x i⟩ -/

/-- 🔴 Exercise L4-3d: Rank uniqueness（主定理 B）。
    HasCharRank T r ⟹ r = T.rank。

    証明: 任意の x に対して
      r(x) ≤ rank(x) : hchar x (rank x) の → 方向に rank_spec を適用
      rank(x) ≤ r(x) : rank_le に hchar x (r x) の ← 方向を適用

    Hint-1: funext x; apply Nat.le_antisymm。
    Hint-2: 一方向は `(hchar x (T.rank x)).1 (T.rank_spec x)`。
    Hint-3: 他方向は `T.rank_le x (r x) ((hchar x (r x)).2 (le_refl _))`。 -/
theorem rank_unique (T : ExhaustiveTower ℕ α)
    (r : α → ℕ) (hchar : HasCharRank T r) :
    r = T.rank := by
  sorry
  /- skeleton:
     funext x
     apply Nat.le_antisymm
     · -- r x ≤ rank x
       exact (hchar x (T.rank x)).1 (T.rank_spec x)
     · -- rank x ≤ r x
       exact T.rank_le x (r x) ((hchar x (r x)).2 (le_refl _)) -/

/-- 🔴 Exercise L4-3e: HasCharRank を持つ塔は Iic-塔と同型。
    level i = {x | r(x) ≤ i} であることを示す。

    Hint-1: ext x; exact hchar x i。
    Hint-2: Set.ext で集合の外延性。
    Hint-3: `ext x; exact hchar x i` -/
theorem level_eq_of_hasCharRank (T : ExhaustiveTower ℕ α)
    (r : α → ℕ) (hchar : HasCharRank T r) (i : ℕ) :
    T.level i = {x | r x ≤ i} := by
  sorry
  /- skeleton:
     ext x
     exact hchar x i -/

/-- 🔴 Exercise L4-3f: 反例構成: 前順序での rank 関数の非一意性。
    添字に同値な元（i ≤ j かつ j ≤ i だが i ≠ j）がある場合、
    level i = level j であっても、r(x) = i と r(x) = j の両方が
    HasCharRank を満たしうる。

    ここでは具体的な反例として、ι = Bool（false ≤ true ∧ true ≤ false）
    を使い、定数塔に対して2つの異なる rank 関数を構成する。

    Hint-1: Bool に「false ≤ true かつ true ≤ false」の前順序を定義。
    Hint-2: 定数塔 level _ := univ に対して、r₁ _ = false, r₂ _ = true。
    Hint-3: 両方が HasCharRank を満たすが r₁ ≠ r₂。 -/
-- この演習は statement が複雑なので、以下のコメントで方針を示す。
-- 実装は読者への課題とする。
/-
  反例の骨格:

  instance : Preorder Bool where
    le := fun _ _ => True
    le_refl := fun _ => trivial
    le_trans := fun _ _ _ _ _ => trivial

  def constExhaustiveTower : ExhaustiveTower Bool α where
    level _ := Set.univ
    monotone_level := fun _ _ _ => Subset.refl _
    exhaustive := fun x => ⟨false, trivial⟩

  -- r₁ _ := false と r₂ _ := true は両方とも HasCharRank を満たす
  -- （le が常に True なので、x ∈ level i ↔ r x ≤ i は常に True ↔ True）
  -- しかし r₁ ≠ r₂。

  これは PartialOrder では起こり得ない（le_antisymm により i = j が帰結）。
-/

end RankUniqueness

-- ════════════════════════════════════════════════════════════
-- §L4-4. ClosedTower の圏  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  ClosedTower cl は StructureTower の「充満部分圏」をなす。
  すなわち:
    - 対象: ClosedTower cl ι（全レベルが cl-不動点である塔）
    - 射:   StructureTower.Hom を制限（追加条件なし）

  さらに unit : T → liftCl cl T は StructureTower の圏から
  ClosedTower の圏への「反射」を与える。
  liftCl cl T は ClosedTower であり（冪等性による）、
  unit が ClosedTower 値の射を「持ち上げる」普遍性を持つ。
-/

section ClosedTowerCategory

variable {α : Type*} (cl : ClosureOperator (Set α))

/-- 🟡 Exercise L4-4a: liftCl cl T は ClosedTower。
    冪等性 cl(cl(S)) = cl(S) より、liftCl cl T の各レベルは cl-不動点。

    Hint-1: level_closed i は cl(cl(T.level i)) = cl(T.level i)。
    Hint-2: cl.idempotent。
    Hint-3: `fun i => cl.idempotent (T.level i)` -/
def liftCl_closedTower (T : StructureTower ι α) :
    ClosedTower cl ι where
  toStructureTower := liftCl cl T
  level_closed := by
    sorry
    /- skeleton:
       intro i
       exact cl.idempotent (T.level i) -/

/-- 🟡 Exercise L4-4b: ClosedTower 間の Hom は追加条件なし。
    T₁, T₂ が ClosedTower のとき、
    StructureTower.Hom T₁ T₂ がそのまま「ClosedTower 間の射」になる。
    （充満部分圏であることの確認。）

    f : Hom T₁.toStructureTower T₂.toStructureTower が与えられれば
    ClosedTower の構造を一切使わずに射が成立する。

    Hint-1: 型変換のみ。f をそのまま返す。
    Hint-2: `f`
    Hint-3: そのまま。 -/
def ClosedTower.homRestrict {cl : ClosureOperator (Set α)}
    (T₁ T₂ : ClosedTower cl ι)
    (f : Hom T₁.toStructureTower T₂.toStructureTower) :
    Hom T₁.toStructureTower T₂.toStructureTower :=
  sorry
  /- skeleton: f -/

/-- 🔴 Exercise L4-4c: unit の普遍性（reflector）。
    任意の Hom f : T → S.toStructureTower（S が ClosedTower）に対して、
    一意な ClosedTower の射 f̄ : liftCl cl T → S.toStructureTower であって
    f = f̄ ∘ unit を満たすものが存在する。

    toFun = id のケースに限定:
    f.toFun = id のとき、f̄.toFun = id で、
    preserves は cl.monotone (f.preserves i) と S.level_closed で導かれる。

    Hint-1: f̄ の preserves: x ∈ cl(T.level i)
            → cl.monotone (f.preserves i) で x ∈ cl(S.level i)
            → S.level_closed i で x ∈ S.level i。
    Hint-2: f = f̄ ∘ unit は toFun が id 同士なので Hom.ext rfl。
    Hint-3: 下の skeleton を完成。 -/
theorem unit_universal_id {cl : ClosureOperator (Set α)}
    (T : StructureTower ι α) (S : ClosedTower cl ι)
    (f : Hom T S.toStructureTower)
    (hf : f.toFun = _root_.id) :
    ∃ (f̄ : Hom (liftCl cl T) S.toStructureTower),
      f̄.toFun = _root_.id ∧
      Hom.comp f̄ (unit cl T) = f := by
  sorry
  /- skeleton:
     refine ⟨⟨_root_.id, fun i x hx => ?_⟩, rfl, Hom.ext ?_⟩
     · -- preserves: x ∈ cl(T.level i) → x ∈ S.level i
       have h1 : cl (T.level i) ⊆ cl (S.level i) := by
         apply cl.monotone
         intro y hy
         have := f.preserves i hy
         simpa [hf] using this
       rw [S.level_closed i] at h1
       exact h1 hx
     · -- f̄ ∘ unit = f  (toFun = id ∘ id = id = f.toFun)
       exact hf.symm -/

/-- 🔴 Exercise L4-4d: reflector の一意性。
    toFun = id の ClosedTower 射 f̄ : liftCl cl T → S.toStructureTower であって
    f̄ ∘ unit = f を満たすものは一意。

    Hint-1: toFun = id なので Hom.ext で f̄₁ = f̄₂。
    Hint-2: `Hom.ext (by rw [hf̄₁, hf̄₂])`
    Hint-3: そのまま。 -/
theorem unit_universal_unique {cl : ClosureOperator (Set α)}
    (T : StructureTower ι α) (S : ClosedTower cl ι)
    (f : Hom T S.toStructureTower)
    (f̄₁ f̄₂ : Hom (liftCl cl T) S.toStructureTower)
    (hf̄₁ : f̄₁.toFun = _root_.id) (hf̄₂ : f̄₂.toFun = _root_.id)
    (_hcomp₁ : Hom.comp f̄₁ (unit cl T) = f)
    (_hcomp₂ : Hom.comp f̄₂ (unit cl T) = f) :
    f̄₁ = f̄₂ := by
  sorry
  /- skeleton:
     exact Hom.ext (by rw [hf̄₁, hf̄₂]) -/

end ClosedTowerCategory

-- ════════════════════════════════════════════════════════════
-- §Summary. Level 4 の全体像
-- ════════════════════════════════════════════════════════════

/-!
  Level 4 で確認したこと:

  §L4-1 **cl-parametric 比較**:
    cl₁ ≤ cl₂ が liftCl の間の自然な射を誘導する。
    推移性、弱化（ClosedTower の包含関係）、吸収条件を確認。
    冪等性は liftCl_absorb の特殊ケースとして再発見。

  §L4-2 **σ-代数の接地**:
    MeasurableTower を ClosureOperator を経由せずに直接定義。
    可測集合の交叉・補集合の可測性、global の可測性を確認。
    位相・代数・可測の3分野で「global の閉性定理」が成立。

  §L4-3 **Rank uniqueness (Theorem B)**:
    HasCharRank T r ⟹ r = T.rank。
    rank は常に HasCharRank を満たし、かつ一意。
    前順序では一意性が崩れる（反例: Bool 上の定数塔）。

  §L4-4 **ClosedTower の圏**:
    liftCl cl T は ClosedTower（冪等性による）。
    unit : T → liftCl cl T が reflector の普遍性を持つ。
    toFun = id に制限すれば存在と一意性がともに成立。

  ──────────────────────────────────────────────
  プロジェクト昇格条件の最終達成状況:

    条件1: 非自明な主定理 3本以上
      ✓ EM代数 ↔ ClosedTower (L3 M6e)
      ✓ 閉包モナド法則 (L3 M4a-c)
      ✓ Rank uniqueness (L4-3d)
      ✓ unit の普遍性 (L4-4c)

    条件2: 3分野以上のケーススタディ
      ✓ 順序論 (L1-L2)
      ✓ 位相空間論 (G1 + L4-2)
      ✓ 群論 (G2)
      ✓ 測度論 (L4-2)

    条件3: 再利用可能なライブラリ
      ✓ cl-parametric 比較で複数 cl の相互作用を記述 (L4-1)
      ✓ ClosedTower の圏構造と reflective subcategory (L4-4)

  次のステップ候補（Level 5 以降）:
    - toFun ≠ id の一般 Kleisli 合成（naturality 条件の公理化）
    - Mathlib CategoryTheory.Monad との正式接続
    - I-adic filtration: FilteredRing + ClosedTower の統合
    - Enriched hom から 2-圏的構造へ
  ──────────────────────────────────────────────
-/

end StructureTower

end BourbakiGuide
