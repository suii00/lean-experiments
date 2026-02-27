/-
  StructureTower 具体例の接地（Level 3+）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  難易度: Level 3+（L3 モナド演習の完了が前提）
  目的: L3 の抽象的な ClosureOperator (Set α) を
        具体的な数学的閉包に接地し、ClosedTower が
        「閉集合の塔」「部分群の塔」を正確に捉えることを実証する。

  動機:
    L3 では ClosureOperator (Set α) を抽象的な cl として扱い、
    ClosedTower = 「全レベルが cl-不動点である塔」を定義した。
    ここでは cl を具体化する:

      cl = 位相的閉包   → ClosedTower = 各レベルが閉集合
      cl = 部分群生成   → ClosedTower = 各レベルが部分群

    同一の API (liftCl, unit, algebra, cl_global_subset) が
    両分野で機能することを確認する。これが
    「3分野以上のケーススタディを同一インターフェースで通す」
    というプロジェクト昇格条件の実証。

  構成:
    §G1. 位相的閉包 → ClosureOperator → ClosedTower  (5問)
    §G2. 部分群生成 → ClosureOperator → ClosedTower  (5問)
    §G3. 統合: 同一 API の実証                        (4問)
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.Closure
import Mathlib.Topology.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. Core definitions（L3 からの再掲）
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β : Type*} [Preorder ι]

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

-- L3 からの定義: liftCl, unit, ClosedTower

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

structure ClosedTower (cl : ClosureOperator (Set α)) (ι : Type*) [Preorder ι]
    extends StructureTower ι α where
  level_closed : ∀ i, cl (level i) = level i

namespace ClosedTower

variable {cl : ClosureOperator (Set α)}

-- L3 で証明済みの定理
theorem liftCl_eq_self (T : ClosedTower cl ι) :
    liftCl cl T.toStructureTower = T.toStructureTower := by
  ext i x; simp [liftCl, T.level_closed i]

def algebra (T : ClosedTower cl ι) :
    Hom (liftCl cl T.toStructureTower) T.toStructureTower where
  toFun := _root_.id
  preserves := by
    intro i x hx; simpa [liftCl, T.level_closed i] using hx

theorem algebra_unit (T : ClosedTower cl ι) :
    Hom.comp (algebra T) (unit cl T.toStructureTower) =
    Hom.id T.toStructureTower := Hom.ext rfl

theorem cl_global_subset (T : ClosedTower cl ι) :
    cl T.global ⊆ T.global := by
  intro x hx
  apply Set.mem_iInter.mpr
  intro i
  have h1 : cl T.global ⊆ cl (T.level i) :=
    cl.monotone (fun y hy => Set.mem_iInter.mp hy i)
  exact T.level_closed i ▸ (h1 hx)

end ClosedTower

-- ════════════════════════════════════════════════════════════
-- §G1. 位相的閉包 → ClosureOperator → ClosedTower
-- ════════════════════════════════════════════════════════════

/-!
  位相空間 [TopologicalSpace α] での closure : Set α → Set α は
  ClosureOperator (Set α) の典型例。

  核心となる3性質:
    - 拡大性: S ⊆ closure S                    (subset_closure)
    - 単調性: S ⊆ T → closure S ⊆ closure T    (closure_mono)
    - 冪等性: closure (closure S) = closure S    (isClosed_closure.closure_eq)

  ClosedTower for topClosure = 「各レベルが位相的閉集合である塔」
-/

section Topology

variable {α : Type*} [TopologicalSpace α]

/-- 🟡 Exercise G1a: 位相的閉包から ClosureOperator を構成する。

    Mathlib API:
      - closure : Set α → Set α
      - closure_mono : S ⊆ T → closure S ⊆ closure T
      - subset_closure : S ⊆ closure S
      - isClosed_closure : IsClosed (closure S)
      - IsClosed.closure_eq : IsClosed S → closure S = S

    冪等性 closure (closure S) = closure S は:
      isClosed_closure.closure_eq

    Hint-1: toFun := closure, monotone' は closure_mono。
    Hint-2: le_closure' は subset_closure。
    Hint-3: idempotent' は fun S => isClosed_closure.closure_eq。 -/
noncomputable def topClosure : ClosureOperator (Set α) where
  toFun := _root_.closure
  monotone' := fun _S _T h => closure_mono h
  le_closure' := sorry
  idempotent' := sorry

/-- 🟢 Exercise G1b: IsClosed S ↔ topClosure の不動点。

    方向→: IsClosed S → closure S = S は IsClosed.closure_eq。
    方向←: closure S = S → IsClosed S は closure_eq_iff_isClosed
            （または isClosed_closure と等式の書き換え）。

    Hint-1: →方向: h.closure_eq。
    Hint-2: ←方向: h ▸ isClosed_closure。
    Hint-3: constructor → 各方向。 -/
theorem isClosed_iff_topClosure_fixed (S : Set α) :
    IsClosed S ↔ topClosure S = S := by
  sorry

/-- 🟢 Exercise G1c: 閉集合の塔から ClosedTower を構成する。
    各レベルが IsClosed であれば、topClosure の ClosedTower になる。

    Hint-1: level_closed i は IsClosed → closure = self。
    Hint-2: (hclosed i).closure_eq。
    Hint-3: そのまま。 -/
def closedSetTower {ι : Type*} [Preorder ι]
    (T : StructureTower ι α)
    (hclosed : ∀ i, IsClosed (T.level i)) :
    ClosedTower topClosure ι where
  toStructureTower := T
  level_closed := by
    sorry

/-- 🟢 Exercise G1d: ClosedTower の各レベルは IsClosed。
    （G1c の逆方向）

    Hint-1: T.level_closed i は topClosure (T.level i) = T.level i。
    Hint-2: isClosed_iff_topClosure_fixed を使う。
    Hint-3: `(isClosed_iff_topClosure_fixed _).mpr (T.level_closed i)` -/
theorem ClosedTower.levels_isClosed {ι : Type*} [Preorder ι]
    (T : ClosedTower topClosure ι) (i : ι) :
    IsClosed (T.level i) := by
  sorry

/-- 🟡 Exercise G1e: 定数閉集合塔。
    閉集合 S をすべてのレベルに配置した塔は ClosedTower。

    Hint-1: level _ := S, monotone は自明。
    Hint-2: level_closed は h.closure_eq。
    Hint-3: 構造体リテラルで直接構成。 -/
def constClosedTower {ι : Type*} [Preorder ι]
    (S : Set α) (h : IsClosed S) :
    ClosedTower topClosure ι where
  level := fun _ => S
  monotone_level := fun _i _j _hij => Subset.rfl
  level_closed := by
    sorry

end Topology

-- ════════════════════════════════════════════════════════════
-- §G2. 部分群生成 → ClosureOperator → ClosedTower
-- ════════════════════════════════════════════════════════════

/-!
  群 [Group G] での Subgroup.closure : Set G → Subgroup G は、
  Set G → Set G に持ち上げると ClosureOperator (Set G) になる。

  核心となる3性質:
    - 拡大性: S ⊆ ↑(Subgroup.closure S)              (Subgroup.subset_closure)
    - 単調性: S ⊆ T → closure S ≤ closure T            (Subgroup.closure_mono)
    - 冪等性: closure ↑(closure S) = closure S          (Subgroup.closure_eq)

  ClosedTower for subgroupClosure = 「各レベルが部分群の台集合である塔」
-/

section SubgroupSection

variable {G : Type*} [Group G]

/-- 🟡 Exercise G2a: 部分群生成から ClosureOperator を構成する。

    Mathlib API:
      - Subgroup.closure : Set G → Subgroup G
      - Subgroup.subset_closure : S ⊆ ↑(Subgroup.closure S)
      - Subgroup.closure_mono : S ⊆ T → Subgroup.closure S ≤ Subgroup.closure T
      - Subgroup.closure_eq : ∀ H : Subgroup G, Subgroup.closure ↑H = H
      - (H ≤ K ↔ ↑H ⊆ ↑K for Subgroup)

    toFun := fun S => ↑(Subgroup.closure S)（Set G → Set G に持ち上げ）

    冪等性の証明:
      ↑(Subgroup.closure ↑(Subgroup.closure S)) = ↑(Subgroup.closure S)
      は congr_arg SetLike.coe (Subgroup.closure_eq _) で得られる。

    Hint-1: monotone' は Subgroup.closure_mono を Set レベルに持ち上げる。
    Hint-2: le_closure' は Subgroup.subset_closure。
    Hint-3: idempotent' は Subgroup.closure_eq の coercion。 -/
def subgroupClosure : ClosureOperator (Set G) where
  toFun := fun S => ↑(Subgroup.closure S)
  monotone' := by
    sorry
    -- skeleton:
    -- intro S T h
    -- exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono h)
  le_closure' := by
    sorry
    -- skeleton: intro S; exact Subgroup.subset_closure
  idempotent' := by
    sorry
    -- skeleton:
    -- intro S
    -- exact congr_arg SetLike.coe (Subgroup.closure_eq (Subgroup.closure S))

/-- 🟢 Exercise G2b: S が部分群の台集合 ↔ subgroupClosure の不動点。

    方向→: S = ↑H → Subgroup.closure S = H → ↑(closure S) = S。
    方向←: ↑(closure S) = S → S は Subgroup.closure S の台集合。

    Hint-1: →方向: congr_arg の活用。
    Hint-2: ←方向: h から S = ↑(Subgroup.closure S)。
    Hint-3: Exists を使って「ある H が存在して S = ↑H」と表現。 -/
theorem isSubgroupCarrier_iff_fixed (S : Set G) :
    (∃ H : Subgroup G, (H : Set G) = S) ↔ subgroupClosure S = S := by
  sorry
  /- skeleton:
     constructor
     · rintro ⟨H, rfl⟩
       show ↑(Subgroup.closure ↑H) = ↑H
       exact congr_arg SetLike.coe (Subgroup.closure_eq H)
     · intro h
       exact ⟨Subgroup.closure S, h.symm⟩ -/

/-- 🟢 Exercise G2c: 部分群の塔から ClosedTower を構成する。
    各レベルに対応する Subgroup が存在すれば、ClosedTower になる。

    Hint-1: level_closed i は (isSubgroupCarrier_iff_fixed _).mp。
    Hint-2: ⟨H i, rfl⟩ のパターン。
    Hint-3: `(isSubgroupCarrier_iff_fixed _).mp ⟨H i, rfl⟩` -/
def subgroupTower {ι : Type*} [Preorder ι]
    (H : ι → Subgroup G)
    (hmono : ∀ ⦃i j : ι⦄, i ≤ j → H i ≤ H j) :
    ClosedTower subgroupClosure ι where
  level := fun i => ↑(H i)
  monotone_level := by
    sorry
    -- skeleton: intro i j hij x hx; exact hmono hij hx
  level_closed := by
    sorry
    -- skeleton: intro i; exact (isSubgroupCarrier_iff_fixed _).mp ⟨H i, rfl⟩

/-- 🟡 Exercise G2d: ClosedTower の各レベルは部分群の台集合。
    （G2c の逆方向）

    Hint-1: T.level_closed i : subgroupClosure (T.level i) = T.level i。
    Hint-2: (isSubgroupCarrier_iff_fixed _).mpr で Subgroup を復元。
    Hint-3: `⟨Subgroup.closure (T.level i), (T.level_closed i).symm⟩` -/
theorem ClosedTower.levels_isSubgroup {ι : Type*} [Preorder ι]
    (T : ClosedTower subgroupClosure ι) (i : ι) :
    ∃ H : Subgroup G, (H : Set G) = T.level i := by
  sorry

/-- 🟡 Exercise G2e: FilteredGroup は subgroupClosure の ClosedTower を与える。

    EscapeExercises §I-2 の FilteredGroup を思い出す:
    各レベルが部分群（one_mem, mul_mem, inv_mem）なので、
    Subgroup.closure (level i) = level i が成り立つ。

    ここでは簡略版として、レベルが部分群の条件を直接仮定する。

    Hint-1: 各レベルから Subgroup を構成して Subgroup.closure_eq を使う。
    Hint-2: Subgroup.mk で carrier, one_mem', mul_mem', inv_mem' を与える。
    Hint-3: 下の skeleton を完成。 -/
def filteredGroupTower {ι : Type*} [Preorder ι]
    (T : StructureTower ι G)
    (hone : ∀ i, (1 : G) ∈ T.level i)
    (hmul : ∀ i {x y : G}, x ∈ T.level i → y ∈ T.level i → x * y ∈ T.level i)
    (hinv : ∀ i {x : G}, x ∈ T.level i → x⁻¹ ∈ T.level i) :
    ClosedTower subgroupClosure ι where
  toStructureTower := T
  level_closed := by
    sorry
    /- skeleton:
       intro i
       have H : Subgroup G := {
         carrier := T.level i
         one_mem' := hone i
         mul_mem' := hmul i
         inv_mem' := hinv i
       }
       show ↑(Subgroup.closure (T.level i)) = T.level i
       have : (H : Set G) = T.level i := rfl
       rw [← this]
       exact congr_arg SetLike.coe (Subgroup.closure_eq H) -/

end SubgroupSection

-- ════════════════════════════════════════════════════════════
-- §G3. 統合: 同一 API の実証
-- ════════════════════════════════════════════════════════════

/-!
  L3 で構築した抽象 API が、位相と代数の両方で機能することを確認する。

  核心: 以下の定理はすべて cl に依存せず、
  cl = topClosure でも cl = subgroupClosure でも同じ形で成立する:

    - liftCl_eq_self: 閉元の塔は liftCl の不動点
    - algebra: ClosedTower → 構造射 (liftCl T → T)
    - algebra_unit: algebra ∘ unit = id
    - cl_global_subset: global は cl-閉
-/

section Synthesis

/-- 🟢 Exercise G3a: 位相版 — liftCl は levelwise closure。
    liftCl topClosure T のレベル i は closure (T.level i)。
    これは T の各レベルを位相的に閉じた塔。

    Hint-1: liftCl_level で展開。
    Hint-2: `rfl`
    Hint-3: そのまま。 -/
theorem liftCl_topClosure_level {α : Type*} [TopologicalSpace α]
    {ι : Type*} [Preorder ι] (T : StructureTower ι α) (i : ι) :
    (liftCl topClosure T).level i = _root_.closure (T.level i) := by
  sorry

/-- 🟢 Exercise G3b: 代数版 — liftCl は levelwise subgroup closure。

    Hint-1: liftCl_level で展開。
    Hint-2: `rfl`
    Hint-3: そのまま。 -/
theorem liftCl_subgroupClosure_level {G : Type*} [Group G]
    {ι : Type*} [Preorder ι] (T : StructureTower ι G) (i : ι) :
    (liftCl subgroupClosure T).level i = ↑(Subgroup.closure (T.level i)) := by
  sorry

/-- 🟡 Exercise G3c: 位相版 — 閉集合塔の global は閉集合。
    cl_global_subset (L3 M6f) を topClosure に適用し、
    結果を IsClosed に翻訳する。

    Hint-1: cl_global_subset で closure (global T) ⊆ global T。
    Hint-2: subset_closure で global T ⊆ closure (global T)。
    Hint-3: 合わせて closure (global T) = global T → IsClosed。 -/
theorem closedTower_global_isClosed {α : Type*} [TopologicalSpace α]
    {ι : Type*} [Preorder ι]
    (T : ClosedTower topClosure ι) :
    IsClosed T.global := by
  sorry
  /- skeleton:
     rw [← isClosed_iff_topClosure_fixed]
     -- or directly:
     -- have hsub := ClosedTower.cl_global_subset T
     -- have hext := topClosure.le_closure T.global
     -- exact isClosedOf... -/

/-- 🟡 Exercise G3d: 代数版 — 部分群塔の global は部分群の台集合。
    cl_global_subset を subgroupClosure に適用し、
    結果を「ある Subgroup が存在」に翻訳する。

    Hint-1: cl_global_subset で ↑(Subgroup.closure (global T)) ⊆ global T。
    Hint-2: Subgroup.subset_closure で global T ⊆ ↑(Subgroup.closure (global T))。
    Hint-3: Set.Subset.antisymm で等式にし、Subgroup.closure (global T) が証人。 -/
theorem closedTower_global_isSubgroup {G : Type*} [Group G]
    {ι : Type*} [Preorder ι]
    (T : ClosedTower subgroupClosure ι) :
    ∃ H : Subgroup G, (H : Set G) = T.global := by
  sorry
  /- skeleton:
     have hsub := ClosedTower.cl_global_subset T
     -- hsub : subgroupClosure T.global ⊆ T.global
     -- i.e. ↑(Subgroup.closure T.global) ⊆ T.global
     have hext : T.global ⊆ subgroupClosure T.global := subgroupClosure.le_closure T.global
     have heq : subgroupClosure T.global = T.global := Set.Subset.antisymm hsub hext
     exact ⟨Subgroup.closure T.global, heq.symm⟩ -/

end Synthesis

-- ════════════════════════════════════════════════════════════
-- §Summary. 具体例の接地で確認したこと
-- ════════════════════════════════════════════════════════════

/-!
  §G1 **位相的閉包**:
    topClosure : ClosureOperator (Set α)
    を構成。closure_mono / subset_closure / isClosed_closure.closure_eq
    が ClosureOperator の3公理に直接対応。

    ClosedTower topClosure ι  ↔  各レベルが IsClosed

  §G2 **部分群生成**:
    subgroupClosure : ClosureOperator (Set G)
    を構成。Subgroup.closure を Set G → Set G に持ち上げ。
    冪等性は Subgroup.closure_eq による。

    ClosedTower subgroupClosure ι  ↔  各レベルが Subgroup の台集合
    FilteredGroup → ClosedTower（部分群条件があれば自動的に閉）

  §G3 **統合**:
    L3 の抽象 API が両分野で機能:
    - liftCl = levelwise closure（位相でも代数でも）
    - cl_global_subset → global は閉（閉集合 / 部分群）

  ──────────────────────────────────────────────
  対応表:

    抽象 API              位相的解釈            代数的解釈
    ──────────────────────────────────────────────
    cl : ClosureOperator   closure              Subgroup.closure ↑·
    cl S = S (不動点)      IsClosed S           S = ↑H for some H
    ClosedTower            閉集合の塔            部分群の塔
    liftCl                 各レベルを閉包        各レベルの生成部分群
    unit : T → liftCl T   包含 S ⊆ closure S   包含 S ⊆ ↑⟨S⟩
    algebra : liftCl T → T  恒等写像（閉なので）  恒等写像（部分群なので）
    cl_global_subset       ⋂ᵢ(閉) は閉         ⋂ᵢ(部分群) は部分群
  ──────────────────────────────────────────────

  プロジェクト昇格条件の達成状況:

    条件1: 非自明な主定理 3本以上
      ✓ EM代数 ↔ ClosedTower (L3 M6e)
      ✓ 閉包モナド法則 (L3 M4a-c)
      ✓ cl_global_subset (L3 M6f, 具体例で実証)

    条件2: 3分野以上のケーススタディ
      ✓ 順序論 (L1-L2: Iic塔, reindex, 積)
      ✓ 位相空間論 (G1: 閉集合の塔)
      ✓ 群論 (G2: 部分群の塔)

    条件3: 再利用可能なライブラリ
      △ 個別ファイルは機能するが、統合パッケージは未整備

  次のステップ候補:
    - TeX 文書化（L1-L3 + 接地の統合論文）
    - σ-代数（MeasurableSpace）への第3の接地
    - ライブラリ統合（单一ファイルへの集約 + lake build 導線）
    - Level 4: Mathlib CategoryTheory.Monad との正式接続
-/

end StructureTower

end BourbakiGuide
