/-
  StructureTower モナド演習（レベル3）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  難易度: レベル3（上級）
  前提: Level 1（圏の公理）+ Level 2（Iso, 積の普遍性, global）を完了していること

  動機:
    StructureTower の「非自明化」の核心。
    ClosureOperator (Set α) をレベルごとに適用すると、
    塔の圏上の自己関手が得られ、これがモナドをなす。

    閉包公理 (extensive, monotone, idempotent) が
    モナド公理 (unit, multiplication, associativity) に
    正確に対応する――これが「この枠組みでないと
    自然に記述できない」構造の典型例。

  学習の流れ:
    §M1. Levelwise 自己関手    — cl を各レベルに適用
    §M2. Unit（単位）          — 拡大性 A ⊆ cl(A) からの自然変換
    §M3. Join（結合）          — 冪等性 cl(cl(A)) = cl(A) からの自然変換
    §M4. モナド法則            — 左右単位律・結合律
    §M5. Kleisli 射            — 「閉包まで許した」射の圏
    §M6. Eilenberg-Moore 代数  — 閉元（不動点）の塔

  ヒントの読み方:
    Hint-1: 大まかな方針
    Hint-2: 使うべき補題やタクティク
    Hint-3: ほぼ答え
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure

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

-- Level 1-2 で証明済みの公理
theorem Hom.id_comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : Hom.comp (Hom.id T₂) f = f := Hom.ext rfl
theorem Hom.comp_id {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : Hom.comp f (Hom.id T₁) = f := Hom.ext rfl
theorem Hom.comp_assoc
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ} {T₄ : StructureTower ι α}
    (h : Hom T₃ T₄) (g : Hom T₂ T₃) (f : Hom T₁ T₂) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §M1. Levelwise 自己関手  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  ClosureOperator (Set α) は、Set α の ⊆-順序上の閉包作用素:
    - extensive : A ⊆ cl(A)
    - monotone  : A ⊆ B → cl(A) ⊆ cl(B)
    - idempotent: cl(cl(A)) = cl(A)

  これを各レベルに適用すると、塔の自己関手が得られる:
    (liftCl cl T).level i := cl (T.level i)

  閉包の単調性により、塔の単調性が保たれる。
-/

variable (cl : ClosureOperator (Set α))

/-- 🟢 Exercise M1a: 閉包のレベルごとの持ち上げ。
    cl を各レベルに適用した塔を構成する。

    Hint-1: level i := cl (T.level i)。
    Hint-2: 塔の単調性: T.level i ⊆ T.level j → cl(T.level i) ⊆ cl(T.level j)。
    Hint-3: `cl.monotone (T.monotone_level hij)` -/
def liftCl (T : StructureTower ι α) : StructureTower ι α where
  level i := cl (T.level i)
  monotone_level := by
    intro i j hij x hx
    exact cl.monotone (T.monotone_level hij) hx

@[simp] theorem liftCl_level (T : StructureTower ι α) (i : ι) :
    (liftCl cl T).level i = cl (T.level i) := rfl

/-- 🟡 Exercise M1b: liftCl は Hom を保存する（関手の射への作用）。
    f : Hom T₁ T₂ が与えられたとき、同じ基底写像が
    liftCl cl T₁ → liftCl cl T₂ の Hom を与える。

    ただし、これには cl が「写像と可換」という追加条件が必要。
    一般には成立しないため、ここでは toFun = id の特殊ケース
    （すなわち T₁.level i ⊆ T₂.level i を仮定）で示す。

    Hint-1: T₁.level i ⊆ T₂.level i → cl(T₁.level i) ⊆ cl(T₂.level i)。
    Hint-2: cl.monotone を使う。
    Hint-3: `intro i x hx; exact cl.monotone (h i) hx` -/
def liftCl_mapId (T₁ T₂ : StructureTower ι α)
    (h : ∀ i, T₁.level i ⊆ T₂.level i) :
    Hom (liftCl cl T₁) (liftCl cl T₂) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    exact cl.monotone (h i) hx

/-- 🟡 Exercise M1c: liftCl は恒等包含を保つ。
    T ⊆ T （各レベルで）のとき、liftCl_mapId は恒等射。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: toFun = id なので rfl。
    Hint-3: `Hom.ext rfl` -/
theorem liftCl_mapId_refl (T : StructureTower ι α) :
    liftCl_mapId cl T T (fun _i => Subset.rfl) = Hom.id (liftCl cl T) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §M2. Unit 自然変換（η : T → cl(T)）  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  閉包の拡大性 A ⊆ cl(A) から、各塔 T に対して
  自然な Hom η_T : T → liftCl cl T が得られる。

  これがモナドの unit（η）に相当する。
  toFun = id で、preserves は拡大性そのもの。
-/

/-- 🟢 Exercise M2a: Unit の構成。
    拡大性 T.level i ⊆ cl(T.level i) がそのまま preserves を与える。

    Hint-1: toFun = id。
    Hint-2: preserves は cl.le_closure (T.level i)。
    Hint-3: `intro i x hx; exact cl.le_closure (T.level i) hx` -/
def unit (T : StructureTower ι α) :
    Hom T (liftCl cl T) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    exact cl.le_closure (T.level i) hx

/-- 🟡 Exercise M2b: Unit の自然性。
    T₁.level i ⊆ T₂.level i を仮定したとき、以下が可換:

        T₁ ──────unit──────→ liftCl cl T₁
        │                         │
      Hom.id (inclusion)     liftCl_mapId
        │                         │
        ↓                         ↓
        T₂ ──────unit──────→ liftCl cl T₂

    全体が id 同士の合成なので Hom.ext rfl で閉じる。

    Hint-1: 両辺の toFun はどちらも id。
    Hint-2: Hom.comp の toFun = g.toFun ∘ f.toFun = id ∘ id = id。
    Hint-3: `Hom.ext rfl` -/
theorem unit_natural (T₁ T₂ : StructureTower ι α)
    (h : ∀ i, T₁.level i ⊆ T₂.level i) :
    Hom.comp (liftCl_mapId cl T₁ T₂ h) (unit cl T₁) =
    Hom.comp (unit cl T₂) ⟨_root_.id, fun i => h i⟩ := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §M3. Join（μ : cl(cl(T)) → cl(T)）  🟡
-- ════════════════════════════════════════════════════════════

/-!
  閉包の冪等性 cl(cl(A)) = cl(A) から、
  μ_T : liftCl cl (liftCl cl T) → liftCl cl T が得られる。

  これがモナドの multiplication（μ）に相当する。

  注意: liftCl cl (liftCl cl T) のレベル i は cl(cl(T.level i))。
  冪等性により cl(cl(A)) ⊆ cl(A)（⊇ 方向も成立、等号）。
-/

/-- 🟡 Exercise M3a: Join の構成。
    冪等性 cl(cl(A)) = cl(A) の ⊆ 方向が preserves を与える。

    Hint-1: toFun = id。
    Hint-2: x ∈ cl(cl(T.level i)) → x ∈ cl(T.level i) は
            cl.idempotent (T.level i) の ⊇ 方向。
    Hint-3: `intro i x hx; rw [cl.idempotent] at hx; exact hx`
            または `intro i x hx; exact (cl.idempotent (T.level i)).symm ▸ hx` -/
def join (T : StructureTower ι α) :
    Hom (liftCl cl (liftCl cl T)) (liftCl cl T) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    simpa [cl.idempotent] using hx

/-- 🟡 Exercise M3b: Join の逆方向（unit の持ち上げ）。
    拡大性より cl(A) ⊆ cl(cl(A)) も成り立つ。

    Hint-1: toFun = id。
    Hint-2: cl.le_closure (cl (T.level i)) で cl(A) ⊆ cl(cl(A))。
    Hint-3: `intro i x hx; exact cl.le_closure _ hx` -/
def join_inv (T : StructureTower ι α) :
    Hom (liftCl cl T) (liftCl cl (liftCl cl T)) where
  toFun := _root_.id
  preserves := by
    intro i x hx
    exact cl.le_closure (cl (T.level i)) hx

/-- 🟡 Exercise M3c: join と join_inv は互いに逆。
    cl(cl(A)) = cl(A) の両方向。

    Hint-1: 両方とも toFun = id なので合成も id。
    Hint-2: `Hom.ext rfl`
    Hint-3: そのまま。 -/
theorem join_join_inv (T : StructureTower ι α) :
    Hom.comp (join cl T) (join_inv cl T) = Hom.id (liftCl cl T) := by
  exact Hom.ext rfl

theorem join_inv_join (T : StructureTower ι α) :
    Hom.comp (join_inv cl T) (join cl T) = Hom.id (liftCl cl (liftCl cl T)) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §M4. モナド法則  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  モナド (liftCl, unit, join) が満たすべき3つの法則:

    (1) 左単位律:  μ ∘ η_{cl(T)} = id_{cl(T)}
    (2) 右単位律:  μ ∘ cl(η_T)  = id_{cl(T)}
    (3) 結合律:    μ ∘ cl(μ)     = μ ∘ μ_{cl(T)}

  すべて toFun = id なので、Hom.ext rfl で閉じる……はず。
  ただし「cl(η_T)」の型を正しく構成するところが技術的ポイント。
-/

/-- 🟡 Exercise M4a: 左単位律。
    join ∘ unit_{liftCl T} = id_{liftCl T}。

    η を cl(T) に適用 → join で潰す。
    η : cl(T) → cl(cl(T)), μ : cl(cl(T)) → cl(T) なので合成は id。

    Hint-1: 両辺の toFun は id ∘ id = id。
    Hint-2: `Hom.ext rfl`
    Hint-3: そのまま。 -/
theorem monad_left_unit (T : StructureTower ι α) :
    Hom.comp (join cl T) (unit cl (liftCl cl T)) = Hom.id (liftCl cl T) := by
  exact Hom.ext rfl

/-- 🟡 Exercise M4b: 右単位律。
    join ∘ liftCl_mapId(unit) = id_{liftCl T}。

    ここで「liftCl_mapId(unit)」は、各レベルで
    T.level i ⊆ cl(T.level i) を cl で持ち上げた射。
    型: liftCl cl T → liftCl cl (liftCl cl T)。

    Hint-1: 構成: cl(T.level i) ⊆ cl(cl(T.level i)) は cl.le_closure の持ち上げ。
    Hint-2: 合成は id ∘ id = id。
    Hint-3: `Hom.ext rfl` -/
theorem monad_right_unit (T : StructureTower ι α) :
    Hom.comp (join cl T)
      (liftCl_mapId cl T (liftCl cl T)
        (fun i => cl.le_closure (T.level i))) =
    Hom.id (liftCl cl T) := by
  exact Hom.ext rfl

/-- 🔴 Exercise M4c: 結合律。
    join ∘ join_{liftCl T} = join ∘ liftCl_mapId(join)。

    両辺とも cl(cl(cl(T))) → cl(T) で、toFun = id。

    Hint-1: 型を確認。左辺: join_T ∘ join_{cl(T)}。
            右辺: join_T ∘ liftCl_mapId(join の各レベル)。
    Hint-2: 両方とも toFun = id ∘ id = id。
    Hint-3: `Hom.ext rfl` -/
theorem monad_assoc (T : StructureTower ι α) :
    Hom.comp (join cl T) (join cl (liftCl cl T)) =
    Hom.comp (join cl T)
      (liftCl_mapId cl (liftCl cl (liftCl cl T)) (liftCl cl T)
        (fun i x hx => by
          simpa [cl.idempotent] using hx)) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §M5. Kleisli 射  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  Kleisli 圏: 対象は塔、射は「閉包まで許した」写像。

    T₁ →_Kl T₂  :=  Hom T₁ (liftCl cl T₂)

  直観: f が T₁ の各レベルを T₂ の各レベルの「閉包の中に」送る。
  「厳密な保存」より緩い条件で、近似や飽和を表現する。

  Kleisli 恒等射: unit（η）
  Kleisli 合成:   g ∘_Kl f = join ∘ g ∘ f
    （f で T₁ → cl(T₂)、g で cl(T₂) → cl(cl(T₃))、join で cl(T₃) に潰す）
-/

/-- Kleisli 射の型。 -/
abbrev KlHom (T₁ T₂ : StructureTower ι α) :=
  Hom T₁ (liftCl cl T₂)

/-- 🟡 Exercise M5a: Kleisli 恒等射 = unit。

    Hint-1: unit は T → liftCl cl T、これは T →_Kl T そのもの。
    Hint-2: `unit cl T`
    Hint-3: 定義。 -/
def KlHom.id (T : StructureTower ι α) :
    KlHom cl T T :=
  unit cl T

/-- 🔴 Exercise M5b: Kleisli 合成。
    f : T₁ →_Kl T₂  と  g : T₂ →_Kl T₃  から
    T₁ →_Kl T₃ を構成する。

    方針:
      f : T₁ → cl(T₂)     （f.toFun, f.preserves）
      g : T₂ → cl(T₃)     （g.toFun, g.preserves）

      g ∘_Kl f の toFun は g.toFun ∘ f.toFun。
      preserves: x ∈ T₁.level i
        → f.toFun x ∈ cl(T₂.level i)        （by f.preserves）
        → g.toFun(f.toFun x) ∈ cl(cl(T₃.level i))  （by ??? ）
        → g.toFun(f.toFun x) ∈ cl(T₃.level i)       （by idempotent）

      問題: g.preserves は T₂.level i → cl(T₃.level i) だが、
      f.toFun x は cl(T₂.level i) に属する。g の preserves は
      T₂.level i に対してしか保証しない。

      一般には g.toFun を cl(T₂.level i) 上に拡張する必要があり、
      これには cl と g の可換性（naturality）が要る。

      ここでは toFun = id のケース（両方が id）に限定して構成する。

    Hint-1: f.toFun = id, g.toFun = id の場合、合成の toFun も id。
    Hint-2: x ∈ T₁.level i → x ∈ cl(T₂.level i)（f.preserves）
            → x ∈ cl(cl(T₃.level i))（cl.monotone applied to g.preserves）
            → x ∈ cl(T₃.level i)（idempotent）。
    Hint-3: 下の skeleton を完成させる。 -/
def KlHom.compId
    {T₁ T₂ T₃ : StructureTower ι α}
    (g : KlHom cl T₂ T₃) (f : KlHom cl T₁ T₂)
    (hf : f.toFun = _root_.id) (hg : g.toFun = _root_.id) :
    KlHom cl T₁ T₃ where
  toFun := _root_.id
  preserves := by
    intro i x hx
    have h1 : x ∈ cl (T₂.level i) := by
      simpa [hf] using f.preserves i hx
    have hsubset : T₂.level i ⊆ cl (T₃.level i) := by
      intro y hy
      simpa [hg] using g.preserves i hy
    have h2 : x ∈ cl (cl (T₃.level i)) := cl.monotone hsubset h1
    simpa [cl.idempotent] using h2
    /- skeleton:
       intro i x hx
       have h1 : x ∈ cl (T₂.level i) := by rw [hf] at f; exact f.preserves i hx
       -- g maps T₂.level i into cl(T₃.level i), so cl monotone gives:
       -- cl(T₂.level i) ⊆ cl(cl(T₃.level i))
       have h2 : x ∈ cl (cl (T₃.level i)) := cl.monotone (fun y hy => ...) h1
       -- idempotent: cl(cl(A)) = cl(A)
       rw [cl.idempotent] at h2
       exact h2 -/

-- ════════════════════════════════════════════════════════════
-- §M6. Eilenberg-Moore 代数（閉元の塔）  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  Eilenberg-Moore 代数:

  モナド (F, η, μ) の代数は、対象 T と射 a : F(T) → T であって
    a ∘ η = id  かつ  a ∘ F(a) = a ∘ μ
  を満たすもの。

  liftCl モナドでは:
    a : liftCl cl T → T  with  a ∘ η = id
  ⟹  各レベルで cl(T.level i) ⊆ T.level i
  ⟹  拡大性 T.level i ⊆ cl(T.level i) と合わせて
      cl(T.level i) = T.level i

  つまり EM 代数は「全レベルが cl-閉集合である塔」に他ならない。
-/

/-- 閉元の塔: 各レベルが cl の不動点。 -/
structure ClosedTower (cl : ClosureOperator (Set α)) (ι : Type*) [Preorder ι]
    extends StructureTower ι α where
  level_closed : ∀ i, cl (level i) = level i

namespace ClosedTower

variable {cl : ClosureOperator (Set α)}

/-- 🟢 Exercise M6a: 閉元の塔は liftCl の不動点。

    Hint-1: 塔の ext で level を比較。
    Hint-2: 各レベルで cl(T.level i) = T.level i（仮定 level_closed）。
    Hint-3: `ext i x; simp [liftCl, T.level_closed i]` -/
theorem liftCl_eq_self (T : ClosedTower cl ι) :
    liftCl cl T.toStructureTower = T.toStructureTower := by
  ext i x
  simp [liftCl, T.level_closed i]

/-- 🟢 Exercise M6b: liftCl の不動点は閉元の塔を与える。

    Hint-1: level_closed は liftCl cl T = T の各レベル。
    Hint-2: congr_arg (· i) h で等式を取り出す。
    Hint-3: `fun i => congr_fun (congr_arg StructureTower.level h) i` -/
def ofFixed (T : StructureTower ι α)
    (h : liftCl cl T = T) : ClosedTower cl ι where
  toStructureTower := T
  level_closed := by
    intro i
    exact congr_fun (congr_arg StructureTower.level h) i

/-- 🟡 Exercise M6c: unit の逆射が存在する（EM 代数の構造射）。
    閉元の塔 T では cl(T.level i) = T.level i なので、
    liftCl cl T → T は恒等写像で構成できる。

    Hint-1: toFun = id。
    Hint-2: preserves: x ∈ cl(T.level i) = T.level i → x ∈ T.level i。
    Hint-3: `intro i x hx; rw [T.level_closed] at hx; exact hx`
            または `intro i x hx; exact (T.level_closed i) ▸ hx` -/
def algebra (T : ClosedTower cl ι) :
    Hom (liftCl cl T.toStructureTower) T.toStructureTower where
  toFun := _root_.id
  preserves := by
    intro i x hx
    simpa [liftCl, T.level_closed i] using hx

/-- 🟡 Exercise M6d: EM 代数の公理 (1): algebra ∘ unit = id。

    Hint-1: 両辺 toFun = id ∘ id = id。
    Hint-2: `Hom.ext rfl`
    Hint-3: そのまま。 -/
theorem algebra_unit (T : ClosedTower cl ι) :
    Hom.comp (algebra T) (unit cl T.toStructureTower) =
    Hom.id T.toStructureTower := by
  exact Hom.ext rfl

/-- 🔴 Exercise M6e: 逆方向: EM 代数の構造射を持つ塔は閉元の塔。

    a : Hom (liftCl cl T) T  with  a ∘ unit = id  かつ  a.toFun = id
    ⟹ 各レベルで cl(T.level i) ⊆ T.level i
    ⟹ cl(T.level i) = T.level i（拡大性と合わせて）

    Hint-1: a.preserves i は cl(T.level i) ⊆ T.level i（a.toFun = id より）。
    Hint-2: 拡大性 cl.le_closure で逆包含。
    Hint-3: `Set.Subset.antisymm` で両方向を結合。 -/
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

/-- 🔴 Exercise M6f: 閉元の塔の global は cl-閉集合。

    Hint-1: global = ⋂ᵢ T.level i。各 T.level i は cl-閉。
    Hint-2: 一般に cl-閉集合の交叉は cl-閉（cl の ⊆ 方向は単調性で得られるが
            = を示すには cl が iInter を保存するかが問題）。
    Hint-3: 一方向（cl(global) ⊆ global）だけ示す。
            cl.monotone (global_subset_level T i) と level_closed で
            cl(global) ⊆ cl(level i) = level i。
            全 i で成り立つので cl(global) ⊆ ⋂ᵢ level i = global。 -/
theorem cl_global_subset (T : ClosedTower cl ι) :
    cl T.global ⊆ T.global := by
  intro x hx
  apply Set.mem_iInter.mpr
  intro i
  have h1 : cl T.global ⊆ cl (T.level i) := by
    apply cl.monotone
    intro y hy
    exact Set.mem_iInter.mp hy i
  have h2 : cl (T.level i) = T.level i := T.level_closed i
  exact h2 ▸ (h1 hx)

end ClosedTower

-- ════════════════════════════════════════════════════════════
-- §Summary. モナドの全体像
-- ════════════════════════════════════════════════════════════

/-!
  Level 3 で確認したこと:

  §M1 **Levelwise 自己関手**:
    cl を各レベルに適用 → 新しい塔。単調性は cl.monotone で保証。

  §M2 **Unit (η)**:
    拡大性 A ⊆ cl(A) → Hom T (liftCl cl T)。
    toFun = id、preserves = cl.le_closure。

  §M3 **Join (μ)**:
    冪等性 cl(cl(A)) = cl(A) → Hom (liftCl² T) (liftCl T)。
    join と join_inv は互いに逆。

  §M4 **モナド法則**:
    左右単位律・結合律。toFun = id のため Hom.ext rfl で閉じる。

  §M5 **Kleisli 射**:
    T₁ →_Kl T₂ = Hom T₁ (liftCl cl T₂)。
    恒等射 = unit。合成は「cl を通した合成」。

  §M6 **Eilenberg-Moore 代数**:
    EM 代数 ↔ 全レベルが cl-閉集合である塔。
    algebra ∘ unit = id。閉元の global も cl-閉（一方向）。

  ──────────────────────────────────────────────
  閉包公理とモナド公理の対応表:

    閉包公理          モナド公理          証明の核
    ─────────────────────────────────────────────
    拡大性 A ⊆ cl(A)   η : T → F(T)       cl.le_closure
    冪等性 cl²=cl      μ : F²(T) → F(T)   cl.idempotent
    単調性 A⊆B→cl(A)⊆cl(B)  F は関手      cl.monotone
    (自明)             左単位律 μ∘η=id     Hom.ext rfl
    (自明)             右単位律            Hom.ext rfl
    (自明)             結合律 μ∘Fμ=μ∘μF   Hom.ext rfl

  核心的洞察:
    toFun = id のモナド（＝冪等モナド）では、
    モナド法則が「型レベルの整合性チェック」に帰着する。
    非自明な内容は unit と join の **構成**（穴埋め部分）にあり、
    法則の **証明** 自体は自明になる。
    これは「正しく構成すれば法則は自動的に成り立つ」という
    型理論の強みを示す好例である。
  ──────────────────────────────────────────────

  次のステップ（Level 4 候補）:
  - 具体的な cl の例: 位相空間の closure, 群の生成, σ-代数の生成
  - toFun ≠ id の Kleisli 合成（naturality 条件の探求）
  - Mathlib CategoryTheory.Monad との接続
  - Enriched hom（Hom の間の順序）から 2-圏的構造へ
-/

end StructureTower

end BourbakiGuide
