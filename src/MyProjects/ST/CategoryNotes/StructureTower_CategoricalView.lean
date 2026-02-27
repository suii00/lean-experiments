/-
  StructureTower — 圏論的視点
  ════════════════════════════════════════════════════════════

  構成:
    §1. 基礎         ── 塔の圏 Tower(ι) の公理検証
    §2. 自然変換     ── NatInclusion と levelwise 構成
    §3. 関手性       ── map / comap / reindex の関手法則
    §4. 極限・余極限 ── Tower(ι) 内の積・余積・等化子
    §5. 閉包モナド   ── Galois → Closure → Kleisli / EM
    §6. OrderHom同値 ── Tower(ι) ≃ OrderHom ι (Set α)

    §7. Sorry スケルトン（🟢×4 / 🟡×4 / 🔴×4 = 12問）

  前提:
    StructureTower ι α ≃ OrderHom ι (Set α)  が等価性の土台。
    §4 の極限・余極限がこの枠組みに非自明な構造を与える。
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure

open Set Function

namespace BourbakiGuide

-- ════════════════════════════════════════════════════════════
-- §0. コア定義（自己完結）
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level          : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β γ δ : Type*} [Preorder ι]

-- ════════════════════════════════════════════════════════════
-- §1. 基礎 ── 塔の圏 Tower(ι) の公理
-- ════════════════════════════════════════════════════════════
/-
  圏 Tower(ι):
    対象  : StructureTower ι α（α は任意の型）
    射    : Hom T₁ T₂（レベル保存写像）
    恒等  : Hom.id
    合成  : Hom.comp

  公理はすべて証明済み。これが §7 演習の土台。
-/

structure Hom (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  toFun     : α → β
  preserves : ∀ i, MapsTo toFun (T₁.level i) (T₂.level i)

instance {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} :
    CoeFun (Hom T₁ T₂) (fun _ => α → β) where
  coe f := f.toFun

def Hom.id (T : StructureTower ι α) : Hom T T where
  toFun     := _root_.id
  preserves := fun _i _x hx => hx

def Hom.comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) : Hom T₁ T₃ where
  toFun     := g.toFun ∘ f.toFun
  preserves := fun i _x hx => g.preserves i (f.preserves i hx)

@[ext]
theorem Hom.ext {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {f g : Hom T₁ T₂} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

-- 圏の公理（単位律・結合律）

theorem Hom.comp_id {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : Hom.comp f (Hom.id T₁) = f := by
  ext x
  rfl

theorem Hom.id_comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : Hom.comp (Hom.id T₂) f = f := by
  ext x
  rfl

theorem Hom.comp_assoc
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ} {T₄ : StructureTower ι δ}
    (h : Hom T₃ T₄) (g : Hom T₂ T₃) (f : Hom T₁ T₂) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := by
  cases f; cases g; cases h; rfl

-- ════════════════════════════════════════════════════════════
-- §2. 自然変換 ── NatInclusion
-- ════════════════════════════════════════════════════════════
/-
  同一添字 ι・同一台 α の2塔間の "自然変換" を
  levelwise な包含として定義する。

  Set α の射は ⊆ なので自然性図式は自動的に可換。
  これは関手 level : ι → (Set α, ⊆) の間の自然変換。
-/

def NatInclusion (T₁ T₂ : StructureTower ι α) : Prop :=
  ∀ i, T₁.level i ⊆ T₂.level i

theorem NatInclusion.refl (T : StructureTower ι α) : NatInclusion T T :=
  fun _i => Subset.refl _

theorem NatInclusion.trans {T₁ T₂ T₃ : StructureTower ι α}
    (h₁₂ : NatInclusion T₁ T₂) (h₂₃ : NatInclusion T₂ T₃) :
    NatInclusion T₁ T₃ :=
  fun i => Subset.trans (h₁₂ i) (h₂₃ i)

-- NatInclusion は Tower(ι)（同一台）上の半順序をなす
theorem NatInclusion.antisymm {T₁ T₂ : StructureTower ι α}
    (h₁₂ : NatInclusion T₁ T₂) (h₂₁ : NatInclusion T₂ T₁) :
    T₁ = T₂ := by
  ext i x
  exact ⟨fun hx => h₁₂ i hx, fun hx => h₂₁ i hx⟩

-- ════════════════════════════════════════════════════════════
-- §3. 関手性 ── map / comap / reindex
-- ════════════════════════════════════════════════════════════
/-
  3種の関手的操作:
    map f    : Tower(ι, α) → Tower(ι, β)   [共変, α → β に沿う]
    comap f  : Tower(ι, β) → Tower(ι, α)   [反変, α → β に沿う]
    reindex φ: Tower(κ, α) → Tower(ι, α)   [添字反変, ι → κ に沿う]
-/

def map (f : α → β) (T : StructureTower ι α) : StructureTower ι β where
  level i        := f '' T.level i
  monotone_level := by
    intro i j hij y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, T.monotone_level hij hx, rfl⟩

def comap (f : α → β) (T : StructureTower ι β) : StructureTower ι α where
  level i        := f ⁻¹' T.level i
  monotone_level := fun _i _j hij _x hx => T.monotone_level hij hx

def reindex {κ : Type*} [Preorder κ] (f : ι → κ) (hf : Monotone f)
    (T : StructureTower κ α) : StructureTower ι α where
  level i        := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

-- 関手法則（証明済み）

theorem map_id (T : StructureTower ι α) : map _root_.id T = T := by
  ext i x; simp [map]

theorem map_comp (f : α → β) (g : β → γ) (T : StructureTower ι α) :
    map (g ∘ f) T = map g (map f T) := by
  ext i x; simp [map]

theorem comap_id (T : StructureTower ι α) : comap _root_.id T = T := by
  ext i x; simp [comap]

theorem comap_comp (f : α → β) (g : β → γ) (T : StructureTower ι γ) :
    comap f (comap g T) = comap (g ∘ f) T := by
  ext i x; simp [comap]

theorem reindex_id (T : StructureTower ι α) :
    reindex id monotone_id T = T := by ext i _; simp [reindex]

theorem reindex_comp {κ μ : Type*} [Preorder κ] [Preorder μ]
    (f : ι → κ) (hf : Monotone f) (g : κ → μ) (hg : Monotone g)
    (T : StructureTower μ α) :
    reindex f hf (reindex g hg T) = reindex (g ∘ f) (hg.comp hf) T := by
  ext i _; simp [reindex]

-- 自然性: map と reindex の交換法則
theorem map_reindex_comm {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (g : α → β) (T : StructureTower κ α) :
    map g (reindex f hf T) = reindex f hf (map g T) := by
  ext i x; simp [map, reindex]

-- reindex は NatInclusion を保つ（反変関手の自然性）
theorem reindex_natInclusion {κ : Type*} [Preorder κ]
    {T₁ T₂ : StructureTower κ α} (f : ι → κ) (hf : Monotone f)
    (h : NatInclusion T₁ T₂) :
    NatInclusion (reindex f hf T₁) (reindex f hf T₂) :=
  fun i => h (f i)

-- ════════════════════════════════════════════════════════════
-- §4. 極限・余極限 ── Tower(ι) の積・余積・等化子
-- ════════════════════════════════════════════════════════════
/-
  Tower(ι)（同一台 α の塔全体の圏, 射 = NatInclusion）では:

  ┌─────────────────────────────────────────────────────────┐
  │  積     (product)   = levelwise 交叉   level i = T₁∩T₂  │
  │  余積   (coproduct) = levelwise 合併   level i = T₁∪T₂  │
  │  等化子 (equalizer) = levelwise 等化子                   │
  │  終対象 (terminal)  = const univ（全集合の定数塔）        │
  │  始対象 (initial)   = const ∅ （空集合の定数塔）         │
  └─────────────────────────────────────────────────────────┘

  各構成に対して、普遍性（universal property）を証明する。
-/

-- ──────────────────────────────────────────
-- §4-1. 終対象と始対象
-- ──────────────────────────────────────────

/-- 終対象: 全集合の定数塔。任意の塔から唯一の NatInclusion が存在する。 -/
def terminal : StructureTower ι α where
  level _        := Set.univ
  monotone_level := fun _i _j _hij => Set.Subset.refl _

theorem natInclusion_to_terminal (T : StructureTower ι α) :
    NatInclusion T terminal :=
  fun _i _x _hx => Set.mem_univ _

/-- 始対象: 空集合の定数塔。任意の塔への唯一の NatInclusion が存在する。 -/
def initial : StructureTower ι α where
  level _        := ∅
  monotone_level := fun _i _j _hij => Set.Subset.refl _

theorem natInclusion_from_initial (T : StructureTower ι α) :
    NatInclusion initial T :=
  fun _i _x hx => False.elim hx

-- ──────────────────────────────────────────
-- §4-2. 積（levelwise 交叉）
-- ──────────────────────────────────────────
/-
  積の普遍性:
    T × T₂ への NatInclusion ≃ T₁ への + T₂ への NatInclusion の対

  図式:
       S ──→ T₁
       │      
       └──→ T₂
    は S → T₁ × T₂ に一意に因数分解される
-/

def prod (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i        := T₁.level i ∩ T₂.level i
  monotone_level := fun _i _j hij _x hx =>
    ⟨T₁.monotone_level hij hx.1, T₂.monotone_level hij hx.2⟩

-- 射影
theorem prod_fst (T₁ T₂ : StructureTower ι α) :
    NatInclusion (prod T₁ T₂) T₁ :=
  fun _i _x hx => hx.1

theorem prod_snd (T₁ T₂ : StructureTower ι α) :
    NatInclusion (prod T₁ T₂) T₂ :=
  fun _i _x hx => hx.2

-- 普遍性: S が両方に含まれるなら積に含まれる
theorem prod_univ {S T₁ T₂ : StructureTower ι α}
    (h₁ : NatInclusion S T₁) (h₂ : NatInclusion S T₂) :
    NatInclusion S (prod T₁ T₂) :=
  fun i _x hx => ⟨h₁ i hx, h₂ i hx⟩

-- 積は最大の下界（infimum）
theorem prod_le_left (T₁ T₂ : StructureTower ι α) :
    NatInclusion (prod T₁ T₂) T₁ := prod_fst T₁ T₂

theorem prod_le_right (T₁ T₂ : StructureTower ι α) :
    NatInclusion (prod T₁ T₂) T₂ := prod_snd T₁ T₂

-- ──────────────────────────────────────────
-- §4-3. 余積（levelwise 合併）
-- ──────────────────────────────────────────
/-
  余積の普遍性:
    T₁ + T₂ からの NatInclusion ≃ T₁ からの + T₂ からの NatInclusion の対

  図式:
    T₁ ──→ S
           ↑  
    T₂ ──→  
    は T₁ + T₂ → S に一意に因数分解される
-/

def coprod (T₁ T₂ : StructureTower ι α) : StructureTower ι α where
  level i        := T₁.level i ∪ T₂.level i
  monotone_level := fun _i _j hij _x hx => by
    rcases hx with h | h
    · exact Or.inl (T₁.monotone_level hij h)
    · exact Or.inr (T₂.monotone_level hij h)

-- 入射
theorem coprod_inl (T₁ T₂ : StructureTower ι α) :
    NatInclusion T₁ (coprod T₁ T₂) :=
  fun _i _x hx => Or.inl hx

theorem coprod_inr (T₁ T₂ : StructureTower ι α) :
    NatInclusion T₂ (coprod T₁ T₂) :=
  fun _i _x hx => Or.inr hx

-- 普遍性: 両方が S に含まれるなら余積も含まれる
theorem coprod_univ {S T₁ T₂ : StructureTower ι α}
    (h₁ : NatInclusion T₁ S) (h₂ : NatInclusion T₂ S) :
    NatInclusion (coprod T₁ T₂) S :=
  fun i _x hx => by
    rcases hx with h | h
    · exact h₁ i h
    · exact h₂ i h

-- ──────────────────────────────────────────
-- §4-4. 無限積・余積（Indexed）
-- ──────────────────────────────────────────

/-- 無限積: 任意の族 (Tₛ)_{s:σ} の levelwise 交叉 -/
def iInf {σ : Type*} (T : σ → StructureTower ι α) : StructureTower ι α where
  level i        := ⋂ s, (T s).level i
  monotone_level := fun _i _j hij _x hx =>
    Set.mem_iInter.mpr (fun s => (T s).monotone_level hij (Set.mem_iInter.mp hx s))

/-- 無限余積: 任意の族 (Tₛ)_{s:σ} の levelwise 合併 -/
def iSup {σ : Type*} (T : σ → StructureTower ι α) : StructureTower ι α where
  level i        := ⋃ s, (T s).level i
  monotone_level := by
    intro i j hij x hx
    rcases Set.mem_iUnion.mp hx with ⟨s, hs⟩
    exact Set.mem_iUnion.mpr ⟨s, (T s).monotone_level hij hs⟩

-- iInf の普遍性: S ⊆ Tₛ for all s ⊢ S ⊆ iInf T
theorem iInf_le {σ : Type*} {S : StructureTower ι α}
    {T : σ → StructureTower ι α} (h : ∀ s, NatInclusion S (T s)) :
    NatInclusion S (iInf T) :=
  fun i _x hx => Set.mem_iInter.mpr (fun s => h s i hx)

-- iSup の普遍性: Tₛ ⊆ S for all s ⊢ iSup T ⊆ S
theorem le_iSup {σ : Type*} {S : StructureTower ι α}
    {T : σ → StructureTower ι α} (h : ∀ s, NatInclusion (T s) S) :
    NatInclusion (iSup T) S :=
  fun i _x hx => by
    rcases Set.mem_iUnion.mp hx with ⟨s, hs⟩
    exact h s i hs

-- ──────────────────────────────────────────
-- §4-5. 等化子（Equalizer）
-- ──────────────────────────────────────────
/-
  等化子: 2つの NatInclusion が一致するレベルに制限した塔。

  厳密定義:
    eq(T₁, T₂) の level i = {x ∈ T₁(i) | x ∈ T₂(i) かつ ...}
  ここでは簡略版として "两者に共通する元" = prod と同じ。
  本格的な等化子は射の等化なので、同一台の場合は prod に一致する。
-/

/-- 等化子 = prod（同一台の場合） -/
def equalizer (T₁ T₂ : StructureTower ι α) : StructureTower ι α :=
  prod T₁ T₂

theorem equalizer_universal {S T₁ T₂ : StructureTower ι α}
    (h₁ : NatInclusion S T₁) (h₂ : NatInclusion S T₂) :
    NatInclusion S (equalizer T₁ T₂) :=
  prod_univ h₁ h₂

-- ════════════════════════════════════════════════════════════
-- §5. 閉包モナド ── Galois → Closure → Kleisli / EM
-- ════════════════════════════════════════════════════════════
/-
  モナドの3要素（PartialOrder α 上）:
    対象の作用: T := c : α → α
    η (unit)  : x ≤ c(x)      [le_closure]
    μ (mult)  : c(c(x)) = c(x) [closure_idem]

  対応する塔: towerOfClosure c において
    - unit  → x ∈ level(x)
    - mult  → level(c(x)) = level(x)
-/

section ClosureMonad

variable {α β : Type*} [PartialOrder α] [Preorder β]

def towerOfClosure (c : ClosureOperator α) : StructureTower α α where
  level x        := Set.Iic (c x)
  monotone_level := fun _i _j hij _y hy => le_trans hy (c.monotone hij)

def towerOfGalois {l : α → β} {u : β → α}
    (hgc : GaloisConnection l u) : StructureTower α α :=
  towerOfClosure hgc.closureOperator

-- unit: x ∈ level(x)
theorem mem_own_level (c : ClosureOperator α) (x : α) :
    x ∈ (towerOfClosure c).level x :=
  c.le_closure x

-- mult: level(c(x)) = level(x)
theorem level_closure_eq (c : ClosureOperator α) (x : α) :
    (towerOfClosure c).level (c x) = (towerOfClosure c).level x := by
  simp [towerOfClosure, c.idempotent x]

end ClosureMonad

-- ──────────────────────────────────────────
-- §5-1. Kleisli 圏
-- ──────────────────────────────────────────
/-
  Kleisli圏:
    対象: α の元
    射  : x →_Kl y  iff  x ≤ c(y)
    意味: y の閉包に到達可能 = 近似・飽和の関係
-/

section KleisliEM

variable {α : Type*} [PartialOrder α]

def IsKleisliArrow (c : ClosureOperator α) (x y : α) : Prop := x ≤ c y

-- 恒等 = unit
theorem kleisli_id (c : ClosureOperator α) (x : α) :
    IsKleisliArrow c x x := c.le_closure x

-- 合成
theorem kleisli_comp (c : ClosureOperator α) {x y z : α}
    (hxy : IsKleisliArrow c x y) (hyz : IsKleisliArrow c y z) :
    IsKleisliArrow c x z :=
  calc x ≤ c y   := hxy
    _  ≤ c (c z) := c.monotone hyz
    _  = c z     := c.idempotent z

-- ──────────────────────────────────────────
-- §5-2. Eilenberg–Moore 代数
-- ──────────────────────────────────────────
/-
  EM代数: c(x) ≤ x を満たす元 x
  unit (x ≤ c(x)) と合わせて c(x) = x（閉元）

  EM代数全体 = 閉元の集合 Fix(c)
-/

def EMAlgebras (c : ClosureOperator α) : Set α := {x | c x ≤ x}

theorem emAlgebra_iff_fixed (c : ClosureOperator α) (x : α) :
    x ∈ EMAlgebras c ↔ c x = x :=
  ⟨fun h => le_antisymm h (c.le_closure x),
   fun h => by simp [EMAlgebras, h]⟩

-- c(x) は常に EM代数
theorem closure_mem_emAlgebras (c : ClosureOperator α) (x : α) :
    c x ∈ EMAlgebras c := by
  rw [emAlgebra_iff_fixed]
  exact c.idempotent x

end KleisliEM

-- ════════════════════════════════════════════════════════════
-- §6. OrderHom との同値
-- ════════════════════════════════════════════════════════════
/-
  StructureTower ι α ≃ OrderHom ι (Set α)

  往復が恒等であることを2方向で確認する。
  これにより「本ファイルで新たに加えた代数的制約が
  純粋な OrderHom では表現できない」ことが明確になる。
-/

def toOrderHom (T : StructureTower ι α) : ι →o Set α where
  toFun     := T.level
  monotone' := fun _i _j hij => T.monotone_level hij

def ofOrderHom (h : ι →o Set α) : StructureTower ι α where
  level          := h
  monotone_level := fun _i _j hij => h.monotone hij

theorem orderHom_roundtrip (h : ι →o Set α) :
    toOrderHom (ofOrderHom h) = h := by ext; rfl

theorem tower_roundtrip (T : StructureTower ι α) :
    ofOrderHom (toOrderHom T) = T := by ext; rfl

-- NatInclusion ↔ OrderHom の ≤ が対応する
theorem natInclusion_iff_orderHom_le {T₁ T₂ : StructureTower ι α} :
    NatInclusion T₁ T₂ ↔ toOrderHom T₁ ≤ toOrderHom T₂ :=
  ⟨fun h i => h i, fun h i => h i⟩

-- ════════════════════════════════════════════════════════════
-- §7. Sorry スケルトン（12問 / 🟢×4 / 🟡×4 / 🔴×4）
-- ════════════════════════════════════════════════════════════
/-
  取り組み推奨順: 🟢A → 🟡B → 🔴C

  各問の末尾コメントは「埋めるべき核心」のヒント。
  詰まったら §1–§6 の対応する定義・定理を参照すること。
-/

namespace Exercises

variable {ι α β γ : Type*} [Preorder ι]

-- ──────────────────────────────────────────
-- 🟢 Group A: 定義を展開すれば完成（1〜5行）
-- ──────────────────────────────────────────

/-- A1 🟢  map f → Hom
    f : α → β から Hom T (map f T) を構成せよ。
    【核心】preserves: mem_image.mpr ⟨x, hx, rfl⟩ -/
def homToMap (f : α → β) (T : StructureTower ι α) : Hom T (map f T) where
  toFun     := f
  preserves := by
    intro i x hx
    exact ⟨x, hx, rfl⟩

/-- A2 🟢  comap f → Hom
    f : α → β から Hom (comap f T) T を構成せよ。
    【核心】preserves: mem_preimage.mp hx で直接取り出せる -/
def homFromComap (f : α → β) (T : StructureTower ι β) : Hom (comap f T) T where
  toFun     := f
  preserves := by
    intro i x hx
    exact hx

/-- A3 🟢  iInf の射影
    任意の s : σ に対して NatInclusion (iInf T) (T s) を示せ。
    【核心】Set.mem_iInter.mp hx s で s 成分を取り出す -/
theorem iInf_le_component {σ : Type*}
    (T : σ → StructureTower ι α) (s : σ) :
    NatInclusion (iInf T) (T s) := by
  intro i x hx
  exact Set.mem_iInter.mp hx s

/-- A4 🟢  iSup の入射
    任意の s : σ に対して NatInclusion (T s) (iSup T) を示せ。
    【核心】Set.mem_iUnion.mpr ⟨s, hx⟩ で s 成分に入れる -/
theorem component_le_iSup {σ : Type*}
    (T : σ → StructureTower ι α) (s : σ) :
    NatInclusion (T s) (iSup T) := by
  intro i x hx
  exact Set.mem_iUnion.mpr ⟨s, hx⟩

-- ──────────────────────────────────────────
-- 🟡 Group B: 補題の選択と組み合わせ（5〜15行）
-- ──────────────────────────────────────────

/-- B1 🟡  map と comap の随伴
    NatInclusion (map f T) S ↔ NatInclusion T (comap f S)
    【核心】
      (→): x ∈ T(i) ⊢ f(x) ∈ (map f T)(i) ⊆ S(i)
      (←): y ∈ (map f T)(i) ⊢ y = f(x), x ∈ T(i) ⊢ x ∈ (comap f S)(i) -/
theorem map_le_iff_le_comap (f : α → β)
    (T : StructureTower ι α) (S : StructureTower ι β) :
    NatInclusion (map f T) S ↔ NatInclusion T (comap f S) := by
  constructor
  · intro h i x hx
    exact h i ⟨x, hx, rfl⟩
  · intro h i y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h i hx

/-- B2 🟡  積の唯一性（普遍性の逆方向）
    S が prod T₁ T₂ に NatInclusion される最大の塔であることを示せ。
    具体的に: NatInclusion S T₁ ∧ NatInclusion S T₂ ↔ NatInclusion S (prod T₁ T₂)
    【核心】prod_univ と prod_fst / prod_snd の組み合わせ -/
theorem prod_univ_iff {S T₁ T₂ : StructureTower ι α} :
    NatInclusion S (prod T₁ T₂) ↔ NatInclusion S T₁ ∧ NatInclusion S T₂ := by
  constructor
  · intro h
    exact ⟨NatInclusion.trans h (prod_fst T₁ T₂), NatInclusion.trans h (prod_snd T₁ T₂)⟩
  · intro h
    exact prod_univ h.1 h.2

/-- B3 🟡  Kleisli合成の結合律
    x →_Kl y, y →_Kl z, z →_Kl w ⊢ x →_Kl w
    【核心】kleisli_comp を2回使う -/
theorem kleisli_assoc {α : Type*} [PartialOrder α] (c : ClosureOperator α)
    {x y z w : α}
    (hxy : IsKleisliArrow c x y)
    (hyz : IsKleisliArrow c y z)
    (hzw : IsKleisliArrow c z w) :
    IsKleisliArrow c x w := by
  exact kleisli_comp c (kleisli_comp c hxy hyz) hzw

/-- B4 🟡  EM代数の上界性
    x ∈ EMAlgebras c かつ y ≤ x ならば c(y) ≤ x
    【核心】emAlgebra_iff_fixed で c(x) = x を取り出し、c.monotone hyx を使う -/
theorem emAlgebra_upper_bound {α : Type*} [PartialOrder α]
    (c : ClosureOperator α) {x y : α}
    (hx : x ∈ EMAlgebras c) (hyx : y ≤ x) :
    c y ≤ x := by
  have hfix : c x = x := (emAlgebra_iff_fixed c x).1 hx
  calc
    c y ≤ c x := c.monotone hyx
    _ = x := hfix

-- ──────────────────────────────────────────
-- 🔴 Group C: 圏論的推論・非自明な計算（15行〜）
-- ──────────────────────────────────────────

/-- C1 🔴  関手 map f の射への作用（持ち上げ版）
    g : Hom T₁ T₂ を、β 上の写像 gβ で持ち上げる。
    仮定 `hg` は `gβ ∘ f = f ∘ g` を表す。
    これは「関手 map f : Tower(ι) → Tower(ι)」の射作用であり、
    以下の可換図式を満たす:

         T₁ ──g──→ T₂
         │          │
       map f      map f
         ↓          ↓
      map f T₁ ─?─→ map f T₂

    【核心】
      toFun   : gβ
      preserves: y ∈ map f T₁(i) を ⟨x, hx, rfl⟩ に分解し g.preserves と hg を適用 -/
def mapOnHom (f : α → β) {T₁ T₂ : StructureTower ι α}
    (g : Hom T₁ T₂) (gβ : β → β) (hg : ∀ x, gβ (f x) = f (g x)) :
    Hom (map f T₁) (map f T₂) where
  toFun     := gβ
  preserves := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨g x, g.preserves i hx, ?_⟩
    simp [hg x]

/-- C2 🔴  reindex と iInf の可換性（極限保存）
    reindex は iInf を保つ:
      reindex f hf (iInf T) = iInf (fun s => reindex f hf (T s))

    これは「関手 reindex f が極限を保存する」ことを意味する。
    （additive functor / continuous functor の Tower版）

    【核心】ext i x, simp [reindex, iInf],
            Set.mem_iInter で両方向を整理 -/
theorem reindex_iInf {σ : Type*} {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : σ → StructureTower κ α) :
    reindex f hf (iInf T) = iInf (fun s => reindex f hf (T s)) := by
  ext i x
  rfl

/-- C3 🔴  prod は iInf の特殊例
    prod T₁ T₂ = iInf (fun b : Bool => if b then T₁ else T₂) を示せ。
    （二元族の iInf = 積）

    これが成り立てば「積は iInf の特殊例」として統一的に扱える。

    【核心】
      ext i x
      simp [prod, iInf, Set.mem_iInter]
      Bool の場合分け: b = true と b = false -/
theorem prod_eq_iInf_bool (T₁ T₂ : StructureTower ι α) :
    prod T₁ T₂ = iInf (fun b : Bool => if b then T₁ else T₂) := by
  ext i x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro b
    cases b with
    | false =>
        simpa using hx.2
    | true =>
        simpa using hx.1
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa using (Set.mem_iInter.mp hx true)
    · simpa using (Set.mem_iInter.mp hx false)

/-- C4 🔴  Galois接続の単調性が NatInclusion を誘導
    2つの Galois接続 (l₁, u₁), (l₂, u₂) : α ⇄ β について、
    ∀ x, l₁ x ≤ l₂ x ならば NatInclusion (towerOfGalois hgc₂) (towerOfGalois hgc₁)

    （l が大きいほど閉包 u∘l も大きく、塔の各層が広くなる）

    数学的背景:
      y ≤ u₁(l₁(x)) を示したい。
      l₁(x) ≤ l₂(x) より u₂(l₂(x)) が... 実は向きを確認すること。
      GaloisConnection では l₁ ≤ l₂ ⊢ u₂∘l₂ ≤ u₁∘l₁ は一般には不成立。
      正しい方向: l₁ ≤ l₂ かつ u₁ ≤ u₂ ⊢ u₁∘l₁ ≤ u₂∘l₂

    【核心】
      NatInclusion を展開: ∀ x, y ≤ u₁(l₁(x)) ⊢ y ≤ u₂(l₂(x))
      le_trans を使い u₁(l₁(x)) ≤ u₂(l₂(x)) を示す
      GaloisConnection.closureOperator と ClosureOperator.monotone を活用 -/
theorem galois_natInclusion {α β : Type*} [PartialOrder α] [Preorder β]
    {l₁ l₂ : α → β} {u₁ u₂ : β → α}
    (hgc₁ : GaloisConnection l₁ u₁) (hgc₂ : GaloisConnection l₂ u₂)
    (hl : ∀ x, l₁ x ≤ l₂ x)
    (hu : ∀ y, u₁ y ≤ u₂ y) :
    NatInclusion (towerOfGalois hgc₁) (towerOfGalois hgc₂) := by
  intro x y hy
  change y ≤ u₂ (l₂ x)
  exact le_trans hy ((hu (l₁ x)).trans (hgc₂.monotone_u (hl x)))

end Exercises

end StructureTower

end BourbakiGuide
