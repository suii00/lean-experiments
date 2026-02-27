/-
  StructureTower 圏論的発展演習（レベル2）
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  難易度: レベル2（中級）
  前提: StructureTower_CategoryExercises.lean（レベル1）を完了していること

  目標:
    StructureTower の圏を7つの視点から掘り下げ、
    圏論的な思考パターンを穴埋め補完で体得する。

  学習の流れ:
    §F1. 層関手と自然変換     — 各レベルへの「評価」が関手をなす
    §F2. 大域切断関手         — 全レベル共通の元を取り出す
    §F3. 同型射               — 逆射・Equiv・対称・推移
    §F4. 直積と射影           — レベルごとの積の構成
    §F5. 直積の普遍性         — 圏論的極限としての積
    §F6. 自由構造塔           — const の普遍性と随伴への準備
    §F7. 射の像と直積の関手性 — prodMap と map の合流

  ヒントの読み方（前回と同じ）:
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
-- §0. Core definitions & Level 1 results
-- ════════════════════════════════════════════════════════════

@[ext]
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j : ι⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α β γ δ : Type*} [Preorder ι]

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

def comap (f : α → β) (T : StructureTower ι β) : StructureTower ι α where
  level i := f ⁻¹' T.level i
  monotone_level := fun _i _j hij _x hx => T.monotone_level hij hx

def map (f : α → β) (T : StructureTower ι α) : StructureTower ι β where
  level i := f '' T.level i
  monotone_level := by
    intro i j hij y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, T.monotone_level hij hx, rfl⟩

def reindex {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) : StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

def const (ι : Type*) [Preorder ι] (S : Set α) : StructureTower ι α where
  level _ := S
  monotone_level := fun _i _j _hij => Subset.refl _

def prod (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    StructureTower ι (α × β) where
  level i := T₁.level i ×ˢ T₂.level i
  monotone_level := fun _i _j hij _p hp =>
    ⟨T₁.monotone_level hij hp.1, T₂.monotone_level hij hp.2⟩

-- ────────────────────────────────────────────────────
-- Hom & Level 1 results（証明済み）
-- ────────────────────────────────────────────────────

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

-- Level 1 で証明済みの公理（再掲）
theorem Hom.id_comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : Hom.comp (Hom.id T₂) f = f := Hom.ext rfl

theorem Hom.comp_id {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : Hom.comp f (Hom.id T₁) = f := Hom.ext rfl

theorem Hom.comp_assoc
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ} {T₄ : StructureTower ι δ}
    (h : Hom T₃ T₄) (g : Hom T₂ T₃) (f : Hom T₁ T₂) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §F1. 層関手と自然変換（Layer Functor & Naturality）  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  各レベル i を「評価する」操作は、塔の圏から型の圏への関手を定める。

    対象:  T  ↦  T.level i     （集合を返す）
    射:    f  ↦  f を level i に制限した写像

  さらに i ≤ j に伴う包含射は「自然変換」の構造を持つ。
  これは圏論における「ファイバー関手」の最も基本的な例である。
-/

/-- 射の level i への制限。部分型（subtype）間の写像を返す。 -/
def Hom.restrictLevel {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) (i : ι) :
    ↥(T₁.level i) → ↥(T₂.level i) :=
  fun ⟨x, hx⟩ => ⟨f.toFun x, f.preserves i hx⟩

/-- 🟢 Exercise F1a: 恒等射の制限は恒等写像。

    Hint-1: funext で部分型の元 ⟨x, hx⟩ に分解。
    Hint-2: restrictLevel と Hom.id の定義を展開すれば値が一致。
    Hint-3: `funext ⟨x, hx⟩; rfl` -/
theorem Hom.restrictLevel_id (T : StructureTower ι α) (i : ι) :
    (Hom.id T).restrictLevel i = _root_.id := by
  funext x
  rcases x with ⟨x, hx⟩
  rfl

/-- 🟢 Exercise F1b: 合成射の制限は制限の合成。

    Hint-1: F1a と同じパターン。
    Hint-2: comp の toFun は g.toFun ∘ f.toFun なので定義的に一致。
    Hint-3: `funext ⟨x, hx⟩; rfl` -/
theorem Hom.restrictLevel_comp
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) (i : ι) :
    (Hom.comp g f).restrictLevel i = (g.restrictLevel i) ∘ (f.restrictLevel i) := by
  funext x
  rcases x with ⟨x, hx⟩
  rfl

/-- 単調性が与えるレベル間の包含射（自然変換の成分）。 -/
def levelInclusion (T : StructureTower ι α) {i j : ι} (hij : i ≤ j) :
    ↥(T.level i) → ↥(T.level j) :=
  fun ⟨x, hx⟩ => ⟨x, T.monotone_level hij hx⟩

/-- 🟡 Exercise F1c: 自然性の正方形（naturality square）。

    任意の Hom f と i ≤ j に対して、以下の図式が可換:

        T₁.level i ──restrictLevel i──→ T₂.level i
            │                                │
      levelInclusion                   levelInclusion
            │                                │
            ↓                                ↓
        T₁.level j ──restrictLevel j──→ T₂.level j

    Hint-1: funext ⟨x, hx⟩ で元に分解。
    Hint-2: 両辺とも ⟨f.toFun x, ...⟩ で、値部分は一致。
    Hint-3: `funext ⟨x, hx⟩; rfl` -/
theorem levelInclusion_natural
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) {i j : ι} (hij : i ≤ j) :
    (f.restrictLevel j) ∘ (levelInclusion T₁ hij) =
    (levelInclusion T₂ hij) ∘ (f.restrictLevel i) := by
  funext x
  rcases x with ⟨x, hx⟩
  rfl

/-- 🟡 Exercise F1d: levelInclusion の推移性。
    i ≤ j ≤ k に対して、包含射は合成可能。

    Hint-1: funext ⟨x, hx⟩ で帰着。
    Hint-2: 両辺の値部分は同じ x。
    Hint-3: `funext ⟨x, hx⟩; rfl` -/
theorem levelInclusion_trans (T : StructureTower ι α)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    (levelInclusion T hjk) ∘ (levelInclusion T hij) =
    levelInclusion T (le_trans hij hjk) := by
  funext x
  rcases x with ⟨x, hx⟩
  rfl

-- ════════════════════════════════════════════════════════════
-- §F2. 大域切断関手（Global Sections Functor）  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  union が「すべてのレベルの和」だったのに対し、
  global は「すべてのレベルの共通部分」を取り出す。

    global(T) = ⋂ᵢ T.level i

  union は忘却関手（最も緩い見方）、global は最も厳しい見方。
  射は global を global に送るため、これも関手的に振る舞う。
-/

/-- 大域切断: すべてのレベルに属する元の集合。 -/
def global (T : StructureTower ι α) : Set α := ⋂ i, T.level i

/-- 🟢 Exercise F2a: global は各 level に含まれる。

    Hint-1: iInter の定義を展開する。
    Hint-2: `Set.mem_iInter` を使う。
    Hint-3: `intro x hx; exact Set.mem_iInter.mp hx i` -/
theorem global_subset_level (T : StructureTower ι α) (i : ι) :
    T.global ⊆ T.level i := by
  intro x hx
  exact Set.mem_iInter.mp hx i

/-- 🟢 Exercise F2b: global は union に含まれる。
    （全レベル共通の元は、少なくとも1つのレベルには属する）

    Hint-1: global_subset_level で任意の i に降ろせる。
    Hint-2: 降ろしたら mem_iUnion で union に戻す。
    Hint-3: `intro x hx; exact Set.mem_iUnion.mpr ⟨i, global_subset_level T i hx⟩`
            ただし i : ι が必要。[Nonempty ι] を前提にする。 -/
theorem global_subset_union [Nonempty ι] (T : StructureTower ι α) :
    T.global ⊆ T.union := by
  intro x hx
  rcases ‹Nonempty ι› with ⟨i⟩
  exact Set.mem_iUnion.mpr ⟨i, global_subset_level T i hx⟩

/-- 🟡 Exercise F2c: 射は global を保存する。

    Hint-1: x ∈ global T₁ ⟹ ∀ i, x ∈ T₁.level i。
    Hint-2: f.preserves i で f x ∈ T₂.level i。
    Hint-3: `intro x hx; exact Set.mem_iInter.mpr (fun i => f.preserves i (Set.mem_iInter.mp hx i))` -/
theorem Hom.mapsTo_global {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : MapsTo f.toFun T₁.global T₂.global := by
  intro x hx
  exact Set.mem_iInter.mpr (fun i => f.preserves i (Set.mem_iInter.mp hx i))

/-- 🟡 Exercise F2d: 定数塔の global はその集合自身。

    Hint-1: const の全レベルが S なので、⋂ᵢ S = S。
    Hint-2: `Set.iInter_const` を使う。
    Hint-3: `simp [global, const, Set.iInter_const]` -/
theorem global_const [Nonempty ι] (S : Set α) :
    (const ι S).global = S := by
  ext x
  constructor
  · intro hx
    rcases ‹Nonempty ι› with ⟨i⟩
    exact Set.mem_iInter.mp hx i
  · intro hx
    exact Set.mem_iInter.mpr (fun _ => hx)

-- ════════════════════════════════════════════════════════════
-- §F3. 同型射（Isomorphisms）  🟢🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  圏における同型射: 逆射が存在して、往復が恒等。

  同型は最も強い「構造の等価性」を表す。
  Equiv（型の全単射）からの構成と、射のレベルでの性質を調べる。
-/

/-- 塔の同型射: 往復が恒等射に等しい射の対。 -/
structure Iso (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  hom : Hom T₁ T₂
  inv : Hom T₂ T₁
  hom_inv_id : Hom.comp inv hom = Hom.id T₁
  inv_hom_id : Hom.comp hom inv = Hom.id T₂

/-- 🟢 Exercise F3a: 恒等同型。

    Hint-1: hom も inv も Hom.id。
    Hint-2: id_comp で公理が満たされる。
    Hint-3: 下の skeleton を完成させる。 -/
def Iso.refl (T : StructureTower ι α) : Iso T T where
  hom := Hom.id T
  inv := Hom.id T
  hom_inv_id := by exact Hom.id_comp (Hom.id T)
  inv_hom_id := by exact Hom.id_comp (Hom.id T)

/-- 🟢 Exercise F3b: 同型の対称性。

    Hint-1: hom と inv を入れ替える。
    Hint-2: 公理も入れ替わる。
    Hint-3: フィールドを e の対応するものに置き換えるだけ。 -/
def Iso.symm {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (e : Iso T₁ T₂) : Iso T₂ T₁ where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

/-- 🟡 Exercise F3c: 同型の推移性。

    Hint-1: hom は e₂.hom ∘ e₁.hom、inv は e₁.inv ∘ e₂.inv。
    Hint-2: 公理の証明には comp_assoc と hom_inv_id を組み合わせる。
    Hint-3: rw [Hom.comp_assoc] でカッコを組み替え、
            ← Hom.comp_assoc で内側の合成を作り、
            hom_inv_id → id_comp で潰す。 -/
def Iso.trans {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ}
    (e₁ : Iso T₁ T₂) (e₂ : Iso T₂ T₃) : Iso T₁ T₃ where
  hom := Hom.comp e₂.hom e₁.hom
  inv := Hom.comp e₁.inv e₂.inv
  hom_inv_id := by
    apply Hom.ext
    funext x
    have h₂ : e₂.inv.toFun (e₂.hom.toFun (e₁.hom.toFun x)) = e₁.hom.toFun x := by
      simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e₂.hom_inv_id) (e₁.hom.toFun x)
    have h₁ : e₁.inv.toFun (e₁.hom.toFun x) = x := by
      simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e₁.hom_inv_id) x
    simpa [Hom.comp, h₂] using h₁
    /- 方針:
       (e₁.inv ∘ e₂.inv) ∘ (e₂.hom ∘ e₁.hom)
       = e₁.inv ∘ (e₂.inv ∘ e₂.hom) ∘ e₁.hom   -- assoc ×2
       = e₁.inv ∘ id ∘ e₁.hom                    -- e₂.hom_inv_id
       = e₁.inv ∘ e₁.hom                          -- id_comp
       = id                                        -- e₁.hom_inv_id -/
  inv_hom_id := by
    apply Hom.ext
    funext x
    have h₁ : e₁.hom.toFun (e₁.inv.toFun (e₂.inv.toFun x)) = e₂.inv.toFun x := by
      simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e₁.inv_hom_id) (e₂.inv.toFun x)
    have h₂ : e₂.hom.toFun (e₂.inv.toFun x) = x := by
      simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e₂.inv_hom_id) x
    simpa [Hom.comp, h₁] using h₂
    -- 同じパターンを e₁ と e₂ を入れ替えて適用

/-- 🟡 Exercise F3d: Equiv からの同型構成。
    型の同値 e : α ≃ β と、双方向のレベル保存条件から Iso を作る。

    Hint-1: hom.toFun = e, inv.toFun = e.symm。
    Hint-2: 公理は e.symm_apply_apply と e.apply_symm_apply。
    Hint-3: `Hom.ext (funext e.symm_apply_apply)` 等。 -/
def Iso.ofEquiv (e : α ≃ β)
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι β)
    (hfwd : ∀ i x, x ∈ T₁.level i → e x ∈ T₂.level i)
    (hbwd : ∀ i y, y ∈ T₂.level i → e.symm y ∈ T₁.level i) :
    Iso T₁ T₂ where
  hom := { toFun := e, preserves := fun i x hx => hfwd i x hx }
  inv := { toFun := e.symm, preserves := fun i y hy => hbwd i y hy }
  hom_inv_id := by exact Hom.ext (funext e.symm_apply_apply)
  inv_hom_id := by exact Hom.ext (funext e.apply_symm_apply)

/-- 🟡 Exercise F3e: 同型射はレベルごとに全単射。

    Hint-1: hom_inv_id から f(g(y)) = y、inv_hom_id から g(f(x)) = x。
    Hint-2: Set.BijOn は InjOn と SurjOn の合成。
    Hint-3: congr_fun (congr_arg Hom.toFun e.hom_inv_id) で
            点ごとの等式を取り出す。 -/
theorem Iso.bijOn_level {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (e : Iso T₁ T₂) (i : ι) :
    Set.BijOn e.hom.toFun (T₁.level i) (T₂.level i) := by
  refine ⟨e.hom.preserves i, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := congrArg e.inv.toFun hxy
    have hx' : e.inv.toFun (e.hom.toFun x) = x := by
      simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e.hom_inv_id) x
    have hy' : e.inv.toFun (e.hom.toFun y) = y := by
      simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e.hom_inv_id) y
    calc
      x = e.inv.toFun (e.hom.toFun x) := by simpa using hx'.symm
      _ = e.inv.toFun (e.hom.toFun y) := h
      _ = y := hy'
  · intro y hy
    refine ⟨e.inv.toFun y, e.inv.preserves i hy, ?_⟩
    simpa [Hom.comp, Hom.id] using congr_fun (congr_arg Hom.toFun e.inv_hom_id) y
  /- skeleton:
     refine ⟨e.hom.preserves i, ?_, ?_⟩
     · -- InjOn: e.inv で左キャンセル
       省略
     · -- SurjOn: e.inv で原像を構成
       省略 -/

-- ════════════════════════════════════════════════════════════
-- §F4. 直積と射影（Product & Projections）  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  prod T₁ T₂ は「レベルごとの直積」。
  射影 fst, snd は自然な Hom を与え、これが圏論的積の候補。
-/

@[simp] theorem mem_prod_level (T₁ : StructureTower ι α) (T₂ : StructureTower ι β)
    (i : ι) (p : α × β) :
    p ∈ (prod T₁ T₂).level i ↔ p.1 ∈ T₁.level i ∧ p.2 ∈ T₂.level i :=
  Set.mem_prod

/-- 🟢 Exercise F4a: 第一射影は Hom。

    Hint-1: toFun = Prod.fst。
    Hint-2: preserves は積の membership の左半分。
    Hint-3: `intro i p hp; exact hp.1` -/
def fst (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    Hom (prod T₁ T₂) T₁ where
  toFun := Prod.fst
  preserves := by
    intro i p hp
    exact hp.1

/-- 🟢 Exercise F4b: 第二射影は Hom。 -/
def snd (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    Hom (prod T₁ T₂) T₂ where
  toFun := Prod.snd
  preserves := by
    intro i p hp
    exact hp.2

/-- 🟡 Exercise F4c: 2つの Hom から直積への Hom を作る（prodMap）。
    f : T₁ → T₂, g : S₁ → S₂ から prod T₁ S₁ → prod T₂ S₂。

    Hint-1: toFun p = (f p.1, g p.2)。
    Hint-2: 積の membership は各成分の membership。
    Hint-3: `intro i p hp; exact ⟨f.preserves i hp.1, g.preserves i hp.2⟩` -/
def Hom.prodMap {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {S₁ : StructureTower ι γ} {S₂ : StructureTower ι δ}
    (f : Hom T₁ T₂) (g : Hom S₁ S₂) :
    Hom (prod T₁ S₁) (prod T₂ S₂) where
  toFun p := (f.toFun p.1, g.toFun p.2)
  preserves := by
    intro i p hp
    exact ⟨f.preserves i hp.1, g.preserves i hp.2⟩

/-- 🟡 Exercise F4d: prodMap は恒等射を保つ。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: 両辺とも (p.1, p.2) = p。
    Hint-3: `Hom.ext (funext fun p => Prod.mk.eta)` -/
theorem Hom.prodMap_id (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    Hom.prodMap (Hom.id T₁) (Hom.id T₂) = Hom.id (prod T₁ T₂) := by
  apply Hom.ext
  funext p
  rcases p with ⟨x, y⟩
  rfl

/-- 🟡 Exercise F4e: prodMap は合成を保つ。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: 各成分で comp の定義を展開すれば一致。
    Hint-3: `Hom.ext rfl` -/
theorem Hom.prodMap_comp
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} {T₃ : StructureTower ι γ}
    {S₁ : StructureTower ι δ} {S₂ : StructureTower ι δ} {S₃ : StructureTower ι δ}
    (f₂ : Hom T₂ T₃) (f₁ : Hom T₁ T₂)
    (g₂ : Hom S₂ S₃) (g₁ : Hom S₁ S₂) :
    Hom.prodMap (Hom.comp f₂ f₁) (Hom.comp g₂ g₁) =
    Hom.comp (Hom.prodMap f₂ g₂) (Hom.prodMap f₁ g₁) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §F5. 直積の普遍性（Universal Property of Product）  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  圏論的極限としての積:

  任意の塔 T と射 f : T → T₁, g : T → T₂ に対して、
  pair f g : T → prod T₁ T₂ が **一意に** 存在し、
  fst ∘ pair f g = f  かつ  snd ∘ pair f g = g  を満たす。

      T
     / \
    f   g
   /     \
  T₁ ←── prod T₁ T₂ ──→ T₂
      fst              snd
-/

/-- 🟡 Exercise F5a: 対角射（universal morphism to product）。

    Hint-1: toFun x = (f.toFun x, g.toFun x)。
    Hint-2: preserves は f.preserves と g.preserves の合成。
    Hint-3: `intro i x hx; exact ⟨f.preserves i hx, g.preserves i hx⟩` -/
def Hom.pair {T : StructureTower ι γ}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T T₁) (g : Hom T T₂) : Hom T (prod T₁ T₂) where
  toFun x := (f.toFun x, g.toFun x)
  preserves := by
    intro i x hx
    exact ⟨f.preserves i hx, g.preserves i hx⟩

/-- 🟡 Exercise F5b: fst ∘ pair = 左成分。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: (fst ∘ pair f g).toFun = Prod.fst ∘ (fun x => (f x, g x)) = f.toFun。
    Hint-3: `exact Hom.ext rfl` -/
theorem Hom.fst_pair {T : StructureTower ι γ}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T T₁) (g : Hom T T₂) :
    Hom.comp (fst T₁ T₂) (Hom.pair f g) = f := by
  exact Hom.ext rfl

/-- 🟡 Exercise F5c: snd ∘ pair = 右成分。 -/
theorem Hom.snd_pair {T : StructureTower ι γ}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T T₁) (g : Hom T T₂) :
    Hom.comp (snd T₁ T₂) (Hom.pair f g) = g := by
  exact Hom.ext rfl

/-- 🔴 Exercise F5d: 一意性。射影条件を満たす射は pair に等しい。

    これが圏論的積の本質: 存在だけでなく一意性も要求する。

    Hint-1: Hom.ext で toFun に帰着、funext で点ごとに。
    Hint-2: hf から (h.toFun x).1 = f.toFun x を取り出す。
            hg から (h.toFun x).2 = g.toFun x を取り出す。
    Hint-3: `congr_arg Hom.toFun` で Hom の等式から toFun の等式を、
            `congr_fun` で点ごとの等式を取り出し、`Prod.ext` で結合。 -/
theorem Hom.pair_unique {T : StructureTower ι γ}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T T₁) (g : Hom T T₂)
    (h : Hom T (prod T₁ T₂))
    (hf : Hom.comp (fst T₁ T₂) h = f)
    (hg : Hom.comp (snd T₁ T₂) h = g) :
    h = Hom.pair f g := by
  apply Hom.ext
  funext x
  have h1 : (h.toFun x).1 = f.toFun x := by
    simpa [Hom.comp, fst] using congr_fun (congr_arg Hom.toFun hf) x
  have h2 : (h.toFun x).2 = g.toFun x := by
    simpa [Hom.comp, snd] using congr_fun (congr_arg Hom.toFun hg) x
  exact Prod.ext h1 h2
  /- skeleton:
     apply Hom.ext; funext x
     have h1 := congr_fun (congr_arg Hom.toFun hf) x
     have h2 := congr_fun (congr_arg Hom.toFun hg) x
     -- h1 : (h.toFun x).1 = f.toFun x
     -- h2 : (h.toFun x).2 = g.toFun x
     exact Prod.ext h1 h2  -/

-- ════════════════════════════════════════════════════════════
-- §F6. 自由構造塔と随伴への準備（Free Tower & Adjunction）  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  const ι S は「S を全レベルに一様に配置した塔」。
  global T は「全レベルの共通部分」。

  この2つの操作は随伴的な関係を持つ:

    Hom(const ι S, T)  ≅  { f : α → β | MapsTo f S (global T) }

  左辺: S からの「全レベル保存写像」
  右辺: S を global T に送る写像

  これは const ⊣ global という「随伴の萌芽」である。
-/

/-- 🟡 Exercise F6a: S を全レベルに送る写像は、const S からの Hom を与える。

    Hint-1: const のレベルは常に S。
    Hint-2: hf i が MapsTo を直接与える。
    Hint-3: preserves := hf -/
def Hom.ofConstMap (f : α → β) (S : Set α) (T : StructureTower ι β)
    (hf : ∀ i, MapsTo f S (T.level i)) :
    Hom (const ι S) T where
  toFun := f
  preserves := by
    intro i x hx
    exact hf i hx

/-- 🟡 Exercise F6b: const からの Hom は S を global に送る。

    Hint-1: h.preserves i は MapsTo h.toFun S (T.level i)。
    Hint-2: 全 i について成り立つので、global に入る。
    Hint-3: `intro x hx; exact Set.mem_iInter.mpr (fun i => h.preserves i hx)` -/
theorem Hom.const_mapsTo_global (S : Set α) {T : StructureTower ι β}
    (h : Hom (const ι S) T) :
    MapsTo h.toFun S T.global := by
  intro x hx
  exact Set.mem_iInter.mpr (fun i => h.preserves i hx)

/-- 🟡 Exercise F6c: S を global T に送る写像は const S からの Hom を与える。
    （F6a の global 版）

    Hint-1: MapsTo f S (global T) を各レベルに分解。
    Hint-2: global_subset_level で global ⊆ level i。
    Hint-3: `Hom.ofConstMap f S T (fun i => hf.mono Subset.rfl (global_subset_level T i))` -/
def Hom.ofConstToGlobal (f : α → β) (S : Set α) (T : StructureTower ι β)
    (hf : MapsTo f S T.global) :
    Hom (const ι S) T where
  toFun := f
  preserves := by
    intro i x hx
    exact global_subset_level T i (hf hx)

/-- 🔴 Exercise F6d: 随伴の往復（round-trip）。
    ofConstToGlobal で作った Hom を const_mapsTo_global に通すと元に戻る。

    Hint-1: MapsTo の等式は Set.MapsTo の定義に立ち返れば ext 的に成り立つ。
    Hint-2: 直接 `rfl` or `Iff.rfl` 等で閉じるか確認。
    Hint-3: これは実質的に定義の展開だけで済む。 -/
theorem adjunction_roundtrip (f : α → β) (S : Set α) (T : StructureTower ι β)
    (hf : MapsTo f S T.global) (x : α) (hx : x ∈ S) :
    f x ∈ T.global := by
  exact hf hx
  -- これは hf hx そのもの

-- ════════════════════════════════════════════════════════════
-- §F7. 射の像と直積の関手性（Image & Product Functoriality）  🟡🔴
-- ════════════════════════════════════════════════════════════

/-!
  最後に、map/comap と prod の相互作用を調べる。
  「map は関手的に積と交換する」ことが核心。
-/

/-- 🟡 Exercise F7a: map f は Hom を誘導する（Level 1 の復習強化版）。

    Hint-1: toFun = f。
    Hint-2: x ∈ T.level i なら f x ∈ f '' T.level i。
    Hint-3: `intro i x hx; exact ⟨x, hx, rfl⟩` -/
def Hom.ofMap (f : α → β) (T : StructureTower ι α) :
    Hom T (map f T) where
  toFun := f
  preserves := by
    intro i x hx
    exact ⟨x, hx, rfl⟩

/-- 🟡 Exercise F7b: comap f は逆方向の Hom を誘導する（f が単射のとき）。
    単射条件は map ∘ comap = id を保証する。

    Hint-1: y ∈ (map f (comap f T)).level i は ∃ x, f x ∈ T.level i ∧ f x = y。
    Hint-2: 単射なので x は一意に定まるが、ここでは Hom の構成のみ。
    Hint-3: preserves は preimage の定義から直接。 -/
def Hom.ofComap (f : α → β) (T : StructureTower ι β) :
    Hom (comap f T) T where
  toFun := f
  preserves := by
    intro i x hx
    exact hx

/-- 🟡 Exercise F7c: prod と map の交換。
    map (f × g) (prod T₁ T₂) = prod (map f T₁) (map g T₂)

    ただし f × g は Prod.map f g。

    Hint-1: ext で level の各点に帰着。
    Hint-2: 積の像 = 像の積（Set.image_prod_map を探す）。
    Hint-3: 直接 iff を示す: ⟨a, ⟨ha₁, ha₂⟩, rfl⟩ ↔ ⟨⟨a.1, ha₁, rfl⟩, ⟨a.2, ha₂, rfl⟩⟩ -/
theorem map_prod (f : α → β) (g : γ → δ)
    (T₁ : StructureTower ι α) (T₂ : StructureTower ι γ) :
    map (Prod.map f g) (prod T₁ T₂) = prod (map f T₁) (map g T₂) := by
  ext i p
  constructor
  · rintro ⟨⟨a, c⟩, ⟨ha, hc⟩, hEq⟩
    exact ⟨⟨a, ha, congrArg Prod.fst hEq⟩, ⟨c, hc, congrArg Prod.snd hEq⟩⟩
  · rintro ⟨⟨a, ha, hb⟩, ⟨c, hc, hd⟩⟩
    refine ⟨(a, c), ⟨ha, hc⟩, ?_⟩
    exact Prod.ext hb hd
  /- skeleton:
     ext i ⟨b, d⟩
     simp only [map, prod, Set.mem_image, Set.mem_prod]
     constructor
     · rintro ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩
       exact ⟨⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩⟩
     · rintro ⟨⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩⟩
       exact ⟨(a, c), ⟨ha, hc⟩, rfl⟩ -/

/-- 🔴 Exercise F7d: fst と pair の自然性。
    任意の f : Hom T T' に対して、以下が可換:

        T ──pair (comp f₁ f) (comp f₂ f)──→ prod T₁ T₂
        │                                       │
        f                                    prodMap id id = id
        │                                       │
        ↓                                       ↓
       T' ──────pair f₁ f₂──────────────→ prod T₁ T₂

    Hint-1: 両辺の toFun を比較。
    Hint-2: comp (pair f₁ f₂) f の toFun x = (f₁(f(x)), f₂(f(x)))。
    Hint-3: `exact Hom.ext rfl` -/
theorem Hom.pair_comp {T T' : StructureTower ι γ}
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f₁ : Hom T' T₁) (f₂ : Hom T' T₂) (f : Hom T T') :
    Hom.comp (Hom.pair f₁ f₂) f = Hom.pair (Hom.comp f₁ f) (Hom.comp f₂ f) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §Summary. 全体の振り返り
-- ════════════════════════════════════════════════════════════

/-!
  Level 2 で確認したこと:

  §F1 **層関手**:
    T ↦ T.level i は圏から集合への関手。
    levelInclusion は自然変換。可換正方形が成り立つ。

  §F2 **大域切断**:
    global = ⋂ᵢ level i。union の双対。
    射は global を保存する。const の global は元の集合。

  §F3 **同型射**:
    Iso = 逆射付きの Hom の対。refl / symm / trans。
    Equiv からの構成。レベルごとの全単射。

  §F4 **直積の関手性**:
    fst, snd は Hom。prodMap は関手的（id保存・comp保存）。

  §F5 **直積の普遍性**:
    pair は積への一意な射。fst ∘ pair = f, snd ∘ pair = g。
    一意性: 射影条件を満たす射は pair に限る。

  §F6 **自由構造塔**:
    const ι S は「自由な」塔。
    Hom(const S, T) ≅ MapsTo(S, global T)  ← 随伴の萌芽。

  §F7 **像と直積の交換**:
    map (f × g) (prod T₁ T₂) = prod (map f T₁) (map g T₂)。
    pair の自然性（前合成との交換）。

  ──────────────────────────────────────────────
  次のステップ（Level 3 候補）:
  - Mathlib.CategoryTheory を import して正式な Category インスタンス
  - イコライザ（equalizer）とプルバック（pullback）
  - comap ⊣ map の随伴を CategoryTheory.Adjunction で定式化
  - モナド（ClosureOperator 由来）の Kleisli / Eilenberg-Moore
  ──────────────────────────────────────────────
-/

end StructureTower

end BourbakiGuide
