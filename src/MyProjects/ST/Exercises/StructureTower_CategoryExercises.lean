/-
  StructureTower 圏論的基礎演習
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  難易度: レベル1（基礎）
  カテゴリ: 圏論的視点（categorical aspects）

  目標:
    StructureTower の射（Hom）が圏をなすことを確認し、
    基本的な関手的性質を空欄補完で体得する。

  前提知識:
    - Lean 4 の基本タクティク（intro, exact, simp, ext, funext）
    - 圏の定義（対象・射・恒等射・合成・結合律）
    - 集合の基本操作（MapsTo, image, preimage）

  学習の流れ:
    §C1. Hom の外延性         — 射が等しいための条件
    §C2. 圏の公理             — 恒等律・結合律
    §C3. map / comap の関手性 — 共変・反変関手
    §C4. 忘却写像             — Hom → (α → β) の整合性
    §C5. reindex の関手性     — 添字変換と射の整合

  各空欄を埋めてください。
  ヒントはコメントで段階的に与えています。
    Hint-1: 大まかな方針
    Hint-2: 使うべき補題やタクティク
    Hint-3: ほぼ答えに近い具体的指示
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

variable {ι α β γ δ : Type*} [Preorder ι]

theorem level_monotone (T : StructureTower ι α) : Monotone T.level :=
  fun _ _ hij => T.monotone_level hij

def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

/-- 逆像による引き戻し -/
def comap (f : α → β) (T : StructureTower ι β) : StructureTower ι α where
  level i := f ⁻¹' T.level i
  monotone_level := fun _i _j hij _x hx => T.monotone_level hij hx

/-- 順像による押し出し -/
def map (f : α → β) (T : StructureTower ι α) : StructureTower ι β where
  level i := f '' T.level i
  monotone_level := by
    intro i j hij y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, T.monotone_level hij hx, rfl⟩

/-- 添字変換 -/
def reindex {κ : Type*} [Preorder κ]
    (f : ι → κ) (hf : Monotone f) (T : StructureTower κ α) : StructureTower ι α where
  level i := T.level (f i)
  monotone_level := fun _i _j hij => T.monotone_level (hf hij)

-- ────────────────────────────────────────────────────
-- Hom: 塔の射
-- ────────────────────────────────────────────────────

/-- 同じ添字集合を持つ2つの塔の間のレベル保存写像 -/
structure Hom (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) where
  toFun : α → β
  preserves : ∀ i, MapsTo toFun (T₁.level i) (T₂.level i)

instance (T₁ : StructureTower ι α) (T₂ : StructureTower ι β) :
    CoeFun (Hom T₁ T₂) (fun _ => α → β) where
  coe f := f.toFun

/-- 恒等射 -/
def Hom.id (T : StructureTower ι α) : Hom T T where
  toFun := _root_.id
  preserves := by intro i x hx; exact hx

/-- 射の合成 -/
def Hom.comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) : Hom T₁ T₃ where
  toFun := g.toFun ∘ f.toFun
  preserves := by intro i x hx; exact g.preserves i (f.preserves i hx)

-- ════════════════════════════════════════════════════════════
-- §C1. Hom の外延性（射が等しいための条件）  🟢
-- ════════════════════════════════════════════════════════════

/-!
  圏の公理を証明するには、まず「2つの射がいつ等しいか」を
  明確にする必要がある。Hom は toFun と preserves を持つが、
  preserves は Prop 型なので証明無関係（proof irrelevance）により、
  toFun が等しければ Hom 全体が等しい。
-/

/-- 🟢 Exercise C1a: Hom の外延性
    2つの射は、その基底写像が等しければ等しい。

    Hint-1: Hom の2つのフィールドのうち preserves は Prop 型。
    Hint-2: cases で構造を分解し、congr で toFun の一致に帰着。
    Hint-3: `cases f; cases g; simp` の後に congr か subst を使う。 -/
theorem Hom.ext {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {f g : Hom T₁ T₂} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  simp

/-- 🟢 Exercise C1b: toFun が点ごとに等しければ Hom は等しい。

    Hint-1: C1a に帰着する。
    Hint-2: funext で関数の外延性を使う。
    Hint-3: `Hom.ext (funext h)` -/
theorem Hom.ext_iff {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {f g : Hom T₁ T₂} : f = g ↔ ∀ x, f.toFun x = g.toFun x := by
  constructor
  · intro h x
    simp [h]
  · intro h
    exact Hom.ext (funext h)

-- ════════════════════════════════════════════════════════════
-- §C2. 圏の公理  🟢
-- ════════════════════════════════════════════════════════════

/-!
  StructureTower の射が圏を構成するために必要な3つの公理:
    (1) 左恒等律:  id ∘ f = f
    (2) 右恒等律:  f ∘ id = f
    (3) 結合律:    (h ∘ g) ∘ f = h ∘ (g ∘ f)

  以下では Hom.comp を ∘ の意味で使う。
-/

/-- 🟢 Exercise C2a: 左恒等律
    恒等射を左から合成しても射は変わらない。

    Hint-1: Hom.ext を使って toFun の等しさに帰着する。
    Hint-2: comp と id の定義を展開すれば自明。
    Hint-3: `Hom.ext rfl` -/
theorem Hom.id_comp {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) :
    Hom.comp (Hom.id T₂) f = f := by
  exact Hom.ext rfl

/-- 🟢 Exercise C2b: 右恒等律
    恒等射を右から合成しても射は変わらない。

    Hint-1: C2a と同じ方針。
    Hint-2: `Hom.ext rfl`
    Hint-3: そのまま。 -/
theorem Hom.comp_id {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) :
    Hom.comp f (Hom.id T₁) = f := by
  exact Hom.ext rfl

/-- 🟢 Exercise C2c: 結合律
    射の合成は結合的である。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: 関数の合成は定義的に結合的。
    Hint-3: `Hom.ext rfl` -/
theorem Hom.comp_assoc
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    {T₃ : StructureTower ι γ} {T₄ : StructureTower ι δ}
    (h : Hom T₃ T₄) (g : Hom T₂ T₃) (f : Hom T₁ T₂) :
    Hom.comp (Hom.comp h g) f = Hom.comp h (Hom.comp g f) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §C3. map / comap の関手性  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  map  : (α → β) → ST(ι, α) → ST(ι, β)   は共変関手的
  comap: (α → β) → ST(ι, β) → ST(ι, α)   は反変関手的

  「関手的」とは:
    F(id) = id        （恒等の保存）
    F(g ∘ f) = F(g) ∘ F(f)  （合成の保存、comap は逆順）
-/

/-- 🟢 Exercise C3a: comap は恒等を保つ。
    id で引き戻しても塔は変わらない。

    Hint-1: 塔の外延性（level が等しければ等しい）を使う。
    Hint-2: `ext i x` で level の各点に帰着。
    Hint-3: `ext i x; simp [comap]` -/
theorem comap_id (T : StructureTower ι α) :
    comap _root_.id T = T := by
  ext i x
  simp [comap]

/-- 🟢 Exercise C3b: comap は合成を（逆順で）保つ。

    Hint-1: ext で帰着。
    Hint-2: comap の定義を展開すれば preimage_comp に帰着。
    Hint-3: `ext i x; simp [comap, Set.preimage_comp]` -/
theorem comap_comp (f : α → β) (g : β → γ) (T : StructureTower ι γ) :
    comap f (comap g T) = comap (g ∘ f) T := by
  ext i x
  simp [comap, Set.preimage_comp]

/-- 🟡 Exercise C3c: map は恒等を保つ。

    Hint-1: ext で帰着し、image_id を使う。
    Hint-2: `Set.image_id` が使える。
    Hint-3: `ext i x; simp [map]` -/
theorem map_id (T : StructureTower ι α) :
    map _root_.id T = T := by
  ext i x
  simp [map]

/-- 🟡 Exercise C3d: map は合成を保つ。

    Hint-1: ext で帰着し、image_comp を使う。
    Hint-2: `Set.image_comp` が使える。
    Hint-3: `ext i x; simp [map, Set.image_comp]` -/
theorem map_comp (f : α → β) (g : β → γ) (T : StructureTower ι α) :
    map g (map f T) = map (g ∘ f) T := by
  ext i x
  simp [map]

-- ════════════════════════════════════════════════════════════
-- §C4. 忘却写像の整合性  🟢🟡
-- ════════════════════════════════════════════════════════════

/-!
  「忘却関手」: 塔 T ↦ T.union（基底集合を取り出す）
  射 f : Hom T₁ T₂ は union 上で整合的に振る舞う。
-/

/-- 🟢 Exercise C4a: 射は union を保つ。
    f が Hom ならば、f は T₁.union の元を T₂.union に送る。

    Hint-1: union の定義を展開し、x ∈ ⋃ i, T₁.level i から出発。
    Hint-2: mem_iUnion で分解し、preserves を使う。
    Hint-3: 下の skeleton に従って rcases で i を取り出す。 -/
theorem Hom.mapsTo_union {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) : MapsTo f.toFun T₁.union T₂.union := by
  intro x hx
  simp only [union, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨i, hi⟩
  exact ⟨i, f.preserves i hi⟩
  -- skeleton: rcases hx with ⟨i, hi⟩; exact ⟨i, ?_⟩

/-- 🟡 Exercise C4b: 恒等射は union 上で恒等写像。

    Hint-1: mapsTo_union を直接使ってもよいが、より強い命題を示す。
    Hint-2: Hom.id の toFun は id なので自明。
    Hint-3: `intro x hx; exact hx` -/
theorem Hom.id_mapsTo_union (T : StructureTower ι α) :
    MapsTo (Hom.id T).toFun T.union T.union := by
  exact (Hom.id T).mapsTo_union

/-- 🟡 Exercise C4c: 射の合成は union 上でも合成。

    Hint-1: comp の mapsTo_union は f と g の mapsTo_union の合成。
    Hint-2: `MapsTo.comp` を使う。
    Hint-3: `exact g.mapsTo_union.comp f.mapsTo_union` -/
theorem Hom.comp_mapsTo_union
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) :
    MapsTo (Hom.comp g f).toFun T₁.union T₃.union := by
  simpa [Hom.comp] using g.mapsTo_union.comp f.mapsTo_union

-- ════════════════════════════════════════════════════════════
-- §C5. reindex の関手性と射との整合  🟡
-- ════════════════════════════════════════════════════════════

/-!
  reindex は「添字集合の圏」から「塔の圏」への（反変）関手。
  既に reindex_id と reindex_comp は OrderExamples で証明済みだが、
  ここでは「射との整合」を確認する。
-/

/-- 🟡 Exercise C5a: reindex は Hom を引き戻す。
    f : Hom T₁ T₂ と添字変換 φ : κ → ι があるとき、
    f は reindex された塔の間の Hom でもある。

    Hint-1: Hom を構成する。toFun は同じ f.toFun。
    Hint-2: preserves の証明は f.preserves (φ k) を使う。
    Hint-3: 下の skeleton を完成させる。 -/
def Hom.reindex {κ : Type*} [Preorder κ]
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β}
    (f : Hom T₁ T₂) (φ : κ → ι) (hφ : Monotone φ) :
    Hom (StructureTower.reindex φ hφ T₁) (StructureTower.reindex φ hφ T₂) where
  toFun := f.toFun
  preserves := by
    intro k x hx
    exact f.preserves (φ k) hx
    -- skeleton: intro k x hx; exact f.preserves (φ k) hx

/-- 🟡 Exercise C5b: reindex は恒等射を恒等射に送る。

    Hint-1: Hom.ext で帰着。
    Hint-2: toFun が id であることを確認。
    Hint-3: `Hom.ext rfl` -/
theorem Hom.reindex_id {κ : Type*} [Preorder κ]
    (T : StructureTower ι α) (φ : κ → ι) (hφ : Monotone φ) :
    (Hom.id T).reindex φ hφ = Hom.id (StructureTower.reindex φ hφ T) := by
  exact Hom.ext rfl

/-- 🟡 Exercise C5c: reindex は合成を保つ。

    Hint-1: Hom.ext で帰着。
    Hint-2: 両辺の toFun が g.toFun ∘ f.toFun であることを確認。
    Hint-3: `Hom.ext rfl` -/
theorem Hom.reindex_comp {κ : Type*} [Preorder κ]
    {T₁ : StructureTower ι α} {T₂ : StructureTower ι β} {T₃ : StructureTower ι γ}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) (φ : κ → ι) (hφ : Monotone φ) :
    (Hom.comp g f).reindex φ hφ = Hom.comp (g.reindex φ hφ) (f.reindex φ hφ) := by
  exact Hom.ext rfl

-- ════════════════════════════════════════════════════════════
-- §C6. 発展問題: map が Hom を誘導する  🟡
-- ════════════════════════════════════════════════════════════

/-!
  写像 f : α → β は、任意の塔 T : ST(ι, α) に対して
  T から map f T への Hom を自然に誘導する。
  これは「f の持ち上げ（lifting）」に相当する。
-/

/-- 🟡 Exercise C6a: 写像は自然な Hom を誘導する。

    Hint-1: toFun は f そのもの。
    Hint-2: preserves は「x ∈ T.level i ならば f x ∈ f '' T.level i」。
    Hint-3: `intro i x hx; exact ⟨x, hx, rfl⟩` -/
def Hom.ofMap (f : α → β) (T : StructureTower ι α) :
    Hom T (map f T) where
  toFun := f
  preserves := by
    intro i x hx
    exact ⟨x, hx, rfl⟩

/-- 🟡 Exercise C6b: ofMap は合成と整合する。

    Hint-1: Hom.ext で toFun に帰着。
    Hint-2: 両辺の toFun はどちらも g ∘ f。
    Hint-3: ただし codomain の塔が異なるため、map_comp を使って書き換える必要がある。 -/
-- この問題は map_comp の結果を使うため、C3d を先に解くこと。
-- 型が合わないため、まず map_comp による塔の等式を経由する必要がある。
-- 以下は型の整合を確認する簡易版:
theorem Hom.ofMap_toFun_comp (f : α → β) (g : β → γ) (T : StructureTower ι α) :
    (Hom.ofMap (g ∘ f) T).toFun = (Hom.ofMap g (map f T)).toFun ∘ (Hom.ofMap f T).toFun := by
  rfl
  -- Hint-3: `rfl`

-- ════════════════════════════════════════════════════════════
-- §Summary. 演習のまとめ
-- ════════════════════════════════════════════════════════════

/-!
  ここまでの演習で確認したこと:

  1. **Hom の外延性** (C1):
     射の等しさは基底写像の等しさで決まる。

  2. **圏の公理** (C2):
     StructureTower と Hom は圏を構成する（id, comp, assoc）。

  3. **map/comap の関手性** (C3):
     map は共変関手、comap は反変関手として振る舞う。

  4. **忘却写像** (C4):
     union への制限は関手的な忘却を与える。

  5. **reindex の関手性** (C5):
     添字変換は射を自然に引き戻す。

  6. **map による Hom の誘導** (C6):
     任意の写像 f が T → map f T の自然な射を与える。

  次のステップ:
  - StructureTower_EscapeExercises.lean の Direction II（次数付き構造）
  - Mathlib の CategoryTheory を用いた正式な圏インスタンスの定義
  - 自然変換としての comap → map の随伴（adjunction）の形式化
-/

end StructureTower

end BourbakiGuide
