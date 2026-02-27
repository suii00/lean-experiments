# AGENTS.md

このファイルは `C:\Users\swan0\repo\lean-experiments` 直下を対象にした、エージェント作業ガイドです。

## 1. 目的
- Lean 4 / Mathlib での実験を、壊れにくく継続しやすい形で進める。
- `src` の証明コードと `TeX` のノートを、必要な範囲で同期する。

## 2. このリポジトリで触る場所
- `src/MyProjects/OrderNotes/*.lean`: 証明・定義の本体
- `TeX/OrderNotes/*.tex`: 人間向けの解説ノート
- `src/MyProjects/OrderNotes/error-fix-log.md`: 失敗/修正の履歴
- `lakefile.lean`, `lean-toolchain`: ビルドと依存の前提

## 3. 作業の基本手順
1. 変更対象の `.lean` と対応する `.tex` を確認する。
2. Lean 側を最小差分で修正する（不要な大規模リネームを避ける）。
3. 必要なら `error-fix-log.md` に「何が壊れて何を直したか」を追記する。
4. 最後にビルドで確認する。

## 4. 検証コマンド
- 全体確認: `lake build`
- 単体確認: `lake env lean src/MyProjects/OrderNotes/ZornsLemmaMathlib.lean`
- 単体確認: `lake env lean src/MyProjects/OrderNotes/ZornsLemma.lean`

## 5. Lean 編集ポリシー
- 可能な限り `sorry` を増やさない。
- 既存の mathlib API（例: `Mathlib.Order.Zorn`）を優先して使う。
- 定理名・定義名は既存の文脈（`zorn_*`, `AC*`, `Est*` など）に合わせる。
- 英語/日本語コメントは混在可。ただし文脈を崩さない。

## 6. TeX との同期ポリシー
- 数学的主張を変更したら、対応する `TeX/OrderNotes/*.tex` の記述ズレを点検する。
- ただし「証明スクリプトの局所リファクタ」は TeX 更新不要な場合がある。

## 7. この AGENTS.md の育て方（種）
- 各作業後に「再発しそうなルール」を 1 行だけ追加する。
- 3 回以上繰り返した手順は、`3. 作業の基本手順` または `4. 検証コマンド` に昇格する。
- 使わなくなったルールは削除し、ファイルを短く保つ。
- `Subgroup` の lattice を使うときは `Mathlib.Algebra.Group.Subgroup.Lattice` を import する（`Mathlib.GroupTheory.Subgroup.Lattice` は存在しない）。
- 新規 `.lean` 追加時は、`lake build` の前に `lake env lean <対象ファイル>` で単体確認する。
- 「最小元存在」と「WellFounded」を往復する証明では `WellFounded.wellFounded_iff_has_min` を優先利用する。
- `MonoidHom` を使うときは `Mathlib.Algebra.Group.Hom.Basic` を import し、像は必要に応じて `Set.range f` で扱う。
- `Homeomorph` の補題を使うときは `Mathlib.Topology.Homeomorph.Lemmas` を import する（`Mathlib.Topology.Homeomorph` 単体はない）。
- `ContractingWith` の存在定理は `ContractingWith.exists_fixedPoint`（`existsFixedPoint` ではない）を使う。
- 区間積分の基本定理を使うときは `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` を import する（旧 `Mathlib.MeasureTheory.Integral.FundThmCalculus` は存在しない）。
- `GaloisConnection` と `ClosureOperator` を往復するときは `gc.closureOperator` と `closureOperator_gi_self` を優先利用する。
- `ClosureOperator` の冪等性は `c.idempotent` を使う（`closure_idem` は現行 API にない）。
- ` /-- ... -/ ` の doc コメントは必ず直後に宣言を置く（説明だけ残す場合は `/- ... -/` にする）。
- CI の `sorry` 検出はコメントやコメントアウト行の文字列にも反応するため、`.lean` 内に `sorry` という語を残さない。
- `Nat.find` / `Nat.find_spec` / `Nat.find_min'` を使うときは `Mathlib.Data.Nat.Find` を import し、必要に応じて `classical` で `DecidablePred` を供給する。
- ゴールが `let T := ...; ...` の形なら `intro` 前に `dsimp` で `let` を展開し、変数取り違えを防ぐ。
