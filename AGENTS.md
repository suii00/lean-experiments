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
