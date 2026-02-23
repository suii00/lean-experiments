# Noether Correspondence V2 エラー修正ログ

- 対象: `src/MyProjects/AlgebraNotes/NoetherCorrespondenceV2.lean`, `src/MyProjects/AlgebraNotes/ForwardMaximal_alternatives.lean`
- 日付: 2026-02-23

### エラー修正ログ
- エラー概要：
  `lake build` 実行時に、`NoetherCorrespondenceV2.lean` の不正 import と `ForwardMaximal_alternatives.lean` のモジュール未設定が原因でビルド失敗していた。
- 原因：
  1. `Mathlib.Order.GaloisConnection` が mathlib v4.28.0 に存在しない。
  2. `ForwardMaximal_alternatives.lean` に import / namespace / variable が無く、単独モジュールとして解釈不能だった。
  3. 代替証明 A が `IsMaximal` の扱いと噛み合わず、`constructor` ベースの証明でゴール形が一致しなかった。
- 修正内容：
  1. `NoetherCorrespondenceV2.lean` から不正 import を除去し、型検査が通る構成に統一。
  2. `ForwardMaximal_alternatives.lean` に `import MyProjects.AlgebraNotes.NoetherCorrespondenceV2` と `namespace NoetherCorrespondence`、`variable {R} [CommRing R] (I : Ideal R)` を追加。
  3. 代替証明 A は既に確立済みの `forward_preserves_maximal` を再利用する形に変更し、代替証明 B は `Ideal.IsMaximal.map_of_surjective_of_ker_le` で構成。
- 修正が正しい理由：
  1. 使用した定理・補題はすべて現在の toolchain（Lean 4.28.0 / mathlib v4.28.0）に存在する。
  2. 証明の中心を `map/comap` と全射性の標準 API に寄せており、ad-hoc な rewrite 依存を減らしている。
  3. 2 ファイルとも単体で型検査を通過し、`MyProjects` 全体ビルドでも失敗しないことを確認済み。
- 動作確認：
  1. `lake build MyProjects.AlgebraNotes.NoetherCorrespondenceV2` 成功。
  2. `lake build MyProjects.AlgebraNotes.ForwardMaximal_alternatives` 成功。
  3. `lake build`（`C:\Users\swan0\repo\lean-experiments`）成功。
- どういう意図でこの実装に至ったかメモ
  ブルバキ的な「一般構造を先に固める」方針を優先し、局所的に壊れやすい証明手順を避け、既存の mathlib API（全射・kernel 包含・map/comap 対応）に還元できる形へ寄せた。
