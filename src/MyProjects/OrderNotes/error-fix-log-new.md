### エラー修正ログ
- エラー概要：
  - `lake build` 時に `src/Myprojects/OrderNotes/ZornsLemmaMathlib.lean` でビルド失敗。
  - 主因は `Mathlib.Order.Chain` の `bad import` と、`sorry` を含む未完了定理の残存。

- 原因：
  - mathlib `v4.28.0` のモジュール構成に対し、import が古い/不一致だった。
  - 応用節の証明（部分写像拡張・超フィルター拡張）が骨格のみで、型検査を通過しなかった。

- 修正内容：
  - import を整理。
    - 削除: `Mathlib.Order.Chain`, `Mathlib.Data.Set.Function`, `Mathlib.Order.WellFounded`
    - 追加: `Mathlib.SetTheory.Cardinal.Order`
  - `zorn_nonempty` を空チェーン分岐まで実装。
  - `zorn_implies_ac_set`, `zorn_implies_ac` の `sorry` を除去して実装。
  - 整列定理の記述を `WellOrderOn`（`{ r : α → α → Prop // IsWellOrder α r }`）に揃えて定式化。
  - `maximal_partial_map_extension` を Zorn 補題で実装。
  - `ultrafilter_extension_pattern` を Zorn 補題で実装。
  - `unnecessarySimpa` 警告を解消。

- 修正が正しい理由：
  - import の不一致が解消され、該当の `bad import` が消える。
  - `sorry` が全て具体証明に置換され、未完了項が残らない。
  - 最大元主張が `zorn_subset_version` / `zorn_nonempty` の型に沿って閉じており、結論が型的に一貫している。

- 動作確認：
  - 実行コマンド：`lake build`
  - 実行ディレクトリ：`C:\Users\swan0\repo\lean-experiments`
  - 結果：`Build completed successfully (812 jobs).`

- どういう意図でこの実装に至ったかメモ
  - ブルバキ流に、先に定義レイヤーを固定し、その上で定理を構造的に接続する方針を採用。
  - Lean では依存型の煩雑化を抑え、mathlib 既存定理（`zorn_le₀` 等）へ寄せて安定性と可読性を優先。
  - 目的を「理論の見通し」と「壊れにくいビルド」の両立に置き、骨格コメントより実証明を優先した。
