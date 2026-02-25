# P3_Calculus エラー修正ログ

対象ファイル: `src/MyProjects/SetNotes/P3_Calculus.lean`  
作業日: 2026-02-25

### エラー概要：
- `lake env lean src/MyProjects/SetNotes/P3_Calculus.lean` 実行時に import エラーが発生した。
- `sorry` が 5 件残っていた。
- 追加で、現行 mathlib API との不一致による型エラー・構文エラー（コメント形式含む）が発生した。

### 原因：
- 旧パスの import を使っていた（例: `Mathlib.MeasureTheory.Integral.FundThmCalculus`）。
- 平均値の定理・単調性・FTC・Taylor で使う補題のシグネチャが現行 mathlib とずれていた。
- `MonotonOn` の綴り誤り（正しくは `MonotoneOn`）。
- 宣言に紐づかない doc comment (`/-- ... -/`) があり、パーサが `lemma` を期待して失敗した。

### 修正内容：
- import を現行 mathlib に合わせて更新した。
  - `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`
  - `Mathlib.Topology.Order.IntermediateValue`
  - `Mathlib.Analysis.SpecialFunctions.Exponential`
- `sorry` だった 5 定理を実装した。
  - `rolle`
  - `mean_value_theorem`
  - `monotone_of_deriv_nonneg`
  - `bolzano`
  - `exp_taylor_converges`
- FTC の補題呼び出しを現行シグネチャへ修正した（`uIcc` と `StronglyMeasurableAtFilter` を含む形）。
- `exp` の Taylor 収束は `NormedSpace.expSeries_div_hasSum_exp` から `tendsto_sum_nat` を使って示した。
- 宣言に紐づかない doc comment を通常コメント (`/- ... -/`) に変更した。

### 修正が正しい理由：
- すべての修正は mathlib の既存定理を使っており、新規公理や `sorry` を追加していない。
- 旧 API 依存を除去し、現行 API の定理名・引数型に整合する形に統一した。
- ファイル全体が Lean で型検査を通過している。

### 動作確認：
- 単体確認: `lake env lean src/MyProjects/SetNotes/P3_Calculus.lean` → 成功
- 全体確認: `lake build`（作業ディレクトリ: `c:\Users\swan0\repo\lean-experiments`）→ 成功
  - `Built MyProjects.SetNotes.P3_Calculus`
  - `Build completed successfully`

### どういう意図でこの実装に至ったかメモ
- 方針は「最小差分で壊れている箇所だけを直し、mathlib 標準 API へ寄せる」。
- Bourbaki 的な構成（章立て・主張）を維持しつつ、証明スクリプトだけを現行環境で動く形へ整えた。
- 将来の再発を防ぐため、非推奨 import とコメント形式由来の構文エラーを先に潰し、次に各定理を局所的に埋める順で進めた。
