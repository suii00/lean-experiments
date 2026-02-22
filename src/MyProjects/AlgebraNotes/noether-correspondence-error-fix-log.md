# Noether Correspondence Theorem エラー修正ログ

- 対象: `src/MyProjects/AlgebraNotes/Noether Correspondence Theorem.lean`
- 日付: 2026-02-22

## エラー修正ログ
- エラー概要：
  `lake env lean` / `lake build` が通らず、import 不整合・型推論停止・証明スクリプト不整合・`sorry` 残存でビルド失敗していた。
- 原因：
  1. mathlib v4.28.0 で存在しない import（`Mathlib.Order.GaloisConnection`）を参照していた。  
  2. `Submodule.mem_map` / `Submodule.mem_comap` の直接利用で型情報が不足し、推論が停止していた。  
  3. 商写像まわりの等式変形（`Ideal.Quotient.eq` の向き）が不適切で rewrite が失敗していた。  
  4. `IdealOver I ≃ Ideal (R ⧸ I)` を `theorem` で宣言しており、非 `Prop` 宣言として不正だった。  
  5. 最大イデアル保存の証明が現在 API と噛み合っておらず、途中に `sorry` が残っていた。
- 修正内容：
  1. 不要かつ不正な import を削除。  
  2. `mem_map_iff` / `mem_comap_iff` を明示的に型が確定する形へ修正。  
  3. `comap_map_eq` の核心部分を `Ideal.Quotient.eq.mp hrs.symm` で整合する向きに修正。  
  4. 対応同値 `noether_correspondence` を `def` 化。  
  5. 素イデアル・最大イデアル保存は `Ideal.map_isPrime_of_surjective`、`Ideal.IsMaximal.map_of_surjective_of_ker_le`、`Ideal.comap_isPrime`、`Ideal.comap_isMaximal_of_surjective` を用いて再構成。  
  6. `sorry` を全削除し、最終定理まで接続。
- 修正が正しい理由：
  1. すべて mathlib v4.28.0 に存在する定理・補題のみを使用している。  
  2. 証明は「商写像の全射性」「kernel に関する包含」「map/comap の標準対応」という一般定理に還元されており、個別の ad-hoc な推論に依存しない。  
  3. 最終的に `noether_correspondence_complete` まで型検査を通過し、途中の未証明項がない。
- 動作確認：
  1. `lake env lean "src/MyProjects/AlgebraNotes/Noether Correspondence Theorem.lean"` 成功。  
  2. `lake build`（`C:\Users\swan0\repo\lean-experiments`）成功。  
  3. `sorry` 検索結果は 0 件（当該ファイル）。
- どういう意図でこの実装に至ったかメモ：
  まず「ブルバキ的に一般構造で押し切る」方針を取り、手作業で複雑化した最大イデアル証明を mathlib の既存同型・map/comap 補題へ寄せた。これにより、局所的な rewrite 事故や API 変更耐性の低い証明を避け、再利用性と保守性を優先した実装になった。
