# エラー修正ログ: StructureTower_EscapeExercises.lean

- 対象ファイル: `src/MyProjects/ST/BeyondOrderHom/StructureTower_EscapeExercises.lean`
- 実施日: 2026-02-27

---

### エラー修正ログ
- エラー概要：
  `StructureTower_EscapeExercises.lean` の未実装箇所を埋めた後、単体チェックで以下が発生した。
  1. `Mathlib.GroupTheory.Subgroup.Basic` の `.olean` が存在しない
  2. `OrderedAddCommMonoid` が unknown identifier
  3. `Nat.find` / `Nat.find_spec` / `Nat.find_min'` が unknown または `DecidablePred` 不足
  4. `push_neg` / `zero_ne_one` 依存部分で証明が不安定

- 原因：
  1. この環境の mathlib では `Subgroup` の import パスが異なる
  2. この toolchain で `OrderedAddCommMonoid` が直接使えず、要求公理に対して型クラス指定が過剰だった
  3. `Nat.find` 系は `Mathlib.Data.Nat.Find` の import と場合によって `classical` が必要
  4. 末尾 example の反証で tactic 依存を増やしており、環境差分に弱かった

- 修正内容：
  1. import を `Mathlib.GroupTheory.Subgroup.Basic` から `Mathlib.Algebra.Group.Subgroup.Lattice` に変更
  2. `FilteredRing` の添字側制約を `[Preorder ι] [AddMonoid ι]` に調整
  3. `Mathlib.Data.Nat.Find` を追加し、`rank` / `rank_spec` / `rank_le` で `classical` を付与
  4. 末尾 example を tactic 依存の少ない直接証明に書き換え
  5. ファイル内の未実装箇所をすべて証明で充填し、`sorry` 文字列を除去

- 修正が正しい理由：
  1. 使っている定数・定理が、実際にこの環境で解決可能な import に一致している
  2. `FilteredRing` で実際に使っているのは「順序」「加法」「環」のみで、`mul_mem : level (i + j)` には `[Preorder] + [AddMonoid]` で十分
  3. `Nat.find` 系の定理は `Mathlib.Data.Nat.Find` 由来であり、`classical` により必要な決定可能性を供給できる
  4. 末尾 example は `{1}` に `0` が入らない事実 (`Int.zero_ne_one`) で直接矛盾を作るため、証明の依存が明確
  5. `lake env lean` と `lake build` の両方を通過しており、ローカル整合性だけでなく全体整合性も確認済み

- 動作確認：
  1. `lake env lean src/MyProjects/ST/BeyondOrderHom/StructureTower_EscapeExercises.lean` 成功
  2. `lake build`（実行場所: `C:\Users\swan0\repo\lean-experiments`）成功  
     `Build completed successfully (8045 jobs).`

- どういう意図でこの実装に至ったかメモ：
  ブルバキ的な「構造を先に置く」方針を保つため、定義の意味を変えずに環境差分だけ吸収する最小修正を優先した。  
  具体的には、(a) 利用可能な mathlib API へ寄せる、(b) 証明は輸送（monotonicity/comap/map）中心で統一する、(c) tactic 依存を減らし可搬性を上げる、の3点を軸に実装した。

