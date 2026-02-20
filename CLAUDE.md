# CLAUDE.md

このファイルは `lean-experiments` ディレクトリにおいて Claude Code が作業する際のローカルルールとコンテキストを定義する「種」です。

## 1. プロジェクトのコンテキスト

- **目的**: Lean 4 / Mathlib4 による数学の形式化（Zorn の補題、順序論など）の実験と、対応する LaTeX ノートの作成。
- **主要な構成**:
  - `src/MyProjects/OrderNotes/`: Lean 4 の証明・定義
  - `TeX/OrderNotes/`: 人間向けの解説ノート（LuaTeX 想定）
  - `lakefile.lean`, `lean-toolchain`: ビルドと依存の前提

## 2. 関連ドキュメントとの棲み分け

- 運用手順・検証コマンド・編集ポリシーの詳細は **`AGENTS.md`** を参照する。
- TeX 作成時の定型ルール（図式・AI disclosure など）は **`GEMINI.md`** も参照する。

## 3. Claude Code に特有のルール

1. **言語**: 返答や追加コメントは基本的に日本語で行う。
2. **最小差分**: 既存証明を壊さないよう、変更は最小限にとどめる。`sorry` は極力増やさない。
3. **Mathlib 優先**: 独自実装より `Mathlib` の既存 API を優先する。
4. **確認してから編集**: 変更対象ファイルを必ず先に読んでから編集する。

## 4. 検証コマンド

```bash
lake build                                                        # 全体ビルド
lake env lean src/MyProjects/OrderNotes/ZornsLemmaMathlib.lean    # 単体確認
lake env lean src/MyProjects/OrderNotes/ZornsLemma.lean           # 単体確認
```

## 5. この CLAUDE.md の育て方

- 作業後に「再発しそうなルール」を 1 行だけ追加する。
- 3 回以上繰り返した手順は上のセクションに昇格する。
- 使わなくなったルールは削除し、ファイルを短く保つ。

<!-- 種：今後ここに追記していく -->
<!-- - [ ] よく使う Mathlib の補題・タクティクのメモ -->
<!-- - [ ] Claude がよく間違えるパターンや error-fix-log から得た教訓 -->
<!-- - [ ] TeX 記法の好み（\varnothing vs \emptyset など） -->
