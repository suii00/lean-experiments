# lean-experiments

**Lean 4 / Mathlib4** の学習目的で、Codex（OpenAI）・Claude Code（Anthropic）・
Antigravity（Google DeepMind）などの AI ツールを用いて構築している実験リポジトリです。

## StructureTower

AI が生成したアイデアを出発点に、定義・公理・反例・Lean 形式化としてこのリポジトリで整備しています。


### 構造の階層を意識する
```
Set → Preorder → PartialOrder → Lattice → DistribLattice
   ↘ Magma → Semigroup → Monoid → Group → CommGroup
      ↘ TopologicalSpace → HausdorffSpace → NormalSpace
```

## ビルド
```bash
lake build
```

## AI エージェントの設定

各ツール向けの作業ルールを以下のファイルで管理しています。

- [AGENTS.md](./AGENTS.md) — 共通ガイド・作業履歴
- [CLAUDE.md](./CLAUDE.md) — Claude Code 用ローカルルール
- [GEMINI.md](./GEMINI.md) — Antigravity 用ルール
