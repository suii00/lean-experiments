import Lake
open Lake DSL

package «myproject» {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

@[default_target]
lean_lib MyProjects where
  srcDir := "src"
  globs := #[.submodules `MyProjects]  -- src/MyProjects/以下を全部対象に

/-!
```

**対応するディレクトリ構成：**
```
lean-experiments/          ← リポジトリルート
├── lakefile.lean
├── lake-manifest.json
├── .lake/                 ← 自動生成（gitignore推奨）
└── src/
    └── MyProjects/        ← ここ以下がすべてビルド対象
        ├── Main.lean
        └── （任意のサブフォルダ・ファイル）
-/
