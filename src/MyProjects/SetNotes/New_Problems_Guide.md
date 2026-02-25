# Bourbaki流Lean 4学習ガイド — 新課題提案 📚

## 既存カバレッジの分析

```
P1          P1_Extended       P1.5 (NEW)        P2              P3 (NEW)        P4 (NEW)
─────────   ──────────────   ──────────────   ──────────────   ──────────────   ──────────────
前順序       Galois接続       環と準同型       測度論           微分の基礎       圏の基礎
半順序       閉包作用素       イデアル         積分論           平均値の定理     関手
束           商群             商環             Lp空間           中間値の定理     自然変換
群準同型     連結性           同型定理         TVS              FTC (基本定理)   米田の補題
コンパクト   同相写像         局所化           Banach空間       Fréchet微分     極限・余極限
有限直積     Urysohn          加群             双対空間         Taylor展開       随伴関手
             完備空間         自由加群         スペクトル       陰関数定理       圏の同値
             普遍射           テンソル積                        凸解析           モナド
                              Noether環                                         Abel圏
                              UFD/PID
                              体の拡大
```

## 依存関係グラフ

```
P1 ─────────┬──→ P1_Extended ──→ P4_CategoryTheory
            │          │
            │          ↓
            ├──→ P1.5_Algebra ──→ P4 (Part IX: Abel圏)
            │          │
            ↓          ↓
     P2_Advanced ←─── P3_Calculus
     Analysis          │
            │          ↓
            └──→ (将来: P5_Probability)
```

---

## 📄 新ファイル詳細

### P1_5_Algebra.lean — 可換代数 (Algèbre Commutative)

**難易度**: 中級〜上級  
**推奨学習時間**: 4〜8週間  
**Bourbaki対応**: Algèbre I, III / Algèbre Commutative I–III, VII

**なぜこれが必要か**:  
P1は群論で終わり、P2はいきなり測度・積分に飛ぶ。環論・加群論は代数学の中心であり、
圏論的視点（P4）への自然な橋渡しでもある。

| パート | 内容 | 証明済み | sorry |
|--------|------|:--------:|:-----:|
| I. 環と準同型 | map_mul, map_add, map_one | 3 | 0 |
| II. イデアル | 和・積、素・極大 | 4 | 0 |
| III. 商環 | 全射性、核、体⟺極大、整域⟺素 | 4 | 0 |
| IV. 同型定理 | 第一・第三同型定理 | 2 | 0 |
| V. 局所化 | 単射性、普遍性 | 0 | 2 |
| VI. 加群 | 像、第一同型、商 | 3 | 0 |
| VII. 自由加群 | 階数の well-definedness | 1 | 0 |
| VIII. テンソル積 | 普遍性 | 1 | 0 |
| IX. Noether環 | 有限生成、ACC | 1 | 1 |
| X. UFD/PID | Noether性、既約⟺素 | 1 | 1 |
| XI. 体の拡大 | 最小多項式の性質 | 2 | 1 |

**合計**: 証明済み 22、演習(sorry) 5

---

### P3_Calculus.lean — 微積分学 (Fonctions d'une variable réelle)

**難易度**: 中級〜上級  
**推奨学習時間**: 4〜6週間  
**Bourbaki対応**: FVR I–II, Topologie IV §6

**なぜこれが必要か**:  
微積分学の基本定理は数学の中核であり、P2の積分論と直結する。
Fréchet微分はBanach空間論（P2 Part V）の自然な続き。

| パート | 内容 | 証明済み | sorry |
|--------|------|:--------:|:-----:|
| I. 微分の基礎 | 定数、恒等、和、積、合成 | 5 | 0 |
| II. 平均値の定理 | Rolle、Lagrange、単調性判定 | 0 | 3 |
| III. 中間値の定理 | IVT、Bolzano | 1 | 1 |
| IV. FTC | Part 1 (積分の微分)、Part 2 (Newton-Leibniz) | 2 | 0 |
| V. Fréchet微分 | 一意性、和、合成 | 3 | 0 |
| VI. Taylor展開 | exp のTaylor収束 | 0 | 1 |
| VII. 陰関数定理 | (概要のみ) | 0 | 0 |
| VIII. 凸解析 | (概要のみ) | 0 | 0 |

**合計**: 証明済み 11、演習(sorry) 5

---

### P4_CategoryTheory.lean — 圏論 (Théorie des catégories)

**難易度**: 上級  
**推奨学習時間**: 6〜10週間  
**Bourbaki対応**: 構造主義の圏論的再解釈

**なぜこれが必要か**:  
P1_Extended §6の普遍射は圏論の萌芽。P1.5のテンソル積・局所化は圏論的概念。
すべてのBourbaki的構造を統一的に理解するための言語。

| パート | 内容 | 証明済み | sorry |
|--------|------|:--------:|:-----:|
| I. 圏の基礎 | 結合律、単位律、同型 | 5 | 0 |
| II. 関手 | 合成保存、恒等保存、同型保存 | 4 | 0 |
| III. 自然変換 | naturality、成分の同型 | 2 | 0 |
| IV. 米田の補題 | 忠実充満性 | 0 | 1 |
| V. 極限と余極限 | (演習概要) | 0 | 0 |
| VI. 随伴関手 | Hom同値 | 0 | 1 |
| VII. 圏の同値 | counit/unit | 2 | 0 |
| VIII. モナド | 随伴→モナド | 0 | 1 |
| IX. Abel圏 | (演習概要) | 0 | 0 |
| X. 統合課題 | P1–P4対応表 | — | — |

**合計**: 証明済み 13、演習(sorry) 3

---

## 🎯 推奨学習順序

```
Week 1-3:    P1_5 Part I–IV   (環・イデアル・商環・同型定理)
Week 4-5:    P1_5 Part V–VIII (局所化・加群・テンソル積)
Week 6-7:    P3 Part I–IV     (微分・平均値・FTC)
Week 8-9:    P1_5 Part IX–XI  (Noether環・UFD・体拡大)
Week 10-11:  P3 Part V–VIII   (Fréchet微分・Taylor・凸解析)
Week 12-15:  P4 Part I–VI     (圏・関手・米田・随伴)
Week 16-18:  P4 Part VII–X    (同値・モナド・統合)
```

---

## 💡 将来の拡張候補

### P5_Probability.lean (確率論)
- P2の測度論の上に構築
- 確率空間、条件付き期待値、マルチンゲール
- 中心極限定理、大数の法則
- Suさんの統計的相関係数の仕事と直結

### P6_HomologicalAlgebra.lean (ホモロジー代数)
- P4のAbel圏の上に構築
- 鎖複体、ホモロジー群
- 導来関手、Ext/Tor
- Bourbaki, Algèbre X

### P7_AlgebraicTopology.lean (代数的位相幾何)
- P1_ExtendedのUrysohnとP4の圏論を統合
- 基本群、被覆空間
- ホモトピー論への入門
