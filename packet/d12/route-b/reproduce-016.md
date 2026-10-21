# 第16報の再現と証明書

Python 3.14.7、macOS、標準ライブラリだけで実行した。
Macの共有研究メモリguardは既存のmemory_pressure・ps・lsofを利用する。
他OSでguardを代替する変更は今回行っていない。

## 入口

原証拠を上書きしない隔離再生成は、verify worktreeで次を実行する。

```bash
.venv/bin/python studies/RouteB/src/reproduce_d12_classification.py
```

このスクリプトは必要な19ソースと固定した候補入力2個だけを、
新しいscratchディレクトリへコピーして5本の検査器を順に実行する。
共有研究メモリguardだけは元の研究ルートを保つため元ソースへのsymlinkを使う。
他チームの研究内容は読まない。
原証拠とは時刻・メモリ値を除く数学的内容を比較し、すべて一致することを要求する。
発見用の探索や120グラフの構築はこの再生成には不要である。
結果のsummary.jsonも新しいscratch内に保存する。
T0250で全5検査器を再実行し、6組の証明書・結果の数学的内容が完全一致した。
その後の変更は再現用summaryの保存先を引数化したものだけで、数学の処理と比較対象は同じである。

## 正式な証拠

| 内容 | 入力・式 | 最終検査結果 |
|---|---|---|
| 小全数120組 | d12.py、plan-076 | [summary.json](evidence/d12-classification-small/summary.json)、各r-sのjson.gz |
| 十分性の境界4系列 | [候補式](evidence/d12-boundary/candidates.json) | [1変数証明書](evidence/d12-boundary/symbolic-check-v3.json) |
| r=2の奇数 | [拡張検査器](src/verify_d12_blocks_r2.py) | [552本の係数](evidence/d12-positive-r2/affine-certificates.json) |
| 短prefixの必要性 | [29候補](evidence/d12-short/candidates-v2.json) | [有効域・排除・被覆](evidence/d12-short/symbolic-check-v5.json) |
| 周期帰納と終端反復 | [式と検査器](src/check_d12_loops.py) | [3変数証明書](evidence/d12-loops/symbolic-check.json) |
| 別実装の再導出・検算 | [検算器](src/audit_d12_classification.py) | [結果・入力hash](evidence/d12-classification-audit/summary-v2.json) |
| 隔離再生成 | [再生成器](src/reproduce_d12_classification.py) | [比較結果](evidence/d12-reproduction/summary.json) |

以前の十分性の合同条件s=qr±1は
[d12-positive-proof.md](d12-positive-proof.md) とそのT0120〜T0123の証拠を再利用した。
今回のr=2への拡張はその原証拠を書き換えていない。

## 証明書を検査する最小の考え方

1変数の不等式at+b≥0は、下限t0での値と傾き、または整数の上下界へ戻して調べる。
空であるべき一次条件の連立では、保存した非負有理数重みw_iに対して
`Σw_i f_i` の変数係数が全て0、定数項が負であることを確かめればよい。
その連立条件は実数でも不可能になる。

被覆の残余は整数係数条件f≥0の否定を-f-1≥0として分割する。
T0249は保存した重みを分母払いの整数計算で検算し、
明示座標から短prefixの幾何と奇数頂点排除を再導出し、46組の被覆を再生した。

一般性には、この計算だけでなく、本文の曲面の構成、開始の全被覆、
巡回5辺連結性からの一意な延長、長い列の帰納、十分性の単純性の議論を合わせる。
この位相・幾何・帰納を含む全体を、Leanで形式化したものではない。

失敗版の証明書は履歴のため残した。最終結果には表に挙げた版を使う。
T0244はfloat演算の可能性があったため、最終証拠として採用しない。
