# 定理 B — シミュレーション帰着と条件付き困難性

[English](../../../docs/hardness.md) · [简体中文](../../zh-CN/docs/hardness.md) · **日本語** · [Esperanto](../../eo/docs/hardness.md)

標準の計算量層は `PredictionDepth/Complexity/Logspace.lean`、`CVP.lean`、`StandardHardness.lean` にあり、名前空間は `PredictionDepth.StandardComplexity` である。`PredictionDepth/Hardness.lean` は汎用の補助定理と単項時刻の問い合わせ符号化を提供する。

## 標準の計算量層

`StandardComplexity.Logspace` では、cslib の有限制御、二進アルファベット、多テープチューリング機械を用いる。入力テープは読み取り専用で、出力テープは追記専用である。作業空間は訪れた作業テープのセル数で測る。`logspace_comp` は、証明済みの再計算コンパイル定理を用いる。二台目の機械が中間出力のある記号を必要とするとき、一台目を再実行することで中間出力全体を保持せずに済む。

`CVP.lean` では、具体的なド・モルガン回路と入力への割当てを単射的に二進符号化する。インポートする `cvp_logSpaceComplete` は、多項式時間機械の計算表を表す回路と対数空間直列化器を用いて、CVP の P 完全性を証明している。始域問題の困難性と帰着に関する閉包性は、標準層の定理ですでに与えられている。

`StandardComplexity.SimulationWitness` が要求するのは、具体的な力学系についての次の情報である。

1. 各妥当な CVP インスタンスを、シミュレーション時刻と初期状態の符号に写す。
2. **単項時刻を含む問い合わせ全体**を生成する対数空間機械の証明を与える。
3. 指定した時刻における力学系の観測結果が元の回路出力に等しいことを証明する。

`SimulationWitness.prediction_P_hard` はこれらの情報から、具体的な `LogSpaceHard @Cslib.Complexity.P` を導く。対象の予測言語が具体的な機械の意味で P に属することも証明すれば、`prediction_P_complete` が得られる。`time_polynomial` と `payload_length_polynomial` は、問い合わせ生成器の対数空間性から時刻フィールドと状態符号の長さに対する多項式上界を導く。

CVP では妥当なインスタンスを型で表す。困難性の定理はすべての入力符号化を対象とし、特に `encBits` 上のすべての二進語を含む。帰着の出力は常に妥当なインスタンスであり、本プロジェクトの対象予測言語はすべての二進語上で定義され、無効な問い合わせを拒否する。従って対象についての結論は、約束問題に限定されない。

標準機械の基盤には固定コミットの [cslib-frontier `3c44ce0b`](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d) を用いる。依存関係のソースコードと本プロジェクトのコードを Lean がともにコンパイルし、証明項を検査する。完全な一様 NC の層と条件付きの結論は、対応する並列計算量モジュールを介して接続する。

## 汎用の補助層

以下は、ほかの種類の帰着にも再利用できる `PredictionDepth.Hardness` のパラメータ化された結果である。

1. `encodeQuery t x = 1^t 0 x` は、時刻を単項表現にした二進問い合わせである。`decode_encodeQuery` と `encode_decodeQuery` は符号化と復号が互いに逆であることを示し、`encodeQuery_injective` は符号化の一意性を示す。`decoded_time_le_length` により、妥当な問い合わせに含まれる時刻はその問い合わせ長以下となる。無効な問い合わせは拒否する。
2. `predictionProblem F observe decodeState` は、妥当な問い合わせに対して `observe ((F^[t]) (decodeState x))` を計算する。入力状態の符号化と力学系の状態型を区別する。
3. `SimulationWitness` は入力の符号化、シミュレーション時刻、両者の多項式上界、およびすべての入力でシミュレーション出力が始域問題の答えと一致することの証明を含む。`query_length_polynomial` は時刻と符号の長さの上界から、単項問い合わせ全体の長さの多項式上界を導く。
4. 問い合わせ全体を生成する関数が許容されることを示すと、`SimulationWitness.reduction` が多対一帰着を構成する。帰着の正しさはシミュレーションの意味論から従う。
5. `Reduction.trans` は帰着を合成し、`prediction_P_hard` は始域問題の P 困難性を予測問題に移す。予測問題が P に属することも示せば、`prediction_P_complete` が従う。
6. `prediction_not_NC` は、選んだ並列計算量クラスが P に含まれ、選んだ帰着について閉じており、かつ P と等しくないなら、予測問題がその並列クラスに属さないことを示す。この結果はクラス分離を仮定した非所属の定理である。

## 定義と明示的な仮定

`InP` は、mathlib の `Turing.TM2ComputableInPolyTime` を使って定義する。入力は二進語のまま符号化し、出力は一つのブール値であり、各スタックのアルファベットに有限性を要求する。現在の mathlib の `FinTM2` は、入力スタックのアルファベットの有限性だけを構造体のフィールドで保証する。ラベルと制御状態の有限性、および有限個のスタックは `FinTM2` が与える。本モジュールでは、mathlib で未証明の `TM2ComputableInPolyTime.comp` を使わない。

`TM2.Stmt` と `stepAux` では、各命令の関数が参照できるのは有限制御状態と高々一つのスタック先頭記号である。各ラベルには有限の命令構文が対応し、ラベルの個数も有限である。したがって、`step` による時間の計測では、一ステップ当たりの計算量は有界である。`Complexity/StackMachineBridge.lean` の `stack_InP_implies_standard_P` は、証明済みの TM2 から多テープ機械へのシミュレーションを使って、補助機械による証拠を標準層の P に埋め込む。

次の四項目は汎用補助層の定理におけるパラメータである。標準層での扱いを右欄に示す。

| 補助層のパラメータ | 想定する標準の具体例 | 標準層での扱い |
| --- | --- | --- |
| `ReductionSystem.Admissible` と恒等写像・合成に関する閉包性 | 全域関数の対数空間変換 | `Complexity/Logspace.lean` が具体的な機械と証明済みの合成閉包性を接続する |
| `hencode` | 単項時刻列を含む問い合わせ全体を対数空間で生成できること | 各シミュレーションの構成で証明する |
| `hsource : PHard S source` | 選んだ符号化の CVP が P 困難であること | `Complexity/CVP.lean` が具体的なチューリング機械の計算表に基づく帰着の証明を用いる |
| `ParallelClassAssumptions S NC` | 対数空間一様 NC が P に含まれ、選んだ帰着について閉じていること | `UniformNC`、`UniformReachability`、`NCClosure` が具体的な定義と証明を与える |

`prediction_P_complete` は `hP` も明示的に要求する。これは、対象予測言語を決定する有限アルファベットの多項式時間チューリング機械の証明である。有限近傍を固定したセル・オートマトンに単項時刻を与える場合は、通常、一ステップずつのシミュレーションでこの証明を与える。各局所規則について具体的な機械を構成する必要がある。

帰着には出力問い合わせ長の多項式上界が必要である。対象の予測過程の軌道全体についての空間上界は、具体的なシステムのシミュレーションを分析して求める。`payload_polynomial` は初期状態の符号長の上界を証明する。局所性、ゲート部品、伝送路、同期、交差の構成は `simulation_correct` と `hencode` を検証するための手段である。困難性の移送に必要なのは、それらから得られる意味論と帰着の性質である。

標準の P 困難性と P 完全性の結論には、具体的な対数空間機械と証明済みの CVP 完全性を用いる `StandardComplexity.SimulationWitness` の定理を使う。具体的なシステムについて証明すべき事項はすべて Lean の型に現れ、`#check` で個別に確認できる。

## 参考文献

CVP の対数空間 P 完全性は Richard E. Ladner の *The Circuit Value Problem is Log Space Complete for P*（SIGACT News 7(1), 18–20, 1975）にさかのぼる。[著者の論文一覧](https://homes.cs.washington.edu/~ladner/papers.html)

P 完全性、NC 帰着、困難性の移送、および P と NC の分離との関係については、Greenlaw、Hoover、Ruzzo の *Limits to Parallel Computation: P-Completeness Theory*、特に帰着と CVP の章を参照されたい。文献は数学的背景を説明し、機械検査は依存ライブラリと本リポジトリの証明項に基づく。[著者が公開している書籍の全文](https://homes.cs.washington.edu/~ruzzo/papers/limits.pdf)
