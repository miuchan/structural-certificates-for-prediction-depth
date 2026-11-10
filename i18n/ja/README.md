# 力学系の予測深さに対する構造的証明書

[English](../../README.md) · [简体中文](../zh-CN/README.md) · **日本語** · [Esperanto](../eo/README.md)

本プロジェクトでは、力学系の予測に必要な回路の深さを Lean 4 で形式化する。主な例は、制御を凍結した片側セル・オートマトンである。制御語は位置ごとに任意に変えられる。制御配置を固定するとデータトラックは線形に発展する。経路を数え上げて予測を接頭辞の集計と組合せ係数の偶奇判定に帰着させ、対数空間一様な NC¹ 回路族を構成する。

Amamiya Miu の論文では、モデル、符号化、定理の正確な記述、証明、適用範囲をまとめている。英語版が原文である。[先行研究との比較](docs/literature.md)

| 論文の言語 | PDF | Typst ソース |
| --- | --- | --- |
| English | [PDF](../../paper/structural-certificates.pdf) | [ソース](../../paper/structural-certificates.typ) |
| 简体中文 | [PDF](../../paper/structural-certificates.zh-CN.pdf) | [ソース](../../paper/structural-certificates.zh-CN.typ) |
| 日本語 | [PDF](../../paper/structural-certificates.ja.pdf) | [ソース](../../paper/structural-certificates.ja.typ) |
| Esperanto | [PDF](../../paper/structural-certificates.eo.pdf) | [ソース](../../paper/structural-certificates.eo.typ) |

## 凍結制御規則族の深さの分類

制御語の幅 $q$ と、滞留と移動を制御する二つの関数を固定する。各予測の入力には格子点 $0,\ldots,T$ の制御語とデータビットを明示的に与える。有効な入力長は $n=(q+1)(T+1)$ であり、長さから時刻 $T$ が定まる。下表の下界は、ファンインが高々二で任意の配線と共有を許す回路に対して成り立つ。上界は具体的なド・モルガン回路で達成する。

| 制御関数 | 予測深さ |
| --- | --- |
| 移動が常に無効 | 定数深さ。正の時刻には原点の滞留フラグとデータビットだけを読む。 |
| 移動が常に有効で、滞留が常に無効 | 深さゼロ。格子点 $T$ のデータビットを直接読む。 |
| 移動関数が非定数、または移動が常に有効で滞留関数が非定数 | $\Theta(\log(T+1))$。少なくとも $T+1$ 個の本質的入力から下界を得る。AND/OR 制御の例を含む。 |
| 移動と滞留がともに常に有効 | $T$ の二進展開に含まれる 1 の個数を $p$ とすると、深さは $p$ 以上 $3p$ 以下。$T=2^r$ では高々三層、$T=2^r-1$ では少なくとも $r$ 層。 |

`classify` は有限個の制御語を接頭辞順に調べ、反例が見つかるとその定数性検査を打ち切る。制御語の全リストを構築する必要はない。全探索では最大 $`2^q`$ 個の制御語を調べる。`classify_eq_iff` は分類結果が表の条件と同値であることを示す。`uniform_depth_classification` は固定した各制御関数の組に対し、多項式サイズで対数空間一様な一つの回路族を与える。この回路族は表の各場合の上界を達成し、斉次 Pascal 規則では深さが $`3p`$ 以下となる。予測言語が一様 NC⁰ に属する必要十分条件は、規則が表の最初の二つのいずれかに属することである。[凍結制御下での予測の数学的根拠](docs/frozen-pascal.md)

## 移動する制御トラックの正確な深さ

$`u,v\in\{0,1\}`$ を固定し、各ステップで $`c'_i=c_{i+u}`$、$`d'_i=c_i\land d_{i+v}`$ と更新する。予測入力は $`0,\ldots,T`$ の両トラックを明示したビット列である。時刻ゼロではデータビットを直接読み、深さはゼロとなる。正の時刻で両トラックが等速なら、初期制御ビット一つとデータビット一つを読み、最小深さは 1 である。速度が異なる場合には $`T`$ 個の初期制御ビットとデータビット一つを読み、最小深さは $`\lceil\log_2(T+1)\rceil`$ となる。Lean ではゲート数が線形の AND 木を構成し、共有を許す二入力回路に対して一致する下界を証明する。この時刻ごとの結果によれば、データが移動しなくても制御トラックの移動だけで対数深さが必要になる場合がある。[移動制御の意味論と深さの定理](../../PredictionDepth/TransportedControl.lean)

## 形式化の基盤

三つの判定基準は、資源上界のある基本回路から予測器をコンパイルする方法（A）、具体的なシミュレーションの証拠から計算量下界を得る方法（B）、本質的入力の個数から有界ファンイン回路の深さの下界を得る方法（C）を与える。標準層は具体的なチューリング機械、回路値問題（CVP）の完全性、一様 NC の帰着に関する閉包性を結びつける。OR セル・オートマトンの例では正確な深さと幾何学的制約を扱い、二元体上の行列の例では合成のコストを扱う。[形式化の範囲](docs/requirements.md) · [依存関係](docs/dependencies.md) · [検証記録](docs/verification.md)

## 再現方法

Lean を `v4.36.0-rc2` に固定し、すべての依存関係を `lake-manifest.json` で固定している。標準計算量の基盤にはコミット `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d` の [cslib-frontier](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d) を用いる。CSLib と Mathlib のバージョンは同コミットの依存関係グラフで決まる。

```sh
lake exe cache get  # 任意。依存関係のビルドキャッシュを取得する
./scripts/check.sh
```

`scripts/check.sh` は既定のエントリーポイントが全モジュールを網羅しているかを確認し、厳格なビルド、推移的な公理依存の監査、負例を使った回帰テストを順に実行する。監査では定義元のモジュールに従って宣言を選び、Lean の `propext`、`Classical.choice`、`Quot.sound` だけを許す。GitHub Actions も対象コミットに同じスクリプトを実行する。[検証手順](docs/verification.md)

論文のビルドには Typst 0.15.1 を用いる。英語版の PDF はリポジトリのルートからコンパイラ内蔵フォントだけで再ビルドできる。

```sh
typst compile --ignore-system-fonts --creation-timestamp 1794268800 \
  paper/structural-certificates.typ paper/structural-certificates.pdf
```

四言語版をすべて再ビルドするには、静的フォントの SC 版と JP 版の Regular および Bold の OTF を一つのディレクトリに置く。必要なファイルは `NotoSerifCJKsc-Regular.otf`、`NotoSerifCJKsc-Bold.otf`、`NotoSerifCJKjp-Regular.otf`、`NotoSerifCJKjp-Bold.otf` である。[Noto Serif CJK 2.003](https://github.com/notofonts/noto-cjk/releases/tag/Serif2.003)

```sh
./scripts/build-papers.sh /path/to/cjk-fonts
```

## 主な定理と対応するコード

| 内容 | モジュールと主な宣言 |
| --- | --- |
| 発展と観測、局所写像の合成 | `Dynamics.lean` の `predict`、`Geometry.Local.comp`、`local_layers` |
| 有界ファンイン回路、共有 DAG、依存関係による下界 | `Circuit.lean` の `essential_count_le_pow`、`DependencyWitness` |
| 繰り返し二乗法の正確な意味論と演算回数 | `FastComposition.lean` の `compile_exponent`、`compile_operations`、`fast_prediction_correct` |
| A。具体的な基本回路から予測器をコンパイルする | `EncodedPathComposition.lean` の `EncodedPathImplementation.compiled_predictor_correct` と資源上界。`CompiledComposition.lean` は大域的に正しい特別な場合を扱う |
| A。具体的な一様生成器と標準 NC への帰結 | `Complexity/UniformComposition.lean` の `UniformRegisterWitness.uniform`、`depth_le_costs`、`mem_uniformNCLevel_of_cost` |
| 二つの回路表現を結ぶ意味論 | `CircuitInterop.lean`、`BinaryCircuit.unfoldOutput_eval` |
| OR セル・オートマトンの正確な最小深さ | `ORAutomaton.lean`。`Complexity/UniformOROptimal.lean` の `exact_uniform_prediction` は具体的な一様生成器も扱う |
| 固定した入力長、サイズ予算、回路族全体の条件と深さ | `Families.lean` の `Policy`、`Admissible`、`RealizesProfile`、`intrinsicDepth` |
| 二元体上の行列を扱う具体的な回路 | `Linear.lean`、`LinearSize.lean` |
| B。シミュレーション帰着のパラメータ化されたメタ定理 | `Hardness.lean`。[適用範囲の説明](docs/hardness.md) |
| B。具体的な機械の定義と標準 CVP の基礎 | `Complexity/Logspace.lean`、`CVP.lean`、`StandardHardness.lean` |
| 標準 NC の閉包性と高速予測への条件付き障壁 | `Complexity/NCClosure.lean` の `uniformNC_closed_logspace`、`SimulationWitness.prediction_not_uniformNC` |
| 並列到達可能性、一様 NC²、ストリーム生成 | `Complexity/Reachability.lean`、`UniformReachability.lean`、`LogspaceBatch.lean` |
| 依存する入力の個数に基づく手法の限界 | `DependencyGrowth.lean` の `dependency_method_limit` |
| 凍結制御の片側規則族 | `FrozenPascal/Semantics.lean` の `iterate_data` と `FrozenPascal/UniformLanguage.lean` の `predictionLanguage_mem_uniformNC_one` |
| 凍結制御の深さの分類 | `FrozenPascal/Classification.lean` の `bounded_prediction_depth_iff` と `varyingGuard_prediction_depth_lower_bound`、`FrozenPascal/HomogeneousPascal.lean` の `pascalSupport_card` および二進展開の 1 の個数による深さの境界 |
| 実行可能な分類器と一様回路の深さの分類 | `FrozenPascal/Classification.lean` の `classify_eq_iff`、`FrozenPascal/UniformClassification.lean` の `uniform_depth_classification` と `predictionLanguage_mem_uniformNC_zero_iff` |
| 移動する制御トラックの本質的入力と正確な深さ | `TransportedControl.lean` の `iterate_data_true_iff`、`essential_prediction_iff`、`exact_prediction_depth`、`constant_depth_iff` |
| 実行可能な境界例と個別例の検査 | `Examples.lean` |

### A。効率よく合成できる表現

`Realization` では恒等写像と一ステップの表現、および合成演算に正しい関数の意味論を要求する。`compile T` は二進展開を用いる実行可能な繰り返し二乗法のプログラムである。二乗では既存のレジスタを再利用し、合成回数は次で上から抑えられる。

```math
2\lceil\log_2(T+1)\rceil.
```

`EncodedPathImplementation` は幅 `L` のビット符号化と、初期化、合成、観測を行う具体的な二入力ブール回路を与える。合成の正しさを要求するのは実行経路上だけであり、経由しない表現は幅 `L` の符号化の範囲外にあってもよい。大域的な状態空間は無限でもよく、有限ビット列の入力を指定の写像でその空間へ写す。コンパイラは出力が厳密に $`O(F^T(\mathrm{input}(x)))`$ に一致し、次の境界を満たすことを示す。

```math
d_{\rm pred}\le d_{\rm init}
 +2\lceil\log_2(T+1)\rceil d_{\rm comp}+d_{\rm obs}.
```

ゲート数にも同じ加法的な上界を与える。また、配線表と合成構文を含む記述サイズの上界を与える。初期化のコストも明示的に数える。符号化は目的の観測に必要な情報を保持すればよい。大域的な正しさを要求する `Implementation` からは、実行経路上の正しさを要求する実装への変換が証明されている。

一様性を扱う `UniformRegisterWitness` は、標準形の二進時刻と四つの局所基本回路の具体的な対数空間生成器から、予測回路族全体の生成器と多項式サイズの上界を導く。生成器は時刻のビット列を添字で読み直すので、値が非常に大きくなりうる $`T`$ を作業テープに保持する必要はない。コンパイラは出力線を連続区間に正規化するため、各段階で一層のコピーゲートを計上する。

```math
d_{\rm uniform}\le\eta+1+
2\lceil\log_2(T+1)\rceil(\delta+1)+\epsilon.
```

$`\delta\ge1`$ のときは $`\eta+1+4\lceil\log_2(T+1)\rceil\delta+\epsilon`$ という上界も従う。標準の一様 NC に属するためには、コスト式全体を**実際の入力長**の多重対数で抑える必要がある。二進時刻のビット列を対数空間で生成できることは、この深さ条件とは別の要件である。

`Linear.implementation` は二元体の元を一ビットで符号化し、行列積を並列 AND 層と平衡 XOR 還元で実装する。これにより次を得る。

```math
d(T,n)\le
2\lceil\log_2(T+1)\rceil(\lceil\log_2 n\rceil+1)
 +(\lceil\log_2 n\rceil+1).
```

ゲート数と完全な記述のサイズには具体的な多項式上界がある。$`n\le(T+1)^k`$ のときは次の有限の不等式も成り立つ。

```math
d(T,n)\le3(k+1)(\lceil\log_2(T+1)\rceil+1)^2.
```

一様性の判定基準を適用するには、具体的な基本回路と初期行列族の生成器および意味論の証拠を与える。定理が予測回路族全体の一様性を導く。各行列が線形作用素であることと、行列族全体を一様に生成できることは別の条件である。

### B。シミュレーションから導く困難性

時刻付き問い合わせを $`1^T0x`$ と符号化する。符号化と復号の正しさ、単射性、無効な問い合わせの拒否、問い合わせ全体の長さの上界を証明している。シミュレーションの証拠には、元の回路インスタンスを状態と時刻に写す符号化と、予測結果が回路の答えとすべての入力で一致することの証明を含める。

`Hardness` は再利用できるパラメータ化された版を提供する。`Complexity/StandardHardness` は具体的な有限多テープチューリング機械、対数空間変換、標準 CVP の完全性に接続し、CVP の困難性や帰着の閉包性に関する抽象的な仮定を定理で置き換える。P 完全性を得るには、対象システムの予測問題が P に属することも証明する。

`NCClosure` は、帰着の出力長が入力内容に依存する場合を含め、一般の対数空間帰着に対する一様 NC の閉包性を証明する。シミュレーションの証拠と明示的なクラス分離の仮定 $`P\ne NC`$ から、予測問題が NC に属さないことが従う。この結論は計算量クラスへの非所属を述べるものである。

### C。入力依存による下界

指定した座標だけが異なり、出力も異なる二つの割当てがあれば、その座標を本質的入力とする。ファンインが高々 `b`、深さが高々 `d` の回路の本質的入力数 `m` に対して、次を示す。

```math
m\le b^d,\qquad
\lceil\log_b m\rceil\le d\quad(b\ge2).
```

`DependencyWitness` は有限個の座標と、それぞれの座標を区別する割当てを証拠として持つ。証明は任意の共有を許す層状 DAG にも適用できる。回路を式に展開するとサイズが指数的に増えうるため、展開を用いるのは下界の証明だけである。

### OR の例と幾何学的制約

無限整数格子上で $`F(x)_i=x_{i-1}\lor x_i\lor x_{i+1}`$ と定め、次を証明する。

```math
F^T(x)_0=\bigvee_{j=-T}^{T}x_j,
\qquad D(T)=\lceil\log_2(2T+1)\rceil.
```

入力は正確に `2*T+1` ビットであり、区間の外をどう補っても予測結果は変わらない。基本モデルでは最小深さを達成する線形サイズの式を与える。標準層ではさらに、最小深さを達成する具体的な対数空間一様ド・モルガン回路族を構成する。ゲート数は $`n\lceil\log_2 n\rceil`$ で、固定された二次の予算を満たす。共有配線を許すすべてのド・モルガン回路に対して一致する下界も証明する。どちらの構成も $`T=0`$ で深さゼロとなる。

一ステップの更新は三入力の OR である。二入力ゲートだけで直接実装すると一ステップに複数の論理層を要する場合があり、時間ステップ数と二入力ゲートの層数は別に数える。

予測器の各層の空間半径が高々 `r` で、遠方の入力が出力に影響する場合は $`T\le d\,r`$ を証明する。この仮定は予測器の配線の幾何学を制約する。長距離の配線が自由な場合には前述の対数深さの境界を適用する。

## 数学的な適用範囲

- `Nat.clog` は切り上げ対数の離散版であり、入力数がゼロまたは一の場合も扱う。実数の対数を用いる漸近的な解釈では正の引数を用いる。
- `intrinsicDepth` は入力長、サイズ上界の定数と指数、および回路族全体の許容条件を固定する。許容される回路族がなければ値は無限大である。各時刻で個別に下限を取ると時刻ごとに異なる回路族が選ばれうる。漸近的なアルゴリズムの結論には、深さのプロファイル全体を一つの回路族が実現することを `RealizesProfile` で要求する。
- 合成によって定まる `BinaryCircuit.depth` は、回路構造から証明された深さの上界である。一致する下界が得られた場合に最適値と呼ぶ。
- A、B、C は十分条件である。Lean は利用者が与える構成と意味論の証明を検査する。一般の規則について証拠を自動で見つけるには別途アルゴリズムが必要である。
- B の困難性の結論には具体的なシステムの完全なシミュレーションの証拠が必要である。P 完全性にはさらに対象言語が P に属することが必要である。クラス分離の仮定から従うのは一様 NC への非所属である。
- C による数え上げの下界は、多項式サイズの光円錐では高々対数である。凍結制御族の下界は二入力回路の深さに対するものである。NC¹ 完全性を証明するには、適切な帰着に関する NC¹ 困難性も必要になる。

第三者が提供する計算量理論の基盤も、モデルと推移的な公理依存の点検対象に含めた。定義と仮定を確認できるよう、プロジェクトの文書にモデルの詳細と監査の範囲を記録している。
