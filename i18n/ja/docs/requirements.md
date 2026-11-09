# 形式化の範囲

[English](../../../docs/requirements.md) · [简体中文](../../zh-CN/docs/requirements.md) · **日本語** · [Esperanto](../../eo/docs/requirements.md)

このプロジェクトは力学系の予測深さに対する構造的判定基準を Lean 4 で証明する。具体的な機械モデル、CVP の P 完全性、一様 NC の帰着に関する閉包性も扱う。下表に、主要な判定基準、計算量理論の基礎、具体例を示す。既定のエントリーポイントは表に挙げるすべてのモジュールを網羅する。

| 要件 | 形式化された証拠 | 状態 |
| --- | --- | --- |
| 離散発展と観測 | `Dynamics.predict`、無限整数格子上の OR の定義 | 実装済み |
| 有界ファンインと任意の配線および共有 | `BoundedCircuit`、`LayeredNetwork`、`BinaryCircuit` と意味論の変換 | 実装済み |
| 入力長、固定サイズ予算、回路族全体の一様性と深さの定義 | `Families.Policy`、`Admissible`、`RealizesProfile`、`intrinsicDepth`、標準層の `UniformNC` と OR および A の具体的な生成器 | コンパイル済み。二つのモデルの適用範囲を記載 |
| A。二進展開を用いる繰り返し二乗法の意味論、演算回数、コンパクトな中間表現 | `FastComposition` | 実装済み |
| A。基本回路から予測回路を構成し、深さ、ゲート数、記述サイズを抑える | `CompiledComposition.Implementation` | 実装済み |
| A。実際に経由する表現と合成だけを制約する | `PathComposition`。大域条件より真に弱い条件である例を含む | Lean 4.36 でコンパイル済み |
| A。無限の大域状態空間と有限入力窓 | `EncodedPathComposition` | Lean 4.36 でコンパイル済み |
| A。基本回路族の生成器から予測器の具体的な対数空間一様性を導く | `Complexity/UniformComposition`。標準形の時刻ビット列、基本回路から完全な回路を生成する変換、多項式サイズの証明を含む | Lean 4.36 でのコンパイルと独立した公理監査を通過 |
| 有限体上の線形系と多重対数の深さ上界 | `Linear`、`LinearSize` | 実装済み |
| B。単項時刻符号化、シミュレーション帰着、条件付きの困難性移送 | `Hardness.SimulationWitness` | パラメータ化されたメタ定理を実装済み |
| 標準の対数空間帰着と合成閉包性 | `Complexity/Logspace.lean` が有限テープの具体的な機械と証明済みの再計算コンパイラを接続 | Lean 4.36 でコンパイル済み |
| 標準 CVP の P 完全性 | `Complexity/CVP.lean` が符号化、評価機械、チューリング機械の計算表を使う帰着を接続 | Lean 4.36 でのコンパイルと公理監査を通過 |
| B の標準計算量版 | `Complexity/StandardHardness.lean` は CVP と閉包性の具体的な証明を使う | Lean 4.36 でコンパイル済み |
| 標準の一様 NC の定義と P への包含 | `Complexity/UniformNC.lean` | Lean 4.36 でコンパイル済み |
| 任意の対数空間帰着に関する一様 NC の閉包性 | `NCClosure`。構成グラフ、並列到達可能性、ストリーム型の一括生成、可変長出力の選択 | Lean 4.36 でのコンパイルと公理監査を通過 |
| P と NC の分離の下での条件付き困難性 | `SimulationWitness.prediction_not_uniformNC`。`P ≠ NC` を明示的に仮定 | Lean 4.36 でのコンパイルと公理監査を通過 |
| 具体的な OR 回路族の機械レベルの一様性と正確な最小深さ | `UniformOROptimal.exact_uniform_prediction` | Lean 4.36 でのコンパイルと公理監査を通過 |
| C。本質的変数の数と検査可能な有限の証拠から深さの下界を得る | `DependencyWitness`、回路とネットワークの下界 | 実装済み |
| OR セル・オートマトンの正確な最小深さと線形サイズの上界 | `ORAutomaton.exact_prediction_depth` | 実装済み |
| 幾何学的な制約のある予測器の伝播下界 | `Geometry.local_layers`、OR の幾何学的下界 | 実装済み |
| 依存する入力数に基づく手法の限界 | `dependency_method_limit` | 実装済み |
| 時刻ゼロ、空入力、単一入力、具体的な線形系の例 | `Examples` | 実装済み |
| 凍結制御の非線形規則族、対数深さ、一様 NC¹ | `FrozenPascal.GuardRules`、`FrozenPascal.UniformLanguage`、`FrozenPascal.LowerBound` | Lean 4.36 でのコンパイルと公理監査を通過 |
| 凍結制御族の定数深さの必要十分条件と時刻ごとの分類 | `FrozenPascal/Classification.lean` の `bounded_prediction_depth_iff` と変動する制御の下界、`FrozenPascal/HomogeneousPascal.lean` の二進展開における 1 の個数に基づく深さの境界 | [検証記録](verification.md) |
| 実行可能な規則分類と具体的な一様深さ分類 | `classify_eq_iff`、`uniform_depth_classification`、`predictionLanguage_mem_uniformNC_zero_iff` | [検証記録](verification.md) |
| プロジェクト全体の厳格なビルド、推移的な公理依存の監査、負例による回帰テスト | `scripts/check.sh`、`Audit.lean`、`scripts/check_audit.py`、`.github/workflows/lean.yml` | [検証記録](verification.md) |
