# 検証記録

[English](../../../docs/verification.md) · [简体中文](../../zh-CN/docs/verification.md) · **日本語** · [Esperanto](../../eo/docs/verification.md)

プロジェクトでは Lean `v4.36.0-rc2` と[依存関係のバージョン](dependencies.md)を固定している。リポジトリのルートから次を実行する。

```sh
./scripts/check.sh
```

スクリプトはまず `lake build --wfail` を実行し、Lean が読み込んだコンパイル済みエントリーポイントの推移的なインポート範囲を調べ、最後にプロジェクト宣言の推移的な公理依存を監査する。インポートの回帰テストは、通常および入れ子のブロックコメント内の記述を除外し、実際の直接・間接インポートを数えることを確かめる。公理監査には別の負例を用いる。

## 過去のローカル検証

この macOS での検証は、斉次 Pascal 規則の最小深さと二つの分岐制御モジュールを対象とした。入口はプロジェクトの 99 モジュールを網羅し、厳格なビルドは 5,008 件のジョブを完了した。3,383 件の宣言の公理監査で使われた公理は `propext`、`Classical.choice`、`Quot.sound` のみで、負例による回帰テストも通過した。

## 記録済みの基準コミット

2026 年 11 月 10 日に、コミット `f867a3016ed872747186faaa61d92ae5b12e6c82` の公開 Ubuntu push ジョブが厳格なビルドと公理監査に合格し、四言語版の論文が再ビルドされた。Lean ジョブは上流の Mathlib キャッシュを使い、新しいランナー上でプロジェクトをビルドした。ログには次の結果が記録されている。[Lean ジョブ](https://github.com/miuchan/structural-certificates-for-prediction-depth/actions/runs/42731331746/job/129549832955) · [論文ジョブ](https://github.com/miuchan/structural-certificates-for-prediction-depth/actions/runs/42731331746/job/129549833258)

```text
Entry point covers all 96 project modules.
Build completed successfully (4972 jobs).
Audited 3282 project declarations: only propext, Classical.choice, Quot.sound.
Audit regression passed: AuditRegressionExternal.unexpectedTheorem transitively depends on unapproved axiom AuditRegressionDependency.unexpectedOracle.
```

ビルドのジョブ数には依存関係を含む。宣言数には定義、定理、および Lean が生成する補助宣言を含む。

同じコミットを macOS 26.6.2（arm64、Python 3.14.5）で別途ビルドし、上記の四項目を再現した。チェックアウトにはプロジェクトのビルド成果物がなく、インストール済みの Lean と既存の依存成果物を使用した。十一の依存関係のコミットはすべてロックファイルと一致し、追跡対象のソースに変更はなかった。検査は成功し、ツールチェーンと依存関係の固定情報に変更はなかった。

監査対象は宣言の定義元モジュールによって決める。`scripts/check_audit.py` は一時ディレクトリでテスト用の定理をコンパイルする。定義元モジュールとは異なる名前空間に属し、中間定理を経由して外部公理に依存する。回帰テストは実際の監査スクリプトが非ゼロの終了コードを返し、該当する定理と公理を報告することを要求する。

ワークフローはチェックアウトした SHA とイベントの SHA を照合し、実行の概要に記録する。push イベントの SHA は push されたコミットを、プルリクエストイベントの SHA は GitHub が生成したマージコミットを指す。版ごとの検証結果を確かめるには、概要の SHA と `gh run list --commit <SHA>` の結果を確認する。[GitHub Actions ワークフロー](../../../.github/workflows/lean.yml)

## 独立再現の手順

Elan、Git、Python 3 を用意し、公開リポジトリを新たにクローンしたディレクトリで Bash から以下を実行する。`revision` には検証対象の版の完全な SHA を指定する。この手順は固定した Lean を使い、Lake のキャッシュを無効にして、固定したソースから依存関係をビルドする。

```bash
set -euo pipefail
revision=f867a3016ed872747186faaa61d92ae5b12e6c82
git checkout --detach "$revision"
git rev-parse HEAD
test -z "$(git status --porcelain)"
test ! -e .lake
uname -sm
python3 --version
lean --version
LAKE_NO_CACHE=1 LAKE_CACHE_DIR= ./scripts/check.sh 2>&1 | tee ../prediction-depth-check.log
git diff --exit-code HEAD -- lean-toolchain lakefile.toml lake-manifest.json
```

キャッシュを使う場合は、初期確認のあと `lake exe cache get` を実行してから `./scripts/check.sh` を実行する。キャッシュの入手元を記録し、プロジェクトのビルド前に `.lake/build` が存在しないことを確認する。どちらの場合も SHA、実行環境、キャッシュの利用方針、完全なログを保存する。日付、レビュー担当者、照合した定理の主張を記した報告書が独立レビューの証拠となる。公開 CI の記録は自動再ビルドの証拠であり、外部レビューの報告書は現時点で記録されていない。

公理監査は、プロジェクトの宣言が直接またはインポートを経由して使う論理公理を検査する。検証は固定した Lean ツールチェーンとそのカーネルを信頼する。キャッシュを使う場合は、インポートするコンパイル済みの依存成果物も信頼の対象となる。依存関係をソースからビルドすれば、そのキャッシュへの依存を解消できる。形式定義と数学的な主張の対応は別途レビューする。[論理的基盤と信頼境界](dependencies.md)

## 数学的な検証項目

- A の有限回路構成、経路上だけの局所条件、任意の大域状態空間、一様生成器、コスト条件に基づく NC への所属には、いずれも対応する Lean の証明がある。一様コンパイラの正規化に伴うコピーゲートのコストを明示的に数える。大きな時刻を二進符号化した場合にも、実際の入力長に関する深さ条件を課す。
- B の標準版は具体的な機械と証明済みの CVP 完全性を使う。可変長の一般の対数空間帰着に関する一様 NC の閉包性は本プロジェクトで証明する。条件付きの結論では `P ≠ NC` を明示的に仮定する。
- C では整数形式 `m ≤ b^d` とその対数形式を証明し、入力を区別する有限個の割当てによる証拠を形式化した。結果は共有回路も含む。
- OR の例では、状態の意味論、有限入力の符号化、具体的な一様生成器、固定した多項式予算、正確な最小深さ、および任意の共有を許すド・モルガン回路に対する一致する下界を証明した。時刻ゼロも対象となる。
- 二元体上の行列の例では具体的な XOR/AND 回路を使い、深さ、ゲート数、完全な記述サイズの上界を与える。幾何学的な伝播下界は予測器自体の局所性を仮定する。
- 凍結制御規則族では、任意の初期制御配置に対する係数公式、経路コンパイルと復号、対数深さの上界、対数空間一様な生成器、AND/OR 規則で一致する下界を扱う。[モデルと適用範囲](frozen-pascal.md)
- 凍結制御の深さの分類は、全時刻に共通する定数深さ上界が存在する必要十分条件を与える。制御関数が変動する場合は二入力ゲートで対数深さの下界があり、斉次 Pascal 規則では時刻ごとの深さを時刻の二進展開の 1 の個数で抑えられる。定数深さと Pascal 規則の専用回路には明示的なゲート数の上界がある。
- 実行可能な分類器の返り値は、四つの意味論的条件とそれぞれ同値である。一様分類の定理は、具体的に生成する同じ回路族について言語の決定の正しさ、多項式ゲート数、場合ごとの深さ上界を示し、標準一様 NC⁰ に属する必要十分条件を与える。
- 移動制御モデルでは、無限格子上の同期発展から有限窓上の論理積を導出し、本質的入力を正確に特徴づける。ゲート数が線形の構成が最小深さを達成し、一致する下界は共有を許す二入力ネットワークにも適用できる。結果は時刻ごとの回路モデルで成り立つ。[Lean の定理](../../../PredictionDepth/TransportedControl.lean)
- 斉次 Pascal 規則の時刻ごとの最小深さは、二入力 XOR が使える場合に $`p`$、NOT を一層と数えるド・モルガン回路では $`p=0`$ でゼロ、$`p>0`$ で $`2p+1`$ である。一様生成器は別の構成で深さの上界 $`3p`$ を実現する。 [二入力 XOR の定理](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [ド・モルガン回路の定理](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean) · [一様生成器](../../../PredictionDepth/FrozenPascal/UniformHomogeneous.lean)
- 一様に移動する制御で二つのデータ分岐を保つとき、移動座標系で制御が凍結することと、制御関数の交換を伴う有限窓の配線を Lean で検証した。時刻ごとの回路の再利用でゲート数は等しく、深さは増えない。 [移動座標系と資源の上界](../../../PredictionDepth/TransportedBranching.lean)
- 加法的制御を持つ分岐規則では、同期反復から共通の Pascal パリティと全ゼロ接尾辞による係数公式を Lean で導いた。Lean は 3 ビット要約の予測器について、一様生成、線形サイズ、対数深さを検証し、ファンインが高々 2 の場合に同じオーダーの下界を証明する。 [加法的制御の反復定理](../../../PredictionDepth/AdditiveBranching.lean) · [一様予測器](../../../PredictionDepth/AdditiveBranching/Summary.lean) · [深さの下界](../../../PredictionDepth/AdditiveBranching/LowerBound.lean)

定理の主張をレビューする際は、標準機械モデルと照らし合わせて作業空間の計上、有限制御、追記専用出力、可変長出力を確認する。クエリと時刻の符号化、A の経路局所的な仮定、B が明示的に使う計算量クラスの分離仮定も確認する。凍結制御では、正しさ、一様性、サイズ、場合ごとの深さ上界が同じ回路族で成り立ち、下界は対象となるすべての予測器に及ぶことを確認する。移動制御では有限窓への射影と時刻ごとの回路深さ界の適用範囲を確認する。[機械モデル](dependencies.md) · [形式化の範囲](requirements.md)

## 論文の再ビルド

`Rebuild paper PDFs` ジョブは Typst 0.15.1 と Noto Serif CJK 2.003 で四言語の PDF を再ビルドし、チェックサムをログに、コミットの SHA を実行の概要に記録する。GitHub で PDF を開いて `y` を押すと、そのコミットへの固定リンクが得られる。同じ完全な SHA で、対応する Typst ソースと Lean コードも参照できる。[ローカルでの再ビルド手順](../README.md) · [GitHub の固定リンク](https://docs.github.com/ja/repositories/working-with-files/using-files/getting-permanent-links-to-files)

macOS では、記録した基準コミットの四つの PDF がリポジトリのファイルとバイト単位で一致した。同じコミットの Ubuntu CI では、英語・簡体字中国語・エスペラント版の SHA-256 が一致し、日本語版は異なった。再ビルドの検査には同じプラットフォームで記録したチェックサムを使う。macOS で使用した四つのフォントは、固定した Noto コミットの Git blob と一致した。[PDF とフォントの検証記録](../../../docs/verification.md#paper-rebuild)
