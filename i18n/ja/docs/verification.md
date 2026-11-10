# 検証記録

[English](../../../docs/verification.md) · [简体中文](../../zh-CN/docs/verification.md) · **日本語** · [Esperanto](../../eo/docs/verification.md)

プロジェクトでは Lean `v4.36.0-rc2` と[依存関係のバージョン](dependencies.md)を固定している。リポジトリのルートから次を実行する。

```sh
./scripts/check.sh
```

スクリプトは既定のエントリーポイントの網羅性を検査し、`lake build --wfail`、プロジェクト宣言の推移的な公理依存の監査、負例による回帰テストを順に実行する。

```text
Entry point covers all 96 project modules.
Build completed successfully (4972 jobs).
Audited 3282 project declarations: only propext, Classical.choice, Quot.sound.
Audit regression passed: AuditRegressionExternal.unexpectedTheorem transitively depends on unapproved axiom AuditRegressionDependency.unexpectedOracle.
```

ビルドのジョブ数には依存関係を含む。宣言数には定義、定理、および Lean が生成する補助宣言を含む。

監査対象は宣言の定義元モジュールによって決める。`scripts/check_audit.py` は一時ディレクトリで、別の名前空間に属し、中間定理を経由して外部公理に依存するプロジェクト定理をコンパイルする。回帰テストは実際の監査スクリプトが非ゼロの終了コードを返し、該当する定理と公理を報告することを要求する。

[GitHub Actions ワークフロー](../../../.github/workflows/lean.yml) は Ubuntu で同じスクリプトを実行する。push イベントでは push されたコミットを、プルリクエストイベントでは GitHub が生成するマージコミットを検査する。ワークフローはチェックアウトした SHA とイベントの SHA が一致することを確認し、成功時には実行の概要に SHA を記録する。対応する公開記録は `gh run list --commit <SHA>` で検索できる。

`Rebuild paper PDFs` ジョブは Typst 0.15.1 と Noto Serif CJK 2.003 で四言語の PDF を再ビルドし、チェックサムをログに、コミットの SHA を実行の概要に記録する。GitHub で PDF を開いて `y` を押すと、そのコミットへの固定リンクが得られる。同じ完全な SHA で、対応する Typst ソースと Lean コードも参照できる。[ローカルでの再ビルド手順](../README.md) · [GitHub の固定リンク](https://docs.github.com/ja/repositories/working-with-files/using-files/getting-permanent-links-to-files)

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

独立したレビューでは、実際の作業空間の計上、追記専用出力、有限制御、可変長出力、標準形の時刻ビット列、経路条件と大域条件の違い、および同じ回路族が一様性・サイズ・深さの条件を同時に満たすことを別途確認した。[論理的基盤と第三者のビルド成果物の信頼境界](dependencies.md)
