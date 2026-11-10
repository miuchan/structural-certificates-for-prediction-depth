# 验证记录

[English](../../../docs/verification.md) · **简体中文** · [日本語](../../ja/docs/verification.md) · [Esperanto](../../eo/docs/verification.md)

项目固定 Lean `v4.36.0-rc2` 和[依赖版本](dependencies.md)。从仓库根目录运行下列命令。

```sh
./scripts/check.sh
```

脚本先运行 `lake build --wfail`，再用 Lean 加载已编译的入口并检查传递导入范围，最后审计项目声明的传递公理依赖。导入覆盖的回归测试验证普通与嵌套块注释中的伪导入均被排除，同时验证实际的直接和间接导入。公理审计另有负向回归。

## 早期本地检查

该次 macOS 本地检查覆盖齐次 Pascal 最优深度及两个分支控制模块。入口覆盖 99 个项目模块，严格构建完成 5,008 个任务，公理审计检查了 3,383 条项目声明，仅使用 `propext`、`Classical.choice`、`Quot.sound`，负向回归通过。

## 历史基线

2026 年 11 月 10 日，提交 `f867a3016ed872747186faaa61d92ae5b12e6c82` 的公开 Ubuntu 推送作业通过严格构建和公理审计，并重建了四种语言的论文。Lean 作业使用上游 Mathlib 缓存，在新运行器上构建项目。日志记录如下。[Lean 作业](https://github.com/miuchan/structural-certificates-for-prediction-depth/actions/runs/42731331746/job/129549832955) · [论文作业](https://github.com/miuchan/structural-certificates-for-prediction-depth/actions/runs/42731331746/job/129549833258)

```text
Entry point covers all 96 project modules.
Build completed successfully (4972 jobs).
Audited 3282 project declarations: only propext, Classical.choice, Quot.sound.
Audit regression passed: AuditRegressionExternal.unexpectedTheorem transitively depends on unapproved axiom AuditRegressionDependency.unexpectedOracle.
```

构建任务数包含依赖。声明数包含定义、定理和 Lean 生成的辅助声明。

同一提交在 macOS 26.6.2（arm64、Python 3.14.5）上另行构建，复现了上述四项结果。检出目录中没有项目构建产物。复跑使用已安装的 Lean 版本及已有的依赖构建产物，十一项依赖的实际提交均与锁文件一致，已跟踪的依赖源文件均无修改。检查成功退出，工具链与依赖锁定版本均未改变。

审计按声明的定义模块选取对象。`scripts/check_audit.py` 在临时目录编译一个测试定理。该定理的命名空间与定义模块不同，且经由一个中间定理依赖外部公理。回归测试要求实际审计脚本以非零状态退出并报告指定定理及公理。

工作流核对检出的 SHA 与事件 SHA，并将其写入运行摘要。推送事件的 SHA 标识被推送的提交，拉取请求事件的 SHA 标识 GitHub 生成的合并提交。按修订版本查证时，同时核对摘要中的 SHA 与 `gh run list --commit <SHA>` 的结果。[GitHub Actions 工作流](../../../.github/workflows/lean.yml)

## 独立复现流程

安装 Elan、Git 和 Python 3 后，从公开仓库的全新克隆中用 Bash 运行以下命令。把 `revision` 设为待复核版本的完整 SHA。此流程使用固定的 Lean 版本，禁用 Lake 缓存，并从固定的源代码版本构建项目依赖。

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

使用缓存复跑时，在初始检查后运行 `lake exe cache get`，再运行 `./scripts/check.sh`。记录缓存来源，并确认构建项目前没有 `.lake/build`。两种方式均应保留 SHA、运行环境、缓存策略和完整日志。注明日期、复核者和所核对定理陈述的报告，可以作为独立审查证据。公开 CI 记录提供自动重建证据，目前尚无外部复核报告入档。

公理审计覆盖项目声明直接或通过导入使用的逻辑公理。验证依赖固定的 Lean 工具链及其内核。使用缓存时还需信任导入的已编译依赖产物。从源代码重建依赖可以去掉这部分缓存信任。核对形式定义是否对应数学主张，需要另行审查。[逻辑基础与信任边界](dependencies.md)

## 数学验收

- A 的有限电路构造、路径局部条件、任意全局状态空间、统一生成器和成本条件下的 NC 成员资格，均有对应 Lean 证明。规范化统一编译器的复制门开销显式计入；大时间的二进制编码不会自动被误判为 NC。
- B 的标准实例使用实际机器及已证明的 CVP 完备性。一般变长 logspace 归约下的统一 NC 闭包在本项目内证明。最终条件结论显式保留 `P ≠ NC`；未声称证明类分离。
- C 的整数形式 `m ≤ b^d`、对数形式及有限区分赋值见证均已证明，覆盖共享电路。
- OR 实例具有已证明的状态语义、有限输入编码、实际统一生成器、固定多项式预算、精确最优深度及任意共享 De Morgan 电路的匹配下界；时间零被覆盖。
- 二元域矩阵实例使用实际 XOR/AND 电路，有具体深度、门数和完整描述规模界。几何传播下界明确限制预测器自身的局域性。
- 冻结控制规则族覆盖任意初始控制分布的系数公式、路径编译与解码、对数深度上界、对数空间统一生成器，以及 AND/OR 规则的匹配下界。模型和适用范围见[冻结控制规则族](frozen-pascal.md)。
- 冻结控制深度分类给出了所有时刻共享一个常数深度界的充要条件。可变控制情形有二输入门的对数深度下界，齐次 Pascal 情形的逐时刻深度界由时刻的二进制置位数决定。常数深度和 Pascal 专用电路都有显式门数界。
- 可执行分类器的返回值与四种语义条件等价。统一分类总定理在同一个实际生成的电路族上证明语言正确性、多项式门数和分支深度上界，并给出标准统一 NC⁰ 的成员资格充要条件。
- 移动控制模型从无限格点的同步演化推出有限窗口上的合取，精确刻画本质输入，并用线性门数的构造达到最优深度。匹配下界覆盖允许共享的二输入网络。结果属于逐时刻电路模型。[Lean 定理](../../../PredictionDepth/TransportedControl.lean)
- 齐次 Pascal 的逐时刻最优深度在允许原生 XOR 时为 $`p`$，在 NOT 计作一层的 De Morgan 模型中为零（$`p=0`$）或 $`2p+1`$（$`p>0`$）。统一生成器使用另一构造，实现 $`3p`$ 的上界。 [原生 XOR 定理](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [De Morgan 定理](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean) · [统一生成器](../../../PredictionDepth/FrozenPascal/UniformHomogeneous.lean)
- 统一平移控制保留两条数据分支时，Lean 验证了移动坐标系下的冻结演化，以及交换控制函数后对有限窗口的重接线。逐时刻电路复用保持门数且不增加深度。 [移动坐标系与资源界](../../../PredictionDepth/TransportedBranching.lean)
- 在加性控制的分支模型中，Lean 验证了从同步迭代得到的共享 Pascal 奇偶值和全零后缀公式。Lean 同时验证三位摘要预测器的统一生成、线性规模、对数深度，以及扇入至多为二时匹配阶数的下界。 [加性控制迭代定理](../../../PredictionDepth/AdditiveBranching.lean) · [统一预测器](../../../PredictionDepth/AdditiveBranching/Summary.lean) · [深度下界](../../../PredictionDepth/AdditiveBranching/LowerBound.lean)

复核定理陈述时，应对照标准机器模型检查工作空间计量、有限控制、只追加的输出及变长输出，并核对查询与时钟编码、A 的路径局部假设及 B 显式使用的复杂性类分离假设。冻结控制分类中，应确认正确性、统一性、规模和分支深度上界由同一电路族实现，下界则适用于所有满足模型条件的预测器。移动控制例子应核对有限窗口投影和逐时刻电路界的范围。[机器模型](dependencies.md) · [形式化范围](requirements.md)

## 重建论文

`Rebuild paper PDFs` 作业使用 Typst 0.15.1 和 Noto Serif CJK 2.003 重建四种语言的 PDF，在日志中记录校验和，在运行摘要中记录提交 SHA。在 GitHub 上查看 PDF 时按 `y` 可取得固定到该提交的永久链接。同一个完整 SHA 也确定对应的 Typst 源稿和 Lean 代码。[本地重建说明](../README.md) · [GitHub 永久链接说明](https://docs.github.com/zh/repositories/working-with-files/using-files/getting-permanent-links-to-files)

上述基线在 macOS 重建得到的四份 PDF 与仓库中的文件逐字节一致。同一提交的 Ubuntu CI 记录中，英语、简体中文和世界语三版的 SHA-256 一致，日语版的 SHA-256 有差异。请与同平台记录的校验和比对。macOS 复跑使用的四个字体文件均与固定 Noto 提交中的 Git blob 一致。[PDF 与字体校验记录](../../../docs/verification.md#paper-rebuild)
