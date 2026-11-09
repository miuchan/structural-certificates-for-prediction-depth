# 动力系统预测深度的结构性判据

本项目用 Lean 4 形式化动力系统的预测深度，证明快速预测、模拟归约和信息依赖下界三条结构性判据。实例包括 OR 元胞自动机、二元域线性系统和冻结控制的非线性元胞自动机。

项目包含三个核心判据的证明，以及具体机器定义下的 logspace 复合闭包、CVP 的 P 完备性、统一 NC 的定义与归约闭包。所有项目模块均由默认入口覆盖；构建和传递公理依赖检查通过 `scripts/check.sh` 复现。逐项范围见 [要求清单](docs/requirements.md)，机器模型与依赖见 [说明](docs/dependencies.md)，最终检查结果见 [验证记录](docs/verification.md)。

## 复现

当前版本固定 Lean `v4.36.0-rc2`，并通过 `lake-manifest.json` 固定全部依赖。标准复杂性基础来自 [cslib-frontier](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d)，提交为 `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d`；其 CSLib、Mathlib 版本由该提交的依赖图确定。

```sh
lake update
lake exe cache get
./scripts/check.sh
```

`scripts/check.sh` 构建默认库并运行 `Audit.lean`。审计递归检查每个 `PredictionDepth` 声明的公理依赖，只允许 Lean 的 `propext`、`Classical.choice`、`Quot.sound`，拒绝 `sorryAx` 及其他公理。缓存用于加快依赖构建；它不代替项目源码的编译，也不代替审查定理陈述是否符合数学目标。

## 核心定理与代码

| 内容 | 模块与主要声明 |
| --- | --- |
| 演化与观测、局域映射复合 | `Dynamics.lean`：`predict`、`Geometry.Local.comp`、`local_layers` |
| 有界扇入电路、共享 DAG、依赖下界 | `Circuit.lean`：`essential_count_le_pow`、`DependencyWitness` |
| 重复平方的精确语义与操作次数 | `FastComposition.lean`：`compile_exponent`、`compile_operations`、`fast_prediction_correct` |
| A：从真实原语电路编译预测器 | `EncodedPathComposition.lean`：`EncodedPathImplementation.compiled_predictor_correct` 及资源界；`CompiledComposition.lean` 保留全局正确的特例 |
| A：实际统一生成器与标准 NC 推论 | `Complexity/UniformComposition.lean`：`UniformRegisterWitness.uniform`、`depth_le_costs`、`mem_uniformNCLevel_of_cost` |
| 两种电路表示的语义连接 | `CircuitInterop.lean`、`BinaryCircuit.unfoldOutput_eval` |
| OR 元胞自动机的精确最优深度 | `ORAutomaton.lean`；`Complexity/UniformOROptimal.lean` 的 `exact_uniform_prediction` 同时包括实际统一生成器 |
| 固定输入长度、规模预算、族级约束与深度 | `Families.lean`：`Policy`、`Admissible`、`RealizesProfile`、`intrinsicDepth` |
| 二元域矩阵的具体电路实现 | `Linear.lean`、`LinearSize.lean` |
| B：参数化模拟归约元定理 | `Hardness.lean`，详细边界见 [说明](docs/hardness.md) |
| B：具体机器定义与标准 CVP 基础 | `Complexity/Logspace.lean`、`CVP.lean`、`StandardHardness.lean` |
| 标准 NC 闭包与条件性不可快进 | `Complexity/NCClosure.lean`：`uniformNC_closed_logspace`、`SimulationWitness.prediction_not_uniformNC` |
| 并行可达性、统一 NC² 与流式生成 | `Complexity/Reachability.lean`、`UniformReachability.lean`、`LogspaceBatch.lean` |
| 信息依赖计数方法的界限 | `DependencyGrowth.lean`：`dependency_method_limit` |
| 冻结控制的一侧非线性规则族 | `FrozenPascal/`，见[系数公式、深度界与文献对照](docs/frozen-pascal.md) |
| 可执行边界与实例检查 | `Examples.lean` |

### A：快速可组合表示

`Realization` 要求单位表示、单步表示和组合操作满足真正的函数语义。`compile T` 是可执行的二进制重复平方程序；平方复用已有寄存器，组合操作次数至多为

```math
2\lceil\log_2(T+1)\rceil.
```

`EncodedPathImplementation` 给出宽度为 `L` 的位编码，以及初始化、组合和观测的实际二输入布尔电路。它只要求实际执行路径上的组合正确，不要求所有未访问表示都能压缩到 `L` 位。全局状态空间可以无限；输入由有限位串通过指定映射进入该空间。编译器证明输出恰为 $`O(F^T(\mathrm{input}(x)))`$，并证明

```math
d_{\rm pred}\le d_{\rm init}
 +2\lceil\log_2(T+1)\rceil d_{\rm comp}+d_{\rm obs}.
```

门数满足相同的加法形式；另有包含接线表和组合语法的描述规模界。初始化成本被显式计入。编码可以是对所需观测充分的表示，无须无条件单射。原先更强的全局 `Implementation` 是路径判据的特例，已有转换证明。

统一性版 `UniformRegisterWitness` 从规范二进制时间和四个局部原语电路的真实 logspace 生成器，推导完整预测电路族的生成器与多项式规模。生成器通过索引重读时间位串，不在工作带上保存数值可能很大的 $`T`$。该编译器将输出线规范为连续区间，因此显式计入每阶段一层复制门：

```math
d_{\rm uniform}\le\eta+1+
2\lceil\log_2(T+1)\rceil(\delta+1)+\epsilon.
```

当 $`\delta\ge1`$ 时，已有 $`\eta+1+4\lceil\log_2(T+1)\rceil\delta+\epsilon`$ 的推论。只有完整成本表达式关于**实际输入长度**满足多对数界时，才推出标准统一 NC 成员资格；时间二进制位串能在 logspace 生成本身不保证这个深度条件。

`Linear.implementation` 用一位编码二元域元素，矩阵乘法采用并行 AND 层与平衡 XOR 归约，得到

```math
d(T,n)\le
2\lceil\log_2(T+1)\rceil(\lceil\log_2 n\rceil+1)
 +(\lceil\log_2 n\rceil+1).
```

门数和完整描述规模均有具体多项式界。当 $`n\le(T+1)^k`$ 时，还有已证明的有限不等式

```math
d(T,n)\le3(k+1)(\lceil\log_2(T+1)\rceil+1)^2.
```

应用统一性判据时，须提供具体原语和初始矩阵族的生成器及语义见证；完整预测族的统一性由定理推出。任意选择的矩阵族不能仅因每个矩阵是线性算子就被视为统一生成的族。

### B：模拟推出困难性

时间查询编码为 $`1^T0x`$。编码/解码正确性、单射性、非法查询拒绝和整个查询长度界均有证明。模拟见证给出原电路实例到状态、时间的编码，以及预测输出等于电路答案的全称语义证明。

`Hardness` 保留可复用的参数化版本；`Complexity/StandardHardness` 接入具体有限多带图灵机定义、实际对数空间转导及标准 CVP 完备性，消除 CVP 困难性和归约闭包的抽象前提。要得到 P 完备性，还需证明具体系统的预测问题属于 P。

`NCClosure` 已证明统一 NC 对一般 logspace 归约封闭，包括归约输出长度随输入内容变化的情况。结合模拟见证，$`P\ne NC`$ 作为显式的类分离假设导出预测问题不属于 NC。这不把 P 完备性转译成某个线性数值深度下界。

### C：信息依赖下界

本质输入通过两份只在指定坐标可能不同、但输出不同的赋值定义。对于扇入至多 `b`、深度至多 `d` 的电路，证明

```math
m\le b^d,\qquad
\lceil\log_b m\rceil\le d\quad(b\ge2).
```

`DependencyWitness` 把有限坐标集合及每个坐标的区分赋值作为见证。证明覆盖任意共享的分层 DAG；展开仅用于下界证明，不把展开后可能指数增长的公式当作高效上界构造。

### OR 实例与几何约束

在无限整数格点上定义
$`F(x)_i=x_{i-1}\lor x_i\lor x_{i+1}`$，证明

```math
F^T(x)_0=\bigvee_{j=-T}^{T}x_j,
\qquad D(T)=\lceil\log_2(2T+1)\rceil.
```

输入精确固定为 `2*T+1` 位；区间外如何延拓不影响预测。核心模型给出最优深度的线性规模公式。标准层另外构造了真正 logspace-uniform 的最优深度 De Morgan 电路族，其门数为 $`n\lceil\log_2 n\rceil`$，满足固定二次预算；并对全部共享布线 De Morgan 电路证明匹配下界。两份构造都在 $`T=0`$ 时给出深度零。

该规则的一轮更新是一个三输入 OR；在严格二输入门模型中，直接实现这一轮需要常数个逻辑层，不能把物理轮数直接等同为二输入门层数。

若预测器每层的空间半径至多为 `r`，则远端输入确实影响输出时证明 $`T\le d\,r`$。这个假设作用于预测器的接线几何。任意远程布线电路使用前述对数深度界。

## 数学边界

- `Nat.clog` 给出离散的上取整对数，统一处理零/单输入；涉及实对数的渐近解释须在正参数范围使用。
- `intrinsicDepth` 先固定输入长度、规模常数、规模指数和整个电路族的可接受性；无可接受族时取无穷。逐点取下确界可能在不同时间选择不同电路族，渐近算法结论通过 `RealizesProfile` 要求同一个族实现整个深度曲线。
- 组合式 `BinaryCircuit.depth` 是经结构证明的深度上界；上下界匹配时才宣称最优值。
- 项目证明的范围是三个充分判据及其具体实例。对规则族给出完整的复杂性分类、在一般电路模型中证明超对数深度下界，以及将结论推广到哈密顿量系统，属于进一步的研究问题。

第三方复杂性基础已纳入模型与传递公理依赖审查。文献链接、库名和绿色构建都不能替代对定义与假设的检查；模型细节与审计范围保存在项目文档中。
