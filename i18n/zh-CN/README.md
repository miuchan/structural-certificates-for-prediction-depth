# 动力系统预测深度的结构性判据

[English](../../README.md) · **简体中文** · [日本語](../ja/README.md) · [Esperanto](../eo/README.md)

本项目研究动力系统的哪些可验证结构条件能够限定观测预测的电路深度。一个预测问题由演化规则、观测、输入编码和允许的电路共同确定。项目在 Lean 4 中验证了三类可复用判据。

Amamiya Miu 的阶段论文研究一类冻结控制的单侧元胞自动机。控制字可随位置变化，固定控制配置后数据轨线性演化。路径计数将预测化为前缀统计与系数奇偶性。移动控制的对照从单路径的精确深度延伸到保留两条更新分支的规则。英文为主版本。[论文 PDF](../../paper/structural-certificates.zh-CN.pdf) · [Typst 源稿](../../paper/structural-certificates.zh-CN.typ) · [文献对照](docs/literature.md)

## 稀疏修正与轨迹预测

在完整依赖锥内比较实际更新与固定线性背景的更新，逐位得到残差。Lean 验证了两种枚举电路及其对数空间统一 NC¹ 结论，分别对应未知位置的常数位数预算和对数规模的已知位置表。可逆三轨碰撞实例在任意间距下恰有三个锥内残差位。Lean 还验证了逐位和整层修复电路及其对数空间生成。Pascal 与自由传输都有完整受迫响应的形式化实例。论文给出任意固定齐次二元线性背景的受迫响应证明。 [原始研究说明](../../docs/sparse-corrections.md) · [Lean 入口](../../PredictionDepth/SparseCorrections.lean)

## 冻结控制规则族的深度分类

固定控制字宽 $q$ 和等待、传输两个控制函数。每次预测显式给出格点 $0,\ldots,T$ 的控制字和数据位，因此合法输入长度为 $n=(q+1)(T+1)$，由长度确定时间 $T$。下表区分一般二输入门的下界、De Morgan 电路的逐时刻最优值和已验证统一族的上界。电路允许任意布线和共享。

| 控制函数 | 预测深度 |
| --- | --- |
| 传输恒关 | 常数深度。正时刻只读原点的等待标志和数据位。 |
| 传输恒开、等待恒关 | 深度零。直接读第 $T$ 格的数据位。 |
| 传输函数非常值，或传输恒开且等待函数非常值 | $\Theta(\log(T+1))$。下界来自至少 $T+1$ 个本质输入位，包含 AND/OR 控制实例。 |
| 传输与等待均恒开 | 令 $`p`$ 为 $`T`$ 的二进制置位数。二输入门含 XOR 时最小深度为 $`p`$。NOT 计为一层时，De Morgan 最小深度为 $`T=0`$ 时的零层或 $`T>0`$ 时的 $`2p+1`$ 层。统一生成器的上界为 $`3p`$。 |

`classify` 按前缀遍历有限控制字，遇到反例就结束当前常值检验，无需构造完整控制字列表。穷举检验仍可能访问 $`2^q`$ 个控制字。`classify_eq_iff` 证明结果与表中的条件等价。`uniform_depth_classification` 为每对固定控制函数给出一个对数空间统一的多项式规模电路族，实现表中的分支上界，包括齐次 Pascal 规则的 $`3p`$ 层上界。语言属于统一 NC⁰ 当且仅当规则落在表中前两类。[冻结控制预测的数学论证](docs/frozen-pascal.md)

## 移动控制的结构性对照

固定 $`u,v\in\{0,1\}`$，每步令 $`c'_i=c_{i+u}`$、$`d'_i=c_i\land d_{i+v}`$。预测输入是 $`0,\ldots,T`$ 上显式给出的两轨位串。零时刻直接读取数据位，深度为零。正时刻同速只读取一个初始控制位和一个数据位，精确深度为 1。异速则读取 $`T`$ 个初始控制位及一个数据位，精确深度为 $`\lceil\log_2(T+1)\rceil`$。Lean 构造了线性门数的 AND 树，并对允许共享的二输入电路证明匹配下界。这个逐时刻结果说明，控制轨一旦移动，即使数据从不跳跃也可能需要对数深度。[移动控制的语义与深度定理](../../PredictionDepth/TransportedControl.lean)

控制轨统一平移时也可保留等待和传输两条分支。Lean 验证了反射后的移动坐标系把规则化为冻结控制，并交换等待、传输函数。对有限窗口重接输入线即可复用冻结预测电路，门数相同，深度至多相同。 [移动坐标系与有限窗口布线](../../PredictionDepth/TransportedBranching.lean)

当 $`c'_i=c_i\oplus c_{i+1}`$、$`x'_i=c_ix_i\oplus x_{i+1}`$ 时，冻结前缀计数不足以恢复系数。Lean 验证了一个有序的系数公式。第 $`T`$ 个数据位的系数为 1。对 $`k<T`$，系数等于共享的 Pascal 奇偶值 $`Q_T=c_0(T)\oplus c_T(0)`$ 乘以控制后缀 $`c_{k+1}(0),\ldots,c_{T-1}(0)`$ 全零的指示值。Lean 验证了通用有序区块编译器生成的三位摘要预测器。该对数空间统一电路族具有线性门数和对数深度。对任意布线、门扇入至多为二的正确电路，Lean 还证明了 $`\lceil\log_2(T+1)\rceil`$ 的深度下界。 [Lean 系数公式](../../PredictionDepth/AdditiveBranching.lean) · [统一预测器](../../PredictionDepth/AdditiveBranching/Summary.lean) · [深度下界](../../PredictionDepth/AdditiveBranching/LowerBound.lean)

## 形式化基础设施

三个判据分别把有资源界的原语电路编译为预测器（A），把具体模拟见证转化为复杂性下界（B），以及把本质输入数转化为有界扇入深度下界（C）。标准层连接具体图灵机、CVP 完备性和统一 NC 的归约闭包。OR 元胞自动机检验精确深度和几何约束，二元域矩阵实例检验组合成本。逐项范围、机器模型与构建结果分别见[要求清单](docs/requirements.md)、[依赖说明](docs/dependencies.md)和[验证记录](docs/verification.md)。

## 复现

当前版本固定 Lean `v4.36.0-rc2`，并通过 `lake-manifest.json` 固定全部依赖。标准复杂性基础来自 [cslib-frontier](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d)，提交为 `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d`；其 CSLib、Mathlib 版本由该提交的依赖图确定。

```sh
lake exe cache get  # 可选，下载依赖的构建缓存
./scripts/check.sh
```

`scripts/check.sh` 执行严格构建，再核对已编译入口的传递导入范围，运行公理审计及两项检查各自的回归测试。审计按声明所属的项目模块选择检查对象，只允许 Lean 的 `propext`、`Classical.choice`、`Quot.sound`。GitHub Actions 对触发运行的提交执行同一脚本。[验证流程](docs/verification.md)

英文论文使用 Typst 0.15.1 和编译器内置字体。从仓库根目录重建英文 PDF。

```sh
typst compile --ignore-system-fonts --creation-timestamp 1794268800 \
  paper/structural-certificates.typ paper/structural-certificates.pdf
```

如需重建四种语言的 PDF，将 Noto Serif CJK SC 和 JP 的 Regular、Bold 静态 OTF 字体放在同一目录，再从仓库根目录运行下列命令。[Noto Serif CJK 2.003](https://github.com/notofonts/noto-cjk/releases/tag/Serif2.003)

```sh
./scripts/build-papers.sh /path/to/cjk-fonts
```

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
| 冻结控制的一侧规则族 | `FrozenPascal/Semantics.lean` 的 `iterate_data` 和 `FrozenPascal/UniformLanguage.lean` 的 `predictionLanguage_mem_uniformNC_one` |
| 冻结控制的深度分类 | `FrozenPascal/Classification.lean` 的 `bounded_prediction_depth_iff` 和 `varyingGuard_prediction_depth_lower_bound`，`FrozenPascal/HomogeneousPascal.lean` 的 `pascalSupport_card` 及二进制位数深度界 |
| 齐次 Pascal 的逐时刻最优深度 | `homogeneousNativeXorPrediction_depth`, `homogeneous_prediction_deMorgan_exact_depth`, `homogeneous_prediction_deMorgan_depth_lower_bound` |
| 可执行分类器与统一深度分类 | `FrozenPascal/Classification.lean` 的 `classify_eq_iff`，`FrozenPascal/UniformClassification.lean` 的 `uniform_depth_classification` 和 `predictionLanguage_mem_uniformNC_zero_iff` |
| 移动控制轨的本质输入与精确深度 | `TransportedControl.lean` 的 `iterate_data_true_iff`、`essential_prediction_iff`、`exact_prediction_depth` 和 `constant_depth_iff` |
| 移动坐标系与逐时刻电路复用 | `TransportedBranching.lean`, `reverseFrame_iterate`, `prediction_correct`, `prediction_depth`, `prediction_size` |
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
- A、B、C 是充分判据。Lean 检查调用者提供的构造和语义证明。对一般规则自动寻找见证仍需另行给出算法。
- B 的困难性结论需要具体系统的完整模拟见证，P 完备性还需要目标语言属于 P。由类分离假设推出的结论是统一 NC 非成员资格。
- C 在多项式大小的光锥中至多给出对数级的计数下界。冻结控制族的下界衡量二输入电路的深度。要证明 NC¹ 完备性，还需给出适当归约下的 NC¹ 困难性。

已验证的分类和布线明确了何时可复用冻结预测器。加性控制的例子则给出另一个可组合的系数摘要。下一步可以改变传输函数，检查同样的控制演化还允许哪些有序摘要。

公理审计沿项目定理的传递依赖追踪到第三方复杂性基础。模型和假设可通过对应的定义、定理声明及验证指南检查。[信任边界](docs/dependencies.md)
