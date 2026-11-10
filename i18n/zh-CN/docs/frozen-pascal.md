# 冻结控制的一侧元胞自动机

[English](../../../docs/frozen-pascal.md) · **简体中文** · [日本語](../../ja/docs/frozen-pascal.md) · [Esperanto](../../eo/docs/frozen-pascal.md)

## 模型与输入

固定控制字宽 $`q`$ 和两个布尔函数 $`s,h:\{0,1\}^q\to\{0,1\}`$。每个格点 $`i\in\mathbb Z`$ 有控制字 $`a_i`$ 和数据位 $`x_i\in\mathbb F_2`$，同步更新为

```math
a_i'=a_i,\qquad x_i'=s(a_i)x_i+h(a_i)x_{i+1}.
```

控制字是初值的一部分，可逐格独立选择。给定控制配置后，数据轨按线性映射演化。联合规则可以非仿射。例如取 $`s=\mathrm{AND}`$、$`h=\mathrm{OR}`$，在 $`x_{i+1}=0`$ 的限制下，$`x_i`$ 的系数仍随 $`a_i`$ 变化，而仿射函数的这一系数必须固定。冻结的是控制轨，数据位可以随时间变化。

时间 $`T`$ 的查询显式给出格点 $`0,\ldots,T`$ 的初值。编码先列出这 $`T+1`$ 个控制字，再列出对应的数据位。标准预测语言的合法长度为 $`n=(q+1)(T+1)`$，所以由长度确定 $`T=n/(q+1)-1`$，并以 $`x_0(T)=1`$ 作为接受条件。空串和无法组成整格的长度被拒绝。因 $`q`$ 固定，对数深度同时是关于 $`T+2`$ 和关于总输入长度的对数界。短初值描述与独立的二进制时刻需要另行定义输入模型。 [窗口语义](../../../PredictionDepth/FrozenPascal/Window.lean) · [输入编码](../../../PredictionDepth/FrozenPascal/GuardRules.lean) · [预测语言](../../../PredictionDepth/FrozenPascal/UniformLanguage.lean)

## 分类定理

固定 $`q`$ 以及计算 $`s,h`$ 的 De Morgan 控制电路，记其深度为 $`d_s,d_h`$。电路可以任意接线和共享中间结果。令 $`p=\operatorname{popcount}(T)`$ 为 $`T`$ 的二进制置位数，$`\ell(v)=\lceil\log_2 v\rceil`$。对于每个合法时刻，任何扇入至多二的正确布尔电路都满足下表的下界。上界由同一个对数空间统一、多项式门数的 De Morgan 电路族实现。这个族决定整个语言，包括拒绝所有非法长度。 [统一分类总定理](../../../PredictionDepth/FrozenPascal/UniformClassification.lean)

| 固定规则的语义条件 | 深度下界 | 统一族的深度上界 |
| --- | --- | --- |
| $`h\equiv 0`$ | $`0`$ | $`1+d_s`$ |
| $`h\equiv 1,\ s\equiv 0`$ | $`0`$ | $`0`$ |
| $`h`$ 非常值，或 $`h\equiv 1`$ 且 $`s`$ 非常值 | $`\ell(T+1)`$ | $`104(\ell(T+3)+1)+\max(d_s,d_h)`$ |
| $`h\equiv 1,\ s\equiv 1`$ | $`p`$ | $`3p`$ |

因此所有固定规则的预测语言都属于对数空间统一 NC¹，且恰好前两类属于统一 NC⁰。第三类在每个正时刻有对数深度界。第四类在时刻 $`2^r`$ 至多三层，在时刻 $`2^r-1`$ 至少 $`r`$ 层，因而所有时刻共用的常数深度界仍然不存在。$`T=0`$ 时实际最小深度一律为零，因为输出就是输入线 $`x_0(0)`$。 [统一 NC¹](../../../PredictionDepth/FrozenPascal/UniformLanguage.lean) · [统一 NC⁰ 充要条件](../../../PredictionDepth/FrozenPascal/UniformClassification.lean)

## 系数公式

把 $`x_0(T)`$ 展开成初始数据位的线性组合。令 $`s_k=\sum_{i=0}^{k}s(a_i)`$ 是整数计数，$`e_k=\prod_{i=0}^{k-1}h(a_i)`$ 是前 $`k`$ 条边的通行标志，空积取 $`1`$。则

```math
x_0(T)=\sum_{k=0}^T e_k\,\operatorname{multichoose}(s_k,T-k)\,x_k(0)
\qquad\text{于 }\mathbb F_2.
```

从格点 $`k`$ 走到原点的每条贡献路径恰好向左移动 $`k`$ 次，依次跨过同一组边，产生公共因子 $`e_k`$。其余 $`r=T-k`$ 步分配给沿途允许等待的格点，包含起点和终点。格点的访问次序固定，每组停留次数恰好决定一条路径。因此，当 $`s_k>0`$ 时，路径数为 $`\binom{s_k+r-1}{r}`$。当 $`s_k=0`$ 时，仅在 $`r=0`$ 时有一条路径。将路径数模 $`2`$ 即得到系数。`iterate_data` 通过系数递推证明该式与无限格点上的实际迭代一致。 [系数递推与 `iterate_data`](../../../PredictionDepth/FrozenPascal/Semantics.lean)

例如，取 $`T=3`$、等待标志为 $`(1,0,1,0)`$，前三条边均通行。从格点 $`2`$ 出发的贡献需要一次等待，路径可在格点 $`0`$ 或 $`2`$ 停留。两条路径在 $`\mathbb F_2`$ 中相消，此时 $`x_0(3)=x_0(0)\oplus x_1(0)\oplus x_3(0)`$。

## 并行算法

对给定长度，时刻 $`T`$ 已在生成电路时确定。电路先在各格并行求两个控制标志，然后为每个 $`0\le k\le T`$ 并行计算以下量。

1. 通过平衡 AND 树求 $`e_k`$，用进位保存加法树对 $`k+1`$ 个等待标志计数。每轮把二进制数分组并行压缩，用常数深度将每组三行变成两行。经过 $`O(\log(T+2))`$ 轮后，只剩两行。最后传播进位，即使用线性于位宽的加法也只需 $`O(\log(T+2))`$ 深度。
2. 从计数 $`s_k`$ 选出 $`\operatorname{multichoose}(s_k,T-k)\bmod 2`$。对每个候选计数 $`v=0,\ldots,k+1`$，生成器预先计算对应的系数位。运行时并行比较 $`s_k=v`$，再用平衡树归约匹配项。对于 $`v>0`$，Lucas 定理把系数位化为二进制蕴含关系。$`T-k`$ 的每个置位都须在 $`v+T-k-1`$ 中置位。$`v=0`$ 时，系数位由 $`T=k`$ 决定。
3. 将系数位与 $`e_k`$、$`x_k(0)`$ 相乘，再用平衡 XOR 树汇总所有项。在 De Morgan 门基中，每个二输入 XOR 可用固定深度的小电路实现。

这些阶段各花 $`O(\log(T+2))`$ 深度，所有前缀各自建立子电路也只需多项式门数。核心是把时空传递系数化为前缀计数、通行标志和组合数的奇偶性。 [计数电路](../../../PredictionDepth/FrozenPascal/UniformWeight.lean) · [Lucas 位测试](../../../PredictionDepth/FrozenPascal/CoefficientBits.lean) · [系数选择与归约](../../../PredictionDepth/FrozenPascal/UniformDecoder.lean)

## Lean 构造与对数空间统一性

上述算法可直接按固定时刻组织。Lean 中的构造把同一解码过程接到通用路径编译器，以展示如何复用带资源界的组合接口。其抽象表示把时刻 $`u`$ 解释为第 $`u`$ 次迭代，组合时将两个时刻相加。电路保存控制标志、数据位和一个窗口内的单热时间标签。初始化将标签置于位置 $`0`$，平方和乘以种子分别将位置翻倍和加一。解码器使用标签从各个时刻的系数行中选出需要的一行。时刻表示与接线路径承担的是组合和选行，利用冻结控制获得的快速性来自解码器内部的系数公式。`no_global_decoder` 刻画了标签编码的窗口边界。对于至少包含两格的窗口，存在一组固定初值，使两个标签同为全零的越界时刻给出不同答案。 [路径见证](../../../PredictionDepth/FrozenPascal/PathWitness.lean) · [越界分离](../../../PredictionDepth/FrozenPascal/Separation.lean)

独立的逐时刻构造 `guardedPrediction` 有显式资源界。设 $`g_s,g_h`$ 是两个控制电路的门数，则该构造的深度和门数分别至多为

```math
7+33\lceil\log_2(T+2)\rceil+\max(d_s,d_h),\qquad
113(T+2)^4+(T+1)(g_s+g_h).
```

另一构造 `uniformGuardedPrediction` 具有独立的对数空间生成器。用 `UniformWeight.basis` 实例化后，合法时刻的深度界为

```math
104\bigl(\lceil\log_2(T+3)\rceil+1\bigr)+\max(d_s,d_h).
```

生成器在只读一元输入 $`1^n`$ 上确定合法性及 $`T`$，用对数位宽的索引生成计数层、系数项、归约树和标签接线。具体计数电路把树中每两个节点的四行压缩成两行，方便统一地排列接线。组合数奇偶性由二进制位扫描生成，工作带只需保存短索引和局部计算状态。形式化证明把各块的序列化程序组合成一台停机的多带转导器，输出完整电路编码，包含门型、前驱编号和输出编号。统一族的多项式规模由该机器的输出长度界推出。`predictionLanguage_mem_uniformNC_one` 将正确性、深度、规模和生成器落实到同一个电路族上。 [逐时刻资源界](../../../PredictionDepth/FrozenPascal/GuardRules.lean) · [生成器与深度界](../../../PredictionDepth/FrozenPascal/UniformPrediction.lean) · [系数位的空间证明](../../../PredictionDepth/FrozenPascal/CoefficientUniform.lean) · [统一 NC 定义](../../../PredictionDepth/Complexity/UniformNC.lean)

## 匹配的深度下界

若有控制字 $`a_{\rm on},a_{\rm off}`$，满足

```math
(s(a_{\rm on}),h(a_{\rm on}))=(1,1),\qquad
(s(a_{\rm off}),h(a_{\rm off}))=(0,1),
```

则可把原点设为 $`a_{\rm on}`$，其余格点设为 $`a_{\rm off}`$。这使每个 $`e_k=1`$、每个 $`s_k=1`$，故预测就是 $`T+1`$ 个数据位的奇偶校验。固定这些控制字后，逐一翻转任一数据位都会翻转结果，因而原预测函数至少有 $`T+1`$ 个本质输入。一个二输入门、深度 $`d`$ 的电路从输出回溯至多覆盖 $`2^d`$ 个输入，即使允许内部共享和任意远程接线。因此

```math
d\ge \lceil\log_2(T+1)\rceil.
```

AND/OR 控制可分别取 $`a_{\rm on}=(1,1)`$ 和 $`a_{\rm off}=(1,0)`$。结合上界，得到 $`\Theta(\log(T+2))`$ 的渐近最优深度。这里的最优性以二输入门电路深度计量。 [一般下界与 AND/OR 实例](../../../PredictionDepth/FrozenPascal/LowerBound.lean)

## 各分支的证明

`classify` 逐个前缀检查控制字，遇到反例就结束当前常值检验。穷举一次检验仍可能访问 $`2^q`$ 个控制字。`classify_eq_iff` 验证返回值与对应语义条件等价，`guard_depth_cases` 验证四种情况覆盖全部固定控制函数。例如固定 $`s\equiv1`$ 时，判定常数深度等价于判定控制电路 $`h`$ 是否不可满足。 [分类器及有界深度充要条件](../../../PredictionDepth/FrozenPascal/Classification.lean)

若 $`h\equiv0`$，正时刻的输出是 $`s(a_0)x_0(0)`$，实现只需等待控制电路和一个 AND 门。若 $`h\equiv1,s\equiv0`$，直接接出 $`x_T(0)`$ 即可，深度和门数都为零。 [两种常数深度构造](../../../PredictionDepth/FrozenPascal/Classification.lean)

若 $`h`$ 非常值，把数据位固定为仅 $`x_T(0)=1`$。输出为 $`e_T`$，因为最远输入只能沿全移动路径到达原点。布尔超立方体上，任意两个控制字之间都有逐位翻转的路径，因此非常值的 $`h`$ 必在某条边上改变取值。对前 $`T`$ 格分别利用这样一条边，固定其他格点使边通行，即可见每格至少有一个本质控制位。令所有边通行还可见 $`x_T(0)`$ 是本质输入。于是深度至少为 $`\lceil\log_2(T+1)\rceil`$。若 $`h\equiv 1`$ 且 $`s`$ 非常值，则前节的奇偶校验限制直接给出同一个下界。 [两种变化情形的统一下界](../../../PredictionDepth/FrozenPascal/Classification.lean)

门的扇入决定了这个下界的适用范围。例如 $`s\equiv0, h(a)=a`$ 时，预测就是 $`x_T(0)\land a_0\land\cdots\land a_{T-1}`$。二输入门需要对数深度，允许无界扇入时一个 AND 门即可完成。

若两个函数恒为 $`1`$，预测就是对 Pascal 行奇系数对应的数据位求奇偶。令 $`p=\operatorname{popcount}(T)`$。奇系数的下标恰是 $`T`$ 的二进制子掩码，因此本质数据位有 $`2^p`$ 个。Lean 验证了允许原生二输入 XOR 时最优深度为 $`p`$，也验证了 NOT 计为一层时的 De Morgan 最优深度在 $`p=0`$ 时为零，在 $`p>0`$ 时为 $`2p+1`$。因此从 $`T=2^r-1`$ 到 $`T=2^r`$，De Morgan 最优深度从 $`2r+1`$ 降到三层（$`r\ge2`$）。逐时刻最优电路与下节的 $`3p`$ 统一上界对应不同的构造。 [支撑集与原生 XOR 定理](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [De Morgan 精确深度定理](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean)

## 统一族的实现

`classifiedPrediction` 按固定规则的分类结果选定生成器。规则在电路族定义时固定，生成器随输入长度变化。无传输和纯移位生成器输出原专用电路的完整编码，分别保留常数深度和零门的界。可变控制规则沿用通用路径电路。齐次 Pascal 生成器扫描 $`k\le T`$，用子掩码测试流式输出奇系数的接线，归约电路只处理这些输入。 [无传输和移位生成器](../../../PredictionDepth/FrozenPascal/UniformLocal.lean) · [Pascal 生成器](../../../PredictionDepth/FrozenPascal/UniformHomogeneous.lean)

Pascal 归约使用 $`p`$ 轮固定宽度的并行 XOR，每轮三层 De Morgan 门。这样可直接流式串接各轮输出，得到 $`3p`$ 深度上界及 $`5p2^p`$ 个门。由于 $`2^p\le T+1`$，门数至多按 $`T\log(T+2)`$ 增长。前面的逐时刻平衡树有更小的门数，统一总定理采用固定宽度构造。 [XOR 归约及编码](../../../PredictionDepth/FrozenPascal/UniformXor.lean)

## 控制演化时的两个对照

控制轨统一平移时也可保留等待和传输两条分支。Lean 验证了反射后的移动坐标系把规则化为冻结控制，并交换等待、传输函数。对有限窗口重接输入线即可复用冻结预测电路，门数相同，深度至多相同。 [移动坐标系与有限窗口布线](../../../PredictionDepth/TransportedBranching.lean)

当 $`c'_i=c_i\oplus c_{i+1}`$、$`x'_i=c_ix_i\oplus x_{i+1}`$ 时，冻结前缀计数不足以恢复系数。Lean 验证了一个有序的系数公式。第 $`T`$ 个数据位的系数为 1。对 $`k<T`$，系数等于共享的 Pascal 奇偶值 $`Q_T=c_0(T)\oplus c_T(0)`$ 乘以控制后缀 $`c_{k+1}(0),\ldots,c_{T-1}(0)`$ 全零的指示值。Lean 验证了通用有序区块编译器生成的三位摘要预测器。该对数空间统一电路族具有线性门数和对数深度。对任意布线、门扇入至多为二的正确电路，Lean 还证明了 $`\lceil\log_2(T+1)\rceil`$ 的深度下界。 [Lean 系数公式](../../../PredictionDepth/AdditiveBranching.lean) · [统一预测器](../../../PredictionDepth/AdditiveBranching/Summary.lean) · [深度下界](../../../PredictionDepth/AdditiveBranching/LowerBound.lean)

## 适用范围与形式化索引

按本质输入数给出的下界，在 $`n`$ 位显式输入上至多为 $`\ell(n)`$。因此仅靠这种计数，即使覆盖固定维度的多项式体积光锥，也至多得到关于 $`T`$ 的对数下界。这里得到的上界适用于冻结控制的一侧规则和单点输出。预测语言的输入包含整个初始窗口，生成器接收一元输入长度。标准 P 困难性框架使用另一套带一元时间字段的查询编码，调用者需要提供具体模拟及生成整条查询的对数空间归约。 [依赖计数的限制](../../../PredictionDepth/DependencyGrowth.lean) · [困难性框架的义务](hardness.md)

| 查证事项 | Lean 声明 |
| --- | --- |
| 无限格点上的同步更新与系数公式 | [`iterate_data`](../../../PredictionDepth/FrozenPascal/Semantics.lean) |
| 任意正确二输入预测器的逐时刻下界 | [`classifiedPrediction_depth_lower_bound`](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| 在时刻索引上共用常数深度界的充要条件 | [`bounded_prediction_depth_iff`](../../../PredictionDepth/FrozenPascal/Classification.lean) |
| Pascal 支撑基数和逐时刻平衡树的资源界 | [`pascalSupport_card`、`homogeneousPrediction_depth`、`homogeneousPrediction_size`](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) |
| 齐次 Pascal 的逐时刻最优深度 | [`homogeneousNativeXorPrediction_depth`](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [`homogeneous_prediction_deMorgan_exact_depth`](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean) |
| 同一族上的语言正确性、对数空间统一性和分支界 | [`uniform_depth_classification`](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| 全部输入长度上的统一 NC⁰ 充要条件 | [`predictionLanguage_mem_uniformNC_zero_iff`](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |

## 文献对照

Moore 在 *Physica D* 的论文用时间区间分治求非自治加性元胞自动机的传递系数，允许这些系数同时随时间和位置变化。预印本 §3 的 Lemma 1 给出带无界扇入模加门的 ACC¹ 电路，换成二输入门可实现 $`O(\log^2 T)`$ 深度。Theorem 1 再处理由另一条轨控制这些系数的拟直积结构。对于空间齐次加性规则，该论文已说明可在对数空间生成 Pascal 行，并在允许无界扇入模加门时得到统一 ACC⁰。奇系数计数也早已由 Glaisher 给出，Rowland 回顾了它与 Lucas 定理的关系。 [期刊论文](https://doi.org/10.1016/S0167-2789(97)80003-6) · [预印本 §3](https://arxiv.org/pdf/patt-sol/9701008) · [Rowland §1](https://arxiv.org/pdf/1001.1783)

固定控制后，数据演化是上双对角线性算子。对角元为 $`s(a_i)`$，超对角元为 $`h(a_i)`$。Higham 的 Theorem 6.1 给出复数域上双对角矩阵函数的乘积与差商公式。对于幂函数，相应的差商是完全齐次对称多项式。把对角变量取为 $`0`$ 或 $`1`$ 后，该多项式只计数总次数为 $`T-k`$ 且支撑在允许等待位置的单项式，从而得到同一个多重组合系数。这里用路径计数在 $`\mathbb F_2`$ 中直接证明该特化，进而控制并行资源并验证统一构造。 [Higham，定理 6.1](https://doi.org/10.13001/ela.2024.8297)

本项目把空间上任意变化、时间上固定的一侧控制特化接到机器级统一 NC¹ 上界和四分支深度分类。这里的 $`O(\log T)`$ 界针对冻结控制，可与 Moore 对更一般系数的分治保证比较。针对这一精确规则族的统一上界和完整分类，现有对照尚不足以确定文献优先权。
