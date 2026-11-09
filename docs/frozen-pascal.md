# 冻结控制的一侧元胞自动机

## 模型与输入

固定控制字宽 $`q`$ 和两个布尔函数 $`s,h:\{0,1\}^q\to\{0,1\}`$。每个格点 $`i\in\mathbb Z`$ 有控制字 $`a_i`$ 和数据位 $`x_i\in\mathbb F_2`$，同步更新为

```math
a_i'=a_i,\qquad x_i'=s(a_i)x_i+h(a_i)x_{i+1}.
```

控制字是初值的一部分，可逐格独立选择。给定控制配置后，数据轨按线性映射演化。联合规则可以非仿射。例如取 $`s=\mathrm{AND}`$、$`h=\mathrm{OR}`$，在 $`x_{i+1}=0`$ 的限制下，$`x_i`$ 的系数仍随 $`a_i`$ 变化，而仿射函数的这一系数必须固定。冻结的是控制轨，数据位可以随时间变化。

时间 $`T`$ 的查询显式给出格点 $`0,\ldots,T`$ 的初值。编码先列出这 $`T+1`$ 个控制字，再列出对应的数据位。标准预测语言的合法长度为 $`n=(q+1)(T+1)`$，所以由长度确定 $`T=n/(q+1)-1`$，并以 $`x_0(T)=1`$ 作为接受条件。空串和无法组成整格的长度被拒绝。因 $`q`$ 固定，对数深度同时是关于 $`T+2`$ 和关于总输入长度的对数界。短初值描述与独立的二进制时刻需要另行定义输入模型。 [窗口语义](../PredictionDepth/FrozenPascal/Window.lean) · [输入编码](../PredictionDepth/FrozenPascal/GuardRules.lean) · [预测语言](../PredictionDepth/FrozenPascal/UniformLanguage.lean)

## 系数公式

把 $`x_0(T)`$ 展开成初始数据位的线性组合。令 $`s_k=\sum_{i=0}^{k}s(a_i)`$ 是整数计数，$`e_k=\prod_{i=0}^{k-1}h(a_i)`$ 是前 $`k`$ 条边的通行标志，空积取 $`1`$。则

```math
x_0(T)=\sum_{k=0}^T e_k\,\operatorname{multichoose}(s_k,T-k)\,x_k(0)
\qquad\text{于 }\mathbb F_2.
```

从格点 $`k`$ 走到原点的每条贡献路径恰好向左移动 $`k`$ 次，依次跨过同一组边，产生公共因子 $`e_k`$。其余 $`r=T-k`$ 步分配给沿途允许等待的格点，包含起点和终点。格点的访问次序固定，每组停留次数恰好决定一条路径。因此，当 $`s_k>0`$ 时，路径数为 $`\binom{s_k+r-1}{r}`$。当 $`s_k=0`$ 时，仅在 $`r=0`$ 时有一条路径。将路径数模 $`2`$ 即得到系数。`iterate_data` 通过系数递推证明该式与无限格点上的实际迭代一致。 [系数递推与 `iterate_data`](../PredictionDepth/FrozenPascal/Semantics.lean)

例如，取 $`T=3`$、等待标志为 $`(1,0,1,0)`$，前三条边均通行。从格点 $`2`$ 出发的贡献需要一次等待，路径可在格点 $`0`$ 或 $`2`$ 停留。两条路径在 $`\mathbb F_2`$ 中相消，此时 $`x_0(3)=x_0(0)\oplus x_1(0)\oplus x_3(0)`$。

## 并行算法

对给定长度，时刻 $`T`$ 已在生成电路时确定。电路先在各格并行求两个控制标志，然后为每个 $`0\le k\le T`$ 并行计算以下量。

1. 通过平衡 AND 树求 $`e_k`$，用进位保存加法树对 $`k+1`$ 个等待标志计数。每轮把二进制数分组并行压缩，用常数深度将每组三行变成两行。经过 $`O(\log(T+2))`$ 轮后，只剩两行。最后传播进位，即使用线性于位宽的加法也只需 $`O(\log(T+2))`$ 深度。
2. 从计数 $`s_k`$ 选出 $`\operatorname{multichoose}(s_k,T-k)\bmod 2`$。对每个候选计数 $`v=0,\ldots,k+1`$，生成器预先计算对应的系数位。运行时并行比较 $`s_k=v`$，再用平衡树归约匹配项。对于 $`v>0`$，Lucas 定理把系数位化为二进制蕴含关系。$`T-k`$ 的每个置位都须在 $`v+T-k-1`$ 中置位。$`v=0`$ 时，系数位由 $`T=k`$ 决定。
3. 将系数位与 $`e_k`$、$`x_k(0)`$ 相乘，再用平衡 XOR 树汇总所有项。在 De Morgan 门基中，每个二输入 XOR 可用固定深度的小电路实现。

这些阶段各花 $`O(\log(T+2))`$ 深度，所有前缀各自建立子电路也只需多项式门数。核心是把时空传递系数化为前缀计数、通行标志和组合数的奇偶性。 [计数电路](../PredictionDepth/FrozenPascal/UniformWeight.lean) · [Lucas 位测试](../PredictionDepth/FrozenPascal/CoefficientBits.lean) · [系数选择与归约](../PredictionDepth/FrozenPascal/UniformDecoder.lean)

## Lean 构造与对数空间统一性

上述算法可直接按固定时刻组织。Lean 中的构造把同一解码过程接到通用路径编译器，以展示如何复用带资源界的组合接口。其抽象表示把时刻 $`u`$ 解释为第 $`u`$ 次迭代，组合时将两个时刻相加。电路保存控制标志、数据位和一个窗口内的单热时间标签。初始化将标签置于位置 $`0`$，平方和乘以种子分别将位置翻倍和加一。解码器使用标签从各个时刻的系数行中选出需要的一行。时刻表示与接线路径承担的是组合和选行，利用冻结控制获得的快速性来自解码器内部的系数公式。`no_global_decoder` 刻画了标签编码的窗口边界。对于至少包含两格的窗口，存在一组固定初值，使两个标签同为全零的越界时刻给出不同答案。 [路径见证](../PredictionDepth/FrozenPascal/PathWitness.lean) · [越界分离](../PredictionDepth/FrozenPascal/Separation.lean)

逐时刻构造 `guardedPrediction` 有显式资源界。设 $`d_s,d_h`$ 是两个控制电路的深度，$`g_s,g_h`$ 是它们的门数，则深度和门数分别至多为

```math
7+33\lceil\log_2(T+2)\rceil+\max(d_s,d_h),\qquad
113(T+2)^4+(T+1)(g_s+g_h).
```

另一构造 `uniformGuardedPrediction` 具有独立的对数空间生成器。用 `UniformWeight.basis` 实例化后，合法时刻的深度界为

```math
104\bigl(\lceil\log_2(T+3)\rceil+1\bigr)+\max(d_s,d_h).
```

生成器在只读一元输入 $`1^n`$ 上确定合法性及 $`T`$，用对数位宽的索引生成计数层、系数项、归约树和标签接线。具体计数电路把树中每两个节点的四行压缩成两行，方便统一地排列接线。组合数奇偶性由二进制位扫描生成，工作带只需保存短索引和局部计算状态。形式化证明把各块的序列化程序组合成一台停机的多带转导器，输出完整电路编码，包含门型、前驱编号和输出编号。统一族的多项式规模由该机器的输出长度界推出。`predictionLanguage_mem_uniformNC_one` 将正确性、深度、规模和生成器落实到同一个电路族上。 [逐时刻资源界](../PredictionDepth/FrozenPascal/GuardRules.lean) · [生成器与深度界](../PredictionDepth/FrozenPascal/UniformPrediction.lean) · [系数位的空间证明](../PredictionDepth/FrozenPascal/CoefficientUniform.lean) · [统一 NC 定义](../PredictionDepth/Complexity/UniformNC.lean)

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

AND/OR 控制可分别取 $`a_{\rm on}=(1,1)`$ 和 $`a_{\rm off}=(1,0)`$。结合上界，得到 $`\Theta(\log(T+2))`$ 的渐近最优深度。这里的最优性以二输入门电路深度计量。 [一般下界与 AND/OR 实例](../PredictionDepth/FrozenPascal/LowerBound.lean)

## 按控制函数分类

`bounded_prediction_depth_iff` 给出了有界深度的充要条件。固定两个控制函数后，存在一族对所有初值正确、且在所有时刻共用一个常数深度界的 De Morgan 电路，当且仅当规则始终禁止传输，或始终传输且始终禁止等待。枚举 $`2^q`$ 个控制字的函数值即可判定这个条件。 [有界深度充要条件](../PredictionDepth/FrozenPascal/Classification.lean)

逐时刻的深度可进一步分成四类。下界适用于任意扇入至多为二的布尔门，上界由 De Morgan 电路实现。$`T=0`$ 时各类规则都可直接输出 $`x_0(0)`$。`guard_depth_cases` 验证四种情况覆盖全部固定控制函数。 [规则分类](../PredictionDepth/FrozenPascal/Classification.lean)

| 控制函数 | 预测深度 |
| --- | --- |
| $`h\equiv 0`$ | 深度至多 $`d_s+1`$，门数至多 $`g_s+1`$。正时刻输出 $`s(a_0)x_0(0)`$。 |
| $`h\equiv 1,\ s\equiv 0`$ | 深度和门数都为 $`0`$。输出 $`x_T(0)`$。 |
| $`h\equiv 1,\ s\equiv 1`$ | 深度随 $`\operatorname{popcount}(T)`$ 增长，见下文。 |
| $`h`$ 非常值，或 $`h\equiv 1`$ 且 $`s`$ 非常值 | 渐近最优深度为 $`\Theta(\log(T+2))`$。 |

若 $`h`$ 非常值，把数据位固定为仅 $`x_T(0)=1`$。输出为 $`e_T`$，因为最远输入只能沿全移动路径到达原点。布尔超立方体上，任意两个控制字之间都有逐位翻转的路径，因此非常值的 $`h`$ 必在某条边上改变取值。对前 $`T`$ 格分别利用这样一条边，固定其他格点使边通行，即可见每格至少有一个本质控制位。令所有边通行还可见 $`x_T(0)`$ 是本质输入。于是深度至少为 $`\lceil\log_2(T+1)\rceil`$。若 $`h\equiv 1`$ 且 $`s`$ 非常值，则前节的奇偶校验限制直接给出同一个下界。 [两种变化情形的统一下界](../PredictionDepth/FrozenPascal/Classification.lean)

若两个函数恒为 $`1`$，系数化为 $`\binom{T}{k}\bmod 2`$。令 $`p=\operatorname{popcount}(T)`$ 表示 $`T`$ 的二进制置位数。按 Lucas 位测试，奇系数对应的 $`k`$ 恰是 $`T`$ 的所有子掩码，每个置位独立决定取或不取。因此有 $`2^p`$ 个本质数据位，给出 $`p`$ 层的下界。Lean 构造只对这些数据位做平衡 XOR，深度至多 $`3p`$，门数为 $`5(2^p-1)`$。若 XOR 可作为原生二输入门，则最优深度恰为 $`p`$。例如 $`T=2^m`$ 时只异或两位，而 $`T=2^m-1`$ 时异或整个窗口。上述专用电路的资源界按时刻给出，统一 NC¹ 成员资格由前面的通用构造给出。 [齐次规则的精细深度界](../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [经典奇系数计数，见 Rowland §1](https://arxiv.org/pdf/1001.1783)

## 文献对照

Moore 与 Pnin 在 *Physica D* 的论文中用时间区间分治求非自治加性元胞自动机的传递系数，允许这些系数同时随时间和位置变化。其 Lemma 1 的算法在二输入门下给出 $`O(\log^2 T)`$ 深度。Theorem 1 再处理由另一条轨控制这些系数的拟直积结构。这里的冻结控制属于该模型的特例，控制轨在任意时刻都等于初值。本例的 $`O(\log T)`$ 界优于把该通用分治算法直接用于这一特例所得的保证。该论文也已用 Pascal 系数处理空间齐次的加性规则。这里的统一上界处理空间上任意变化的冻结控制，其文献优先权仍待核对。 [Moore 与 Pnin，§3](https://arxiv.org/pdf/patt-sol/9701008) · [作者的出版记录](https://sites.santafe.edu/~moore/pubs/semi.html)

固定控制后，数据演化是上双对角线性算子。对角元为 $`s(a_i)`$，超对角元为 $`h(a_i)`$。Higham 的 Theorem 6.1 给出复数域上双对角矩阵函数的乘积与差商公式。对于幂函数，相应的差商是完全齐次对称多项式。把对角变量取为 $`0`$ 或 $`1`$ 后，该多项式只计数总次数为 $`T-k`$ 且支撑在允许等待位置的单项式，从而得到同一个多重组合系数。这里用路径计数在 $`\mathbb F_2`$ 中直接证明该特化，进而控制并行资源并验证统一构造。 [Higham，定理 6.1](https://doi.org/10.13001/ela.2024.8297)
