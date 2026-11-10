# 预测深度的文献对照

[English](../../../docs/literature.md) · **简体中文** · [日本語](../../ja/docs/literature.md) · [Esperanto](../../eo/docs/literature.md)

这次文献核对围绕当前结论，比较加性元胞自动机和拟直积的并行预测、双对角矩阵幂和二项式系数奇偶性、布尔单项式动力学、全状态冻结和电路复杂性。比较时区分输入编码、门基、统一性和规则族。

完整的定理陈述、证明思路和引用见论文。 [论文 PDF](../../../paper/structural-certificates.zh-CN.pdf) · [Typst 源稿](../../../paper/structural-certificates.zh-CN.typ)

## 结构判据

- **A，有资源界的可组合表示。** Ladner 与 Fischer 为结合运算构造并行前缀电路。Moore 合成加性元胞自动机在各时间区间上的传递映射。判据 A 对所选的迭代表示给出证明义务，包括二进制幂算法实际访问的编码、所执行电路操作的资源开销，以及需要时的统一生成。 [Ladner 与 Fischer（1980）](https://doi.org/10.1145/322217.322232) · [Moore，§3](https://arxiv.org/pdf/patt-sol/9701008#page=7) · [有限编码的路径判据](../../../PredictionDepth/EncodedPathComposition.lean) · [统一组合](../../../PredictionDepth/Complexity/UniformComposition.lean)
- **B，模拟与归约。** 困难性传递沿用经典归约方法。判据明确具体规则要提供的证据，包括生成完整一元时刻查询的对数空间机器，以及模拟输出等于预测观测的证明。目标属于 P 和排除统一 NC 所需的分离条件是各自独立的假设。 [困难性及其假设](hardness.md)
- **C，本质输入依赖。** 深度为 $`d`$ 的二输入门电路，其单个输出至多依赖 $`2^d`$ 个坐标。每个计入的坐标都由一对仅在该处取值不同、输出也不同的输入见证。每个格点的位数固定且光锥体积按多项式增长时，这种计数给出的下界数值至多随时间对数增长。实际电路深度可以更大。 [依赖见证](../../../PredictionDepth/Circuit.lean) · [计数上限](../../../PredictionDepth/DependencyGrowth.lean)

## 比较基准

固定控制字宽 $`q`$ 及等待、传输函数 $`s,h`$。初值显式包含 $`0,\ldots,T`$ 的控制字和数据位，合法长度为 $`n=(q+1)(T+1)`$。输出是第 $`T`$ 步原点的数据位。上界采用扇入至多二的 De Morgan 门，允许共享与任意布线。统一性由同一台确定性对数空间转导器从 $`1^n`$ 输出整张电路。本质输入计数下界适用于任何扇入至多二的布尔门集。De Morgan 模型中，NOT 门计为一层，输入连线深度为零。 [模型与编码](frozen-pascal.md) · [统一性定义](../../../PredictionDepth/Complexity/UniformNC.lean)

| 主题 | 文献结果 | 与仓库定理的对应 |
| --- | --- | --- |
| 齐次加性预测 | Robison 在只有一个非零初始格点时，用 $`O(\log T)`$ 串行时间计算单个格林函数系数。Moore 用 Pascal 行预测整个初值窗口所决定的输出，二输入门深度为对数阶，允许无界扇入模加门时属于对数空间统一 ACC⁰。 | `homogeneous_prediction_sum` 连接实际迭代和奇系数的异或和。每个 $`T`$ 的任意二输入门预测电路深度至少为 $`p`$，所构造的 De Morgan 电路深度至多为 $`3p`$，其中 $`p=\operatorname{popcount}(T)`$。 [Robison（1987）](https://www.complex-systems.com/abstracts/v01_i01_a15/) · [Moore，§3](https://arxiv.org/pdf/patt-sol/9701008#page=6) · [Lean 定理](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) |
| 时空变化的加性预测 | 同一论文的引理 1 按时间区间分治，合成随时空变化的传递系数。二输入门深度为 $`O(\log^2(T+2))`$，允许无界扇入模加门时为 $`O(\log(T+2))`$。定理 1 给出 ACC¹ 下的拟直积闭包，控制轨独立演化。例 1 将其用于二元数据轨，允许控制轨从八种二输入仿射布尔函数中选择。 | 冻结控制采用恒等演化，只用例 1 中无常数项的四种函数，即恒零、两个投影和异或。时间不变的一侧结构将系数化为前缀统计，从而在同样的有界扇入条件下给出 $`O(\log(T+2))`$ 深度。这里比较的是通用算法保证与受限模型上的专门上界。 [Moore，§3，引理 1、定理 1 与例 1](https://arxiv.org/pdf/patt-sol/9701008#page=7) · [系数公式](../../../PredictionDepth/FrozenPascal/Semantics.lean) · [统一分类](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| 按格点选择的单侧规则 | Salo 在引理 4 后的有限环例子中，让各格点选择恒等或与右邻异或。整体映射为双射，当且仅当至少一处使用恒等规则。 | 固定控制并在需要时对控制位取反后，这两种局部更新与 $`s\equiv1,\ h(c)=c`$ 相同。这里把控制位也作为输入，要求从有限光锥预测指定时刻的一个数据位。 [Salo（2014），§3，引理 4 及其后的例子](https://villesalo.com/article/RPfNCA.pdf#page=7) |
| Pascal 行奇系数 | Glaisher 在 1899 年利用 Lucas 定理给出了奇系数计数 $`2^{\operatorname{popcount}(T)}`$。Fine 在 1947 年给出任意素数下的非零系数计数。 | `pascalSupport_card` 验证二进制子掩码的计数。这一经典恒等式给出异或预测器的输入个数。 [Glaisher，§14，原刊卷 30](https://books.google.com/books/about/The_Quarterly_Journal_of_Pure_and_Applie.html?id=o8TxAAAAMAAJ) · [Fine (1947)](https://doi.org/10.2307/2304500) · [Rowland (2011)，§1 的历史与证明](https://arxiv.org/abs/1001.1783) |
| 双对角矩阵的幂 | Higham 的定理 6.1 给出复数域上的上双对角矩阵函数公式，将一个矩阵元写成超对角元乘积乘以对角元上的差商。 | 对幂函数，差商是完全齐次多项式。将 0/1 系数提升为整数后，该多项式数的是允许停留格点上的弱组合。矩阵幂再模二约化即可恢复仓库系数。仓库在二元域上直接用递推验证同一特化，再将它用于电路资源分析。 [Higham (2024)，定理 6.1](https://doi.org/10.13001/ela.2024.8297) · [Lean 语义证明](../../../PredictionDepth/FrozenPascal/Semantics.lean) |
| 并行原语和统一性 | Wallace 描述了用进位保存压缩并行汇总多项输入的电路。Ruzzo 研究了多种统一性定义及其与并行复杂性的关系。 | 仓库的电路用进位保存树计算等待前缀的权重，并使用平衡布尔归约及组合系数位测试。`uniform_depth_classification` 的一个电路族同时满足正确性、多项式规模、对数空间统一性和各分支深度上界。统一性按仓库定义的整图生成器理解。 [Wallace (1964)](https://doi.org/10.1109/PGEC.1964.263830) · [Ruzzo (1981)](https://doi.org/10.1016/0022-0000(81)90038-6) · [Lean 统一分类](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| P 完全性与具体模拟 | Ladner 给出 CVP 的对数空间 P 完全性。Neary 与 Woods 通过多项式时间模拟及从通用机器模拟问题出发的对数空间归约，证明固定 Rule 110 预测的 P 完全性。 | 仓库接入具体 CVP 编码的完备性证明。`SimulationWitness` 仍要求调用者提供完整一元时刻查询的对数空间转导器及预测正确性。若还提供目标语言的 P 成员资格，即可推出 P 完全性。推出不属于统一 NC 则另需 $`\mathrm P\ne\mathrm{NC}`$。 [Ladner (1975)](https://doi.org/10.1145/990518.990519) · [Neary 与 Woods（2006），引理 3](https://mural.maynoothuniversity.ie/id/eprint/15737/1/DW_P-completeness.pdf) · [仓库的归约定理](hardness.md) |
| 全状态冻结与有限次变化 | Ollinger 与 Theyssier 的 freezing 要求每个格点的整个状态按固定偏序单调下降。其命题 6 给出一维 bounded-change 规则的短期预测 NLOGSPACE 上界，一侧邻域的上界为确定性 LOGSPACE。命题 4 给出二维 freezing 规则中的 P 完全例。 | 本仓库固定的是控制轨。齐次 Pascal 规则在仅有 $`x_1(0)=1`$、其他数据位均为零时，右邻恒为 1，原点因而每步翻转。两种冻结约束涉及不同状态。 [Ollinger 与 Theyssier (2022)，命题 4、6](https://arxiv.org/pdf/1908.06751) |
| 已有 Lean 形式化 | Silváši 与 Tomášek 形式化了有界网格和可计算的元胞自动机，支持求值各代状态及机械化推理。 | 仓库当前案例的验证对象还包括显式光锥语言上的电路深度上下界与统一电路生成。形式化元胞自动机本身已有先例。 [Silváši 与 Tomášek (2020)](https://doi.org/10.1016/j.scico.2020.102471) |

齐次情形的精确 De Morgan 深度可由 Khrapchenko 的奇偶函数公式下界推出。对于 $`p>0`$，将电路展开为公式并把否定推至叶子后，$`2^p`$ 位奇偶函数至少需要 $`2^{2p}`$ 个叶子。奇偶函数非单调，原公式中必有一元 NOT。深度为 $`2p`$、扇入至多为二的树只要含有这样的结点，叶子就严格少于 $`2^{2p}`$ 个。上界先用一层 NOT 生成输入的补值，再沿平衡树每级用两层 AND/OR 同时计算奇偶值及其补值。因此 $`p>0`$ 时最优深度是 $`2p+1`$，$`p=0`$ 时为零。允许二输入 XOR 门时，最优深度恰为 $`p`$。当 $`r\ge2`$ 时，从 $`T=2^r-1`$ 到 $`T=2^r`$，最优 De Morgan 深度从 $`2r+1`$ 降到三层。现有统一生成器实现的上界为 $`3p`$。 [Khrapchenko（1971）](https://www.mathnet.ru/eng/mzm9639) · [统一生成器](../../../PredictionDepth/FrozenPascal/UniformHomogeneous.lean) · [原生 XOR 定理](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) · [De Morgan 精确深度](../../../PredictionDepth/FrozenPascal/PascalExactDepth.lean)

*书目说明。* 1998 年期刊记录将 *Predicting nonlinear cellular automata quickly by decomposing them into linear ones* 署名为 Cristopher Moore。对应预印本 PDF 另列 Timofey Pnin。此处采用期刊署名，章节定位指向可读的预印本。 [期刊版本](https://doi.org/10.1016/S0167-2789(97)80003-6) · [预印本](https://arxiv.org/abs/patt-sol/9701008)

Goles、Montealegre、Ríos-Wilson 与 Theyssier 证明，有限冻结网络的状态数、度数和树宽有界时，轨迹规格检查属于 NC。其定理涵盖预测，并把图、网络规则和规格作为输入。这里的冻结控制定理固定规则，读取显式初值窗口，并按控制函数给出有界扇入深度分类。 [Goles 等（2024），定理 17](https://doi.org/10.1016/j.aam.2024.102706)

## 移动控制的对照

新增案例仍是拟直积的特例。位置 $`i`$ 的控制轨从 $`i+u`$ 取旧控制位，数据轨从 $`i+v`$ 取旧数据位，再与位置 $`i`$ 的旧控制位相乘，其中 $`u,v\in\{0,1\}`$。Moore 的一般框架允许这类随时间变化的系数。这里借助单条反向数据路径，直接数出不同初始控制位的个数，得到每个合法时刻的精确二输入门深度。同速时反复读取同一个初始控制位，正时刻深度为一。异速时路径读取 $`T`$ 个不同的初始控制位，深度为 $`\lceil\log_2(T+1)\rceil`$。特别地，控制移动时，数据保持原位仍可产生对数深度。 [Moore，§3，定理 1](https://arxiv.org/pdf/patt-sol/9701008) · [Lean 精确深度定理](../../../PredictionDepth/TransportedControl.lean)

Colón-Reyes、Laubenbacher 与 Pareigis 证明，有限布尔单项式系统的非零迭代中，出现的变量恰对应于固定长度依赖路径的终点。这一结论适用于移动控制规则的有限光锥，因为其坐标更新均为合取。本项目把支持集的大小显式写成两轨速度的函数，由此得到精确深度。 [Colón-Reyes 等，命题 2.3](https://arxiv.org/pdf/math/0403166#page=4)

分支规则 $`c'_i=c_i\oplus c_{i+1}`$、$`x'_i=c_ix_i\oplus x_{i+1}`$ 属于 Moore 的例 1 和例 3 涵盖的范围。数据更新由当前控制位在纯移位和 Pascal 更新之间选择。本文用一个共享的 Pascal 奇偶值和全零后缀判定给出该规则的专门传递公式，以及匹配的对数深度界。传递系数能区分冻结前缀计数相同的控制序列。 [Moore，§3，例 1 与例 3](https://arxiv.org/pdf/patt-sol/9701008#page=9) · [论文](../../../paper/structural-certificates.zh-CN.pdf) · [Lean 系数公式](../../../PredictionDepth/AdditiveBranching.lean)

## 比较结论与边界

- 仓库的分类覆盖所有固定的 $`s,h`$。恒关传输和纯移位有统一常数深度。齐次 Pascal 的最优深度由置位数控制。其余规则有匹配的对数深度上下界。可执行的分类器和同一族上的全长正确性、深度、规模、统一性均有 Lean 定理对应。 [分类器与四个分支](../../../PredictionDepth/FrozenPascal/Classification.lean) · [分类总定理](../../../PredictionDepth/FrozenPascal/UniformClassification.lean)
- 本质输入计数给出的是有界扇入下界。取 $`q=1, s\equiv0, h(a)=a`$，预测是初始最远数据位和沿路控制位的合取。允许无界扇入 AND 时一层即可完成。显式初值长度与 $`T`$ 同阶，简短初值描述配二进制时间会改变复杂性参数。
- 对照的具体主张是四分支的有限控制函数测试、可变控制分支中匹配的对数深度界，以及实现各分支深度上界的同一个 Lean 验证的对数空间统一电路族。本次查阅不足以判定这组结果的优先权。移动控制对照单独检验相对速度如何改变本质输入集合。
