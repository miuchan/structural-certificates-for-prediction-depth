# 预测深度的文献对照

[English](../../../docs/literature.md) · **简体中文** · [日本語](../../ja/docs/literature.md) · [Esperanto](../../eo/docs/literature.md)

本文按四条线索核对原始论文及其参考文献，分别是加性元胞自动机和拟直积的并行预测、Pascal 行的奇系数与双对角矩阵幂、统一电路与具体预测问题的 P 完全性，以及既有的 Lean 元胞自动机形式化。比较时分别核对输入编码、门基和扇入、深度参数、统一性及定理量化的规则族。

完整的定理陈述、证明思路和引用见论文。 [论文 PDF](../../../paper/structural-certificates.zh-CN.pdf) · [Typst 源稿](../../../paper/structural-certificates.zh-CN.typ)

## 比较基准

固定控制字宽 $`q`$ 及等待、传输函数 $`s,h`$。初值显式包含 $`0,\ldots,T`$ 的控制字和数据位，合法长度为 $`n=(q+1)(T+1)`$。输出是第 $`T`$ 步原点的数据位。上界采用扇入至多二的 De Morgan 门，允许共享与任意布线。统一性由同一台确定性对数空间转导器从 $`1^n`$ 输出整张电路。下界适用于任何扇入至多二的布尔门集。 [模型与编码](frozen-pascal.md) · [统一性定义](../../../PredictionDepth/Complexity/UniformNC.lean)

| 主题 | 文献结果 | 与仓库定理的对应 |
| --- | --- | --- |
| 齐次加性预测 | Moore 在 §3 用 Pascal 行作格林函数。允许无界扇入模加门时，Pascal 行可在对数空间生成，预测属于对数空间统一 ACC⁰。 | `homogeneous_prediction_sum` 连接实际迭代和奇系数的异或和。仓库按每个 $`T`$ 给出二输入门深度 $`p\le d_{\min}\le3p`$，其中 $`p=\operatorname{popcount}(T)`$。两种结论采用的门基不同。 [Moore，*Physica D* 111 (1998)，§3](https://arxiv.org/pdf/patt-sol/9701008) · [Lean 定理](../../../PredictionDepth/FrozenPascal/HomogeneousPascal.lean) |
| 时空变化的加性预测 | 同一论文的引理 1 按时间区间分治，合成随时空变化的传递系数。二输入门深度为 $`O(\log^2(T+2))`$，允许无界扇入模加门时为 $`O(\log(T+2))`$。定理 1 将该算法用于由独立演化的上层轨控制的拟直积。 | 冻结控制是下层线性且上层为恒等演化的特例。时间不变的一侧结构将系数化为前缀统计，从而在同样的有界扇入条件下给出 $`O(\log(T+2))`$ 深度。这里比较的是通用算法保证与受限模型上的专门上界。 [Moore，§3，引理 1 与定理 1](https://arxiv.org/pdf/patt-sol/9701008) · [系数公式](../../../PredictionDepth/FrozenPascal/Semantics.lean) · [统一分类](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| Pascal 行奇系数 | Glaisher 在 1899 年利用 Lucas 定理给出了奇系数计数 $`2^{\operatorname{popcount}(T)}`$。Fine 在 1947 年给出任意素数下的非零系数计数。 | `pascalSupport_card` 验证二进制子掩码的计数。结合实际演化及本质输入下界后，这一经典恒等式给出深度曲线，例如从 $`T=2^r-1`$ 到 $`T=2^r`$，最优深度由至少 $`r`$ 层降到至多三层（$`r\ge4`$）。 [Glaisher，§14，原刊卷 30](https://books.google.com/books/about/The_Quarterly_Journal_of_Pure_and_Applie.html?id=o8TxAAAAMAAJ) · [Fine (1947)](https://doi.org/10.2307/2304500) · [Rowland (2011)，§1 的历史与证明](https://arxiv.org/abs/1001.1783) |
| 双对角矩阵的幂 | Higham 的定理 6.1 给出复数域上的上双对角矩阵函数公式，将一个矩阵元写成超对角元乘积乘以对角元上的差商。 | 对幂函数，差商是完全齐次多项式。将 0/1 系数提升为整数后，该多项式数的是允许停留格点上的弱组合。矩阵幂再模二约化即可恢复仓库系数。仓库在二元域上直接用递推验证同一特化，再将它用于电路资源分析。 [Higham (2024)，定理 6.1](https://doi.org/10.13001/ela.2024.8297) · [Lean 语义证明](../../../PredictionDepth/FrozenPascal/Semantics.lean) |
| 并行原语和统一性 | Wallace 描述了用进位保存压缩并行汇总多项输入的电路。Ruzzo 研究了多种统一性定义及其与并行复杂性的关系。 | 仓库的电路用进位保存树计算等待前缀的权重，并使用平衡布尔归约及组合系数位测试。`uniform_depth_classification` 的一个电路族同时满足正确性、多项式规模、对数空间统一性和各分支深度上界。统一性按仓库定义的整图生成器理解。 [Wallace (1964)](https://doi.org/10.1109/PGEC.1964.263830) · [Ruzzo (1981)](https://doi.org/10.1016/0022-0000(81)90038-6) · [Lean 统一分类](../../../PredictionDepth/FrozenPascal/UniformClassification.lean) |
| P 完全性与具体模拟 | Ladner 给出 CVP 的对数空间 P 完全性。Neary 与 Woods 以多项式时间模拟给出固定 Rule 110 预测的 P 完全性。 | 仓库接入具体 CVP 编码的完备性证明。`SimulationWitness` 仍要求调用者提供完整一元时刻查询的对数空间转导器及预测正确性。若还提供目标语言的 P 成员资格，即可推出 P 完全性。推出不属于统一 NC 则另需 $`\mathrm P\ne\mathrm{NC}`$。 [Ladner (1975)](https://doi.org/10.1145/990518.990519) · [Neary 与 Woods (2006)](https://doi.org/10.1007/11786986_13) · [仓库的归约定理](hardness.md) |
| 全状态冻结与有限次变化 | Ollinger 与 Theyssier 的 freezing 要求每个格点的整个状态按固定偏序单调下降。其命题 6 给出一维 bounded-change 规则的短期预测 NLOGSPACE 上界，一侧邻域的上界为确定性 LOGSPACE。命题 4 给出二维 freezing 规则中的 P 完全例。 | 本仓库固定的是控制轨。齐次 Pascal 规则在仅有 $`x_1(0)=1`$、其他数据位均为零时，右邻恒为 1，原点因而每步翻转。两种冻结约束涉及不同状态。 [Ollinger 与 Theyssier (2022)，命题 4、6](https://arxiv.org/pdf/1908.06751) |
| 已有 Lean 形式化 | Silváši 与 Tomášek 形式化了有界网格和可计算的元胞自动机，支持求值各代状态及机械化推理。 | 仓库当前案例的验证对象还包括显式光锥语言上的电路深度上下界与统一电路生成。形式化元胞自动机本身已有先例。 [Silváši 与 Tomášek (2020)](https://doi.org/10.1016/j.scico.2020.102471) |

*书目说明。* 1998 年期刊记录将 *Predicting nonlinear cellular automata quickly by decomposing them into linear ones* 署名为 Cristopher Moore。对应预印本 PDF 另列 Timofey Pnin。此处采用期刊署名，章节定位指向可读的预印本。 [期刊版本](https://doi.org/10.1016/S0167-2789(97)80003-6) · [预印本](https://arxiv.org/abs/patt-sol/9701008)

## 移动控制的对照

新增案例仍是拟直积的特例。位置 $`i`$ 的控制轨从 $`i+u`$ 取旧控制位，数据轨从 $`i+v`$ 取旧数据位，再与位置 $`i`$ 的旧控制位相乘，其中 $`u,v\in\{0,1\}`$。Moore 的一般框架允许这类随时间变化的系数。这里借助单条反向数据路径，直接数出不同初始控制位的个数，得到每个合法时刻的精确二输入门深度。同速时反复读取同一个初始控制位，正时刻深度为一。异速时路径读取 $`T`$ 个不同的初始控制位，深度为 $`\lceil\log_2(T+1)\rceil`$。特别地，控制移动时，数据保持原位仍可产生对数深度。 [Moore，§3，定理 1](https://arxiv.org/pdf/patt-sol/9701008) · [Lean 精确深度定理](../../../PredictionDepth/TransportedControl.lean)

## 比较结论与边界

- 仓库的分类覆盖所有固定的 $`s,h`$。恒关传输和纯移位有统一常数深度。齐次 Pascal 的最优深度由置位数控制。其余规则有匹配的对数深度上下界。可执行的分类器和同一族上的全长正确性、深度、规模、统一性均有 Lean 定理对应。 [分类器与四个分支](../../../PredictionDepth/FrozenPascal/Classification.lean) · [分类总定理](../../../PredictionDepth/FrozenPascal/UniformClassification.lean)
- 本质输入计数给出的是有界扇入下界。取 $`q=1, s\equiv0, h(a)=a`$，预测是初始最远数据位和沿路控制位的合取。允许无界扇入 AND 时一层即可完成。显式初值长度与 $`T`$ 同阶，简短初值描述配二进制时间会改变复杂性参数。
- 该固定规则族的四分支分类及其统一实现是否已出现在其他表述下，所核对的文献不足以判定。对数深度界针对这里的一侧冻结控制，P 完全性文献针对各自的模拟与编码。普适的线性预测深度需要独立的论证及明确的计算模型。
