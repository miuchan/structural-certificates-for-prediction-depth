#let title = "动力系统预测深度的结构性判据"
#let author = "Amamiya Miu"
#set document(title: title, author: author)
#set page(
  paper: "a4",
  margin: (x: 24mm, top: 22mm, bottom: 22mm),
  numbering: "1",
  number-align: center,
)
#set text(font: ("Noto Serif CJK SC", "Libertinus Serif"), size: 11pt, lang: "zh", region: "CN")
#set par(justify: true, leading: 0.6em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)", supplement: [式])
#show heading.where(level: 1): set block(above: 1.2em, below: 0.65em)
#show heading.where(level: 2): set block(above: 1em, below: 0.5em)
#show bibliography: set text(font: ("Libertinus Serif", "Noto Serif CJK SC"), size: 10pt, lang: "en")

#let theorem(name, body) = figure(
  kind: "theorem",
  supplement: [定理],
  numbering: "1",
  caption: [],
  block(width: 100%, above: 0.85em, below: 0.85em, breakable: false)[
    #set align(left)
    *定理 #context counter(figure.where(kind: "theorem")).display("1")（#name）。*
    #body
  ],
)
#show figure.where(kind: "theorem"): it => it.body
#let qed = [#h(1fr) $square$]

#align(center, block(above: 0pt, below: 1.4em)[
  #text(size: 23pt, weight: "bold", title)
  #v(0.2em)
  #text(size: 13pt)[单侧元胞自动机中的冻结控制与移动控制]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*摘要。* 本文对一类单侧元胞自动机的预测深度进行分类。冻结控制字决定有限域 $bb(F)_2$ 上的数据更新中，等待项和传输项是否启用。输入显式给出初始光锥，输出为光锥顶点的数据位。对于每条固定规则，同一个多项式规模、对数空间统一的 De Morgan 电路族满足分类所得的深度上界。控制函数可变时，深度为 $Theta(log(T+1))$。齐次 Pascal 规则的预测深度介于 $T$ 的二进制表示中置位数与其三倍之间。本文还研究移动控制模型，其中唯一的数据路径累积沿途的布尔控制值。正时刻下，控制轨和数据轨同速时，深度恰为一。异速时，深度恰为 $ceil(log_2(T+1))$。这些有限结论以 Lean 4 验证的动力学、电路正确性和扇入下界为依据。

*关键词。* 元胞自动机、电路深度、对数空间统一性、Lean 4。
]

= 引言

代数结构可以使预测元胞自动机未来状态的电路远浅于逐层模拟的电路 @moore。本文考察单侧双轨元胞自动机中，哪些固定控制函数允许常数深度预测，以及预测深度如何随观测时刻变化。

控制冻结时，路径计数导出统一的对数深度构造，限制输入赋值则给出下界。所得四类规则包括一种齐次规则，其最优深度可在相邻时刻之间下降（@frozen-classification）。控制移动时，两轨的相对速度决定数据路径遇到多少个不同的初始控制位。平衡合取电路达到由此得到的下界（@transport-depth）。两种分类均用 Lean 4 形式化。

= 预备知识

对整数格点 $bb(Z)$ 上的构型迭代局部规则 $T$ 次，并读取原点的数据位。本文主要结果涉及的模型均采用半径为一的单侧更新，因此初始窗口由格点 $0, dots, T$ 组成。冻结模型的输入先给出 $q(T+1)$ 个控制位，再给出 $T+1$ 个数据位。控制字宽 $q$ 及两个控制电路均固定，与 $T$ 无关。合法输入长度 $n=(q+1)(T+1)$ 唯一确定 $T$。预测语言由预测结果为一的合法位串组成，其他长度一律拒绝。

上界所用的布尔电路包含二输入 AND 门和 OR 门、NOT 门以及常量。输入线的深度为零。门的输出可以共享，接线可以跨越任意格点。在此接线模型中，逐时刻下界适用于任意扇入至多为二的布尔门。对固定规则，记 $D(T)$ 为时刻 $T$ 合法窗口上的最小 De Morgan 电路深度，并令 $ell(m)=ceil(log_2 m)$，其中 $m >= 1$。统一电路族按输入长度索引。确定性对数空间转导器读取一元编码的长度，并写出包含门、接线和输出的完整电路编码。本文关于 $"NC"$ 的结论均采用对数空间统一性。

如果两个仅在某一坐标上取值不同的赋值导致输出不同，则称该坐标为*本质坐标*。

#block(breakable: false)[
*本质输入下界。* 深度为 $d$、扇入至多为 $b$ 的电路至多有 $b^d$ 个本质坐标。当 $b >= 2$ 时，具有 $m >= 1$ 个本质坐标的函数所需深度至少为 $ceil(log_b m)$。

*证明。* 只有位于输出反向光锥内的输入线才能影响输出。深度为零时，光锥最多包含一个输入。每增加一层，一个门最多连接 $b$ 个前驱光锥，因此归纳可得输入线数至多为 $b^d$。在允许共享的电路中，重复计算同一前驱只会增大该上界。 #qed
]

= 冻结控制元胞自动机
== 迭代公式

#block(breakable: false)[
设 $a_i in {0,1}^q$ 为控制字，$x_i in bb(F)_2$ 为初始数据位，$s,h : {0,1}^q -> {0,1}$ 分别为等待和传输控制函数。同步更新规则为
$
  a'_i = a_i, quad
  x'_i = s(a_i) x_i + h(a_i) x_(i+1),
$ <frozen-rule>
]
其中数据运算在 $bb(F)_2$ 中进行。终止于格点 $k$ 的反向路径有 $k$ 次传输与 $T-k$ 次等待。令
$
  e_k = product_(j=0)^(k-1) h(a_j), quad
  w_k = sum_(j=0)^k s(a_j),
$
其中第二个求和在自然数上进行。对自然数 $w,r$，令 $M(w,r)$ 为将 $r$ 写成 $w$ 个非负整数之和的有序分拆数。若 $w>0$，则 $M(w,r)=binom(w+r-1,r)$。若 $w=0$，则 $M(0,0)=1$，且 $M(0,r)=0$ 对一切 $r>0$ 成立。

#theorem("迭代公式")[
  对任意初始构型和时刻 $T$，原点的数据位为
  $
    x_0(T) = sum_(k=0)^T e_k (M(w_k,T-k) mod 2) x_k.
  $ <frozen-sum>
  平移下标后，同一恒等式适用于任意格点。
]<frozen-iterate>

*证明。* 逐步展开局部递推式，即可把输出写成所有反向路径的贡献之和。每一步传输均须启用，对应乘积 $e_k$。路径依次访问格点 $0$ 至 $k$。指定各可等待格点上的等待次数便确定了路径，其中也允许在最后一次传输之后等待。这样的分配共有 $M(w_k,T-k)$ 种。路径贡献在 $bb(F)_2$ 中相加，得到 @frozen-sum。Lean 证明对 @frozen-rule 的迭代次数归纳，建立相应的系数递推。公式只涉及初始窗口。 #qed

== 深度分类

记 $p(T)$ 为 $T$ 的二进制表示中置位的个数，$d_s,d_h$ 分别为两个固定控制电路的深度。如果一个控制函数能取到两个布尔值，就称它为可变控制函数。以下各界对所有有限时刻成立，包括 $T=0$。

#figure(
  table(
    columns: (1.65fr, 0.75fr, 1.55fr),
    align: (left, left, left),
    inset: (x: 7pt, y: 5pt),
    stroke: none,
    table.hline(stroke: 0.7pt),
    table.header([*控制条件*], [*下界*], [*统一上界*]),
    table.hline(stroke: 0.4pt),
    [$h equiv 0$], [$0$], [$1+d_s$],
    [$h equiv 1$，$s equiv 0$], [$0$], [$0$],
    [$h$ 可变，或 $h equiv 1$ 且 $s$ 可变],
      [$ell(T+1)$], [$104(ell(T+3)+1)+max(d_s,d_h)$],
    [$s equiv h equiv 1$], [$p(T)$], [$3p(T)$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [固定冻结控制函数在合法长度上的深度界。],
  kind: table,
  supplement: [表],
) <regimes>

#theorem("统一分类")[
  对每一对固定控制电路，都存在同一个对数空间统一的多项式规模 De Morgan 电路族，判定整个预测语言，并在每个合法长度上满足 @regimes 中相应的深度上界。它在所有长度上的深度均为 $O(log(n+2))$。表中的下界适用于 $D(T)$，也适用于任意扇入至多为二的布尔电路。预测语言属于对数空间统一 $"NC"^0$，当且仅当 $h equiv 0$，或 $h equiv 1$ 且 $s equiv 0$。
]<frozen-classification>

== 统一分类的证明

*局域情形与纯移位情形。* 若 $h equiv 0$ 且 $T>0$，由幂等性知输出为 $s(a_0)x_0$。纯移位情形输出 $x_T$。当 $T=0$ 时，所有规则都输出 $x_0$。

*可变控制情形。* 若 $h$ 可变，将 $x_T$ 以外的数据位全部置零。无论 $s$ 如何，@frozen-sum 中唯一可能非零的项为 $x_T product_(j=0)^(T-1) h(a_j)$。任何非常值布尔控制函数都至少有一个本质输入位。这可由连接两个不同输出的控制字的逐位翻转路径看出。在这个受限输入上，前 $T$ 个控制字各贡献一个本质输入位，$x_T$ 再贡献一个。若 $h equiv 1$ 且 $s$ 可变，则选取控制字，使 $s(a_0)=1$ 且格点 $1$ 至 $T$ 上的 $s(a_i)=0$。于是每个 $w_k=1$，@frozen-sum 为全部 $T+1$ 个数据位的奇偶性。两种情形都由本质坐标数给出相同的下界。

为构造上界，并行计算各控制函数值，并按 @frozen-iterate 求各前缀权重 $w_k$ 和乘积 $e_k$。权重电路通过平衡的保留进位归约和一次二进制加法求和。若 $w_k>0$，则 $M(w_k,T-k)$ 的奇偶性取决于 $T-k$ 中的每个置位是否也在 $w_k+T-k-1$ 中置位。若 $w_k=0$，则采用零项分拆的约定。统一构造使用对数空间生成的系数表，再按算出的前缀权重选择系数。最后通过平衡奇偶性归约合并各数据项。@regimes 的深度上界计入控制函数计算、算术、选择和归约各阶段。

*齐次 Pascal 规则。* 当 $s equiv h equiv 1$ 时，系数为 $binom(T,k) mod 2$。在 $bb(F)_2$ 上，恒等式
$
  (1+z)^T = product_(j : "bit"_j(T)=1) (1+z^(2^j))
$
表明恰有 $T$ 的二进制子掩码对应的项出现。因此有 $2^(p(T))$ 个本质数据位，深度下界为 $p(T)$。平衡异或树用 $p(T)$ 轮归约这些叶节点，每个异或门至多需要三层 De Morgan 电路。统一生成器扫描 $k=0, dots, T$，输出子掩码对应的接线，并写出门数为 $5 p(T) 2^(p(T))$ 的规则异或归约电路。

*同一个统一电路族。* 控制电路及分类选定的分支均已固定。对合法长度，对数空间转导器写出相应分支的预测器。对其他长度，它写出拒绝电路。输出编码的长度为多项式，因而门数也为多项式。局域分支和纯移位分支的深度具有常数上界。可变分支的下界随 $T$ 增长，齐次分支的下界沿 $T=2^r-1$ 增长。这给出了常数深度的充要条件。 #qed

齐次规则在 $T=2^r-1$ 时至少需要 $r$ 层，而在紧接着的 $T=2^r$ 时至多需要三层。对于 $r>3$，最优深度严格下降。配套分类器按前缀遍历控制字，以检查控制函数是否恒定。一次检查在遇到首个反例时结束，最坏情况下可访问 $2^q$ 个控制字。

= 移动控制

接下来赋予控制轨独立的动力学。固定速度 $u,v in {0,1}$，并设 $(c_i,d_i)$ 为布尔控制轨和数据轨。同步规则为
$
  c'_i=c_(i+u), quad d'_i=c_i and d_(i+v).
$ <transport-rule>
#block(breakable: false)[
窗口含有 $2(T+1)$ 位。沿唯一一条反向数据路径可知，时刻 $T$ 的格点 $i$ 上的数据位为
$
  d_(i+v T) and
  and.big_(k=0)^(T-1) c_(i+k v+(T-1-k)u),
$ <transport-iterate>
其中右端各位均取初始值，且 $T=0$ 时的合取为空。
]

#theorem("移动控制下的精确深度")[
  当 $T=0$ 时，深度为零。若 $T>0$ 且 $u=v$，深度恰为一。若 $T>0$ 且 $u != v$，深度恰为 $ell(T+1)$。形式化的上界构造使用带填充的合取树。若有 $m$ 个本质输入，则二输入 AND 门至多为 $2m$ 个。下界适用于预测该数据位的所有扇入至多为二的布尔电路。
]<transport-depth>

*证明。* 反向路径上的第 $k$ 步读取格点 $i+k v$ 在时刻 $T-1-k$ 的控制位。该位来自初始格点 $i+k v+(T-1-k)u$，故得 @transport-iterate。当 $T=0$ 时，输出即输入线 $d_i$。正时刻且两轨同速时，所有控制位的初始下标相同，因而只需求一个控制位和一个数据位的合取。两轨异速时，初始控制下标按正序或逆序遍历 $i, dots, i+T-1$。每个不同因子都是本质输入，因为将其他因子都设为一时，翻转该因子即改变输出。因此同速时有两个本质坐标，异速时有 $T+1$ 个。对 $m$ 个因子，高度为 $ell(m)$ 的平衡合取树达到本质输入下界。将叶节点数补至不小于 $m$ 的最小的二的幂，使用的二输入门数为 $2^(ell(m))-1 <= 2m$。 #qed

速度对 $(u,v)=(0,0)$ 是以 $c_i$ 为等待控制的冻结无传输情形。只把 $u$ 改为一后，数据仍不传输，深度却成为对数级。当 $(u,v)=(1,1)$ 时，两轨都移动，但同速带来常数深度。对于这种单路径规则，起决定作用的是随数据路径移动时遇到的不同初始控制位的数量。文献 @moore 的时变框架涵盖该规则。单路径结构使精确深度可求。

= 相关工作

*Pascal 奇偶性与快速预测。* 奇数项计数 $2^(p(T))$ 是经典结果。Rowland 将二进制计数归于 Glaisher，并用 Lucas 定理推导该式 @rowland。文献 @moore 已将 Pascal 系数用于齐次加性规则的快速预测，其中模求和门可采用无界扇入。本文的 Pascal 结论给出逐时刻的有界扇入下界，并通过经验证的统一 De Morgan 电路生成器，使上界在常数因子内匹配整个深度曲线。

*依赖控制的线性轨与系数公式。* Moore 对时空依赖的线性阶段给出了通用分治法。在该文设定下，其有界扇入预测深度为 $O(log^2(T+2))$ @moore。冻结控制与单侧等待、传输结构使本文可以利用前缀统计，在这一特例中达到 $O(log(T+2))$。@frozen-sum 中的系数也有经典矩阵解释。单步数据映射在相应的有限窗口上是上双对角矩阵。Higham 的矩阵函数差商公式把中间超对角元素的乘积，与对角元素上的差商相乘 @higham。对于单项式 $z^T$，该差商是 $T-k$ 次完全齐次多项式。在对角元素为零或一时，它计数同一批非负整数有序分拆。先将多项式恒等式特化到整数零一元素，再模二约化，无须在 $bb(F)_2$ 上作除法。

*机械化证明与冻结的含义。* Silváši 和 Tomášek 在 Lean 中形式化了有界格网和可计算元胞自动机 @silvasi，为元胞自动机的机械化验证提供了先例。本项目验证规则族的深度分类和实际电路生成器。Ollinger 和 Theyssier 的冻结模型要求每个格点的完整状态按偏序单调变化 @ollinger。@frozen-rule 只固定控制字，格点的数据位仍可周期性变化。以上文献包含本文所用主要方法的先例。四分支精确分类和移动控制特化的文献优先权仍待确定。

= 讨论

#block(breakable: false)[
冻结控制的分类适用于显式给出的光锥和固定的一对有限控制函数。对数深度以随 $T$ 线性增长的输入长度 $n$ 为基准。给出简洁表示的初始状态并以二进制编码时刻，定义的是另一种预测问题。统一性结论针对冻结规则族，移动控制结果给出每个窗口长度上的最优深度。本文的电路模型允许任意接线。若允许无界扇入，移动控制的合取可以用一层计算，输入计数不再给出该对数深度。反过来，若每层的空间接线半径至多为 $r$，则距离 $T$ 的本质坐标迫使深度 $d$ 满足 $T <= d r$。仓库中的 OR 元胞自动机几何下界使用这一附加假设。在任意接线且扇入至多为二时，OR 元胞自动机的精确深度是 $ell(2T+1)$。
]

*复合判据。* 给定演化 $F$、把位串解码到状态空间的 $I$ 与观测 $O$，假设有有限寄存器布尔电路实现初始化、沿实际执行路径的复合，以及观测。若其深度分别为 $eta, delta, epsilon$，重复平方可从 $x$ 计算 $O(F^T(I(x)))$，深度至多为 $eta + 2 ell(T+1) delta + epsilon$。另一个统一编译器要求原语具有对数空间生成器，并将规范化中的复制纳入成本。若 $delta$ 同时界定两种复合原语的深度，则编译后的深度至多为 $eta + 1 + 2 ell(T+1)(delta+1) + epsilon$。属于 $"NC"$ 还要求以实际输入长度衡量的多对数界。

*模拟判据。* 对指定系统，若有从电路值实例到完整查询 $1^T 0 x$ 的对数空间转导器，并证明预测观测值等于电路值，则其预测语言在对数空间多对一归约下为 P 困难 @ladner。再给出目标语言的多项式时间判定器，即得 P 完全性。若假设 P 与对数空间统一 NC 不相等，经验证的困难性见证可排除该语言属于对数空间统一 NC。该结论涉及复杂性类归属，具体深度的增长率需要另证。规则 110 是文献中另一个具体的 P 完全性结果 @neary。

= 结论

冻结控制的分类将允许常数深度预测的固定规则，与预测深度至少沿某个子序列增长的规则区分开来。在深度增长的分支中，齐次规则的逐时刻深度由观测时刻的二进制置位决定。移动控制模型揭示了另一种机制。只有两轨速度不同时，数据路径才会累积不同的初始控制位。两种分类都先确定本质输入，再构造能够在相应深度内合并这些输入的电路。

#heading(numbering: none)[形式化材料与复现]

#block(breakable: false)[
Lean 形式化代码、Typst 源文件和构建说明均在#link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[项目仓库]中。Lean 工具链和依赖由 `lean-toolchain` 与 `lake-manifest.json` 固定。在仓库根目录运行 #box[`./scripts/check.sh`]，即可检查入口模块覆盖，按警告视为错误的方式构建，审计传递公理依赖并执行审计回归测试。@lean-map 列出主要结果对应的声明。
]

#counter(heading).update(0)
#set heading(numbering: "A.1")
#heading(supplement: [附录])[Lean 声明对应表] <lean-map>

下列路径均相对于 `PredictionDepth/`。所列名称对应于支撑主要结论的机器检验声明。

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 5pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*结果*], [*Lean 模块与声明*]),
  table.hline(stroke: 0.4pt),
  [冻结控制迭代],
  [`FrozenPascal/Semantics.lean` #linebreak() `iterate_data`],
  [统一分类],
  [`FrozenPascal/UniformClassification.lean` #linebreak()
   `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [Pascal 支撑集],
  [`FrozenPascal/HomogeneousPascal.lean` #linebreak() `pascalSupport_card`],
  [移动控制],
  [`TransportedControl.lean` #linebreak()
   `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
   `exact_prediction_depth`, `constant_depth_iff`],
  [复合判据],
  [`EncodedPathComposition.lean` #linebreak()
   `EncodedPathImplementation.predictor_depth_le` #linebreak()
   `Complexity/UniformComposition.lean` #linebreak()
   `UniformRegisterWitness.depth_le_costs`],
  [模拟判据],
  [`Complexity/StandardHardness.lean` #linebreak()
   `SimulationWitness.prediction_P_complete` #linebreak()
   `Complexity/NCClosure.lean` #linebreak()
   `SimulationWitness.prediction_not_uniformNC`],
  table.hline(stroke: 0.7pt),
)

#bibliography("references.bib", style: "ieee", title: [参考文献])
