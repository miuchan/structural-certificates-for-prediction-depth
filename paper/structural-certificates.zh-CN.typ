#let title = "单侧受控元胞自动机的预测深度"
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
  #text(size: 21pt, weight: "bold", title)
  #v(0.2em)
  #text(size: 13pt)[Lean 形式化分类]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*摘要。* 本文对一类单侧元胞自动机的预测深度进行分类。冻结控制字决定有限域 $bb(F)_2$ 上的数据更新中，等待项和传输项是否启用。输入显式给出初始窗口，输出为光锥顶点的预测数据位。对每条固定规则，可执行分类器选定一个分支，同一个多项式规模、对数空间统一的 De Morgan 电路族在每个时刻都满足该分支的深度上界。预测语言属于对数空间统一 $"NC"^0$，当且仅当传输恒关，或传输恒开且等待恒关。当传输控制函数非常值，或传输恒开且等待控制函数非常值时，深度为 $Theta(log(T+1))$。齐次 Pascal 规则的深度介于 $T$ 的二进制置位数及其三倍之间。作为结构性对照，本文另求解一种单路径移动控制规则。正时刻下，两轨同速时深度恰为一，异速时恰为 $ceil(log_2(T+1))$。Lean 4 验证了分类、动力学与有限预测的对应，以及冻结规则的电路界和生成器。

*关键词。* 元胞自动机、电路深度、对数空间统一性、Lean 4。
]

= 引言

代数结构可以使预测元胞自动机未来状态的电路远浅于逐层模拟的电路 @moore。本文考察单侧双轨元胞自动机中，哪些固定控制函数允许常数深度预测，以及预测深度如何随观测时刻变化。

主结果是冻结规则的四分支分类（@frozen-classification）。有限的控制函数测试选定分支。每个分支都有逐时刻下界，并由同一个实际电路生成器在每个时刻达到相应上界。齐次分支的深度由观测时刻的二进制置位数控制，且随时刻非单调变化。核心构造将路径计数化为并行计算的前缀统计，再在对数深度内选择系数（@uniform-construction）。作为结构性对照，本文另求解一个单路径移动控制规则（@transport-depth），其中相对速度决定路径遇到的不同初始控制位数。

= 预备知识

对整数格点 $bb(Z)$ 上的构型迭代局部规则 $T$ 次，并读取原点的数据位。本文主要结果涉及的模型均采用半径为一的单侧更新，因此初始窗口由格点 $0, dots, T$ 组成。冻结模型的输入先给出 $q(T+1)$ 个控制位，再给出 $T+1$ 个数据位。控制字宽 $q$ 及两个控制电路均固定，与 $T$ 无关。合法输入长度 $n=(q+1)(T+1)$ 唯一确定 $T$。预测语言 $L_(s,h)$ 由预测结果为一的合法位串组成，其他长度一律拒绝。

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

记 $p(T)$ 为 $T$ 的二进制表示中置位的个数，$d_s,d_h$ 分别为两个固定控制电路的深度。控制函数非常值，指它能取到两个布尔值。以下各界对所有有限时刻成立，包括 $T=0$。

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
    [$h$ 非常值，或 $h equiv 1$ 且 $s$ 非常值],
      [$ell(T+1)$], [$104(ell(T+3)+1)+max(d_s,d_h)$],
    [$s equiv h equiv 1$], [$p(T)$], [$3p(T)$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [固定冻结控制函数在合法长度上的深度界。],
  kind: table,
  supplement: [表],
) <regimes>

#theorem("统一分类")[
  对每一对固定控制电路，都存在同一个对数空间统一的多项式规模 De Morgan 电路族，判定整个预测语言，并在每个合法长度上满足 @regimes 中相应的深度上界。它在所有长度上的深度均为 $O(log(n+2))$。表中的下界适用于 $D(T)$，也适用于任意扇入至多为二的布尔电路。常数深度的充要条件为
  $
    L_(s,h) in "logspace-uniform " "NC"^0
    quad <=> quad h equiv 0 or (h equiv 1 and s equiv 0).
  $
]<frozen-classification>

== 统一分类的证明

*局域情形与纯移位情形。* 若 $h equiv 0$ 且 $T>0$，由幂等性知输出为 $s(a_0)x_0$。纯移位情形输出 $x_T$。当 $T=0$ 时，所有规则都输出 $x_0$。

*非常值控制情形。* 若 $h$ 非常值，将 $x_T$ 以外的数据位全部置零。无论 $s$ 如何，@frozen-sum 中唯一可能非零的项为 $x_T product_(j=0)^(T-1) h(a_j)$。任何非常值布尔控制函数都至少有一个本质输入位。这可由连接两个不同输出的控制字的逐位翻转路径看出。在这个受限输入上，前 $T$ 个控制字各贡献一个本质输入位，$x_T$ 再贡献一个。若 $h equiv 1$ 且 $s$ 非常值，则选取控制字，使 $s(a_0)=1$ 且格点 $1$ 至 $T$ 上的 $s(a_i)=0$。于是每个 $w_k=1$，@frozen-sum 为全部 $T+1$ 个数据位的奇偶性。两种情形都由本质坐标数给出相同的下界。

该分支的上界由 @uniform-construction 中的电路构造给出。

*齐次 Pascal 规则。* 当 $s equiv h equiv 1$ 时，系数为 $binom(T,k) mod 2$。在 $bb(F)_2$ 上，恒等式
$
  (1+z)^T = product_(j : "bit"_j(T)=1) (1+z^(2^j))
$
表明恰有 $T$ 的二进制子掩码对应的项出现。因此有 $2^(p(T))$ 个本质数据位，深度下界为 $p(T)$。平衡异或树用 $p(T)$ 轮归约这些叶节点，每个异或门至多需要三层 De Morgan 电路。统一生成器扫描 $k=0, dots, T$，输出子掩码对应的接线，并写出门数为 $5 p(T) 2^(p(T))$ 的规则异或归约电路。

*同一个统一电路族。* 控制电路及分类选定的分支均已固定。对合法长度，对数空间转导器写出相应分支的预测器。对其他长度，它写出拒绝电路。输出编码的长度为多项式，因而门数也为多项式。局域分支和纯移位分支的深度具有常数上界。非常值控制分支的下界随 $T$ 增长，齐次分支的下界沿 $T=2^r-1$ 增长。这给出了常数深度的充要条件。 #qed

齐次规则在 $T=2^r-1$ 时至少需要 $r$ 层，而在紧接着的 $T=2^r$ 时至多需要三层。对于 $r>3$，最优深度严格下降。配套分类器按前缀遍历控制字，以检查控制函数是否恒定。Lean 证明返回值与对应的分支条件等价。一次检查在遇到首个反例时结束，最坏情况下可访问 $2^q$ 个控制字。

== 统一预测电路 <uniform-construction>

令 $m=T+1$。在所有格点上并行计算两个控制函数后，电路将所得的控制位、数据轨与一个 $m$ 位独热时刻标记 $tau$ 一起存入寄存器。标记从 $u=0$ 开始。按 $T$ 的二进制位依次执行下标加倍 $u -> 2u$，遇到一位时再执行 $u -> u+1$。这些操作只需重接标记线，并用零填充空位。控制轨和数据轨直接传递，最终只有 $tau_T$ 为一。

*并行前缀统计。* 对每个 $k$，统计前 $k+1$ 个等待控制位中的一得到 $w_k$，并取前 $k$ 个传输控制位的合取得到 $e_k$。各前缀相互独立、并行计算。对 $a$ 个输入位，计数器的字宽为 $b=ell(a+1)$，填充后有 $P=2^b$ 个字对。每个初始字对表示一个输入位或零。三输入字压缩器逐位计算异或得到和字，逐位取多数再左移一位得到进位字。两个输出字保持模 $2^b$ 的总和，无需跨位传播进位。每轮用两个这样的压缩器将两个字对合并成一个字对。经过 $b$ 轮，只需读取根节点的字对。最后连续 $b$ 次把该字对与零字送入压缩器，每次清除进位字中一个新的低位。由于 $a<2^b$，输出就是准确的计数。每条路径只在末尾解析进位，故深度为 $O(b)$。

*系数选择。* 生成电路时，枚举满足 $0 <= u,k < m$ 和 $0 <= j <= k+1$ 的三元组 $(u,k,j)$。当 $u<k$ 时令 $C_(u,k,j)=0$，其余情形取 $M(j,u-k) mod 2$。若 $u>=k$ 且 $j=0$，该系数在且仅在 $u=k$ 时为一。若 $j>0$，由 Lucas 定理可知，系数为一当且仅当 $u-k$ 的置位集合包含于 $j+u-k-1$ 的置位集合 @rowland。生成器可以逐位扫描这两个整数。系数为一的表项将权重的各位与 $j$ 逐一比较，再把相等测试与 $tau_u$ 相与。系数为零的表项输出常量零。恰有一对 $(u,j)$ 满足时刻和权重条件，因此格点 $k$ 的表项异或结果为 @frozen-sum 所需的系数 $C_(T,k,w_k)$。电路先沿 $j$、再沿 $u$ 归约，将结果与 $e_k$、$x_k$ 相与，最后沿 $k$ 归约。每个异或归约读取一个保留进位计数器的最低位。

#figure(
  table(
    columns: (2.1fr, 1fr, 1.15fr),
    inset: (x: 6pt, y: 4pt),
    align: left,
    stroke: none,
    table.hline(stroke: 0.7pt),
    table.header([*阶段*], [*并行实例数*], [*深度上界*]),
    table.hline(stroke: 0.4pt),
    [控制函数计算], [$2m$], [$max(d_s,d_h)$],
    [寄存器初始化与时刻标记], [一个寄存器], [$6B$],
    [等待位计数与传输位合取], [各 $m$ 个], [$22B$ 和 $5B$],
    [系数表项测试], [$m^2(m+3)/2$], [$5B$],
    [先沿 $j$、再沿 $u$ 异或], [先 $m^2$，后 $m$], [各 $23B$],
    [与传输前缀和数据相与，再异或], [先 $m$，后一个], [$2+23B$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [冻结预测电路的资源，$B=ell(T+3)+1$。两种前缀统计并行。],
  kind: table,
  supplement: [表],
) <uniform-resources>

*规模与生成。* 系数表有 $m sum_(k=0)^(m-1) (k+2)$ 行。按构造中的规则合取电路计，每行使用 $O(log^2(m+1))$ 个门。对 $a$ 位的填充计数器，每轮有 $O(a+1)$ 个块，每块有 $O(log(a+2))$ 个位通道，共 $O(log(a+2))$ 轮。即使为每个输出复制压缩器，每个位通道也只用 $O(log(a+2))$ 个门。计入各异或归约，计数器共有 $O(m^2)$ 个，每个至多有 $m+1$ 个输入。控制函数副本、标记接线和合取也都计入 $O(m^3 log^3(m+1))$ 的总门数上界。整条路径只串接常数个对数深度阶段，故总深度为 $O(log(m+1))$。@depth-budget 推导 @regimes 中的常数。

序列化器对一元长度 $n$ 计数，检查是否为 $q+1$ 的正整数倍，并在合法长度上求出 $m$ 与 $T$。它用 $(k,u,j)$ 枚举系数表项，再逐位扫描。寄存器的时刻、等待、传输与数据各占一个宽为 $m$ 的连续块。每轮的第 $e$ 个计数块读取前一轮的第 $2e$ 和 $2e+1$ 个块，越界时补零。门记录由轮数、块下标、块内位号和局部模板中的位置确定。并行拼接时，生成器统计前面各块的门数，据此平移内部接线编号。串行复合时，按下标重新生成前级对应的输出编号。对于宽度为 $W$ 的串行链，生成器追加恒等门 $y and y$，使每个阶段的输出连续编号。若有 $N$ 个原始输入和 $G$ 个在前的门，局部线号 $a$ 就映射为 $N+G-W+a$。这样便可逐轮计数，无需维护栈。生成器对这些块的嵌套层数是固定的，下标、偏移和引用均以 $n$ 的多项式为上界。因此只需常数个计数器和算术临时变量，共占 $O(log(n+2))$ 位工作空间。门列表和输出引用列表均按顺序写出。

= 移动控制的结构性对照

在这个单独的模型中，控制轨有独立的动力学，数据只沿一条路径传播。固定速度 $u,v in {0,1}$，并设 $(c_i,d_i)$ 为布尔控制轨和数据轨。同步规则为
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

*证明。* 反向路径上的第 $k$ 步读取格点 $i+k v$ 在时刻 $T-1-k$ 的控制位。该位来自初始格点 $i+k v+(T-1-k)u$，故得 @transport-iterate。当 $T=0$ 时，输出即输入线 $d_i$。正时刻且两轨同速时，所有控制位的初始下标相同，因而只需求一个控制位和一个数据位的合取。一般地，初始控制下标为 $i+(T-1)u+k(v-u)$。两轨异速时，初始控制下标按正序或逆序遍历 $i, dots, i+T-1$。每个不同因子都是本质输入，因为将其他因子都设为一时，翻转该因子即改变输出。因此同速时有两个本质坐标，异速时有 $T+1$ 个。对 $m$ 个因子，高度为 $ell(m)$ 的平衡合取树达到本质输入下界。将叶节点数补至不小于 $m$ 的最小的二的幂，使用的二输入门数为 $2^(ell(m))-1 <= 2m$。 #qed

速度对 $(u,v)=(0,0)$ 是以 $c_i$ 为等待控制的冻结无传输情形。只把 $u$ 改为一后，数据仍不传输，深度却成为对数级。当 $(u,v)=(1,1)$ 时，两轨都移动，但同速带来常数深度。对于这种单路径规则，起决定作用的是随数据路径移动时遇到的不同初始控制位的数量。文献 @moore 的时变框架涵盖该规则。单路径结构使精确深度可求。

= 相关工作

*Pascal 奇偶性与快速预测。* 奇数项计数 $2^(p(T))$ 是经典结果。Rowland 将二进制计数归于 Glaisher，并用 Lucas 定理推导该式 @rowland。文献 @moore 已将 Pascal 系数用于齐次加性规则的快速预测，其中模求和门可采用无界扇入。本文的 Pascal 结论给出逐时刻的有界扇入下界，并通过经验证的统一 De Morgan 电路生成器，使上界在常数因子内匹配整个深度曲线。

*依赖控制的线性轨与系数公式。* Moore 对时空依赖的线性阶段给出了通用分治法。在该文设定下，其有界扇入预测深度为 $O(log^2(T+2))$ @moore。冻结控制与单侧等待、传输结构使本文可以利用前缀统计，在这一特例中达到 $O(log(T+2))$。@frozen-sum 中的系数也有经典矩阵解释。单步数据映射在相应的有限窗口上是上双对角矩阵。Higham 的矩阵函数差商公式把中间超对角元素的乘积，与对角元素上的差商相乘 @higham。对于单项式 $z^T$，该差商是 $T-k$ 次完全齐次多项式。在对角元素为零或一时，它计数同一批非负整数有序分拆。先将多项式恒等式特化到整数零一元素，再模二约化，无须在 $bb(F)_2$ 上作除法。

*机械化证明与冻结的含义。* Silváši 和 Tomášek 在 Lean 中形式化了有界格网和可计算元胞自动机 @silvasi，为元胞自动机的机械化验证提供了先例。本项目验证规则族的深度分类和实际电路生成器。Ollinger 和 Theyssier 的冻结模型要求每个格点的完整状态按偏序单调变化 @ollinger。@frozen-rule 只固定控制字，格点的数据位仍可周期性变化。本文把可执行分类器、逐时刻深度界和经验证的统一电路生成器结合起来，覆盖整个冻结规则族。精确四分支分类和单路径移动模型的文献优先权仍待确定。

= 形式化方法与适用范围

窗口接口把无限格点上的动力学与有限输入连接起来。`rawSample` 从构型读取窗口，`decodeRaw` 把任意合法窗口扩展为无限构型。Lean 证明，从这个扩展中采样恰好恢复输入位。因此，在采样窗口上证明的正确性适用于所有合法输入。由时间提升到输入长度后，合法长度沿用同一个预测器，其余长度使用拒绝电路。

统一性证明生成的正是深度证明中所用电路的编码，其中包含长度可变的门列表和输出引用列表。可复用的编码组合操作验证并行拼接和串行复合中的引用范围与编号平移，使生成器可以在对数空间内通过重新计算恢复单个引用。分类定理用选中的同一个电路族见证正确性、规模、统一性和逐时刻深度界。移动控制定理给出各窗口长度上的最优深度。

每个冻结控制字从 $0$、$x_i$、$x_(i+1)$ 和 $x_i+x_(i+1)$ 四种局部数据映射中选取一种。控制给定后，数据动力学是单向线性的。输入显式给出窗口，长度随 $T$ 线性增长，电路允许跨格点接线。配套形式化开发还给出适用于其他模型的复合和模拟判据，应用时需要为对应模型提供实现或归约的见证。

= 结论

精确的 $"NC"^0$ 判据和 Pascal 曲线刻画了冻结控制下预测深度随时间变化的不同方式。在非常值控制分支中，前缀统计使路径系数可在对数深度内求得，同一个统一电路族由此在各合法长度上满足深度上界。在移动控制的单路径模型中，相对速度通过改变路径所读的不同初始控制位数来决定深度。

#heading(numbering: none)[形式化材料与复现]

形式化结果对应这一 #link("https://github.com/miuchan/structural-certificates-for-prediction-depth/tree/08e9aa3dfad7132226849b39386005397469d656")[固定的 Lean 源码版本]。Typst 稿件与构建说明见 #link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[项目仓库]。使用与 PDF 对应的完整提交 SHA 可定位同一源码快照。仓库记录了重建四种语言版本所需的固定 Typst 和字体版本。GitHub Actions 检查所检出的提交能否重建四种语言的 PDF。运行 #box[`./scripts/check.sh`] 可执行严格的 Lean 构建与公理审计。@lean-map 列出主结果对应的声明。

#counter(heading).update(0)
#set heading(numbering: "A.1")
#heading(supplement: [附录])[深度预算] <depth-budget>

归一化计数树至多使用 $2+14b$ 层，其中包括初始化和各轮合并中的复制。末尾加法至多使用 $1+8b$ 层，合计至多 $22(b+1)$ 层。因此前缀计数至多用 $22B$ 层。奇偶归约读取计数的最低位，计入空输入情形后至多用 $23B$ 层。表项测试使用 $5B$ 层预算，包含逐位匹配、合取和时刻标记。传输前缀合取至多用 $5B$ 层，与查表并行。因此解码器总深度至多为 $22B+5B+3 dot 23B+2=96B+2 <= 98B$。计入归一化，寄存器初始化至多两层，之后至多有 $2 ell(T+1)$ 个阶段，每阶段至多两层。因此寄存器路径至多用 $6B$ 层，加上控制函数计算后，总深度至多为 $104B+max(d_s,d_h)$。

#heading(supplement: [附录])[Lean 声明对应表] <lean-map>

以下路径均相对于 `PredictionDepth/`。

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 5pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*结果*], [*Lean 模块与声明*]),
  table.hline(stroke: 0.4pt),
  [冻结迭代], [`FrozenPascal/Semantics.lean` #linebreak() `iterate_data`],
  [窗口接口], [`FrozenPascal/GuardRules.lean` #linebreak() `rawSample_decodeRaw`],
  [可执行分类器], [`FrozenPascal/Classification.lean` #linebreak() `classify`, `classify_eq_iff`],
  [统一分类], [`FrozenPascal/UniformClassification.lean` #linebreak()
    `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [统一预测器], [`FrozenPascal/UniformPrediction.lean` #linebreak()
    `uniformGuardedPrediction_code_logspace` #linebreak() `uniformGuardedPrediction_depth`],
  [编码复合], [`Complexity/CodeLogspace.lean` #linebreak() `compCode_logspace`],
  [Pascal 支撑集], [`FrozenPascal/HomogeneousPascal.lean` #linebreak() `pascalSupport_card`],
  [移动控制], [`TransportedControl.lean` #linebreak()
    `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
    `exact_prediction_depth`, `constant_depth_iff`],
  table.hline(stroke: 0.7pt),
)

#bibliography("references.bib", style: "ieee", title: [参考文献])
