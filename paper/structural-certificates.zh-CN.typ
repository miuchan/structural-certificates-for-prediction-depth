#import "transported-control-figure.typ": transported-control-figure

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
*摘要。* 本文对一类单侧元胞自动机的预测深度进行分类。冻结控制字决定有限域 $bb(F)_2$ 上的数据更新中，等待项和传输项是否启用。输入显式给出初始窗口，输出为光锥顶点的预测数据位。对每条固定规则，可执行分类器选定一个分支，同一个多项式规模、对数空间统一的 De Morgan 电路族在每个时刻都满足该分支的深度上界。预测语言属于对数空间统一 $"NC"^0$，当且仅当传输恒关，或传输恒开且等待恒关。当传输控制函数非常值，或传输恒开且等待控制函数非常值时，深度为 $Theta(log(T+1))$。对正时刻 $T$，齐次 Pascal 规则的最小 De Morgan 电路深度为 $2p(T)+1$，其中 $p(T)$ 是 $T$ 的二进制置位数。经验证的统一生成器使用至多 $3p(T)$ 层。单路径移动控制规则在两轨同速时的正时刻深度恰为一，异速时恰为 $ceil(log_2(T+1))$。对于加性控制，有序区块摘要给出线性规模、对数空间统一的预测器和匹配阶数的对数深度界。Lean 4 验证了冻结分类、逐时刻深度界和上述统一构造。

*关键词。* 元胞自动机、电路深度、对数空间统一性、Lean 4。
]

= 引言

给定输入编码与电路模型，演化规则 $F$ 和观测 $O$ 的哪些可验证结构条件能限定 $O(F^T(x))$ 的电路深度？代数结构可以使预测元胞自动机的电路远浅于逐层模拟的电路 @moore。本文考察单侧双轨元胞自动机中，哪些固定控制函数允许常数深度预测，以及预测深度如何随观测时刻变化。

主结果是冻结规则的四分支分类（@frozen-classification）。有限的控制函数测试选定分支，对应的同一个对数空间生成器在每个时刻达到所述上界。核心构造利用传输次序固定这一事实，以两种前缀统计概括到同一终点的所有路径，再用二进制无进位判据识别抵消后留下的系数（@uniform-construction）。齐次分支的深度随时刻的二进制置位数非单调变化。作为结构性对照，单路径移动模型中，相对速度决定路径遇到的不同初始控制位数（@transport-depth）。

= 预备知识

对整数格点 $bb(Z)$ 上的构型迭代局部规则 $T$ 次，并读取原点的数据位。本文主要结果涉及的模型均采用半径为一的单侧更新，因此初始窗口由格点 $0, dots, T$ 组成。冻结模型的输入先给出 $q(T+1)$ 个控制位，再给出 $T+1$ 个数据位。控制字宽 $q$ 及两个控制电路均固定，与 $T$ 无关。合法输入长度 $n=(q+1)(T+1)$ 唯一确定 $T$。预测语言 $L_(s,h)$ 由预测结果为一的合法位串组成，其他长度一律拒绝。

上界所用的布尔电路包含二输入 AND 门和 OR 门、NOT 门以及常量。输入线的深度为零，NOT 门计一层。门的输出可以共享，接线可以跨越任意格点。在此接线模型中，分类表的下界适用于任意扇入至多为二的布尔门。对固定规则，记 $D(T)$ 为时刻 $T$ 合法窗口上的最小 De Morgan 电路深度，并令 $ell(m)=ceil(log_2 m)$，其中 $m >= 1$。统一电路族按输入长度索引。确定性对数空间转导器读取一元编码的长度，并写出包含门、接线和输出的完整电路编码。本文关于 $"NC"$ 的结论均采用对数空间统一性。

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
      [$ell(T+1)$], [$O(log(T+2))$],
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

配套分类器按前缀遍历控制字，以检查控制函数是否恒定。Lean 证明返回值与对应的分支条件等价。一次检查在遇到首个反例时结束，最坏情况下可访问 $2^q$ 个控制字。

== Pascal 分支的精确深度 <pascal-exact>

令 $p=p(T)$，$N=2^p$。Pascal 规则的输出为 $N$ 个输入的奇偶性。若 XOR 是原生二输入门，平衡异或树达到下界 $p$。若采用 De Morgan 门，精确深度在 $T=0$ 时为零，在 $T>0$ 时为 $2p+1$。

*证明。* 上界构造从每个叶节点同时提供数据位及其否定。设两个子树的奇偶性分别为 $a,b$。用两层门即可从这两个值及其否定计算正、反两种结果，分别为 $(a and not b) or (not a and b)$ 与 $(a and b) or (not a and not b)$。因此叶节点的一层否定加上 $p$ 轮合并，共用 $2p+1$ 层。

为证下界，先把无关输入置为常量，再把共享电路展开为深度不增的公式。将否定移至叶节点并化简常量。Khrapchenko 的奇偶性下界要求至少 $N^2$ 个文字叶节点 @khrapchenko。移动否定保持叶节点数，化简常量只可能减少它。深度至多为 $2p$ 的公式最多有 $2^(2p)=N^2$ 个叶节点。等号要求每个内节点均为二叉分支，且全部叶节点都在深度 $2p$。原展开树因而只含 AND 和 OR，计算单调函数。但 $N>=2$ 个输入的奇偶性并不单调，故深度必须超过 $2p$。 #qed

Lean 验证了两种门基下的逐时刻最优深度。De Morgan 深度在 $T=2^r-1$ 时为 $2r+1$，到 $T=2^r$ 时降至三，其中 $r>=2$。@regimes 的统一分类采用独立的 $3p$ 层生成器。

== 统一预测电路 <uniform-construction>

记 $B(a)$ 为非负整数 $a$ 的二进制置位集合。若 $w>0$，Lucas 定理表明，$M(w,r)$ 为奇数当且仅当 $B(r) subset.eq B(w+r-1)$ @rowland。等价地，$r$ 与 $w-1$ 的二进制相加无进位。若和包含 $r$ 的所有置位，减去 $r$ 时无需借位，只须清除这些位，剩余置位属于 $w-1$。补上 $w=0$ 的情形，得到系数判据
$
  M(w,r) mod 2 = 1 quad <=> quad
  (w=0 and r=0) or (w>0 and B(r) inter B(w-1) = emptyset).
$ <no-carry>

传输前缀 $e_k$ 决定能否抵达 $k$。传输全部启用时，每个允许等待的格点均可吸收任意次等待，所以只需知道这样的格点数 $w_k$。例如，将一次等待分配给两个可等待格点之一，得到的两条路径相互抵消。在 @no-carry 中，这对应 $r=1$ 与 $w_k-1=1$ 共用最低位。

*从判据到电路。* 并行计算控制函数。用平衡 AND 树计算各 $e_k$，用保留进位的计数器计算各 $w_k$。每轮在常数深度内将两个字对压缩为一个字对，末尾加法只需在 $O(log(T+2))$ 位上传播进位。生成器对每个 $k$ 已知 $r=T-k$，逐位扫描候选计数 $j=0,dots,k+1$ 并按 @no-carry 筛选。电路并行检验通过筛选的候选值是否等于 $w_k$，至多一个匹配。将选出的系数与 $e_k$、$x_k$ 相与，再对各格点取奇偶性。即使给每个前缀单独配一个计数器，也只需串联常数个对数深度阶段，规模为多项式。

*经验证的生成器。* Lean 验证的共享解码器适用于窗口内任意时刻 $u$。生成器用 Lucas 逐位测试建立各时刻的系数表，再由独热标记选出 $T$ 对应的表项。标记按 $T$ 的二进制位重接线路，从而实现通用复合接口。各奇偶归约读取保留进位计数器的最低位。对数空间转导器通过重新计算确定接线引用，写出此电路的完整门列表和输出列表。显式深度界为 $104(ell(T+3)+1)+max(d_s,d_h)$，布局与资源核算见 @depth-budget。


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

#transported-control-figure(
  caption: [取 $i=0$、$T=4$，图示反向路径第 $k$ 步读到的初始控制格点 $j(k)$。两种情况的路径终点都是初始数据位 $d_4$。],
  alt: "左图中两轨同速，四步都读取初始格点 3 的控制位。右图中两轨异速，依次读取初始格点 0、1、2、3 的控制位。",
  supplement: [图],
) <transport-controls-figure>

@transport-controls-figure 固定数据路径，只改变 $u$。速度对 $(u,v)=(0,0)$ 是以 $c_i$ 为等待控制的冻结无传输情形。只把 $u$ 改为一后，数据仍不传输，深度却成为对数级。当 $(u,v)=(1,1)$ 时，两轨都移动，但同速带来常数深度。对于这种单路径规则，起决定作用的是随数据路径移动时遇到的不同初始控制位的数量。文献 @moore 的时变框架涵盖该规则。对有限布尔单项式系统，迭代的变量支集与固定长度依赖游走之间的对应是经典结果 @boolean-monomial。对有限预测窗口，两轨的平移直接确定了这个支集。

= 有分支的演化控制 <branching-boundary>

*整体平移。* 保留 @frozen-rule 的等待项和传输项，同时令控制轨整体移动，$a_i(t+1)=a_(i+1)(t)$。在反射后的移动坐标系 $y_j(t)=x_(-j-t)(t)$ 中，代入即得
$
  y_j(t+1)=h(a_(-j-1)(0)) y_j(t)+s(a_(-j-1)(0)) y_(j+1)(t).
$
控制函数随之冻结，等待与传输互换。观测 $x_0(T)$ 等于 $y_(-T)(T)$，数据窗口为原窗口的逆序。冻结控制窗口是 $a_(T-1)(0),dots,a_0(0)$，末尾补一个控制字。路径无法在最后一个虚拟格点等待，故结果与填充值无关。Lean 验证了坐标变换和带成本的预测归约。输入重接和恒等输出解码均增加零层、零门，输入重接的电路编码可在对数空间生成。由此把冻结预测的上界传递给平移模型。

*加性控制演化。* 现令控制轨为一位，按 $c_i(t+1)=c_i(t)+c_(i+1)(t)$ 演化，数据按 $x_i(t+1)=c_i(t)x_i(t)+x_(i+1)(t)$ 更新。两式均在 $bb(F)_2$ 上计算。输入将前 $T$ 个格点的控制位和数据位按格点交错排列，末尾附加 $x_T(0)$。当 $T=2$ 时，原点对 $x_1(0)$ 的系数为 $(c_0(0)+c_1(0))+c_1(0)=c_0(0)$。初始控制对 $(1,0)$ 和 $(0,1)$ 在这一终点有相同的等待计数和传输标记，取相同的数据上下文 $(0,1,0)$ 时，预测结果不同。Lean 验证了这一摘要碰撞，据此排除只使用旧摘要和数据上下文的正确读出函数。

此规则仍有简洁的系数公式。令 $Q_T(i)=c_i(T)+c_(i+T)(0)$，即去掉最右一项后的初始控制 Pascal 奇偶性。对 $0 <= k < T$，令
$
  P_(T,k)(i)=product_(j=k+1)^(T-1)(1+c_(i+j)(0)).
$
在 $x_i(T)$ 中，$x_(i+k)(0)$ 的系数在 $k<T$ 时为 $P_(T,k)(i) Q_T(i)$，在 $k=T$ 时为一。各终点共用一次奇偶计算，再由后缀全零测试决定哪些终点取得这个系数。

*证明。* 令 $b_(T,k)(i)$ 为该系数，窗口之外取零。更新规则给出
$
  b_(T+1,k)(i)=c_i(T)b_(T,k)(i)+b_(T,k-1)(i+1).
$
由于布尔位的平方等于自身，$c_i(T)Q_T(i)=(1+c_(i+T)(0))c_i(T)$。对 $k<T$，等待项因此包含后缀因子 $P_(T+1,k)(i)$。当 $k>0$ 时，传输项也有此因子，因为 $P_(T,k-1)(i+1)=P_(T+1,k)(i)$。当 $k=0$ 时，没有传输项，但 $P_(T+1,0)(i)=1$ 会将 $Q_T(i+1)$ 所需的所有初始控制位都置零，故此时 $Q_T(i+1)=0$。提出后缀因子后，剩余的和为 $c_i(T)+Q_T(i+1)=Q_(T+1)(i)$。若 $k=T$，等待项为 $c_i(T)$，传输项为 $Q_T(i+1)$，空后缀下仍为同一个和。$T=0$ 时 $Q_0(i+1)=0$，结论亦成立。全程传输项的系数始终为一。 #qed

对一段连续格点，取摘要 $(Z,V,Q)$。$Z$ 检查段内控制位是否全零，$V$ 是段内右侧控制位均为零的数据位的奇偶性，$Q$ 累计该段对 $Q_T(0)$ 的贡献。令 $lambda_j=binom(T,j) mod 2$，则单格点的摘要是 $(1+c_j(0),x_j(0),lambda_j c_j(0))$。相邻两段按下式合并
$
  (Z_L,V_L,Q_L),(Z_R,V_R,Q_R) |-> (Z_L Z_R,V_L Z_R+V_R,Q_L+Q_R).
$
合并满足结合律，单位元为 $(1,0,0)$。按原顺序合并前 $T$ 个格点后，输出 $x_T(0)+Q V$。生成器根据时刻和位置确定 $lambda_j$。Lean 的通用有序摘要编译器逐轮合并相邻区块，计入叶节点初始化、复制门和读出。它验证所得 De Morgan 电路族的正确性、对数空间统一性、$108(T+1)$ 的门数上界，以及 $T>=1$ 时 $6+5ell(T)$ 的深度上界。合法长度为 $2T+1$，偶数长度由拒绝电路处理。$T=0$ 时预测函数直接返回 $x_0(0)$。

令 $c_0(0)=1$，并将 $c_1(0)$ 至 $c_(T-1)(0)$ 置零，则正时刻的输出为全部 $T+1$ 个数据位的奇偶性。Lean 据此证明任意扇入至多为二的布尔预测电路深度至少为 $ell(T+1)$，与统一上界合得 $Theta(log(T+1))$。正文还可得到更强的有限下界。只保留数据位 $x_0(0)$ 时，输出为 $x_0(0)c_0(0) product_(j=1)^(T-1)(1+c_j(0))$，故前 $T$ 个控制位也均为本质输入。这给出 $ell(2T+1)$ 的深度下界。

= 相关工作

*Pascal 奇偶性与快速预测。* 奇数项计数 $2^(p(T))$ 是经典结果。Rowland 将二进制计数归于 Glaisher，并用 Lucas 定理推导该式 @rowland。Moore 已将 Pascal 系数用于齐次加性规则的预测，在二输入门下达到对数深度，在使用无界扇入模和门时达到对数空间统一 $"ACC"^0$ @moore。Robison 给出了从单一初始种子串行计算单个系数的方法 @robison。@pascal-exact 的逐时刻最优值源于经典奇偶性复杂度。经验证的统一电路族在常数因子内达到这一深度。

*依赖控制的线性轨与系数公式。* @moore 的引理 1 将时间区间对半划分，再合成时空转移系数。定理 1 将此方法用于拟直积，例 1 和例 3 分别涵盖由另一轨控制的二值数据轨，以及加性控制示例这类三角形依赖的线性轨。对模和使用平衡异或树，通用方法在本文的二值轨上给出 $O(log^2(T+2))$ 深度。时间不变性和单侧邻域使冻结系数化为前缀统计。@salo 第 3 节考察有限环上各格点在恒等映射与右邻异或之间的选择，这与 $s equiv 1$、$h(a)=a$ 的局部映射相同。其结论涉及满射性和周期性。本文将控制字纳入输入，并读取有限窗口的一个预测位。

并行前缀电路是经典工具 @ladner-fischer。本文结合平衡合取、保留进位计数和系数判据，得到 $O(log(T+2))$ 的深度。@frozen-sum 的系数也可用经典矩阵公式解释。Higham 的定理 6.1 将上双对角矩阵函数的元素表示为中间超对角元素的乘积乘以主对角元素的差商 @higham。对于 $z^T$，该差商是 $T-k$ 次完全齐次多项式。在对角元素为零或一时，它计数相同的等待分配。可先将多项式恒等式特化到整数零一元素，再模二约化。

*机械化证明与冻结的含义。* Silváši 和 Tomášek 已在 Lean 中形式化有界格网和可计算元胞自动机 @silvasi。Ollinger 和 Theyssier 的冻结模型要求各格点的完整状态按偏序单调变化 @ollinger。@frozen-rule 固定的是控制字，格点数据仍可周期性变化。本文的贡献在于可执行的四分支分类、非常值控制的匹配对数深度界，以及对每条规则以同一个经验证的对数空间生成器在所有长度实现所述上界。上述比较不作优先权主张。


= 形式化方法与适用范围

窗口接口把无限格点上的动力学与有限输入连接起来。`rawSample` 从构型读取窗口，`decodeRaw` 把任意合法窗口扩展为无限构型。Lean 证明，从这个扩展中采样恰好恢复输入位。因此，在采样窗口上证明的正确性适用于所有合法输入。由时间提升到输入长度后，合法长度沿用同一个预测器，其余长度使用拒绝电路。

统一性证明生成的正是深度证明中所用电路的编码，其中包含长度可变的门列表和输出引用列表。可复用的编码组合操作验证并行拼接和串行复合中的引用范围与编号平移，使生成器可以在对数空间内通过重新计算恢复单个引用。分类定理用选中的同一个电路族见证正确性、规模、统一性和逐时刻深度界。移动控制定理给出各窗口长度上的最优深度。

在加性控制和 OR 实例中，同一编译器从有序摘要及其电路生成器导出预测器。OR 实例使用有限识别器检查给定求值器和摘要模板的局部条件，再由归纳覆盖任意长度。将求值器连接到目标动力学仍需语义证明。检查未通过时，该次检查未建立证书。碰撞和位宽下界针对指定摘要或固定切分的独立摘要接口。

本文的输入为指定长度的显式位串，预测电路允许跨任意格点接线。演化规则的局域性与预测器的接线约束是两个独立条件。限制合法初态或要求局域接线，会改变这里的预测任务或电路模型。

配套的 Lean 项目形式化了三类充分判据。A 用有资源界的复合电路构造预测器。B 在给定对数空间模拟见证时，从电路求值问题传递 P 困难性。通过 B 排除统一 $"NC"$ 依赖 $"P" != "NC"$，所得结论是复杂性类的非成员资格。C 从本质输入数推出无条件深度下界。当扇入、维数、半径和位宽固定时，若光锥体积为多项式量级，C 给出的*计数下界*至多为 $O(log(T+2))$。实际预测深度可以超过这一数值。Lean 检查给出的见证，对任意规则寻找见证是另一个问题。本文的可执行分类器在有限控制字母表上检验控制函数的常值性，选定冻结规则的深度分支。

= 结论

冻结控制的常值性决定哪些规则可以常数深度预测，前缀统计为非常值控制提供统一的对数深度预测器。Pascal 分支的深度由时刻的二进制置位数决定。允许路径分支后，整体平移可借坐标变换保留冻结摘要。加性控制中，旧摘要的碰撞给出明确反例，新的有序摘要则可编译为具有匹配阶数深度界的统一预测器。

#heading(numbering: none)[形式化材料与复现]

Lean 源码、Typst 稿件和构建说明见 #link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[项目仓库]。@lean-map 中的声明可在与本 PDF 配套的仓库快照中查阅。仓库记录了重建四种语言版本所需的 Typst 和字体版本。运行 #box[`./scripts/check.sh`] 可执行严格的 Lean 构建、导入覆盖检查、传递公理审计和回归测试。验证指南区分了构建证据与对模型假设的审查。

#counter(heading).update(0)
#set heading(numbering: "A.1")
#heading(supplement: [附录])[生成器布局与深度预算] <depth-budget>

令 $m=T+1$，$B=ell(T+3)+1$。寄存器按宽度 $m$ 分成四块，依次保存时刻标记 $tau$、等待位、传输位和数据。标记从下标零开始，按 $T$ 的二进制位从高到低逐位更新。每次将下标加倍，遇到一再加一，所需操作只有重接线路和补零。

在格点 $k$，解码器枚举 $0 <= u < m$ 与 $0 <= j <= k+1$。若 $u>=k$ 且 $M(j,u-k)$ 为奇数，表项输出 $(w_k=j) and tau_u$，其余表项输出零。先沿 $j$、再沿 $u$ 取奇偶性以选出系数，随后乘以传输前缀和数据位，再沿 $k$ 取奇偶性。

对 $a$ 个输入位，计数器字宽为 $b=ell(a+1)$。归一化计数树至多使用 $2+14b$ 层，其中包括初始化和各轮合并中的复制。末尾加法至多使用 $1+8b$ 层，合计至多 $22(b+1)$ 层。因此前缀计数至多用 $22B$ 层。奇偶归约读取计数的最低位，计入空输入情形后至多用 $23B$ 层。表项测试使用 $5B$ 层预算，包含逐位匹配、合取和时刻标记。传输前缀合取至多用 $5B$ 层，与查表并行。因此解码器总深度至多为 $22B+5B+3 dot 23B+2=96B+2 <= 98B$。计入归一化，寄存器初始化至多两层，之后至多有 $2 ell(T+1)$ 个阶段，每阶段至多两层。因此寄存器路径至多用 $6B$ 层，加上控制函数计算后，总深度至多为 $104B+max(d_s,d_h)$。

系数表有 $m^2(m+3)/2$ 行，另有 $O(m^2)$ 个计数器，每个至多接收 $m+1$ 位。对固定控制函数，规则布局使用 $O(m^3 log^3(m+1))$ 个门。门记录由阶段、块、块内位号及局部模板中的位置索引。对并行拼接，序列化器累计前面各块的门数以取得偏移量。对宽度为 $W$ 的串行链，恒等门 $y and y$ 使每阶段的输出连续编号。若已有 $N$ 个原始输入、$G$ 个门，阶段输出槽 $a$ 对应线号 $N+G-W+a$。固定层数的嵌套循环与对数位宽的计数器足以重新计算接线引用。转导器从一元长度出发，按顺序写出门和输出列表。

#block(breakable: true)[
#set text(size: 9.5pt)
#heading(supplement: [附录])[Lean 声明对应表] <lean-map>

以下路径均相对于 `PredictionDepth/`。

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 3pt),
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
  [Pascal 支撑集与 XOR 深度], [`FrozenPascal/HomogeneousPascal.lean` #linebreak()
    `pascalSupport_card` #linebreak() `homogeneousNativeXorPrediction_depth`],
  [Pascal 的精确 De Morgan 深度], [`FrozenPascal/PascalExactDepth.lean` #linebreak()
    `homogeneous_prediction_deMorgan_exact_depth`],
  [移动控制], [`TransportedControl.lean` #linebreak()
    `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
    `exact_prediction_depth`, `constant_depth_iff`],
  [带成本的预测归约], [`Complexity/PredictionReduction.lean` #linebreak()
    `compile_depth`, `compile_size`, `compile_code_logspace`],
  [整体平移与路径分支], [`TransportedBranching.lean` #linebreak()
    `reverseFrame_iterate`, `reduction`, `prediction_uniform`],
  [加性控制的系数公式], [`AdditiveBranching.lean` #linebreak()
    `trimmedParity_eq_sum`, `iterate_data`],
  [有序摘要编译器], [`Complexity/BlockSummary.lean` #linebreak()
    `compile_eval`, `compile_depth`, `compile_size`, `compile_code_logspace`],
  [加性控制的统一预测与碰撞], [`AdditiveBranching/Summary.lean` #linebreak()
    `predictionFamily_uniform`, `prediction_depth`, `prediction_size` #linebreak()
    `frozenEndpointCollision`, `frozenEndpoint_noReadout`],
  [加性控制的深度下界], [`AdditiveBranching/LowerBound.lean` #linebreak()
    `prediction_depth_lower_bound`],
  [模板检查与摘要界], [`BlockSummary.lean` #linebreak()
    `recognize?`, `findCollision?_sound`, `width_lower_bound`],
  [OR 实例], [`ORAutomaton/Summary.lean` #linebreak()
    `summary_recognized`, `summaryFamily_uniform`],
  table.hline(stroke: 0.7pt),
)
]

#block(breakable: false)[
  #bibliography("references.bib", style: "ieee", title: [参考文献])
]
