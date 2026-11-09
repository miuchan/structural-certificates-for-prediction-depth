# 定理 B：模拟归约与条件性困难性

[English](../../../docs/hardness.md) · **简体中文** · [日本語](../../ja/docs/hardness.md) · [Esperanto](../../eo/docs/hardness.md)

标准复杂性层在 `PredictionDepth/Complexity/Logspace.lean`、`CVP.lean` 和 `StandardHardness.lean` 中，命名空间为 `PredictionDepth.StandardComplexity`。`PredictionDepth/Hardness.lean` 保留通用辅助定理与一元查询编码。

## 标准复杂性层

`StandardComplexity.Logspace` 使用 cslib 的有限控制、二进制字母表、多带图灵机：输入带只读，输出带只能追加，工作空间按访问过的工作带单元数计量。`logspace_comp` 调用已证明的重算编译定理：当第二台机器需要中间结果的某个符号时，重新运行第一台机器，而不储存整个中间串。

`CVP.lean` 使用具体的 De Morgan 电路、输入赋值和单射二进制编码。导入的 `cvp_logSpaceComplete` 已经通过多项式时间机器的计算表电路与对数空间序列化器证明 CVP 的 P 完备性。源问题困难性和归约闭包不再是本层定理的参数。

`StandardComplexity.SimulationWitness` 仅要求具体动力系统的模拟数据：

1. 把每个合法 CVP 实例映为模拟时间与初始状态编码。
2. 给出产生**整个一元时间查询**的对数空间机器证明。
3. 证明动力系统在该时间的观测结果等于原电路输出。

`SimulationWitness.prediction_P_hard` 据此得出实际 `LogSpaceHard @Cslib.Complexity.P`；再给出目标预测语言属于实际 P 的机器证明，便得到 `prediction_P_complete`。`time_polynomial` 和 `payload_length_polynomial` 从查询生成器的对数空间性质推导多项式时间字段与编码长度界，未预先假定困难性结论。

CVP 使用合法实例类型不会把目标结论弱化为 promise 问题：其困难性定理涵盖所有输入编码，特别包括 `encBits` 上的全部二进制字；归约输出总是合法实例，而本项目的目标预测语言定义在全部二进制字上，非法查询一律拒绝。

标准机器基础来自固定提交 [cslib-frontier `3c44ce0b`](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d)。依赖源代码和本项目代码共同由 Lean 编译；文献陈述不是外部证明 oracle。完整的统一 NC 层及其条件性结论由相应并行复杂性模块连接。

## 通用辅助层

以下说明对应 `PredictionDepth.Hardness`，便于复用到其他归约类别。其参数化结论不应与上面的标准实例混淆。

1. `encodeQuery t x = 1^t 0 x` 是时间采用一元编码的二进制查询。`decode_encodeQuery` 与 `encode_decodeQuery` 证明编码、解码互逆，`encodeQuery_injective` 证明编码无歧义。`decoded_time_le_length` 保证任何合法查询中的时间不超过查询长度。非法查询被拒绝。
2. `predictionProblem F observe decodeState` 对合法查询计算 `observe ((F^[t]) (decodeState x))`。输入状态的编码与动力系统状态类型明确分开。
3. `SimulationWitness` 携带输入编码、模拟时间、两者的多项式界，以及所有输入上模拟输出等于源问题答案的证明。`query_length_polynomial` 从时间和编码长度界推出整个一元查询的多项式长度界。
4. 给定整个查询生成函数的可接受性证明，`SimulationWitness.reduction` 构造 many-one 归约。归约的正确性由模拟语义推出，未作为最终困难性结论预先假定。
5. `Reduction.trans` 构造复合归约；`prediction_P_hard` 将源问题的 P-hard 性传递到预测问题；再给出预测问题属于 P 的证明，即得 `prediction_P_complete`。
6. `prediction_not_NC` 证明：若所选并行类包含于 P、对所选归约封闭，且 P 与此类不相等，则该预测问题不属于此类。证明没有推出线性深度，也没有证明 P 与 NC 的分离。

## 哪些内容是定义，哪些是显式假设

`InP` 并非任意谓词：它用 mathlib 的 `Turing.TM2ComputableInPolyTime` 定义，输入编码为二进制字本身，输出为一个布尔位，并额外要求每条栈的字母表有限。原因是当前 mathlib 的 `FinTM2` 只在结构字段中保证输入栈字母表有限。有限标签、有限控制状态及有限栈数由 `FinTM2` 提供。本模块没有使用 mathlib 中尚待证明的 `TM2ComputableInPolyTime.comp`。

检查 `TM2.Stmt` 和 `stepAux` 可知，每条指令中的函数只访问有限控制状态及至多一个栈顶符号，不能一次读取整条无限增长的栈。每个标签对应有限的指令语法，标签总数也有限，因此按 `step` 计时不会把无界计算藏在一次步骤内。`Complexity/StackMachineBridge.lean` 的 `stack_InP_implies_standard_P` 使用经过证明的 TM2 到多带机模拟，将这种辅助机器见证嵌入标准层 P；没有另行假定模型等价性。

以下四项只出现在通用辅助层的参数化定理中；这不是标准版本的待补前提。标准版本的调用者不需要提供 CVP 困难性或复杂性类闭包证明：

| 辅助层参数 | 预期的标准实例 | 标准层的处理 |
| --- | --- | --- |
| `ReductionSystem.Admissible` 及恒等、复合闭包 | 全函数的对数空间转导 | `Complexity/Logspace.lean` 接入实际机器及已证明的复合闭包 |
| `hencode` | 包括一元时间串在内的整个查询可在对数空间生成 | 否；这是具体模拟构造的义务 |
| `hsource : PHard S source` | 选定编码的 CVP 为 P-hard | `Complexity/CVP.lean` 使用具体图灵机表格归约的证明 |
| `ParallelClassAssumptions S NC` | 对数空间统一 NC 包含于 P，且对所选归约封闭 | `UniformNC`、`UniformReachability`、`NCClosure` 给出实际定义和证明 |

`prediction_P_complete` 还显式要求 `hP`，即目标预测语言的一个有限字母表多项式时间 TM 证明。对固定有限邻域元胞自动机及一元时间输入，这通常通过逐步模拟建立；本模块没有替某个未指定的局域规则构造该机器。

归约需要给出输出查询的多项式长度界。目标预测过程的完整轨迹空间界由具体系统的模拟分析给出。`payload_polynomial` 证明初始状态编码的长度界。局域性、门构件、通道、同步和交叉构造属于验证 `simulation_correct` 与 `hencode` 的方法；困难性传递本身只需要它们导出的语义与归约义务。

这些接口假设只属于通用辅助层；标准 P-hard/P-complete 结论应使用 `StandardComplexity.SimulationWitness` 的定理，那里已实例化实际对数空间机器与已证明的 CVP 完备性。所有具体系统的义务均出现在 Lean 类型中，可通过 `#check` 逐项检查。

## 参考文献

CVP 的对数空间 P 完备性可追溯到 Richard E. Ladner，*The Circuit Value Problem is Log Space Complete for P*，SIGACT News 7(1), 18–20, 1975。[作者论文目录](https://homes.cs.washington.edu/~ladner/papers.html)

P-completeness、NC 归约、困难性传递及其与 P/NC 分离的关系参见 Greenlaw、Hoover、Ruzzo 的 *Limits to Parallel Computation: P-Completeness Theory*，尤其关于归约和 CVP 的章节。文献说明数学背景；机器检查的依据是依赖库与本仓库中的证明项。[作者提供的全书](https://homes.cs.washington.edu/~ruzzo/papers/limits.pdf)
