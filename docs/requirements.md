# 形式化范围

项目用 Lean 4 证明动力系统预测深度的结构性判据，并涵盖具体机器模型、CVP 的 P 完备性和统一 NC 的归约闭包。下表列出核心判据、复杂性基础及实例。所有列出的模块都由默认入口覆盖。

| 要求 | 形式化证据 | 状态 |
| --- | --- | --- |
| 离散演化与观测 | `Dynamics.predict`；OR 的无限整数格点定义 | 已实现 |
| 有界扇入、任意布线和共享电路 | `BoundedCircuit`、`LayeredNetwork`、`BinaryCircuit` 及语义翻译 | 已实现 |
| 输入长度、固定规模预算、族级统一性与深度定义 | `Families.Policy`、`Admissible`、`RealizesProfile`、`intrinsicDepth`；标准层 `UniformNC` 与具体 OR/A 生成器 | 编译通过；两层模型边界已说明 |
| A：二进制重复平方的语义、次数、紧凑中间表示 | `FastComposition` | 已实现 |
| A：从原语电路构造预测电路及深度、门数、描述规模界 | `CompiledComposition.Implementation` | 已实现 |
| A：只约束实际经过的表示与组合 | `PathComposition`，含严格弱于全局条件的例子 | Lean 4.36 编译通过 |
| A：无限全局状态空间与有限输入窗口 | `EncodedPathComposition` | Lean 4.36 编译通过 |
| A：从原语族生成器推导通用预测器的实际 logspace 统一性 | `Complexity/UniformComposition`，含规范时间位串、原语到完整电路生成器与多项式规模证明 | Lean 4.36 编译和独立公理审计通过 |
| 有限域线性系统实例及多对数深度界 | `Linear`、`LinearSize` | 已实现 |
| B：一元时间编码、模拟归约、条件性困难性传递 | `Hardness.SimulationWitness` | 已实现的参数化元定理 |
| 标准 logspace 归约及复合闭包 | `Complexity/Logspace.lean` 接入具体有限带机器与已证明的重计算编译器 | Lean 4.36 编译通过 |
| 标准 CVP 的 P 完备性 | `Complexity/CVP.lean` 接入编码、求值机器和图灵机表格归约 | Lean 4.36 编译和公理审计通过 |
| B 的标准复杂性版本 | `Complexity/StandardHardness.lean` 无抽象 CVP/闭包前提 | Lean 4.36 编译通过 |
| 标准统一 NC 的定义、NC 包含于 P | `Complexity/UniformNC.lean` | Lean 4.36 编译通过 |
| 统一 NC 对任意 logspace 归约封闭 | `NCClosure`：配置图、并行可达性、流式批生成及变长输出选择 | Lean 4.36 编译和公理审计通过 |
| P 与 NC 分离下的条件性困难性 | `SimulationWitness.prediction_not_uniformNC`；保留显式 `P ≠ NC` 假设 | Lean 4.36 编译和公理审计通过 |
| 具体 OR 电路族的机器级统一性与精确最优深度 | `UniformOROptimal.exact_uniform_prediction` | Lean 4.36 编译和公理审计通过 |
| C：本质变量数及可检查的有限见证推出深度下界 | `DependencyWitness`、电路和网络下界 | 已实现 |
| OR 元胞自动机的精确最优深度与线性规模上界 | `ORAutomaton.exact_prediction_depth` | 已实现 |
| 几何受限预测器的传播下界 | `Geometry.local_layers`、OR 几何下界 | 已实现 |
| 输入依赖计数方法的局限 | `dependency_method_limit` | 已实现 |
| 零时刻、空输入、单输入、具体线性实例 | `Examples` | 已实现 |
| 冻结控制的非线性规则族、对数深度与统一 NC¹ | `FrozenPascal.GuardRules`、`FrozenPascal.UniformLanguage`、`FrozenPascal.LowerBound` | Lean 4.36 编译和公理审计通过 |
| 冻结控制族的常数深度充要条件及逐时刻分类 | `FrozenPascal/Classification.lean` 的 `bounded_prediction_depth_iff` 和可变控制下界，`FrozenPascal/HomogeneousPascal.lean` 的二进制位数深度界 | 见[验证记录](verification.md) |
| 可执行规则分类及实际统一深度分类 | `classify_eq_iff`、`uniform_depth_classification`、`predictionLanguage_mem_uniformNC_zero_iff` | 见[验证记录](verification.md) |
| 全项目严格构建、传递公理审计和负向回归 | `scripts/check.sh`、`Audit.lean`、`scripts/check_audit.py`、`.github/workflows/lean.yml` | 见[验证记录](verification.md) |

术语采用“结构性判据（Structural Criteria）”；具体包含数学数据及证明的结构使用“见证（Witness）”。Certificate 本身是规范的理论计算机术语，这一命名选择不表示原术语错误，也不自动宣称所有见证存在统一多项式时间验证算法。
