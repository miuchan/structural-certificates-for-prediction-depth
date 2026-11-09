# 依赖、模型和信任边界

[English](../../../docs/dependencies.md) · **简体中文** · [日本語](../../ja/docs/dependencies.md) · [Esperanto](../../eo/docs/dependencies.md)

本项目的可复现版本固定在 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 中。

| 依赖 | 固定版本 | 作用 |
| --- | --- | --- |
| Lean | `v4.36.0-rc2`，`b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` | 证明项内核检查 |
| cslib-frontier | `3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d` | 具体复杂性理论、图灵机编译器与电路编码 |
| CSLib | `254e30e6d4299c51323aaeaf5f51a4763b375d4a` | 有限控制、多带图灵机和通用计算模型 |
| Mathlib | `69552756cd8a2d2d48763cf7279fd814d6a1224d` | 数学基础、矩阵、有限集、自然数对数等 |

第三方代码通过固定提交的 [cslib-frontier 源码](https://github.com/cslib-community/cslib-frontier/tree/3c44ce0b2e9d39041ebd662cf65edf5c03b00e8d) 及其依赖图引入。项目未用文献中的非形式化陈述替代证明项，也没有把 CVP 完备性、logspace 复合闭包、NC 包含于 P 写成自定义公理。

## 标准机器模型

标准层 `PredictionDepth.StandardComplexity` 使用有限控制、固定数量工作带、二元字母表的多带图灵机。每一步只能读取当前输入符号和各工作带当前符号，移动头、改写局部符号，并至多输出一个符号。输入只读，输出只追加且不能被计算过程读取。

工作空间按运行前缀实际访问的工作带单元计费。`ComputableInLogSpace` 定义要求机器停机及对数工作空间，**没有把多项式时间塞入定义**；多项式时间和多项式输出长度由有限配置数界另行证明。

标准 CVP 使用带有合法性证明的电路实例及其单射二进制编码。其 P-hard 定理量化所有被编码的源问题，特别覆盖以恒等编码表示的全部二进制字，因此可用于本项目定义在全部查询字上的预测语言。无效预测查询被明确拒绝。

统一 NC 的同一个电路族同时满足语义、规模、深度和真实 logspace 生成条件。P 类使用实际多项式时间机器。`NCClosure` 在本项目内证明一般变长 logspace 归约闭包，没有用一个抽象闭包字段充当证明。

## 项目新增的基础证明

- 配置图的真实统一邻接电路、有限有向图最短路径界、布尔关系重复平方、平方对数深度界。
- 任意多项式次数的流式 logspace 批处理，保留原输入于只读带，通过重计算获取中间输出，不存储整个批结果。
- 不同规模电路块的真实 logspace 串联、并列、硬编码和流式电路族生成。
- `NL ⊆ uniform NC²`、`uniform NC ⊆ P`、一般 logspace 归约下的统一 NC 闭包，以及 P-hard 问题在 `P ≠ NC` 下不属于统一 NC。

## 检查的含义

`scripts/check_imports.py` 要求默认入口覆盖全部项目证明文件。`lake build` 编译全部项目模块。`Audit.lean` 按定义模块选取项目声明，涵盖 Lean 在其他命名空间生成的辅助声明。审计逐一检查传递公理依赖，只接受 `propext`、`Classical.choice`、`Quot.sound`。

Mathlib 与上游库可使用缓存加快构建。导入的编译产物与任何 Lean 依赖一样属于构建信任基础；需要独立重编译时，可以清理依赖构建产物和关闭缓存，按照固定源码版本重建。公理审计检查逻辑依赖，不能单独发现数学定义选错的问题，因此项目还保留源文档、假设说明和逐项要求清单。
