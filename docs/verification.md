# 验证记录

项目固定 Lean `v4.36.0-rc2` 和[依赖版本](dependencies.md)。从仓库根目录运行下列命令。

```sh
./scripts/check.sh
```

脚本依次检查默认入口的模块覆盖、运行 `lake build --wfail`、审计项目声明的传递公理依赖，并运行负向回归测试。

```text
Entry point covers all 96 project modules.
Build completed successfully (4972 jobs).
Audited 3282 project declarations: only propext, Classical.choice, Quot.sound.
Audit regression passed: AuditRegressionExternal.unexpectedTheorem transitively depends on unapproved axiom AuditRegressionDependency.unexpectedOracle.
```

构建任务数包含依赖。声明数包含定义、定理和 Lean 生成的辅助声明。

审计按声明的定义模块选取对象。`scripts/check_audit.py` 在临时目录编译一个项目定理。该定理位于其他命名空间，且经由一个中间定理依赖外部公理。回归测试要求生产审计脚本以非零状态退出并报告指定定理及公理。

[GitHub Actions 工作流](../.github/workflows/lean.yml) 在 Ubuntu 上运行同一脚本。推送事件检查推送的提交，拉取请求事件检查 GitHub 生成的合并提交。工作流核对检出的 SHA 和触发 SHA，并在成功时把 SHA 写入运行摘要。可用 `gh run list --commit <SHA>` 查找对应的公开记录。

## 数学验收

- A 的有限电路构造、路径局部条件、任意全局状态空间、统一生成器和成本条件下的 NC 成员资格，均有对应 Lean 证明。规范化统一编译器的复制门开销显式计入；大时间的二进制编码不会自动被误判为 NC。
- B 的标准实例使用实际机器及已证明的 CVP 完备性。一般变长 logspace 归约下的统一 NC 闭包在本项目内证明。最终条件结论显式保留 `P ≠ NC`；未声称证明类分离。
- C 的整数形式 `m ≤ b^d`、对数形式及有限区分赋值见证均已证明，覆盖共享电路。
- OR 实例具有已证明的状态语义、有限输入编码、实际统一生成器、固定多项式预算、精确最优深度及任意共享 De Morgan 电路的匹配下界；时间零被覆盖。
- 二元域矩阵实例使用实际 XOR/AND 电路，有具体深度、门数和完整描述规模界。几何传播下界明确限制预测器自身的局域性。
- 冻结控制规则族覆盖任意初始控制分布的系数公式、路径编译与解码、对数深度上界、对数空间统一生成器，以及 AND/OR 规则的匹配下界。模型和适用范围见[冻结控制规则族](frozen-pascal.md)。
- 冻结控制深度分类给出了所有时刻共享一个常数深度界的充要条件。可变控制情形有二输入门的对数深度下界，齐次 Pascal 情形的逐时刻深度界由时刻的二进制置位数决定。常数深度和 Pascal 专用电路都有显式门数界。
- 可执行分类器的返回值与四种语义条件等价。统一分类总定理在同一个实际生成的电路族上证明语言正确性、多项式门数和分支深度上界，并给出标准统一 NC⁰ 的成员资格充要条件。
- 移动控制模型从无限格点的同步演化推出有限窗口上的合取，精确刻画本质输入，并用线性门数的构造达到最优深度。匹配下界覆盖允许共享的二输入网络。结果属于逐时刻电路模型。[Lean 定理](../PredictionDepth/TransportedControl.lean)

独立审查另行检查了实际工作空间计费、输出只写、有限控制、变长输出、规范时间位串、路径条件与全局条件的区别，以及同一电路族同时满足统一性、规模和深度要求。项目使用的逻辑基础与第三方编译产物信任边界见 [依赖说明](dependencies.md)。
