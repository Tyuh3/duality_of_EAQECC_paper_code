# 说明

EAQECLean 是纠缠辅助量子纠错码（EAQECC）对偶理论的 Lean 4 形式化工程。工程建立二元辛空间和四元加性码模型，证明原码与对偶码的参数、稳定子、正规化子及距离关系，并验证 Li 和 Kim 文献中的具体实例。

Pauli 算子、二元辛表示及普通稳定子码等基础接口沿用 QECLean，通用线性代数理论复用 Mathlib。本工程验证代数模型及相关证明，不包括 Bell 态制备、编码与解码线路及噪声信道过程。部分实例使用原生计算，相关计算结果的可靠性还依赖Lean编译器和运行时的正确性。

## 证明规模

`.lean` 文件数量：21个； 代码量：总计 10007行；定理数量：537个

统计范围为 `EAQECC.lean` 及 `EAQECC/` 下的工程源码，不包含 `.lake/` 中的依赖库和生成文件。源码总行数包含注释和空行。定理数量按 `theorem` 和 `lemma` 声明统计，包含私有辅助定理。

## 环境

Lean 4.30.0-rc2，由根目录的 `lean-toolchain` 文件固定。

## 依赖库

- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [QECLean](https://github.com/Stavan-Jain/QECLean)

依赖的精确提交号由 `lakefile.toml` 和 `lake-manifest.json` 固定。

## 构建命令

安装 Git 和 elan，使 `lean` 与 `lake` 命令可用。在包含 `lakefile.toml` 和 `lean-toolchain` 的项目根目录依次运行：

```sh
# 确认 Lean 版本。
lean --version

# 获取固定依赖及 Mathlib 编译缓存。
lake exe cache get

# 构建全部源码。
lake build
```

首次构建需要联网获取依赖和编译缓存；成功构建会输出 `Build completed successfully`。Lake 根据各文件的 import 自动安排编译顺序，编辑器也应打开项目根目录。

## 代码文件夹目录

**★ 表示论文正文或附录中的定理所在文件，并注明定理编号。** 正文定理5、6由完整对偶定理提取部分结论得到，完整版本分别位于标注定理A1、A2的文件中。

```text
EAQECLean/
├── EAQECC.lean                              # 工程总入口，导入全部20个内部模块。
├── EAQECC/
│   ├── Basic.lean                          # 候选生成元、冲突矩阵、对易扩展及EA码模型。
│   ├── Distance.lean                       # 非平凡逻辑算子、发送端距离及带距离的EA码。
│   ├── Minimality.lean                     # ★ 定理4：固定候选生成元下的纠缠参数下界。
│   ├── Symplectic/
│   │   ├── Basic.lean                      # ★ 定理1：辛对偶类型；定义辛根空间、辛类型及输入数据。
│   │   ├── Decomposition.lean              # 辛根空间与非退化部分的分解及标准辛基。
│   │   ├── Construction.lean               # 补零嵌入、坐标投影及扩展子空间的实现条件。
│   │   ├── StabilizerCode.lean             # 将辛子空间的辅助扩展转换为普通稳定子码。
│   │   ├── Distance.lean                   # ★ 定理A1：完整二元辛对偶定理及距离对应。
│   │   └── EACode.lean                     # ★ 定理5：二元对偶推论；将扩展码封装为EA码。
│   ├── Quaternary/
│   │   ├── Field.lean                      # 四元域、共轭、域迹及有序二元基。
│   │   ├── AdditiveCode.lean               # 四元加性码、迹内积、迹对偶及迹根空间。
│   │   ├── SymplecticBridge.lean           # 二元与四元向量的互逆映射及内积、重量保持。
│   │   ├── SubspaceTransport.lean          # ★ 定理2、3：迹类型判定及辛对偶与迹对偶的对应。
│   │   ├── Distance.lean                   # 排除迹根空间后的最小汉明重量及距离对应。
│   │   ├── Duality.lean                    # ★ 定理6、A2：四元输入数据及四元EAQECC对偶定理。
│   │   └── LinearCode.lean                 # 将四元线性码视为加性码并应用一般对偶构造。
│   ├── Applications/
│   │   ├── BinaryEuclideanHullEAQECC.lean  # 欧几里得正交包、Gram秩及Kim生成矩阵与校验矩阵。
│   │   └── SymplecticTypeEAQECC.lean       # 辛矩阵到Pauli候选生成元的转换及纠缠参数下界。
│   └── Examples/
│       ├── Li2025DualConstruction.lean     # ★ 定理7—9：Li实例的迹类型、对偶对应及两侧码构造。
│       └── Kim2023BinaryExample.lean       # ★ 定理10：Kim辛对偶空间；另含距离及完整对偶码实例。
├── lean-toolchain                          # 固定Lean版本。
├── lakefile.toml                           # 工程名称、构建入口及直接依赖配置。
├── lake-manifest.json                      # 固定全部依赖的来源与提交号。
├── .gitignore                              # 排除依赖缓存与临时文件。
└── README.md                               # 工程说明、环境、依赖、构建命令及文件目录。
```
