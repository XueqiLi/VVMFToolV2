VVMF notebook package — data-file I/O correction (revision 6)

本次错误在 VVMF_Results_Data.wl 的语法，不是 q 展开本身。
错误日志中的横向分数线属于显示排版，不能当作 Wolfram Language 输入读回。
仅替换 Results.nb 不能修复已经写坏的数据文件。

请将本包解压到一个新文件夹，四个运行文件保持同目录：
  VVMF_Compute.nb
  VVMF_Engine.wl
  VVMF_Results.nb
  VVMF_Results_Data.wl

使用随附结果：
1. 在 Mathematica 中关闭旧 notebook，并退出旧 kernel（菜单 Evaluation >
   Quit Kernel > Local；不同语言界面的菜单名称可能不同）。
2. 打开新文件夹中的 VVMF_Results.nb，执行首个输入单元。
3. 应返回 Ready -> True、Version -> 6、Order -> 20、Vectors -> 820。
4. 可直接查询各章节结果，无需先运行 Compute。

重新计算：
打开同一新文件夹里的 VVMF_Compute.nb，只修改 qOrder，例如 qOrder = 20;，
再选择 Evaluation > Evaluate Notebook。计算 notebook 仍只有一个依赖
VVMF_Engine.wl。不要把旧版 Engine.wl 复制回来。
导出器现在用 Put 写入 Wolfram Language 表达式，不经显示文本转换。
先写临时文件，回读并与完整内存结果逐项作 SameQ 比较；核对成功才替换
正式的 VVMF_Results_Data.wl。成功输出含 RoundTripVerified -> True。
临时文件在成功完成后移走，不是额外依赖。

本版结果数据只保存数据，不再序列化函数 DownValues。
查询和 LaTeX 导出的可读源程序已直接放入 Results.nb 的首个输入单元。
Results.nb 仍只依赖 Results_Data.wl，格式版本为 2。
它也接受语法有效的旧版格式 1，但不能自动恢复已被二维排版破坏的文件。

常用命令及其含义没有变化：
VVMFNames["72-42"]
Y72x42R3pF[]
VVMFTeX["Y72x42R3pF"]
VVMFStatus[]
展开默认阶数来自数据文件；q 请保持未赋值。

随附 q^20 的全部 174 个独立模型系数沿用已核对的精确参考值，
对应 820 个生成元；本次没有重新执行全部高阶递推。
本次验证重点为实际文件写入、回读、替换和全新会话加载。
当前环境无原生 Mathematica；可执行检查使用 Mathics3。
本次不改论文正文与参考文献。
