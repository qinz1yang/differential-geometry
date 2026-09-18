# Moise 光滑化车道的常驻规则

本目录下的工作按车道分支进行（`codex/moise-smoothing` = F、`codex/moise-s` = S、`codex/moise-e3` = L/C、
`codex/moise-h` = H），整合分支是 `codex/moise-integration`。本文件是这些车道的常驻规则，随整合分支下发，
不必在每次任务里重复。当前任务、里程碑与跨车道接口见同目录的 `NIGHT_PLAN.md` 与各自的 `HANDOFF_CODEX_*.md`。

## 1. 提交粒度

一个已闭合的结果 = 一次提交。把该结果的 Lean 源码与它在 `HANDOFF_CODEX_*.md`、`PHASE3_APPROXIMATION_PLAN.md`、
`MOISE_PLAN.md`、`VENDOR.md` 里的记录**一起暂存、一起提交**。不要另发"记录里程碑"、"Record …"之类只改文档的提交。
只有两种例外：确实只改文档的工作（例如按要求重排计划行），以及合并提交。

提交信息用英文描述数学内容，不写文件名清单，末尾附带指定的 `Co-Authored-By` 行。

## 2. 验证

- 平时自检：`python .lake/scratch/tools/fresh.py`。不跑 Lean，做禁用模式扫描与 olean 新鲜度检查
  （`check-f.ps1` 编译前先删目标 olean，所以 olean 比源码新即等于这份源码编译成功过）。
  必须在本工作树没有 `lean.exe` 时跑。
- 聚焦检查（`check-f.ps1`）加命名空间感知的 `#print axioms` 审计只在三种场合做：宣布里程碑 done；
  端点模块并入整合分支前；某个声明的陈述被重述之后的下游模块。
- 一批模块要按依赖顺序编译时用 `python .lake/scratch/tools/toposort.py <文件清单>`（传递闭包版本，输出 LF）。
  用 shell 循环喂模块名前先 `tr -d '\r'`：带回车的模块名会让每次检查在 0.1 秒内失败且不报错。
- 审计文件留在本工作树的 `.lake\scratch`。

## 3. 共享 olean 库

`E:\differential-geometry-dev\.lake\build\lib\lean` 是所有工作树共用的唯一 olean 存储。同一时刻只能有一个工作树
编译同一个模块。收到"整合验证中，暂停 Lean"的通知后停止全部 Lean 调用，收到"恢复"再继续。
不要用未推送的源码去编译别的工作树正在验证的模块。

## 4. 与其它车道的关系

- 别的车道的文件与定理只通过 `git fetch origin && git merge --no-ff origin/codex/moise-integration` 取得。
  不复制、不 cherry-pick、不直接合并别的车道分支。不修改别的车道拥有的文件。
- 计划文件冲突时两边都保留，只删冲突标记行。
- 需要别的车道尚未交付的定理时，按 `NIGHT_PLAN.md` §1 的接口写成**显式假设**（参数或结构字段，不是 `sorry`），
  继续往下做；对方交付后在下一次合并时消参。

## 5. 数学纪律

不得为绕开缺口而弱化端点，不得把缺口写成结论型假设，不得引入 `sorry`、顶层 `axiom`、`nolint`、`maxHeartbeats`、
`set_option` 或正文注释；仅允许标准 header linter 必需的 Apache 版权/作者头和 import 后模块文档。
`Topology/Homology/HurewiczLowDegrees.lean` 含 `sorry`，任何车道不得导入。
遇到真实的数学障碍：在本车道的 `HANDOFF_CODEX_*.md` 末尾写清确切义务、已证到哪一层、可选路线，然后转下一个里程碑。

## 6. 汇报

按里程碑列 done / partial / blocked，每项给端点定理名、提交哈希、审计条数与确切的未闭合义务。
不要贴完整的检查输出。
