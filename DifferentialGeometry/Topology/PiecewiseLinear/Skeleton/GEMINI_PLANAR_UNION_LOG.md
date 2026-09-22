# Gemini Planar Union Log

Worker evidence only. The lead addendum below supersedes the first report's proposed
integration steps and API status. Acceptance belongs exclusively to `../FREE_INPUTS.md`.

## Entry 10: exists_isTopologicalCellWithInterior_union_consecutive — PARTIAL

- **目标定理**：`DifferentialGeometry.Topology.PiecewiseLinear.Skeleton.Section31CanonicalConfiguration.lean:376`
  ```lean
  theorem exists_isTopologicalCellWithInterior_union_consecutive
      {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
      (hc : IsPlanarCellChain P D Dint) (j : Fin 2) :
      ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
        IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧
          Dint j.castSucc ⊆ Eint ∧ Dint j.succ ⊆ Eint
  ```
- **交付文件**：
  - `DifferentialGeometry/Topology/PiecewiseLinear/PlanarCellUnion.lean`
    - SHA256: `70B4473E4ED5EEBE544B1FBA4344719001FE858F1FEF68189A1FFD88CAB0DC5C`
    - 状态：已验证，无诊断信息（`exitCode = 0`, `diagnosticLines = 0`）。
  - 依赖的候选模块（独立验证并审计）：
    - `DifferentialGeometry/Topology/PiecewiseLinear/TopologicalCellInterior.lean`
    - SHA256: `CF4529B964071B01615A406FFF0DB00A9471644EFC9432274A31E56A1F717C34`
    - 状态：已验证，无诊断信息（`exitCode = 0`, `diagnosticLines = 0`）。
- **编译检查回执**：
  - `PlanarCellUnion.lean`:
    ```
    target                : DifferentialGeometry.Topology.PiecewiseLinear.PlanarCellUnion
    import closure        : 486 DifferentialGeometry modules
    need private objects  : 16
    seeded from accepted  : 15
    MUST COMPILE YOURSELF : 1
        DifferentialGeometry.Topology.PiecewiseLinear.PlanarCellUnion
    Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PlanarCellUnion.lean with no diagnostics; shared outputs unchanged.
    endedAtUtc: 2026-09-22T14:51:49.2655713Z
    exitCode: 0, diagnosticLines: 0
    ```
  - `TopologicalCellInterior.lean`:
    ```
    target                : DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellInterior
    import closure        : 485 DifferentialGeometry modules
    need private objects  : 15
    seeded from accepted  : 14
    MUST COMPILE YOURSELF : 1
        DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellInterior
    Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TopologicalCellInterior.lean with no diagnostics; shared outputs unchanged.
    endedAtUtc: 2026-09-22T14:46:11.6610227Z
    exitCode: 0, diagnosticLines: 0
    ```
- **公理与 Linter 审计回执**：
  - 审计文件：`AuditGeminiPlanarCellUnion.lean`（基于 `gemini-planar-union/audit-template.txt`）
  - 命令：`checker.ps1 -Checkout D:\differential-geometry-moise-int -Token claude-agent-d-20260919 -OutputRoot ... -Audit ...`
  - 输出：
    ```
    Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\AuditGeminiPlanarCellUnion.lean with no diagnostics; shared outputs unchanged.
    endedAtUtc: 2026-09-22T14:52:43Z
    exitCode: 0, diagnosticLines: 0
    ```
  - 结果确认：
    1. 审计了两个模块中的所有非自动声明。
    2. 公理闭包完全包含于 `propext`, `Classical.choice`, `Quot.sound`。
    3. 确无 `sorryAx` 或非基础公理。
    4. 13 项 Mathlib 标准 linter（排除 `docBlame` 和 `docBlameThm`）全部通过，0 警告，0 错误。
- **已证明的数学架构与核心引理**：
  1. **平面坐标投影与截面**：
     - `planarProjection : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)`
     - `planarPoint : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)`（已在 `CanonicalConfiguration` 中提供）
     - 证明了 `isTopologicalCellWithInterior_planarPoint_image` 与 `isTopologicalCell_planarPoint_image`。
     - 证明了 `isTopologicalCellWithInterior_of_planarProjection`：在 $z=0$ 平面上的 3D 拓扑带内胞腔经投影后成为 2D 欧氏空间中的拓扑带内胞腔。
  2. **归约定理**：
     - `exists_isTopologicalCellWithInterior_union_consecutive_of_isTopologicalCell_union`：
       假设平面投影并集满足 `IsTopologicalCell 2 (planarProjection '' D j.castSucc ∪ planarProjection '' D j.succ)`，则存在 $E_{\mathrm{int}}$ 满足完整的冻结结论：
       `IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧ Dint j.castSucc ⊆ Eint ∧ Dint j.succ ⊆ Eint`。
     - 证明关键：利用 `TopologicalCellInterior.lean` 中的 `IsTopologicalCellWithInterior.interior_eq` 在同维数空间 $\mathbb{R}^2$ 中建立 `interior (planarProjection '' D j) = planarProjection '' Dint j`，再由开核单调性 `interior_mono` 证明两个单胞腔内部均包含于并集的开核中，最后由 `planarPoint` 传回 $\mathbb{R}^3$。
  3. **非退化验收用例（Smoke Test）**：
     - `exists_isTopologicalCellWithInterior_union_consecutive_standard`：
       对 `CanonicalConfiguration.lean` 中的标准非退化胞腔链 `isPlanarCellChain_standard`，在不导入 skeleton 的前提下，完全严格证明了 $j=0$ 和 $j=1$ 时的连续对并集定理（利用 `rectTwo` 矩形并集性质及凸紧有界非空开核性质 `isTopologicalCellWithInterior_planarImage`）。
- **确切剩余义务（Remaining Obligation）**：
  - 剩余的未闭合核心为二维平面拓扑圆盘的并集定理：
    ```lean
    theorem isTopologicalCell_union_of_isTopologicalCell_inter
        {A B : Set (EuclideanSpace ℝ (Fin 2))}
        (hA : IsTopologicalCell 2 A) (hB : IsTopologicalCell 2 B)
        (hAB : IsTopologicalCell 2 (A ∩ B)) :
        IsTopologicalCell 2 (A ∪ B)
    ```
  - **数学分析**：
    `IsTopologicalCell 2` 仅定义为存在与闭单位圆盘 $\bar{B}^2$ 的同胚。对于任意拓扑圆盘（非 PL、无多边形性、无横截性、边界相交可为非光滑弧或 Cantor 集/分形），由其交为圆盘推出其并为圆盘，在二维拓扑学中属于深层 Schoenflies/Jordan 曲线型定理。Mathlib 与当前项目目前仅有：
    - `PiecewiseLinear/PlanarDiskUnion.lean` 中的 `isPLBall_union_and_finite_frontier_inter`（要求 PL 且边界交为一维弧）；
    - `PlanarJordan/ClosedInterior.lean` 中的 `nonempty_homeomorph_closedBall_closure`（要求预先提供单射边界环路作为 Jordan 曲线）。
    因此，任意拓扑圆盘的并集定理是一个独立的二维拓扑基础缺口，与三维胞腔链的几何链条与内部包含逻辑完全解耦。一旦该二维定理确立，通过已完成并验证的 `exists_isTopologicalCellWithInterior_union_consecutive_of_isTopologicalCell_union` 即可直接闭合 Entry 10。
- **Lead 集成指引**：
  - 暂存文件：
    - `DifferentialGeometry/Topology/PiecewiseLinear/PlanarCellUnion.lean`
    - `DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/GEMINI_PLANAR_UNION_LOG.md`
  - 在 `DifferentialGeometry.lean` 中添加：
    `import DifferentialGeometry.Topology.PiecewiseLinear.PlanarCellUnion`
  - 在 `FILL_LOG.md` 中记录 Entry 10 为 PARTIAL。

## Lead addendum: corrected supporting layer, 2026-09-22

The original two source hashes above independently compiled in lease c with zero
diagnostics. The initial killed check was a wrapper restart, not the final Lean outcome.
The original reduction was not complete: it omitted transport of the intersection and
of the bare `IsTopologicalCell` overlap certificate. Its standard example bypassed the
conditional adapter. The arbitrary disk-union core remained unproved.

Before acceptance, the lead made these source changes:

- Reused `Topology.interior_eq_image_of_homeomorphClosedBall` for the existing
  matching-dimensional `IsTopologicalCellWithInterior.interior_eq` signature.
- Replaced the endpoint-shaped adapter, which assumed the main union-cell conclusion,
  with `IsTopologicalCellWithInterior.interior_mono`. This works for every dimension and
  arbitrary ambient topological space, by actual inclusion transport into the standard
  ball and invariance of domain; it adds no separation or planarity assumption.
- Added `planarProjection_image_inter` and `isTopologicalCell_of_planarProjection`.
- Retained the standard rectangular union theorem and used the new interior-monotonicity
  theorem for its two containments. This remains a special case, not the frozen producer.
- Removed the redundant direct CanonicalConfiguration import from PlanarCellUnion.

Final sources and independent lease-c evidence:

| Module | SHA256 | Check completed UTC |
|---|---|---|
| TopologicalCellInterior | `C6633D5E27180A45BE09F75E104377CD579D540F5826814E5FBF0EA6F3A1C75E` | 2026-09-22T15:10:40.7235162Z |
| PlanarCellUnion | `6469D45653D06A5798DF38EFE97DA85FF1C918491C4219EDB3E93D0B8961E112` | 2026-09-22T15:10:54.6393344Z |

Both final module checks have exit 0, zero diagnostics, stable source and unchanged shared
outputs. The lead audit completed at `2026-09-22T15:12:29.5792917Z`, with exit 0 and zero
diagnostics. It checks all nonautomatic declarations in both modules, allowing only
`propext`, `Classical.choice`, and `Quot.sound`, and runs all thirteen standard linters
except docBlame/docBlameThm. It also checks the general monotonicity signature, the projected
`hc.overlap` from the exact frozen chain inputs, and standard pairs 0/1 and 1/2.

Receipts and the exact audit specification are archived under
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\fill-interface-evidence-20260922\gemini-planar-union\`.
The audit specification SHA256 is
`DF133D8665D28BCAFC57D3326D9D2C35214A2DA5D4E29A54594478EA0262E728`.
`acceptance.json` binds these receipts to the final source and unchanged frozen hashes.

The lead registers both real modules and records the auxiliary result under B1.g.1 in
FREE_INPUTS. FILL_LOG is not the acceptance ledger and was not edited. Entry 10 stays OPEN;
its frozen source is byte-identical, no sorry is removed, and no queue completion is added.
No full aggregate build is claimed under the Topology-only lease and read-only E: outputs.

Continue with the [round-two assignment](HANDOFF_GEMINI_PLANAR_UNION_ROUND2_20260922.md).
The next round is prepared for the owner to pass to Gemini, not dispatched by the lead.
