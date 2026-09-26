# Lane H1 log: history L-windows (DESIGN_22 §2, brick H1)

- 2026-09-26: new file `Surgery/Topology/HistoryLGeometry/Window.lean` (1374 lines; about 210 of
  them are generic manifold-AC lemmas that belong in `Analysis/Calculus/Manifold/AbsolutelyContinuous`,
  so the history part is about 1160). No sorry, no nolint, no heartbeat options. No edits elsewhere, no
  git writes, root aggregate not touched (the lead must register the module).
- Compile: `LEAN_NUM_THREADS=2 lake env lean <file>` in place. Clean: no errors, warnings or info.
  One transient "failed to read GradedMonoid.olean" during development; the retry passed.
- Axioms, checked on a scratch copy for all 19 public declarations: propext, Classical.choice,
  Quot.sound. No sorryAx.
- Where it deviates from the §2 sketch:
  - `LWindow H lo hi T` is indexed by the window's own stage range `lo ≤ hi`, not `first last`. The
    sketch needs `f j` for every stage of the history, which is junk for stages outside the window.
  - `upper : T - a^2 ∈ stageDomain hi` and `lower : T - b^2 ∈ stageDomain lo`.
  - `crossing` is required for all `z`.
  - `metric` is in `localPullMetric` form on `Ioo (regularizedStageStart T a j) (regularizedStageEnd T b j)`.
  - So H3a states `IsHistoryLGeodesicOn` as `∃ lo hi (first ≤ lo) (hi ≤ last) (W : H.LWindow lo hi T)`,
    with `α ⟨j.val, _, _⟩ = W.f j ∘ γ` on the pieces.
- Delivered:
  - Generic AC:
    - `AbsolutelyContinuousOnInterval.of_forall_nhds`
    - `Manifold.absolutelyContinuousOnInterval_of_forall_left_right`
    - `Manifold.absolutelyContinuousOnInterval_of_subset_iUnion_Icc`
    - `Manifold.absolutelyContinuousOnInterval_comp_of_contMDiffOn`
  - AC join inside a stage:
    - `regularizedExtendedAction_eq_add_at_parameter`
    - `mem_regularizedActionValues_{upper,lower}_restrict`
    - `mem_regularizedActionValues_split_at_parameter`, the sibling of `_split_at_event`; it needs a
      scalar floor on the split stage.
  - Window API:
    - `LWindow`, `LWindow.restrict`
    - `LWindow.coe_lRegularizedAction_mem_regularizedActionValues` (window C¹ curve → history competitor)
    - `LWindow.exists_lift` (history curve → continuous window curve, AC; the seam hand-off is used
      exactly at `√(T - time i.succ)`)
    - `LWindow.stageRegularizedLagrangian_ae_eq`, `absolutelyContinuousOnInterval_of_eqOn_comp`
    - `regularizedExtendedAction_eq_coe`, `regularizedExtendedAction_eq_top_iff`
    - `exists_splice`, `lRegularizedAction_le_of_regularizedCost_eq`
  - Constructors:
    - `LWindow.ofStage` (open set of one stage, any stage flow agreeing with `stageMetric`)
    - `LWindow.exists_seam` (from `exists_survivor_solution_across_event`, `SurvivorMetricSeam.lean:31`;
      the old chart is `val ∘ val`, the new chart is `F`; the range of the old chart is `val '' W`)
- §7 rows these must match:
  - "H2a | Regular minimizers: stage-interior L-geodesic and initial vector | …/Regularity | H1"
  - "H2b | Seam C¹ matching `mfderiv F (α_old' w) = α_new' w` | …/Seam | H1, H2a"
  - "H3a | `IsHistoryLGeodesicOn`, `historyLExpDomain`, `historyLExp`, uniqueness | …/Exponential | H1, G3"
- How they match:
  - H2a/H2b: pick a window with `ofStage` / `exists_seam`, shrink it with `restrict`, and lift with
    `exists_lift`, which gives a `Continuous γ`.
  - The single-flow `hmin` (C¹ `δ` on ℝ with the same endpoints) is exactly
    `lRegularizedAction_le_of_regularizedCost_eq`.
  - The single-flow lemmas need `[PseudoMetricSpace X]`. Use `TopologicalSpace.metrizableSpaceMetric`,
    as `EventAction.lean:891` does.
  - The seam `G` for `i.succ = last` must be built from `finalSlab`. There is no `ClosedSlab →
    IncomingSlab` conversion in the tree yet.
