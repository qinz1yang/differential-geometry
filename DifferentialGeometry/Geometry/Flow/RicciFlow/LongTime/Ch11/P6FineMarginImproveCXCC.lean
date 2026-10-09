import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapMarginCXCC

/-!
# CX-CAPCORE G2：改善定理孪生——余项只剩 whole-component（后缀 `_CXCC`）

`fineGood_implies_fineMarginGood_P6ST4` 的孪生：neck 型（STAB4 G1′）+ cap 型（本车道 G1
`exists_hasMargins_of_cap_CXCC`）都创造 margins，余项只剩 whole-component（positive / round，
`domain = connectedComponent x`，归 OPEN-C，不碰）。常数：`13000 η ≤ η' < 1/11`、
`max C1 9 + √C2 ≤ C1'`、`1200 C2 ≤ C2'`、`m ≤ 1/20`、`m ≤ 1/(10 C1 √C2)`。
* `fineGood_implies_fineMarginGood_CXCC`：Good ⇒ FineMarginGood ∨ whole-component witness；
* `whole_of_not_fineMarginGood_CXCC`（逆否）：margin 层坏 ⇒ finer 层每个 witness 都是 whole-component；
* event 层 `MetricCutCapEvent.frequently_whole_of_not_witness_CXCC`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M} {x : M}

/-- cap witness ⇒ `(η', C1', C2', m)`-FineMarginGood（常数放大到 `C1' ≥ C1 + √C2`、`C2' ≥ 1200 C2`）。 -/
theorem fineMarginGood_of_cap_CXCC {η η' C1 C2 C1' C2' m : ℝ} (hη : 13000 * η ≤ η')
    (hη' : η' < 1 / 11) (hC1 : C1 + Real.sqrt C2 ≤ C1') (hC2 : 1200 * C2 ≤ C2')
    (hm : m ≤ 1 / (10 * C1 * Real.sqrt C2)) (W : SpatialCanonicalWitness g η C1 C2 x)
    (hW : W.capTubeHasNeckChart η) (hcap : ∃ c d, W.alternative = .cap c d) :
    ∃ W' : SpatialCanonicalWitness g η' C1' C2' x, W'.capTubeHasNeckChart η' ∧ W'.HasMargins m := by
  obtain ⟨W₁, hW₁, hM₁, -⟩ := exists_hasMargins_of_cap_CXCC hη hη' W hW hcap hm
  exact ⟨W₁.enlargeConstants hC1 hC2, hW₁.enlarge_constants hC1 hC2, hM₁.enlarge_constants hC1 hC2⟩

/-- **改善定理孪生**：`(η, C1, C2)`-Good ⇒ `(η', C1', C2', m)`-FineMarginGood，或存在 whole-component
型 `(η, C1, C2)`-witness（`domain = connectedComponent x`）。cap 支已由 core-collar 延伸闭合。 -/
theorem fineGood_implies_fineMarginGood_CXCC {η η' C1 C2 C1' C2' m : ℝ}
    (hη : 13000 * η ≤ η') (hη' : η' < 1 / 11) (hC1 : max C1 9 + Real.sqrt C2 ≤ C1')
    (hC2 : 1200 * C2 ≤ C2') (hm : m ≤ 1 / 20) (hm' : m ≤ 1 / (10 * C1 * Real.sqrt C2))
    (hgood : ∃ W : SpatialCanonicalWitness g η C1 C2 x, W.capTubeHasNeckChart η) :
    (∃ W' : SpatialCanonicalWitness g η' C1' C2' x, W'.capTubeHasNeckChart η' ∧ W'.HasMargins m) ∨
      ∃ W : SpatialCanonicalWitness g η C1 C2 x, W.capTubeHasNeckChart η ∧
        W.domain.carrier = connectedComponent x := by
  obtain ⟨W, hW⟩ := hgood
  have hηpos : 0 < η := W.eps_pos
  have hC2one : 1 ≤ C2 := W.one_le_comparison_constant
  have hsq : 0 ≤ Real.sqrt C2 := Real.sqrt_nonneg _
  have hηle : η ≤ η' := by linarith
  have hC1n : max C1 9 ≤ C1' := by linarith
  have hC1c : C1 + Real.sqrt C2 ≤ C1' := by linarith [le_max_left C1 9]
  have hC2n : C2 ≤ C2' := by linarith
  cases hA : W.alternative with
  | neck data =>
    exact Or.inl (fineMarginGood_of_neck_P6ST4 hηle hη' hC1n hC2n hm W ⟨data, hA⟩)
  | cap data deep =>
    exact Or.inl (fineMarginGood_of_cap_CXCC hη hη' hC1c hC2 hm' W hW ⟨data, deep, hA⟩)
  | positive whole data sec => exact Or.inr ⟨W, hW, whole⟩
  | round whole data => exact Or.inr ⟨W, hW, whole⟩

/-- **逆否**：`¬FineMarginGood(η', C1', C2', m)` ⇒ finer 层 `(η, C1, C2)` 的每个（带 neck tube chart 的）
witness 都是 whole-component 型。 -/
theorem whole_of_not_fineMarginGood_CXCC {η η' C1 C2 C1' C2' m : ℝ}
    (hη : 13000 * η ≤ η') (hη' : η' < 1 / 11) (hC1 : max C1 9 + Real.sqrt C2 ≤ C1')
    (hC2 : 1200 * C2 ≤ C2') (hm : m ≤ 1 / 20) (hm' : m ≤ 1 / (10 * C1 * Real.sqrt C2))
    (hbad : ¬ ∃ W' : SpatialCanonicalWitness g η' C1' C2' x,
      W'.capTubeHasNeckChart η' ∧ W'.HasMargins m)
    (W : SpatialCanonicalWitness g η C1 C2 x) (hW : W.capTubeHasNeckChart η) :
    W.domain.carrier = connectedComponent x := by
  cases hA : W.alternative with
  | neck data =>
    exact absurd (fineMarginGood_of_neck_P6ST4 (by linarith [W.eps_pos]) hη'
      (by linarith [Real.sqrt_nonneg C2]) (by linarith [W.one_le_comparison_constant]) hm W
      ⟨data, hA⟩) hbad
  | cap data deep =>
    exact absurd (fineMarginGood_of_cap_CXCC hη hη'
      (by linarith [le_max_left C1 9]) hC2 hm' W hW ⟨data, deep, hA⟩) hbad
  | positive whole data sec => exact whole
  | round whole data => exact whole

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {p : P.Carrier} {q : Q.Carrier} {ηfine ηout C1' C2 m : ℝ} {k : ℕ}

/-- **event 层 consumer**：STAB2 footprint 层 `D`（`C1'`、`C2`、`m`）+ 目标层 `¬witness` ⇒ frequently 在
`(v n, p)` 处每个 finer `(η, C1, C2f)`-witness（带 neck tube chart）都是 whole-component 型
（`13000 η ≤ ηfine`、`max C1 9 + √C2f ≤ C1'`、`1200 C2f ≤ C2`、`m ≤ min (1/20) (1/(10 C1 √C2f))`）。 -/
theorem frequently_whole_of_not_witness_CXCC (D : E.BufferedFootprintData_P6ST2 p q ηout C1' C2 m k)
    (hle : ηfine ≤ neckModelTolerance (ηout / 2)) {η C1 C2f : ℝ} (hη : 13000 * η ≤ ηfine)
    (hC1 : max C1 9 + Real.sqrt C2f ≤ C1') (hC2 : 1200 * C2f ≤ C2) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1 * Real.sqrt C2f)) {C1out C2out : ℝ} (h1 : 2 * C1' ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout) :
    ∃ᶠ n in atTop, ∀ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n)) η C1 C2f p,
      W.capTubeHasNeckChart η → W.domain.carrier = connectedComponent p := by
  have hfine : ηfine < 1 / 11 := by
    have := (hle.trans (neckModelTolerance_le _))
    linarith [D.ηout_lt]
  exact (frequently_not_fineMargin_P6ST2 D hle h1 h2 hnot).mono fun n hn W hW =>
    whole_of_not_fineMarginGood_CXCC hη hfine hC1 hC2 hm hm' hn W hW

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
