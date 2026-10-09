import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FineMarginImproveCXCC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RoundTransferP6SF

/-!
# CX-HTRANS G1：`htrans` 的 event 层组装（类型鸽笼 + 四型 transfer，后缀 `_CXHT`）

`htrans` 槽（`P6HbdLateP6HB2`）的 event 层证明：footprint 数据 `D` + 目标层 `¬witness (ε, C1, C2)` ⇒
frequently `(D.v n, p)` 无 `(η₁, C1₁, C2₁)` witness（带 neck tube chart）。常数全部参数化（数值前提，
非 binder），D-15′ 赋值留给最后一个文件。

* `alt_posOrRound_of_not_fineMarginGood_CXHT`（逐点）：margin 层坏 ⇒ finer 层每个带 chart 的 witness
  的 alternative 是 positive 或 round（neck：G1′；cap：`fineMarginGood_of_cap_CXCC`）。
* `htrans_event_CXHT`：类型鸽笼 —— 若 eventually 有 witness，则 frequently 有 positive ∨ round 型；
  round frequently → `wholeComponent_round_transfer_P6SF`；否则 frequently positive，取子列后用
  `wholeComponent_positive_transfer_P6ST4`（eventually 版，子列 `v ∘ φ ↑ s`）。
* 唯一 binder：`htube`（`comp(p)` 与 cut tubes 不交；PROVISIONAL，owner = STAB3/OPEN-C）。
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

/-- **逐点类型分类**：finer 层 `(η₁, C1₁, C2₁)` witness（带 chart）若不产生 `(η', C1', C2', m)`
margin witness，则其 alternative 是 positive 或 round。 -/
theorem alt_posOrRound_of_not_fineMarginGood_CXHT {η₁ η' C1₁ C2₁ C1' C2' m : ℝ}
    (hη : 13000 * η₁ ≤ η') (hη' : η' < 1 / 11) (hC1 : max C1₁ 9 + Real.sqrt C2₁ ≤ C1')
    (hC2 : 1200 * C2₁ ≤ C2') (hm : m ≤ 1 / 20) (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁))
    (hbad : ¬ ∃ W' : SpatialCanonicalWitness g η' C1' C2' x,
      W'.capTubeHasNeckChart η' ∧ W'.HasMargins m)
    (W : SpatialCanonicalWitness g η₁ C1₁ C2₁ x) (hW : W.capTubeHasNeckChart η₁) :
    (∃ wh d sc, W.alternative = .positive wh d sc) ∨ ∃ wh R, W.alternative = .round wh R := by
  cases hA : W.alternative with
  | neck data =>
    exact absurd (fineMarginGood_of_neck_P6ST4 (by linarith [W.eps_pos]) hη'
      (by linarith [Real.sqrt_nonneg C2₁]) (by linarith [W.one_le_comparison_constant]) hm W
      ⟨data, hA⟩) hbad
  | cap data deep =>
    exact absurd (fineMarginGood_of_cap_CXCC hη hη'
      (by linarith [le_max_left C1₁ 9]) hC2 hm' W hW ⟨data, deep, hA⟩) hbad
  | positive whole data sec => exact Or.inl ⟨whole, data, sec, rfl⟩
  | round whole data => exact Or.inr ⟨whole, data, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {p : P.Carrier} {q : Q.Carrier}

/-- **`htrans` event 层（类型鸽笼 + 四型 transfer）**：`RegularCrossing p q` + `htube` + footprint 数据
`D`（`ε, C1f, C2f, m, kk`）+ 目标层 `¬ witness (ε, C1, C2)` ⇒ frequently `(D.v n, p)` 无
`(η₁, C1₁, C2₁)` witness。数值前提：`13000 η₁ ≤ neckModelTolerance (ε/2)`、
`η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊`、
`max C1₁ 9 + √C2₁ ≤ C1f`、`1200 C2₁ ≤ C2f`、`m ≤ min (1/20) (1/(10 C1₁ √C2₁))`、
`2 C1f ≤ C1`、`1000 C2f ≤ C2`。 -/
theorem htrans_event_CXHT (hcross : E.RegularCrossing p q)
    (htube : ∀ i, Disjoint (connectedComponent p)
      (Set.range (E.transition.trace.tubes.tube i)))
    {ε C1f C2f m : ℝ} {kk : ℕ} (D : E.BufferedFootprintData_P6ST2 p q ε C1f C2f m kk)
    {η₁ C1₁ C2₁ C1 C2 : ℝ} (hε : 0 < ε) (hη₁ : 0 < η₁)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric ε C1 C2 q, W.capTubeHasNeckChart ε) :
    ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n))
      η₁ C1₁ C2₁ p, W.capTubeHasNeckChart η₁ := by
  have hlt : neckModelTolerance (ε / 2) < 1 / 11 := by
    have := neckModelTolerance_le (ε / 2)
    linarith [D.ηout_lt]
  have hA := frequently_not_fineMargin_P6ST2 D (le_refl (neckModelTolerance (ε / 2))) h1 h2 hnot
  intro hev
  have hev' : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      (E.incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p, W.capTubeHasNeckChart η₁ :=
    hev.mono fun n hn => not_not.mp hn
  have hη₁ε : η₁ < ε := by
    have := neckModelTolerance_le (ε / 2)
    linarith
  have hε1 : ε < 1 := by linarith [D.ηout_lt]
  have hC1out : 2 * C1₁ ≤ C1 := by linarith [le_max_left C1₁ 9, Real.sqrt_nonneg C2₁]
  have hC2out : 1000 * C2₁ ≤ C2 := by linarith
  have hposround : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      (E.incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p,
      (∃ wh d sc, W.alternative = .positive wh d sc) ∨ ∃ wh R, W.alternative = .round wh R := by
    refine (hA.and_eventually hev').mono fun n ⟨hbad, W, hW⟩ => ⟨W, ?_⟩
    exact alt_posOrRound_of_not_fineMarginGood_CXHT (g := E.incoming.flow.base.metric (D.v n))
      hη (by linarith) hC1f hC2f hm hm' hbad W hW
  by_cases hR : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      (E.incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p, ∃ wh R, W.alternative = .round wh R
  · obtain ⟨W, hW, -⟩ := E.wholeComponent_round_transfer_P6SF hcross htube D.v_mem D.v_tendsto
      D.Q_pos hC1₁ hC2₁ hR hη₁ hη₁ε (by linarith [D.ηout_lt]) hsmall hC1out hC2out
    exact hnot ⟨W, hW⟩
  · rw [not_frequently] at hR
    have hP : ∃ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
        (E.incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p,
        ∃ wh d sc, W.alternative = .positive wh d sc := by
      refine (hposround.and_eventually hR).mono fun n ⟨⟨W, hW⟩, hnR⟩ => ⟨W, ?_⟩
      rcases hW with hpos | hrd
      · exact hpos
      · exact absurd ⟨W, hrd⟩ hnR
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hP
    obtain ⟨W, hW, -⟩ := E.wholeComponent_positive_transfer_P6ST4 hcross htube
      (v := fun n => D.v (φ n)) (fun n => D.v_mem (φ n))
      (D.v_tendsto.comp hφ.tendsto_atTop) D.Q_pos hC1₁ hC2₁ (Eventually.of_forall hφP) hε hε1
      hC1out hC2out
    exact hnot ⟨W, hW⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
