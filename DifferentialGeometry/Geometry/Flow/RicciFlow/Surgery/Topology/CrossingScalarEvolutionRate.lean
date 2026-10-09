import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.ScalarLaplacianRicciTerms
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabStartSliceBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCrossingJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem hasDerivAt_scalar_scalarEvolutionRate {t : ℝ} (ht : t ∈ Ioo a s) (y : P.Carrier) :
    HasDerivAt (fun v => G.flow.scalar v y) (scalarEvolutionRate (G.flow.base.metric t) y) t := by
  have h := scalar_curvature_evolution G.flow G.equation ⟨t, ht⟩ y
  have hnhds : (RealTimeInterval.closedOpen a s G.lt).carrier ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ico_self
  refine (h.hasDerivAt hnhds).congr_deriv ?_
  rw [scalarEvolutionRate_def]
  simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
    SolutionOn.family_metric]
  rfl

private theorem tendsto_nhdsGT_of_continuousWithinAt_start {f : ℝ × P.Carrier → ℝ}
    {T : Set ℝ} (hT : T ∈ 𝓝[>] a) (y : P.Carrier)
    (hf : ContinuousWithinAt f (T ×ˢ univ) (a, y)) :
    Tendsto (fun t => f (t, y)) (𝓝[>] a) (𝓝 (f (a, y))) := by
  have hpath : ContinuousWithinAt (fun t : ℝ => (t, y)) T a :=
    (continuous_id.prodMk continuous_const).continuousWithinAt
  exact (ContinuousWithinAt.comp (f := fun t : ℝ => (t, y)) hf hpath
    fun t ht => ⟨ht, mem_univ y⟩).mono_of_mem_nhdsWithin hT

theorem derivWithin_Ici_scalar_at_start_eq_scalarEvolutionRate (y : P.Carrier) :
    derivWithin (fun v => G.flow.scalar v y) (Ici a) a =
      scalarEvolutionRate (G.flow.base.metric a) y := by
  have hIoo : Ioo a s ∈ 𝓝[>] a := Ioo_mem_nhdsGT G.lt
  have hL := tendsto_nhdsGT_of_continuousWithinAt_start (self_mem_nhdsWithin (s := Ioi a)) y
    ((G.continuousWithinAt_derivWithin_Ici_scalar_at_start y).mono
      (prod_mono Ioi_subset_Ici_self subset_rfl))
  have hR : Tendsto (fun t => scalarEvolutionRate (G.flow.base.metric t) y) (𝓝[>] a)
      (𝓝 (scalarEvolutionRate (G.flow.base.metric a) y)) :=
    ((continuousWithinAt_scalarEvolutionRate_of_chartGramFamilySmoothWithinOn
      G.flow.base.metric y (G.chartGramFamilySmoothWithinOn_Ico y)
        ⟨le_rfl, G.lt⟩)).mono_of_mem_nhdsWithin (mem_of_superset hIoo Ioo_subset_Ico_self)
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [hIoo] with t ht
  exact ((G.hasDerivAt_scalar_scalarEvolutionRate ht y).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici t)).symm

theorem TerminalLimitMetric.abs_scalarEvolutionRate_le (L : G.TerminalLimitMetric) {C : ℝ≥0}
    {q : ℝ} (hder : G.DerivativeBoundBefore C q s) (x : G.terminalRegularOpen)
    (hx : q < metricScalarAt L.metric x) :
    |scalarEvolutionRate L.metric x| ≤ C * metricScalarAt L.metric x ^ 2 := by
  have hG : chartGramFamilySmoothWithinOn (I := ThreeModel) L.extendedMetric x (Icc a s) :=
    chartGramFamilySmoothWithinOn_of_contMDiffOn L.extendedMetric x fun i j =>
      chartGramMatrix_joint_contMDiffOn L.extendedMetric (Icc a s)
        (L.extendedMetric_jointContMDiffOn le_rfl G.lt) x i j
  have hlim : Tendsto (fun t => scalarEvolutionRate (L.extendedMetric t) x) (𝓝[<] s)
      (𝓝 (scalarEvolutionRate L.metric x)) := by
    have h := continuousWithinAt_scalarEvolutionRate_of_chartGramFamilySmoothWithinOn
      L.extendedMetric x hG ⟨G.lt.le, le_rfl⟩
    have h2 : Tendsto (fun t => scalarEvolutionRate (L.extendedMetric t) x) (𝓝[<] s)
        (𝓝 (scalarEvolutionRate (L.extendedMetric s) x)) :=
      h.mono_of_mem_nhdsWithin (mem_of_superset (Ioo_mem_nhdsLT G.lt) Ioo_subset_Icc_self)
    rwa [L.extendedMetric_terminal] at h2
  have hR := L.tendsto_scalar x
  refine le_of_tendsto_of_tendsto hlim.abs ((hR.pow 2).const_mul (C : ℝ)) ?_
  filter_upwards [Ioo_mem_nhdsLT G.lt, hR.eventually (lt_mem_nhds hx)] with t ht hq
  rw [L.extendedMetric_before ht.2, scalarEvolutionRate_restrictOpen,
    ← ((G.hasDerivAt_scalar_scalarEvolutionRate ht x.val).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Iic t))]
  exact hder x.val t ht hq

end OrientedThreeStage.IncomingSlab

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem RegularCrossing.scalarEvolutionRate_eq {p : E.incoming.terminalRegularOpen}
    {y : Q.Carrier} (h : E.RegularCrossing p.val y) :
    scalarEvolutionRate E.terminal.metric p = scalarEvolutionRate E.outputMetric y := by
  obtain ⟨F, _, hp, heq, _, _, hmetric⟩ := h.exists_survivor_partialDiffeomorph E
  let U : Opens E.incoming.terminalRegularOpen := ⟨F.source, F.open_source⟩
  let V : Opens Q.Carrier :=
    ⟨(F : E.incoming.terminalRegularOpen → Q.Carrier) ''
      (U : Set E.incoming.terminalRegularOpen),
      DifferentialGeometry.image_opens_isOpen F Subset.rfl⟩
  let e : U ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo F Subset.rfl
  have hiso : ∀ (x : U) (v w : TangentSpace ThreeModel x),
      (E.terminal.metric.restrictOpen U).inner x v w =
        (E.outputMetric.restrictOpen V).inner (e x)
          (mfderiv ThreeModel ThreeModel e x v) (mfderiv ThreeModel ThreeModel e x w) := by
    intro x v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner]
    have hd := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      F (show (U : Set E.incoming.terminalRegularOpen) ⊆ F.source from Subset.rfl) x
    change _ = E.outputMetric.inner (F x.val) (mfderiv ThreeModel ThreeModel e x v)
      (mfderiv ThreeModel ThreeModel e x w)
    rw [hd v, hd w]
    exact (hmetric x.val x.property v w).symm
  have hk := scalarEvolutionRate_eq_of_local_isometry _ _ e e.isLocalDiffeomorph hiso ⟨p, hp⟩
  rw [scalarEvolutionRate_restrictOpen, scalarEvolutionRate_restrictOpen] at hk
  change scalarEvolutionRate E.terminal.metric p = scalarEvolutionRate E.outputMetric (F p) at hk
  rw [hk, heq]

theorem abs_derivWithin_Ici_scalar_le_at_slab_start_of_regularCrossing {s' : ℝ} {C : ℝ≥0}
    {q : ℝ} (G : Q.IncomingSlab s s') (hG : G.flow.base.metric s = E.outputMetric)
    {p : E.incoming.terminalRegularOpen} {y : Q.Carrier} (h : E.RegularCrossing p.val y)
    (hder : E.incoming.DerivativeBoundBefore C q s) (hy : q < G.flow.scalar s y) :
    |derivWithin (fun v => G.flow.scalar v y) (Ici s) s| ≤ C * G.flow.scalar s y ^ 2 := by
  have hR : G.flow.scalar s y = metricScalarAt E.terminal.metric p := by
    change metricScalarAt (G.flow.base.metric s) y = _
    rw [hG, h.scalar_eq E]
  rw [G.derivWithin_Ici_scalar_at_start_eq_scalarEvolutionRate y, hG,
    ← h.scalarEvolutionRate_eq E, hR]
  exact OrientedThreeStage.IncomingSlab.TerminalLimitMetric.abs_scalarEvolutionRate_le
    E.incoming E.terminal hder p (hR ▸ hy)

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
