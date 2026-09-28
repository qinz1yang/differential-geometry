import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckAppend
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CylinderReferenceCopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.CylinderBackwardConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CompactProductTraceSurvival
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CylindricalResetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckIncomingAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Neck.NormalizedFootprint
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

section
set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Geometry.Curvature CheegerGromovCompactness

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem normalized_restrict_inner
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {g : DifferentialGeometry.SmoothRiemannianMetric ThreeModel M}
    {eps δ : ℝ} {k : ℕ} (N : NormalizedNeck g eps k) (hprec : eps ≤ δ)
    (z : neckBuffer δ) (a b : TangentSpace NeckCylinderModel z) :
    (N.normalizedMetric.restrictOpenOfSubset
      (neckBuffer_le_of_le N.delta_pos hprec)).inner z a b =
      (scaleMetric N.scale N.scale_pos g).inner
        (N.chart (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hprec) z))
        (mfderiv NeckCylinderModel ThreeModel
          (fun w : neckBuffer δ => N.chart
            (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hprec) w)) z a)
        (mfderiv NeckCylinderModel ThreeModel
          (fun w : neckBuffer δ => N.chart
            (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hprec) w)) z b) := by
  rw [DifferentialGeometry.SmoothRiemannianMetric.restrictSubset_inner,
    N.normalized_inner (TopologicalSpace.Opens.inclusion
      (neckBuffer_le_of_le N.delta_pos hprec) z) a b, scaleMetric_inner]
  have hmd : MDifferentiableAt NeckCylinderModel ThreeModel
      (N.chart : neckBuffer eps → M)
      (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hprec) z) :=
    N.chart_smooth.contMDiff.mdifferentiableAt (by simp)
  have hinc : MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos hprec)) z :=
    (contMDiff_inclusion (I := NeckCylinderModel) (n := ∞)
    (neckBuffer_le_of_le N.delta_pos hprec)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hda := mfderiv_comp_apply z (f := TopologicalSpace.Opens.inclusion
    (neckBuffer_le_of_le N.delta_pos hprec)) (g := N.chart) hmd hinc a
  have hdb := mfderiv_comp_apply z (f := TopologicalSpace.Opens.inclusion
    (neckBuffer_le_of_le N.delta_pos hprec)) (g := N.chart) hmd hinc b
  rw [DifferentialGeometry.mfderiv_opens_incl] at hda hdb
  erw [hda,hdb]
  rfl

private theorem normalized_restrict_inner_of_index_eq
    {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold ThreeModel ∞ (M i)]
    {g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric ThreeModel (M i)}
    {eps : ℕ → ℝ} {order : ℕ → ℕ}
    (O : ∀ i, NormalizedNeck (g i) (eps i) (order i))
    {p q : ℕ} (hpq : p = q) {δ : ℝ} (hp : eps p ≤ δ) (hq : eps q ≤ δ)
    (z : neckBuffer δ) (a b : TangentSpace NeckCylinderModel z) :
    ((O p).normalizedMetric.restrictOpenOfSubset
      (neckBuffer_le_of_le (O p).delta_pos hp)).inner z a b =
      (scaleMetric (O q).scale (O q).scale_pos (g q)).inner
        ((O q).chart (TopologicalSpace.Opens.inclusion
          (neckBuffer_le_of_le (O q).delta_pos hq) z))
        (mfderiv NeckCylinderModel ThreeModel
          (fun w : neckBuffer δ => (O q).chart (TopologicalSpace.Opens.inclusion
            (neckBuffer_le_of_le (O q).delta_pos hq) w)) z a)
        (mfderiv NeckCylinderModel ThreeModel
          (fun w : neckBuffer δ => (O q).chart (TopologicalSpace.Opens.inclusion
            (neckBuffer_le_of_le (O q).delta_pos hq) w)) z b) := by
  subst q
  exact normalized_restrict_inner (O p) hp z a b

private theorem exists_normalized_selected_neck_metric_rows
    {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold ThreeModel ∞ (M i)]
    {g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric ThreeModel (M i)}
    {eps : ℕ → ℝ} {order : ℕ → ℕ}
    (O : ∀ i, NormalizedNeck (g i) (eps i) (order i))
    (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Gm : ℕ → DifferentialGeometry.SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ),
      MetricCInfConvergenceOnCompacts Gm
        (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) ∧
      ∀ᶠ i in atTop, ∃ hprec : eps i ≤ δ,
        ∀ (z : neckBuffer δ) (a b : TangentSpace NeckCylinderModel z),
          (Gm i).inner z a b = (scaleMetric (O i).scale (O i).scale_pos (g i)).inner
            ((O i).chart (TopologicalSpace.Opens.inclusion
              (neckBuffer_le_of_le (O i).delta_pos hprec) z))
            (mfderiv NeckCylinderModel ThreeModel
              (fun w : neckBuffer δ => (O i).chart (TopologicalSpace.Opens.inclusion
                (neckBuffer_le_of_le (O i).delta_pos hprec) w)) z a)
            (mfderiv NeckCylinderModel ThreeModel
              (fun w : neckBuffer δ => (O i).chart (TopologicalSpace.Opens.inclusion
                (neckBuffer_le_of_le (O i).delta_pos hprec) w)) z b) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((heps.eventually (Iio_mem_nhds hδ)).mono fun i hi => hi.le)
  have hprec (j : ℕ) : eps (j + N) ≤ δ := hN (j + N) (by omega)
  let Gtail := fun j => (O (j + N)).normalizedMetric.restrictOpenOfSubset
    (neckBuffer_le_of_le (O (j + N)).delta_pos (hprec j))
  let Gm := fun i => Gtail (i - N)
  have htail : ∀ K : Set (neckBuffer δ), MetricCInfConvergenceOn K Gtail
      (roundCylinderMetric.restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) :=
    NormalizedNeck.metricCInfConvergenceOn_restrict_of_precision_tendsto_zero
      (fun j => O (j + N)) hprec
      (heps.comp (tendsto_add_atTop_nat N)) (horder.comp (tendsto_add_atTop_nat N))
  refine ⟨Gm,?_,?_⟩
  · intro K _ p η hη
    obtain ⟨j0,hj0⟩ := htail K p η hη
    exact ⟨j0 + N,fun i hi => hj0 (i - N) (Nat.le_sub_of_add_le hi)⟩
  · filter_upwards [eventually_ge_atTop N] with i hi
    refine ⟨hN i hi,?_⟩
    intro z a b
    dsimp only [Gm,Gtail]
    exact normalized_restrict_inner_of_index_eq O (Nat.sub_add_cancel hi)
      (hprec (i - N)) (hN i hi) z a b

private theorem exists_pointed_cylinder_convergence_of_selected_necks
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (eps : ℕ → ℝ) (order : ℕ → ℕ)
    (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
    (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
    (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (mark : Sphere 2) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := { obj := fun i => {
      M := (G i).terminalRegularOpen
      basepoint := (O i).chart ⟨(mark,0),by
        constructor <;> dsimp <;> linarith [inv_pos.mpr (O i).delta_pos]⟩
      metric := scaleMetric (O i).scale (O i).scale_pos (L i).metric } };
    let P₀ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := {
      P with
      basepoint := e (mark,0)
      metric := Diffeomorph.pullbackMetricCross
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0) e.symm };
    RiemannianMetricComplete P₀.metric ∧
      (∀ y : P₀.M, metricScalarAt P₀.metric y = 1) ∧
      Diffeomorph.pullbackMetricCross P₀.metric e = roundCylinderMetric ∧
      ∃ f : ℕ → ℕ, StrictMono f ∧
        ∃ maps : PointedRiemannianConvergenceMaps X P₀ f,
          (∀ i (z : neckBuffer (eps (f i))), maps.map i (e z) = (O (f i)).chart z) ∧
          (∀ i, maps.source i ⊆ e.symm ⁻¹' neckBuffer (eps (f i))) ∧
          (∀ i, IsCompact (closure (maps.source i))) ∧
          (∀ i, IsConnected (maps.source i)) ∧
          ∃ C : MetricConvergenceData maps,
            ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i := by
  intro X P₀
  let Pmark : PointedRiemannianManifold.{u, 0, 0} ThreeModel := { P with basepoint := e (mark,0) }
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 2)⁻¹
  have hδ : ∀ n, 0 < δ n := fun n => inv_pos.mpr (by positivity)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  choose Gm hconv hmetric using fun n =>
    exists_normalized_selected_neck_metric_rows O heps horder (hδ n)
  have hp : ∀ i, e.symm Pmark.basepoint ∈ neckBuffer (eps i) := by
    intro i
    change e.symm (e (mark,0)) ∈ neckBuffer (eps i)
    rw [e.symm_apply_apply]
    constructor <;> dsimp <;> linarith [inv_pos.mpr (O i).delta_pos]
  have hpsi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (O i).chart := by
    intro i
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (O i).chart_smooth.contMDiff
    · intro z
      exact DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel
        (O i).chart z ((O i).chart_smooth.isImmersion.isImmersionAt z)
    · simp [ThreeSpace]
  have hbase : ∀ i, (O i).chart ⟨e.symm Pmark.basepoint,hp i⟩ = (X.obj i).basepoint := by
    intro i
    apply congrArg (O i).chart
    apply Subtype.ext
    exact e.symm_apply_apply _
  have hzero : PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0 = roundCylinderMetric :=
    PDE.RicciFlow.shrinkingCylinderMetric_zero.trans roundCylinderMetric_eq_geometry.symm
  have hc := exists_pointed_convergence_of_cylindrical_local_pullbacks (X := X) Pmark e
    (v := 0) le_rfl id eps (fun i => (O i).delta_pos) heps hp
    (fun i => (O i).chart) hpsi (fun i => (O i).chart_smooth.isEmbedding.injective) hbase
    δ hδ hδlim Gm
    (fun n => by simpa only [hzero] using hconv n)
    hmetric
  dsimp only at hc
  simp only [sub_zero,inv_one,Function.id_comp] at hc
  obtain ⟨hcomplete,hscalar,_,_,f,hf,maps,hmap,hsource,hcompact,hconnected,C,hcanonical⟩ := hc
  refine ⟨?_,?_,?_,f,hf,maps,hmap,hsource,hcompact,hconnected,C,hcanonical⟩
  · exact hcomplete
  · exact hscalar
  · change Diffeomorph.pullbackMetricCross
      (Diffeomorph.pullbackMetricCross
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0) e.symm) e = _
    rw [show Diffeomorph.pullbackMetricCross
      (Diffeomorph.pullbackMetricCross
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0) e.symm) e =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0 from
      Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl]
    exact hzero

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem exists_uniform_backward_trace_window_of_cylindrical_limit
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
    Tendsto Q atTop atTop → ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i => {
          M := (G i).terminalRegularOpen
          basepoint := x i
          metric := scaleMetric (Q i) (hQ i) (L i).metric } };
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (subseq : ℕ → ℕ), StrictMono subseq →
    ∀ (Phi : PointedRiemannianConvergenceMaps X P subseq) (Cm : MetricConvergenceData Phi),
    (∀ i, Cm.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) →
    ∀ (e : NeckCylinder ≃ₘ⟮NeckCylinderModel,ThreeModel⟯ P.M) (v : ℝ), v ≤ 0 →
    Diffeomorph.pullbackMetricCross P.metric e = PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v →
    ∀ (K : Set P.M), IsCompact K →
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ last (subseq i),
        (H (subseq i)).time first ≤ s (subseq i) - θ / Q (subseq i) ∧
        0 ≤ s (subseq i) - θ / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
          (Phi.map i y).val) := by
  obtain ⟨theta,eps0,delta0,htheta,heps0,hdelta0,hwindow⟩ :=
    exists_common_backward_trace_window_of_pointed_product_limit D r eps a₀ Ctime ha₀ heps
      hepssmall hr hfit 1 zero_lt_one
  refine ⟨theta,eps0,delta0,htheta,heps0,hdelta0,?_⟩
  intro H last s G L hinit x Q hQ hQlim a ha hsa X P subseq hsubseq maps Cm hcanonical e v hv he K hK
  have hv1 : v < 1 := hv.trans_lt zero_lt_one
  have hmetric : P.metric = Diffeomorph.pullbackMetricCross
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm := by
    exact (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp he).symm
  have hcomplete : MetricComplete P := by
    have hc : RiemannianMetricComplete P.metric := by
      rw [hmetric]
      exact RiemannianMetricComplete.pullbackCross _ e.symm
        (PDE.RicciFlow.shrinkingCylinderMetric_complete v)
    exact hc.complete
  have hscalar (y : P.M) : metricScalarAt P.metric y = (1-v)⁻¹ := by
    rw [hmetric,metricScalar_cross,
      PDE.RicciFlow.shrinkingCylinderMetric_scalar hv1]
  let hprod := scaleMetric (2 * (1-v)) (mul_pos (by norm_num) (by linarith))
    (Geometry.roundMetric (E := ThreeSpace) (n := 2))
  have hp : Diffeomorph.pullbackMetricCross P.metric e = hprod.prod (euclideanMetric (E := ℝ)) := by
    rw [he]
    exact PDE.RicciFlow.shrinkingCylinderMetric_eq_prod hv1
  let _ : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  exact hwindow H last s G L hinit x Q hQ hQlim ha hsa P subseq hsubseq maps Cm hcanonical
    hcomplete hprod (by simp) e hp (fun y => by rw [hscalar]; exact inv_le_one_of_one_le₀ (by linarith))
    K hK (fun y _ => by rw [hscalar]; exact inv_pos.mpr (by linarith))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩


private theorem exists_uniform_initial_trace_window_of_selected_necks
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel),
      (NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) → Sphere 2 →
    ∃ f : ℕ → ℕ, StrictMono f ∧
    ∀ (K : Set NeckCylinder), IsCompact K →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (f i)).eventCount + 1),
      ∃ hle : first ≤ last (f i),
        (H (f i)).time first ≤ s (f i) - θ / (O (f i)).scale ∧
        0 ≤ s (f i) - θ / (O (f i)).scale ∧
        ∀ x ∈ (O (f i)).chart '' {z | z.val ∈ K},
          Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val) := by
  obtain ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,hwindow⟩ :=
    exists_uniform_backward_trace_window_of_cylindrical_limit D r eps a₀ Ctime
      ha₀ heps hepssmall hr hfit
  refine ⟨θ,ε₀,δ₀,hθ,hε₀,hδ₀,?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa P e mark
  let x := fun i => (O i).chart
    ⟨(mark,0),by constructor <;> dsimp <;> linarith [inv_pos.mpr (O i).delta_pos]⟩
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := { obj := fun i => {
    M := (G i).terminalRegularOpen
    basepoint := x i
    metric := scaleMetric (O i).scale (O i).scale_pos (L i).metric } }
  let P₀ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := {
    P with
    basepoint := e (mark,0)
    metric := Diffeomorph.pullbackMetricCross
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0) e.symm }
  obtain ⟨_,_,hproduct,f,hf,maps,hmap,_,_,_,C,hcanonical⟩ :=
    exists_pointed_cylinder_convergence_of_selected_necks H last s G L eta m O heta hm P e mark
  refine ⟨f,hf,?_⟩
  intro K hK parameters records hfixed hlower hdelta haccuracy hmargin horder
    q₀ hq₀ hderiv hfinal hcap center precision order d w Jbig hJbig hzero hmark
  have he : Diffeomorph.pullbackMetricCross P₀.metric e =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0 := by
    rw [PDE.RicciFlow.shrinkingCylinderMetric_zero,← roundCylinderMetric_eq_geometry]
    exact hproduct
  have htraces := hwindow H last s G L hinit x (fun i => (O i).scale)
    (fun i => (O i).scale_pos) hscale ha hsa P₀ f hf maps C hcanonical e 0 le_rfl he
    (e '' K) (hK.image e.continuous) parameters records hfixed hlower hdelta haccuracy
    hmargin horder q₀ hq₀ hderiv hfinal hcap center precision order d w Jbig hJbig hzero hmark
  filter_upwards [htraces] with i hi
  obtain ⟨first,hle,hfirst,hnonneg,hpoints⟩ := hi
  refine ⟨first,hle,hfirst,hnonneg,?_⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := hy
  have hh := hpoints (e z) (mem_image_of_mem e hz)
  simpa only [hmap i z] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

private local instance sphereThreeDim : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

private theorem exists_common_cylindrical_reset
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {T a b : ℝ} (ha : -T < a) (hab : a < b) (hb : b < 0)
    (hslab : Icc (-T) 0 ⊆ D.carrier) (hreg : Ioo (-T) 0 ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc (-T) 0 →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    (C : ℝ≥0) (q Q : ℕ → ℝ) (hq : ∀ᶠ i in atTop, q i ≤ 1)
    (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hderiv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q (i + N n) < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤ C * (S n i).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ i in atTop, PhiAlmostNonnegative (S n i)
      (Icc (-T) 0) (rescalePinchingFunction (Q (i + N n)) Phi))
    (H : ℕ → ObservedHistory.{u}) (s : ℕ → ℝ) :
    ∃ (rho : ℕ → ℕ) (v : ℝ), StrictMono rho ∧ v ∈ Ioo a b ∧
      (∀ i, s i + v / Q i ∉ range (H i).time) ∧
      RiemannianMetricComplete (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) ∧
      (∀ x, 0 < metricScalarAt (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) x ∧
        metricScalarAt (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) x ≤ 1) ∧
      ∀ n, MetricCInfConvergenceOnCompacts
        (fun i => (S n (rho i - N n)).base.metric v)
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer (δ n)))
        (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) := by
  obtain ⟨rho,hrho,hconv⟩ :=
    exists_subsequence_converges_to_shrinkingCylinder_on_subinterval_of_scalar_deriv_bound
      hδ hδlim S hS (show 0 < -a by linarith) (show -a < T by linarith)
      hslab hreg hterminal N hcompat C q Q hq hQpos hQ hderiv hPhi hpinch
  let bad : Set ℝ := ⋃ i : ℕ, (fun t => Q i * (t - s i)) '' range (H i).time
  have hbad : bad.Countable := countable_iUnion fun i =>
    ((finite_range (H i).time).image _).countable
  have hnotsub : ¬ Ioo a b ⊆ bad := by
    intro hsub
    have hle : b ≤ a := by
      simpa only [Cardinal.Real.Ioo_countable_iff] using hbad.mono hsub
    linarith
  obtain ⟨v,hv,hnot⟩ := not_subset.mp hnotsub
  have hv0 : v < 0 := by linarith [hv.2]
  refine ⟨rho,v,hrho,hv,?_,PDE.RicciFlow.shrinkingCylinderMetric_complete v,?_,?_⟩
  · intro i htime
    apply hnot
    apply mem_iUnion.mpr
    refine ⟨i,s i + v / Q i,htime,?_⟩
    field_simp [(hQpos i).ne']
    ring
  · intro x
    exact ⟨PDE.RicciFlow.shrinkingCylinderMetric_scalar_pos (hv0.trans zero_lt_one) x,
      PDE.RicciFlow.shrinkingCylinderMetric_scalar_le_one hv0.le x⟩
  · intro n K hK p eta heta
    obtain ⟨j,hj⟩ := hconv n K hK p eta heta
    exact ⟨j,fun i hi => hj i hi v ⟨by simpa only [neg_neg] using hv.1.le,hv0.le⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private prospective_historical_normalized_pullback_overlap from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckConvergence

private local instance (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

variable (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (offset : ℕ → ℕ)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  (Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen)
  (htrace : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (last (j + offset n))
    (hle (j + offset n)) x.val))
  (hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (T : ℝ) (hT : 0 < T)
  (hstart : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (C : ℝ≥0) (qPhysical : ℕ → ℝ)
  (hq : ∀ᶠ i in atTop, qPhysical i / (O i).scale ≤ 1)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      qPhysical i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    qPhysical i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)

include heps horder hprecision htrace hinside hstart hinit hderivative hfinal hphi hpinching hpinchFinal in
private theorem exists_actual_prospective_rows_on_finite_window :
    ∃ (F : ∀ n i, neckBuffer (δ n) → (H (i + offset n)).backwardSurvivorIncomingFootprint
        (first (i + offset n)) (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)) (Footprint n i))
      (hF : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F n i))
      (gflow : ∀ n i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H (i + offset n)).backwardSurvivorIncomingFootprint (first (i + offset n))
          (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)) (Footprint n i)))
      (S : ∀ n, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n))
        (RealTimeInterval.closed (-T) 0 (by linarith))),
      (∀ n i, (H (i + offset n)).backwardSurvivorIncomingFootprintMap
        (first (i + offset n)) (last (i + offset n)) (hle (i + offset n)) (J (i + offset n))
        (Footprint n i) ∘ F n i = ((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart) ∧
      (∀ n i, IsSolutionOn (S n i)) ∧
      (∀ n i, (S n i).base.metric 0 = ((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).normalizedMetric) ∧
      (∀ n i t, (S n i).base.metric t = localPullMetric
        (scaleMetric (O (i + offset n)).scale (O (i + offset n)).scale_pos
          (gflow n i (s (i + offset n) + t / (O (i + offset n)).scale))) (F n i) (hF n i)) ∧
      (∀ n i (j : Fin (H (i + offset n)).eventCount) (hf : first (i + offset n) ≤ j.castSucc)
        (hl : j.succ ≤ last (i + offset n)),
        ∀ t ∈ Icc ((H (i + offset n)).time j.castSucc) ((H (i + offset n)).time j.succ),
          gflow n i t = (((H (i + offset n)).backwardSurvivorSlabMetric (first (i + offset n))
            (last (i + offset n)) (hle (i + offset n)) j hf hl t).restrictOpen
              ((H (i + offset n)).backwardSurvivorIncomingDomain (first (i + offset n))
                (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)))).restrictOpen
                ((H (i + offset n)).backwardSurvivorIncomingFootprint (first (i + offset n))
                  (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)) (Footprint n i))) ∧
      (∀ n i t, t ∈ Icc ((H (i + offset n)).time (last (i + offset n))) (s (i + offset n)) →
        gflow n i t = ((H (i + offset n)).backwardSurvivorIncomingMetric (first (i + offset n))
          (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)) (L (i + offset n)) t).restrictOpen
            ((H (i + offset n)).backwardSurvivorIncomingFootprint (first (i + offset n))
              (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)) (Footprint n i))) ∧
      (∀ n, MetricCInfConvergenceOnCompacts
        (fun i => (S n i).base.metric 0)
        (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
        (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))) ∧
      (∀ n m t, t ∈ Icc (-T) 0 →
        (fun i => ((S n (i - offset n)).base.metric t).restrictOpenOfSubset
          (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
        (fun i => ((S m (i - offset m)).base.metric t).restrictOpenOfSubset
          (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m)))) ∧
      (∀ n, ∀ A : Set (neckBuffer (δ n)), IsCompact A → ∀ᶠ i in atTop,
        ∀ x ∈ A, ∀ t ∈ Ioo (-T) 0,
          qPhysical (i + offset n) / (O (i + offset n)).scale < (S n i).scalar t x →
          |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
            C * (S n i).scalar t x ^ 2) ∧
      (∀ n, ∀ᶠ i in atTop, Perelman.PhiAlmostNonnegative (S n i)
        (Icc (-T) 0) (Perelman.rescalePinchingFunction (O (i + offset n)).scale phi)) := by
  classical
  have hrow (n j : ℕ) := (H (j + offset n)).exists_historical_pullback_solution_from_incoming_slab_with_scalar_bounds
    (first (j + offset n)) (last (j + offset n)) (hle (j + offset n))
    (J (j + offset n)) (L (j + offset n)) (hinit (j + offset n))
    ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n))
    (Footprint n j) (htrace n j) (hinside n j) hT.le
    (hstart (j + offset n)) (hderivative (j + offset n)) (hfinal (j + offset n))
    hphi.contDiff.continuous (hpinching (j + offset n)) (hpinchFinal (j + offset n))
  choose F hF GG SS hmap hS hzero hmetric hslabs hlast hderiv hpinch using hrow
  refine ⟨F,hF,GG,SS,hmap,hS,hzero,hmetric,hslabs,hlast,?_,?_,?_,?_⟩
  · intro n A hA
    have htail : Tendsto (fun j : ℕ => j + offset n) atTop atTop := tendsto_add_atTop_nat _
    have hc := NormalizedNeck.metricCInfConvergenceOn_restrict_of_precision_tendsto_zero
      (fun j => O (j + offset n)) (hprecision n) (heps.comp htail) (horder.comp htail) A
    intro p eta heta
    obtain ⟨j0,hj0⟩ := hc p eta heta
    refine ⟨j0,fun j hj => ?_⟩
    change metricDerivNormSupOn A p ((SS n j).base.metric 0) _ _ < eta
    rw [hzero n j]
    exact hj0 j hj
  · intro n m t ht
    filter_upwards [eventually_ge_atTop (max (offset n) (offset m))] with j hj
    have hjn : offset n ≤ j := (le_max_left _ _).trans hj
    have hjm : offset m ≤ j := (le_max_right _ _).trans hj
    have hn : j - offset n + offset n = j := Nat.sub_add_cancel hjn
    have hm : j - offset m + offset m = j := Nat.sub_add_cancel hjm
    rw [hmetric n (j - offset n) t, hmetric m (j - offset m) t]
    let jn := j - offset n
    let jm := j - offset m
    have htime : s j + t / (O j).scale ∈
        Icc ((H j).time (first j)) (s j) := by
      have hlo : -T / (O j).scale ≤ t / (O j).scale :=
        div_le_div_of_nonneg_right ht.1 (O j).scale_pos.le
      have hhi : t / (O j).scale ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht.2 (O j).scale_pos.le
      have hstart := hstart j
      rw [neg_div] at hlo
      constructor <;> linarith
    have hrowsame : ∀ (an am : ℕ) (hpn : eps an ≤ δ n) (hpm : eps am ≤ δ m),
        an = j → am = j →
        ∀ (Kn : Set (J an).terminalRegularOpen)
          (Km : Set (J am).terminalRegularOpen)
          (Fn : neckBuffer (δ n) → (H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn)
          (Fm : neckBuffer (δ m) → (H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)
          (hFn : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Fn)
          (hFm : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Fm)
          (Gn : ℝ → SmoothRiemannianMetric ThreeModel
            ((H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn))
          (Gm : ℝ → SmoothRiemannianMetric ThreeModel
            ((H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)),
          ((H an).backwardSurvivorIncomingFootprintMap (first an) (last an) (hle an) (J an) Kn ∘ Fn =
            ((O an).monoDelta hpn (hδ1 n)).chart) →
          ((H am).backwardSurvivorIncomingFootprintMap (first am) (last am) (hle am) (J am) Km ∘ Fm =
            ((O am).monoDelta hpm (hδ1 m)).chart) →
          (∀ (r : Fin (H an).eventCount) (hf : first an ≤ r.castSucc)
            (hl : r.succ ≤ (last an)), ∀ u ∈ Icc ((H an).time r.castSucc) ((H an).time r.succ),
              Gn u = (((H an).backwardSurvivorSlabMetric (first an) (last an)
                (hle an) r hf hl u).restrictOpen ((H an).backwardSurvivorIncomingDomain (first an) (last an) (hle an) (J an))).restrictOpen
                  ((H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn)) →
          (∀ (r : Fin (H am).eventCount) (hf : first am ≤ r.castSucc)
            (hl : r.succ ≤ (last am)), ∀ u ∈ Icc ((H am).time r.castSucc) ((H am).time r.succ),
              Gm u = (((H am).backwardSurvivorSlabMetric (first am) (last am)
                (hle am) r hf hl u).restrictOpen ((H am).backwardSurvivorIncomingDomain (first am) (last am) (hle am) (J am))).restrictOpen
                  ((H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)) →
          (∀ u ∈ Icc ((H an).time (last an)) (s an),
            Gn u = ((H an).backwardSurvivorIncomingMetric (first an) (last an) (hle an) (J an) (L an) u).restrictOpen
              ((H an).backwardSurvivorIncomingFootprint (first an) (last an) (hle an) (J an) Kn)) →
          (∀ u ∈ Icc ((H am).time (last am)) (s am),
            Gm u = ((H am).backwardSurvivorIncomingMetric (first am) (last am) (hle am) (J am) (L am) u).restrictOpen
              ((H am).backwardSurvivorIncomingFootprint (first am) (last am) (hle am) (J am) Km)) →
          (localPullMetric (scaleMetric (O an).scale (O an).scale_pos
              (Gn (s an + t / (O an).scale))) Fn hFn).restrictOpenOfSubset
                (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n)) =
            (localPullMetric (scaleMetric (O am).scale (O am).scale_pos
              (Gm (s am + t / (O am).scale))) Fm hFm).restrictOpenOfSubset
                (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m)) := by
      intro an am hpn hpm han ham
      subst an
      subst am
      intro Kn Km Fn Fm hFn hFm Gn Gm hmapn hmapm hslabn hslabm hlastn hlastm
      exact prospective_historical_normalized_pullback_overlap (O j) hpn hpm (hδ1 n) (hδ1 m)
        Kn Km Fn Fm hFn hFm hmapn hmapm Gn Gm hslabn hslabm hlastn hlastm htime
    exact hrowsame (jn + offset n) (jm + offset m) (hprecision n jn) (hprecision m jm)
      hn hm (Footprint n jn) (Footprint m jm) (F n jn) (F m jm) (hF n jn) (hF m jm)
      (GG n jn) (GG m jm) (hmap n jn) (hmap m jm) (hslabs n jn) (hslabs m jm)
      (hlast n jn) (hlast m jm)
  · intro n A hA
    exact Eventually.of_forall fun j x hx t ht hh => hderiv n j t ht x hh
  · intro n
    apply Eventually.of_forall
    intro j
    exact hpinch n j


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_actual_interior_source_reset
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ), gflow t =
        ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ t ∈ Icc (H.time last) s, gflow t =
      (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {τ : ℝ} (hτ : τ ∈ Ioo (H.time first) s) (hneq : τ ∉ range H.time) :
    ∃ (reset : Fin (H.eventCount + 1)) (hf : first ≤ reset) (hl : reset ≤ last)
      (J : (H.stage reset).IncomingSlab (H.time reset) τ) (Lτ : J.TerminalLimitMetric)
      (Ψ : H.backwardSurvivorIncomingFootprint first last hle G K → J.terminalRegularOpen)
      (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ),
      J.flow.base.metric (H.time reset) = H.initialMetric reset ∧
      J.terminalRegularRegion = univ ∧
      Lτ.metric = (J.flow.base.metric τ).restrictOpen J.terminalRegularOpen ∧
      Function.Injective Ψ ∧
      (∀ z, (Ψ z).val = H.backwardSurvivorIncomingFootprintStageMap first last hle G K reset hf hl z) ∧
      localPullMetric Lτ.metric Ψ hΨ = gflow τ ∧
      ((reset = last ∧ τ < s ∧ ∀ t, HEq (J.flow.base.metric t) (G.flow.base.metric t)) ∨
        ∃ j : Fin H.eventCount, reset = j.castSucc ∧ j.succ ≤ last ∧ τ < H.time j.succ ∧
          ∀ t, HEq (J.flow.base.metric t) (H.stageMetric j.castSucc t)) := by
  by_cases hlt : H.time last < τ
  · obtain ⟨J,Lτ,Ψ,hΨ,hmetric,hregular,hterminal,hinj,hmap,hpull⟩ :=
      H.exists_backwardSurvivorIncomingFootprint_final_interior_endpoint first last hle G K ⟨hlt,hτ.2⟩
    refine ⟨last,hle,le_rfl,J,Lτ,Ψ,hΨ,?_,hregular,?_,hinj,?_,?_,Or.inl ⟨rfl,hτ.2,fun t => heq_of_eq (hmetric t)⟩⟩
    · rw [hmetric]
      exact hinit
    · rw [hmetric τ]
      exact hterminal
    · intro z
      exact (hmap z).trans (H.backwardSurvivorIncomingFootprintStageMap_last first last hle G K z).symm
    · rw [hlast τ ⟨hlt.le,hτ.2.le⟩]
      exact hpull L
  · have hbefore : τ < H.time last :=
      lt_of_le_of_ne (not_lt.mp hlt) (fun he => hneq ⟨last,he.symm⟩)
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨τ,(H.time_nonneg first).trans hτ.1.le,hbefore.le.trans (H.time_le_horizon_at last)⟩
    let reset := H.activeStage tH
    have hresetlast : reset < last := by
      apply H.time_strictMono.lt_iff_lt.mp
      exact (H.activeStage_time_le tH).trans_lt hbefore
    have hfirst : first ≤ reset := H.le_activeStage tH first hτ.1.le
    let j : Fin H.eventCount := ⟨reset.val,by have := last.isLt; change reset.val < H.eventCount; omega⟩
    have hj : τ ∈ Ioo (H.time j.castSucc) (H.time j.succ) := by
      refine ⟨lt_of_le_of_ne (H.activeStage_time_le tH) (fun he => hneq ⟨j.castSucc,he⟩),?_⟩
      exact H.activeStage_before_next tH (show reset.val < H.eventCount from j.isLt)
    have hjl : j.succ ≤ last := hresetlast
    obtain ⟨J,Lτ,Ψ,hΨ,hmetric,hJinit,hregular,hterminal,hinj,hmap,hpull⟩ :=
      H.exists_backwardSurvivorIncomingFootprint_interior_endpoint first last hle G K j hfirst hjl hj
    refine ⟨j.castSucc,hfirst,j.castSucc_lt_succ.le.trans hjl,J,Lτ,Ψ,hΨ,hJinit,hregular,?_,hinj,hmap,?_,?_⟩
    · rw [hmetric τ]
      exact hterminal
    · rw [hslabs j hfirst hjl τ ⟨hj.1.le,hj.2.le⟩]
      exact hpull
    · refine Or.inr ⟨j,rfl,hjl,hj.2,?_⟩
      intro t
      apply heq_of_eq
      simpa only [stageMetric, Fin.lastCases_castSucc] using hmetric t

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end
end

section
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open private slabMetric_restrict_eq_localPull incomingMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

private theorem exists_actual_reset_map_on_footprint
    (H : ObservedHistory.{u}) (first reset last : Fin (H.eventCount + 1))
    (hf : first ≤ reset) (hl : reset ≤ last)
    {s τ : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (J : (H.stage reset).IncomingSlab (H.time reset) τ) (Lτ : J.TerminalLimitMetric)
    (hregular : J.terminalRegularRegion = univ)
    (hterminal : Lτ.metric = (J.flow.base.metric τ).restrictOpen J.terminalRegularOpen)
    (hsource : (reset = last ∧ τ < s ∧ ∀ t, HEq (J.flow.base.metric t) (G.flow.base.metric t)) ∨
      ∃ j : Fin H.eventCount, reset = j.castSucc ∧ j.succ ≤ last ∧ τ < H.time j.succ ∧
        ∀ t, HEq (J.flow.base.metric t) (H.stageMetric j.castSucc t))
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last (hf.trans hl) G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hfj : first ≤ j.castSucc) (hlj : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ), gflow t =
        ((H.backwardSurvivorSlabMetric first last (hf.trans hl) j hfj hlj t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last (hf.trans hl) G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last (hf.trans hl) G K))
    (hlast : ∀ t ∈ Icc (H.time last) s, gflow t =
      (H.backwardSurvivorIncomingMetric first last (hf.trans hl) G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last (hf.trans hl) G K)) :
    ∃ (Ψ : H.backwardSurvivorIncomingFootprint first last (hf.trans hl) G K → J.terminalRegularOpen)
      (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ), Function.Injective Ψ ∧
      (∀ z, (Ψ z).val = H.backwardSurvivorIncomingFootprintStageMap
        first last (hf.trans hl) G K reset hf hl z) ∧
      localPullMetric Lτ.metric Ψ hΨ = gflow τ := by
  let f := H.backwardSurvivorIncomingFootprintStageMap first last (hf.trans hl) G K reset hf hl
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last (hf.trans hl) G K reset hf hl
  have hmem (z : H.backwardSurvivorIncomingFootprint first last (hf.trans hl) G K) :
      f z ∈ J.terminalRegularOpen := by
    change f z ∈ J.terminalRegularRegion
    rw [hregular]
    trivial
  let Ψ : H.backwardSurvivorIncomingFootprint first last (hf.trans hl) G K → J.terminalRegularOpen :=
    fun z => ⟨f z,hmem z⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ :=
    fun z => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem (hlocal z)
  refine ⟨Ψ,hΨ,?_,fun _ => rfl,?_⟩
  · intro z w hzw
    have h := H.backwardSurvivorMap_injective first last (hf.trans hl) reset hf hl
      (congrArg Subtype.val hzw)
    exact Subtype.ext (Subtype.ext h)
  have hpull : localPullMetric Lτ.metric Ψ hΨ = localPullMetric (J.flow.base.metric τ) f hlocal := by
    rw [hterminal]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner,localPullMetric_inner]
    change (J.flow.base.metric τ).inner (f z)
      (mfderiv ThreeModel ThreeModel Ψ z v) (mfderiv ThreeModel ThreeModel Ψ z w) = _
    have hd : mfderiv ThreeModel ThreeModel Ψ z = mfderiv ThreeModel ThreeModel f z :=
      (DifferentialGeometry.mfderiv_subtypeVal_comp Ψ z).symm
    rw [hd]
    rfl
  rw [hpull]
  rcases hsource with ⟨heq,hts,hmetric⟩ | ⟨j,heq,hjl,htj,hmetric⟩
  · subst reset
    have ht0 : H.time last < τ := J.lt
    rw [hlast τ ⟨ht0.le,hts.le⟩,eq_of_heq (hmetric τ)]
    exact (incomingMetric_restrict_eq_localPull H first last (hf.trans hl) G L K hts).symm
  · subst reset
    have ht0 : H.time j.castSucc < τ := J.lt
    rw [hslabs j hf hjl τ ⟨ht0.le,htj.le⟩,eq_of_heq (hmetric τ)]
    simpa only [stageMetric,Fin.lastCases_castSucc,f] using
      (slabMetric_restrict_eq_localPull H first last (hf.trans hl) G K j hf hjl htj).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end
end

section
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


private local instance (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

variable (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (offset : ℕ → ℕ) (hoffset : offset 0 = 0)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  (Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen)
  (htrace : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (last (j + offset n))
    (hle (j + offset n)) x.val))
  (hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (T : ℝ) (hT : 0 < T)
  (hstart : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (C : ℝ≥0) (qPhysical : ℕ → ℝ)
  (hq : ∀ᶠ i in atTop, qPhysical i / (O i).scale ≤ 1)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      qPhysical i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    qPhysical i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)

include hT hδ hδlim heps horder hprecision htrace hinside hstart hinit hderivative hfinal
  hphi hpinching hpinchFinal hq hscale hoffset in
private theorem exists_actual_cylindrical_source_reset
    {a b : ℝ} (ha : -T < a) (hab : a < b) (hb : b < 0) :
    ∃ v : ℝ, v ∈ Ioo a b ∧
      ∃ (reset : ∀ i, Fin ((H i).eventCount + 1))
        (hf : ∀ i, first i ≤ reset i) (hl : ∀ i, reset i ≤ last i)
        (Jτ : ∀ i, ((H i).stage (reset i)).IncomingSlab ((H i).time (reset i)) (s i + v / (O i).scale))
        (Lτ : ∀ i, (Jτ i).TerminalLimitMetric),
        (∀ i, (Jτ i).flow.base.metric ((H i).time (reset i)) = (H i).initialMetric (reset i)) ∧
        (∀ i, (Jτ i).terminalRegularRegion = univ) ∧
        (∀ i, (Lτ i).metric = ((Jτ i).flow.base.metric (s i + v / (O i).scale)).restrictOpen (Jτ i).terminalRegularOpen) ∧
        (∀ i, ((reset i = last i ∧ s i + v / (O i).scale < s i ∧
          ∀ t, HEq ((Jτ i).flow.base.metric t) ((J i).flow.base.metric t)) ∨
          ∃ j : Fin (H i).eventCount, reset i = j.castSucc ∧ j.succ ≤ last i ∧
            s i + v / (O i).scale < (H i).time j.succ ∧
            ∀ t, HEq ((Jτ i).flow.base.metric t) ((H i).stageMetric j.castSucc t))) ∧
        ∃ (psi : ∀ n i, neckBuffer (δ n) → (Jτ (i + offset n)).terminalRegularOpen)
          (hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i)),
          (∀ n i, Function.Injective (psi n i)) ∧
          (∀ n i (z : neckBuffer (δ n)),
            ∃ A : BackwardPointTrace (H (i + offset n)) (first (i + offset n)) (last (i + offset n))
                (hle (i + offset n)) (((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z).val,
              (psi n i z).val = A.point (reset (i + offset n)) (hf (i + offset n)) (hl (i + offset n))) ∧
          ∃ rho : ℕ → ℕ, StrictMono rho ∧
            ∀ n, MetricCInfConvergenceOnCompacts
              (fun i => localPullMetric
                (scaleMetric (O (rho i - offset n + offset n)).scale
                  (O (rho i - offset n + offset n)).scale_pos (Lτ (rho i - offset n + offset n)).metric)
                (psi n (rho i - offset n)) (hpsi n (rho i - offset n)))
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer (δ n)))
              (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) := by
  classical
  obtain ⟨tail,rfl⟩ : ∃ tail : ℕ → ℕ, offset = fun n => Nat.casesOn n 0 tail := by
    refine ⟨fun n => offset (n+1),funext ?_⟩
    intro n
    cases n with
    | zero => exact hoffset
    | succ n => rfl
  let offset : ℕ → ℕ := fun n => Nat.casesOn n 0 tail
  obtain ⟨F,hF,gflow,S,hmap,hS,hzero,hmetric,hslabs,hlast,hterminal,hcompat,hderiv,hpinch⟩ :=
    exists_actual_prospective_rows_on_finite_window H last first hle s J L hinit δ hδ1
      eps order O heps horder offset hprecision Footprint htrace hinside T hT hstart C qPhysical
      hderivative hfinal hphi hpinching hpinchFinal
  obtain ⟨rho,v,hrho,hv,havoid,_,_,hconv⟩ := exists_common_cylindrical_reset hδ hδlim S hS
    ha hab hb Subset.rfl Subset.rfl hterminal offset hcompat C
      (fun i => qPhysical i / (O i).scale) (fun i => (O i).scale) hq
      (fun i => (O i).scale_pos) hscale hderiv hphi hpinch H s
  have htime (i : ℕ) : s i + v / (O i).scale ∈ Ioo ((H i).time (first i)) (s i) := by
    have hvT : -T < v := ha.trans hv.1
    have hv0 : v < 0 := hv.2.trans hb
    have hlo := div_lt_div_of_pos_right hvT (O i).scale_pos
    have hhi := div_neg_of_neg_of_pos hv0 (O i).scale_pos
    rw [neg_div] at hlo
    constructor <;> linarith [hstart i]
  have hreset (i : ℕ)  := ObservedHistory.exists_actual_interior_source_reset (H i) (first i) (last i) (hle i)
    (J i) (L i) (hinit i) (Footprint 0 i) (gflow 0 i) (hslabs 0 i) (hlast 0 i)
    (htime i) (havoid i)
  choose reset hf hl Jτ Lτ Psi hPsi hinitτ hregτ htermτ hinjτ hstageτ hpullτ hsourceτ using hreset
  have hrow (n i : ℕ) := ObservedHistory.exists_actual_reset_map_on_footprint (H (i + offset n))
    (first (i + offset n)) (reset (i + offset n)) (last (i + offset n))
    (hf (i + offset n)) (hl (i + offset n)) (J (i + offset n)) (L (i + offset n))
    (Jτ (i + offset n)) (Lτ (i + offset n)) (hregτ (i + offset n)) (htermτ (i + offset n))
    (hsourceτ (i + offset n)) (Footprint n i) (gflow n i) (hslabs n i) (hlast n i)
  choose Row hRow hinjRow hstage hpull using hrow
  let psi := fun n i => Row n i ∘ F n i
  have hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i) :=
    fun n i => DifferentialGeometry.isLocalDiffeomorph_comp (hRow n i) (hF n i)
  have hinj : ∀ n i, Function.Injective (psi n i) := by
    intro n i
    apply (hinjRow n i).comp
    intro z w hzw
    apply ((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart_smooth.isEmbedding.injective
    rw [← hmap n i]
    exact congrArg ((H (i + offset n)).backwardSurvivorIncomingFootprintMap
      (first (i + offset n)) (last (i + offset n)) (hle (i + offset n)) (J (i + offset n)) (Footprint n i)) hzw
  have hmetricτ (n i : ℕ) : localPullMetric
      (scaleMetric (O (i + offset n)).scale (O (i + offset n)).scale_pos (Lτ (i + offset n)).metric)
      (psi n i) (hpsi n i) = (S n i).base.metric v := by
    rw [hmetric n i v]
    rw [← localPullMetric_comp _ (Row n i) (F n i) (hRow n i) (hF n i) (hpsi n i),
      localPullMetric_scaleMetric,hpull n i]
  refine ⟨v,hv,reset,hf,hl,Jτ,Lτ,hinitτ,hregτ,htermτ,hsourceτ,psi,hpsi,hinj,?_,rho,hrho,?_⟩
  · intro n i z
    let z' := ((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z
    have hzK : z' ∈ Footprint n i := interior_subset (hinside n i (mem_range_self z))
    obtain ⟨A⟩ := htrace n i z' hzK
    refine ⟨A,?_⟩
    change (Row n i (F n i z)).val = _
    rw [hstage n i]
    have hz : (F n i z).val.val.val = z'.val := congrArg Subtype.val (congrFun (hmap n i) z)
    let zD : (H (i + offset n)).backwardSurvivorDomain
        (first (i + offset n)) (last (i + offset n)) (hle (i + offset n)) := ⟨z'.val,⟨A⟩⟩
    have hzz : (F n i z).val.val = zD := Subtype.ext hz
    change (H (i + offset n)).backwardSurvivorMap _ _ _ _ _ _ (F n i z).val.val = _
    rw [hzz]
    exact (H (i + offset n)).backwardSurvivorMap_eq_point _ _ _ _ _ _ zD A
  · intro n
    change MetricCInfConvergenceOnCompacts
      (fun i => localPullMetric
        (scaleMetric (O (rho i - offset n + offset n)).scale
          (O (rho i - offset n + offset n)).scale_pos (Lτ (rho i - offset n + offset n)).metric)
        (psi n (rho i - offset n)) (hpsi n (rho i - offset n)))
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
    simpa only [hmetricτ] using hconv n

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_strict_subsequence_above_offsets
    (rho offset : ℕ → ℕ) (hrho : StrictMono rho) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ i, ∀ n ≤ i, offset n ≤ rho (k i) := by
  let k : ℕ → ℕ := fun i => i + (Finset.range (i+1)).sup offset
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hm : (Finset.range (i+1)).sup offset ≤ (Finset.range (i+1+1)).sup offset :=
      Finset.sup_mono (Finset.range_mono (by omega))
    dsimp [k]
    omega
  refine ⟨k,hk,?_⟩
  intro i n hn
  have hbound : offset n ≤ (Finset.range (i+1)).sup offset :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hle : (Finset.range (i+1)).sup offset ≤ k i := by dsimp [k]; omega
  exact hbound.trans (hle.trans (hrho.id_le (k i)))

private theorem eventually_subset_growing_neckBuffer
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (K : Set NeckCylinder) (hK : IsCompact K) :
    ∀ᶠ i in atTop, K ⊆ neckBuffer (δ i) := by
  obtain ⟨B,hB⟩ := hK.bddAbove_image (continuous_snd.abs.continuousOn)
  have hsmall : ∀ᶠ i in atTop, δ i < (max B 0 + 2)⁻¹ :=
    hδlim.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hsmall] with i hi x hx
  have hupper : |x.2| ≤ max B 0 := (hB ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  have hrad : max B 0 + 2 < (δ i)⁻¹ := by
    rw [inv_eq_one_div] at hi ⊢
    have hmul := (lt_div_iff₀ (by positivity : 0 < max B 0 + 2)).mp hi
    apply (lt_div_iff₀ (hδ i)).mpr
    nlinarith
  have hxabs := abs_le.mp hupper
  constructor <;> linarith [hxabs.1,hxabs.2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

private theorem actual_reset_maps_eq_of_same_selected_chart
    (H : ObservedHistory.{u}) (first reset last : Fin (H.eventCount + 1))
    (hf : first ≤ reset) (hl : reset ≤ last)
    {s τ : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (J : (H.stage reset).IncomingSlab (H.time reset) τ)
    {eps d₁ d₂ : ℝ} {k : ℕ} (O : NormalizedNeck L.metric eps k)
    (h₁ : eps ≤ d₁) (h₂ : eps ≤ d₂) (hd₁ : d₁ < 1) (hd₂ : d₂ < 1)
    (psi₁ : neckBuffer d₁ → J.terminalRegularOpen)
    (psi₂ : neckBuffer d₂ → J.terminalRegularOpen)
    (hpoint₁ : ∀ z : neckBuffer d₁, ∃ A : BackwardPointTrace H first last (hf.trans hl)
        ((O.monoDelta h₁ hd₁).chart z).val, (psi₁ z).val = A.point reset hf hl)
    (hpoint₂ : ∀ z : neckBuffer d₂, ∃ A : BackwardPointTrace H first last (hf.trans hl)
        ((O.monoDelta h₂ hd₂).chart z).val, (psi₂ z).val = A.point reset hf hl)
    (z₁ : neckBuffer d₁) (z₂ : neckBuffer d₂) (hz : z₁.val = z₂.val) :
    psi₁ z₁ = psi₂ z₂ := by
  obtain ⟨A,hA⟩ := hpoint₁ z₁
  obtain ⟨B,hB⟩ := hpoint₂ z₂
  have hchart : ((O.monoDelta h₁ hd₁).chart z₁).val = ((O.monoDelta h₂ hd₂).chart z₂).val := by
    change (O.chart (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le O.delta_pos h₁) z₁)).val =
      (O.chart (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le O.delta_pos h₂) z₂)).val
    exact congrArg (fun z => (O.chart z).val) (Subtype.ext hz)
  apply Subtype.ext
  rw [hA,hB]
  have hpoint : ∀ (x y : (H.stage last).Carrier), x = y →
      ∀ (A : BackwardPointTrace H first last (hf.trans hl) x)
        (B : BackwardPointTrace H first last (hf.trans hl) y),
          A.point reset hf hl = B.point reset hf hl := by
    intro x y hxy
    subst y
    intro A B
    exact A.point_unique B reset hf hl
  exact hpoint _ _ hchart A B

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)


variable {H : ℕ → ObservedHistory.{u}} {reset : ∀ i, Fin ((H i).eventCount + 1)}
  {τ : ℕ → ℝ} (J : ∀ i, ((H i).stage (reset i)).IncomingSlab ((H i).time (reset i)) (τ i))
  {δ : ℕ → ℝ} {offset : ℕ → ℕ}
  (psi : ∀ n i, neckBuffer (δ n) → (J (i + offset n)).terminalRegularOpen)

private def reindexResetMap {d : ℝ} {p q : ℕ} (hpq : p = q)
    (f : neckBuffer d → (J p).terminalRegularOpen) :
    neckBuffer d → (J q).terminalRegularOpen := hpq ▸ f

private theorem reindexResetMap_heq {d : ℝ} {p q : ℕ} (hpq : p = q)
    (f : neckBuffer d → (J p).terminalRegularOpen) : HEq (reindexResetMap J hpq f) f := by
  subst q
  rfl

private theorem reindexResetMap_isLocalDiffeomorph {d : ℝ} {p q : ℕ} (hpq : p = q)
    (f : neckBuffer d → (J p).terminalRegularOpen)
    (hf : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ f) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (reindexResetMap J hpq f) := by
  subst q
  exact hf

private theorem reindexResetMap_injective {d : ℝ} {p q : ℕ} (hpq : p = q)
    (f : neckBuffer d → (J p).terminalRegularOpen) (hf : Function.Injective f) :
    Function.Injective (reindexResetMap J hpq f) := by
  subst q
  exact hf

private def resetRowMap (n p : ℕ) (hp : offset n ≤ p) :
    neckBuffer (δ n) → (J p).terminalRegularOpen :=
  reindexResetMap J (Nat.sub_add_cancel hp) (psi n (p - offset n))

private theorem resetRowMap_heq (n p : ℕ) (hp : offset n ≤ p) :
    HEq (resetRowMap J psi n p hp) (psi n (p - offset n)) :=
  reindexResetMap_heq J _ _

private theorem resetRowMap_isLocalDiffeomorph
    (hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i))
    (n p : ℕ) (hp : offset n ≤ p) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (resetRowMap J psi n p hp) :=
  reindexResetMap_isLocalDiffeomorph J _ _ (hpsi n (p - offset n))

private theorem resetRowMap_injective
    (hinj : ∀ n i, Function.Injective (psi n i))
    (n p : ℕ) (hp : offset n ≤ p) :
    Function.Injective (resetRowMap J psi n p hp) :=
  reindexResetMap_injective J _ _ (hinj n (p - offset n))

private theorem reindexResetMap_localPullMetric
    (M : ∀ i, DifferentialGeometry.SmoothRiemannianMetric ThreeModel (J i).terminalRegularOpen)
    {d : ℝ} {p q : ℕ} (hpq : p = q)
    (f : neckBuffer d → (J p).terminalRegularOpen)
    (hf : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ f)
    (hfq : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (reindexResetMap J hpq f)) :
    localPullMetric (M q) (reindexResetMap J hpq f) hfq = localPullMetric (M p) f hf := by
  subst q
  rfl

private theorem resetRowMap_localPullMetric
    (M : ∀ i, DifferentialGeometry.SmoothRiemannianMetric ThreeModel (J i).terminalRegularOpen)
    (hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i))
    (n p : ℕ) (hp : offset n ≤ p) :
    localPullMetric (M p) (resetRowMap J psi n p hp)
        (resetRowMap_isLocalDiffeomorph J psi hpsi n p hp) =
      localPullMetric (M (p - offset n + offset n)) (psi n (p - offset n))
        (hpsi n (p - offset n)) :=
  reindexResetMap_localPullMetric J M (Nat.sub_add_cancel hp) _ _ _

private theorem growing_reset_maps_row_inner
    (M : ∀ i, DifferentialGeometry.SmoothRiemannianMetric ThreeModel (J i).terminalRegularOpen)
    (hδ : ∀ n, 0 < δ n) (hmono : Antitone δ)
    (hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i))
    (rho k : ℕ → ℕ) (hbound : ∀ i, ∀ n ≤ i, offset n ≤ rho (k i))
    (f : ∀ i, neckBuffer (δ i) → (J (rho (k i))).terminalRegularOpen)
    (hrow : ∀ n i (hni : n ≤ i), f i ∘ TopologicalSpace.Opens.inclusion
        (neckBuffer_le_of_le (hδ i) (hmono hni)) =
      resetRowMap J psi n (rho (k i)) (hbound i n hni))
    (n i : ℕ) (hni : n ≤ i) (z : neckBuffer (δ n))
    (v w : TangentSpace NeckCylinderModel z) :
    (localPullMetric (M (rho (k i) - offset n + offset n))
      (psi n (rho (k i) - offset n)) (hpsi n (rho (k i) - offset n))).inner z v w =
      (M (rho (k i))).inner
        (f i (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) (hmono hni)) z))
        (mfderiv NeckCylinderModel ThreeModel
          (f i ∘ TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) (hmono hni))) z v)
        (mfderiv NeckCylinderModel ThreeModel
          (f i ∘ TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) (hmono hni))) z w) := by
  rw [← resetRowMap_localPullMetric J psi M hpsi n (rho (k i)) (hbound i n hni)]
  change _ = (M (rho (k i))).inner
    ((f i ∘ TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) (hmono hni))) z) _ _
  rw [hrow n i hni,localPullMetric_inner]

variable {first last : ∀ i, Fin ((H i).eventCount + 1)}
  (hf : ∀ i, first i ≤ reset i) (hl : ∀ i, reset i ≤ last i)
  {s : ℕ → ℝ}
  (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (G i).TerminalLimitMetric)
  {eps : ℕ → ℝ} {order : ℕ → ℕ}
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))

private theorem reindexResetMap_point {d : ℝ} (hd : d < 1) {p q : ℕ} (hpq : p = q)
    (hprec : eps p ≤ d) (hprecq : eps q ≤ d)
    (f : neckBuffer d → (J p).terminalRegularOpen)
    (hpoint : ∀ z : neckBuffer d, ∃ A : BackwardPointTrace (H p) (first p) (last p)
        ((hf p).trans (hl p)) (((O p).monoDelta hprec hd).chart z).val,
      (f z).val = A.point (reset p) (hf p) (hl p)) :
    ∀ z : neckBuffer d, ∃ A : BackwardPointTrace (H q) (first q) (last q)
        ((hf q).trans (hl q)) (((O q).monoDelta hprecq hd).chart z).val,
      (reindexResetMap J hpq f z).val = A.point (reset q) (hf q) (hl q) := by
  subst q
  exact hpoint

private theorem resetRowMap_point (hδ1 : ∀ n, δ n < 1)
    (hprecision : ∀ n i, eps (i + offset n) ≤ δ n)
    (hpoint : ∀ n i (z : neckBuffer (δ n)),
      ∃ A : BackwardPointTrace (H (i + offset n)) (first (i + offset n)) (last (i + offset n))
          ((hf (i + offset n)).trans (hl (i + offset n)))
          (((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z).val,
        (psi n i z).val = A.point (reset (i + offset n)) (hf (i + offset n)) (hl (i + offset n)))
    (n p : ℕ) (hp : offset n ≤ p) (hprec : eps p ≤ δ n) :
    ∀ z : neckBuffer (δ n),
      ∃ A : BackwardPointTrace (H p) (first p) (last p) ((hf p).trans (hl p))
          (((O p).monoDelta hprec (hδ1 n)).chart z).val,
        (resetRowMap J psi n p hp z).val = A.point (reset p) (hf p) (hl p) :=
  reindexResetMap_point J hf hl G L O (hδ1 n) (Nat.sub_add_cancel hp)
    (hprecision n (p - offset n)) hprec _ (hpoint n (p - offset n))

private theorem resetRowMap_eq_on_overlap (hδ1 : ∀ n, δ n < 1)
    (hprecision : ∀ n i, eps (i + offset n) ≤ δ n)
    (hpoint : ∀ n i (z : neckBuffer (δ n)),
      ∃ A : BackwardPointTrace (H (i + offset n)) (first (i + offset n)) (last (i + offset n))
          ((hf (i + offset n)).trans (hl (i + offset n)))
          (((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z).val,
        (psi n i z).val = A.point (reset (i + offset n)) (hf (i + offset n)) (hl (i + offset n)))
    (m n p : ℕ) (hm : offset m ≤ p) (hn : offset n ≤ p)
    (z : neckBuffer (δ m)) (w : neckBuffer (δ n)) (hzw : z.val = w.val) :
    resetRowMap J psi m p hm z = resetRowMap J psi n p hn w := by
  have hpm : eps p ≤ δ m := by simpa only [Nat.sub_add_cancel hm] using hprecision m (p - offset m)
  have hpn : eps p ≤ δ n := by simpa only [Nat.sub_add_cancel hn] using hprecision n (p - offset n)
  exact actual_reset_maps_eq_of_same_selected_chart (H p) (first p) (reset p) (last p)
    (hf p) (hl p) (G p) (L p) (J p) (O p) hpm hpn (hδ1 m) (hδ1 n)
    (resetRowMap J psi m p hm) (resetRowMap J psi n p hn)
    (resetRowMap_point J psi hf hl G L O hδ1 hprecision hpoint m p hm hpm)
    (resetRowMap_point J psi hf hl G L O hδ1 hprecision hpoint n p hn hpn) z w hzw

private theorem exists_growing_actual_reset_maps
    (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1) (hmono : Antitone δ)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (hprecision : ∀ n i, eps (i + offset n) ≤ δ n)
    (hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i))
    (hinj : ∀ n i, Function.Injective (psi n i))
    (hpoint : ∀ n i (z : neckBuffer (δ n)),
      ∃ A : BackwardPointTrace (H (i + offset n)) (first (i + offset n)) (last (i + offset n))
          ((hf (i + offset n)).trans (hl (i + offset n)))
          (((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z).val,
        (psi n i z).val = A.point (reset (i + offset n)) (hf (i + offset n)) (hl (i + offset n)))
    (rho : ℕ → ℕ) (hrho : StrictMono rho) (mark : Sphere 2) :
    ∃ (k : ℕ → ℕ) (_ : StrictMono k)
      (hbound : ∀ i, ∀ n ≤ i, offset n ≤ rho (k i))
      (f : ∀ i, neckBuffer (δ i) → (J (rho (k i))).terminalRegularOpen),
      (∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f i)) ∧
      (∀ i, Function.Injective (f i)) ∧
      (∀ i, HEq (f i) (psi i (rho (k i) - offset i))) ∧
      (∀ n i (hni : n ≤ i), f i ∘ TopologicalSpace.Opens.inclusion
          (neckBuffer_le_of_le (hδ i) (hmono hni)) =
        resetRowMap J psi n (rho (k i)) (hbound i n hni)) ∧
      (∀ i, f i ⟨(mark,0),by constructor <;> dsimp <;> linarith [inv_pos.mpr (hδ i)]⟩ =
        resetRowMap J psi 0 (rho (k i)) (hbound i 0 (Nat.zero_le i))
          ⟨(mark,0),by constructor <;> dsimp <;> linarith [inv_pos.mpr (hδ 0)]⟩) ∧
      (∀ K : Set NeckCylinder, IsCompact K → ∀ᶠ i in atTop, K ⊆ neckBuffer (δ i)) := by
  obtain ⟨k,hk,hbound⟩ := exists_strict_subsequence_above_offsets rho offset hrho
  let f := fun i => resetRowMap J psi i (rho (k i)) (hbound i i le_rfl)
  refine ⟨k,hk,hbound,f,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact resetRowMap_isLocalDiffeomorph J psi hpsi i (rho (k i)) _
  · intro i
    exact resetRowMap_injective J psi hinj i (rho (k i)) _
  · intro i
    exact resetRowMap_heq J psi i (rho (k i)) _
  · intro n i hni
    funext z
    exact resetRowMap_eq_on_overlap J psi hf hl G L O hδ1 hprecision hpoint
      i n (rho (k i)) (hbound i i le_rfl) (hbound i n hni) _ z rfl
  · intro i
    exact resetRowMap_eq_on_overlap J psi hf hl G L O hδ1 hprecision hpoint
      i 0 (rho (k i)) (hbound i i le_rfl) (hbound i 0 (Nat.zero_le i)) _ _ rfl
  · exact eventually_subset_growing_neckBuffer hδ hδlim

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)


variable {H : ℕ → ObservedHistory.{u}} {reset : ∀ i, Fin ((H i).eventCount + 1)}
  {τ : ℕ → ℝ} (J : ∀ i, ((H i).stage (reset i)).IncomingSlab ((H i).time (reset i)) (τ i))
  {δ : ℕ → ℝ} {offset : ℕ → ℕ}
  (psi : ∀ n i, neckBuffer (δ n) → (J (i + offset n)).terminalRegularOpen)
variable {first last : ∀ i, Fin ((H i).eventCount + 1)}
  (hf : ∀ i, first i ≤ reset i) (hl : ∀ i, reset i ≤ last i)
  {s : ℕ → ℝ}
  (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (G i).TerminalLimitMetric)
  {eps : ℕ → ℝ} {order : ℕ → ℕ}
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))

private theorem exists_canonical_actual_reset_convergence
    (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1) (hmono : Antitone δ)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (hprecision : ∀ n i, eps (i + offset n) ≤ δ n)
    (hpsi : ∀ n i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi n i))
    (hinj : ∀ n i, Function.Injective (psi n i))
    (hpoint : ∀ n i (z : neckBuffer (δ n)),
      ∃ A : BackwardPointTrace (H (i + offset n)) (first (i + offset n)) (last (i + offset n))
          ((hf (i + offset n)).trans (hl (i + offset n)))
          (((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z).val,
        (psi n i z).val = A.point (reset (i + offset n)) (hf (i + offset n)) (hl (i + offset n)))
    (Lτ : ∀ i, (J i).TerminalLimitMetric)
    (rho : ℕ → ℕ) (hrho : StrictMono rho) (mark : Sphere 2)
    {v : ℝ} (hv : v ≤ 0)
    (hconv : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => localPullMetric
        (scaleMetric (O (rho i - offset n + offset n)).scale (O (rho i - offset n + offset n)).scale_pos
          (Lτ (rho i - offset n + offset n)).metric)
        (psi n (rho i - offset n)) (hpsi n (rho i - offset n)))
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (hmark : e (mark, 0) = P.basepoint) :
    ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ (x : ∀ i, (J (rho (k i))).terminalRegularOpen),
      let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := { obj := fun i => {
        M := (J (rho (k i))).terminalRegularOpen
        basepoint := x i
        metric := scaleMetric (O (rho (k i))).scale (O (rho (k i))).scale_pos (Lτ (rho (k i))).metric } }
      let Pτ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := { P with
        metric := Diffeomorph.pullbackMetricCross (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm }
      RiemannianMetricComplete Pτ.metric ∧
        (∀ y : Pτ.M, 0 < metricScalarAt Pτ.metric y ∧ metricScalarAt Pτ.metric y ≤ 1) ∧
        Diffeomorph.pullbackMetricCross Pτ.metric e =
          (scaleMetric (2 * (1 - v)) (mul_pos (by norm_num) (by linarith))
            (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod (euclideanMetric (E := ℝ)) ∧
        ∃ (ell : ℕ → ℕ), StrictMono ell ∧
          ∃ maps : PointedRiemannianConvergenceMaps X Pτ ell,
            (∀ i (z : neckBuffer (δ (ell i))),
              ∃ hprec : eps (rho (k (ell i))) ≤ δ (ell i),
              ∃ A : BackwardPointTrace (H (rho (k (ell i)))) (first (rho (k (ell i))))
                  (last (rho (k (ell i)))) ((hf (rho (k (ell i)))).trans (hl (rho (k (ell i)))))
                  (((O (rho (k (ell i)))).monoDelta hprec (hδ1 (ell i))).chart z).val,
                (maps.map i (e z)).val = A.point (reset (rho (k (ell i))))
                  (hf (rho (k (ell i)))) (hl (rho (k (ell i))))) ∧
            ∃ C : MetricConvergenceData maps,
              ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i := by
  classical
  obtain ⟨k,hk,hbound,f,hfLocal,hfInj,hfHEq,hrow,hbase,hexhaust⟩ :=
    exists_growing_actual_reset_maps J psi hf hl G L O hδ hδ1 hmono hδlim hprecision hpsi hinj hpoint rho hrho mark
  let x := fun i => f i ⟨(mark, 0),by constructor <;> dsimp <;> linarith [inv_pos.mpr (hδ i)]⟩
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := { obj := fun i => {
    M := (J (rho (k i))).terminalRegularOpen
    basepoint := x i
    metric := scaleMetric (O (rho (k i))).scale (O (rho (k i))).scale_pos (Lτ (rho (k i))).metric } }
  let Gm := fun n i => localPullMetric
    (scaleMetric (O (rho (k i) - offset n + offset n)).scale
      (O (rho (k i) - offset n + offset n)).scale_pos (Lτ (rho (k i) - offset n + offset n)).metric)
    (psi n (rho (k i) - offset n)) (hpsi n (rho (k i) - offset n))
  have hp : ∀ i, e.symm P.basepoint ∈ neckBuffer (δ i) := by
    intro i
    rw [← hmark,e.symm_apply_apply]
    constructor <;> dsimp <;> linarith [inv_pos.mpr (hδ i)]
  have hmetric : ∀ n, ∀ᶠ i in atTop, ∃ hni : δ i ≤ δ n,
      ∀ (z : neckBuffer (δ n)) (a b : TangentSpace NeckCylinderModel z),
        (Gm n i).inner z a b = (X.obj i).metric.inner
          (f i (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) hni) z))
          (mfderiv NeckCylinderModel ThreeModel
            (fun w : neckBuffer (δ n) => f i (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) hni) w)) z a)
          (mfderiv NeckCylinderModel ThreeModel
            (fun w : neckBuffer (δ n) => f i (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (hδ i) hni) w)) z b) := by
    intro n
    filter_upwards [eventually_ge_atTop n] with i hni
    refine ⟨hmono hni,?_⟩
    exact growing_reset_maps_row_inner J psi (fun p => scaleMetric (O p).scale (O p).scale_pos (Lτ p).metric)
      hδ hmono hpsi rho k hbound f hrow n i hni
  have hprod := exists_pointed_convergence_of_cylindrical_local_pullbacks (X := X) P e hv id δ hδ hδlim hp f hfLocal hfInj
    (fun i => by dsimp [x]; congr 1; apply Subtype.ext; exact e.symm_apply_eq.mpr hmark.symm)
    δ hδ hδlim Gm (fun n => (hconv n).comp_subseq hk) hmetric
  obtain ⟨hc, hscalar, hscalarle, hproduct, ell, hell, maps, hmaps, _, _, _, C, hC⟩ := hprod
  refine ⟨k, hk, x, hc, ?_, hproduct, ell, hell, maps, ?_, C, hC⟩
  · intro y
    exact ⟨by rw [hscalar]; exact inv_pos.mpr (by linarith), hscalarle y⟩
  · intro i z
    have hprec : eps (rho (k (ell i))) ≤ δ (ell i) := by
      simpa only [Nat.sub_add_cancel (hbound (ell i) (ell i) le_rfl)] using
        hprecision (ell i) (rho (k (ell i)) - offset (ell i))
    obtain ⟨A, hA⟩ := resetRowMap_point J psi hf hl G L O hδ1 hprecision hpoint
      (ell i) (rho (k (ell i))) (hbound (ell i) (ell i) le_rfl) hprec z
    refine ⟨hprec, A, ?_⟩
    rw [hmaps]
    have hfrow := congrFun (hrow (ell i) (ell i) le_rfl) z
    have hinc : TopologicalSpace.Opens.inclusion
        (neckBuffer_le_of_le (hδ (ell i)) (hmono (le_refl (ell i)))) z = z := rfl
    simp only [Function.comp_apply, hinc] at hfrow
    exact (congrArg Subtype.val hfrow).trans hA

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


private local instance (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

variable (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (offset : ℕ → ℕ) (hoffset : offset 0 = 0)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  (Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen)
  (htrace : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (last (j + offset n))
    (hle (j + offset n)) x.val))
  (hinside : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (T : ℝ) (hT : 0 < T)
  (hstart : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (C : ℝ≥0) (qPhysical : ℕ → ℝ)
  (hq : ∀ᶠ i in atTop, qPhysical i / (O i).scale ≤ 1)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      qPhysical i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    qPhysical i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)

include hT hδ hδlim heps horder hprecision htrace hinside hstart hinit hderivative hfinal
  hphi hpinching hpinchFinal hq hscale hoffset in
private theorem exists_actual_reset_pointed_convergence
    (hmono : Antitone δ) (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (mark : Sphere 2)
    (hmark : e (mark, 0) = P.basepoint)
    {a b : ℝ} (ha : -T < a) (hab : a < b) (hb : b < 0) :
    ∃ (v : ℝ) (hv : v ∈ Ioo a b),
      ∃ (reset : ∀ i, Fin ((H i).eventCount + 1))
        (hf : ∀ i, first i ≤ reset i) (hl : ∀ i, reset i ≤ last i)
        (Jτ : ∀ i, ((H i).stage (reset i)).IncomingSlab ((H i).time (reset i)) (s i + v / (O i).scale))
        (Lτ : ∀ i, (Jτ i).TerminalLimitMetric),
        (∀ i, (Jτ i).flow.base.metric ((H i).time (reset i)) = (H i).initialMetric (reset i)) ∧
        (∀ i, (Jτ i).terminalRegularRegion = univ) ∧
        (∀ i, (Lτ i).metric = ((Jτ i).flow.base.metric (s i + v / (O i).scale)).restrictOpen (Jτ i).terminalRegularOpen) ∧
        (∀ i, ((reset i = last i ∧ s i + v / (O i).scale < s i ∧
          ∀ t, HEq ((Jτ i).flow.base.metric t) ((J i).flow.base.metric t)) ∨
          ∃ j : Fin (H i).eventCount, reset i = j.castSucc ∧ j.succ ≤ last i ∧
            s i + v / (O i).scale < (H i).time j.succ ∧
            ∀ t, HEq ((Jτ i).flow.base.metric t) ((H i).stageMetric j.castSucc t))) ∧
        ∃ rho : ℕ → ℕ, StrictMono rho ∧
        ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ (x : ∀ i, (Jτ (rho (k i))).terminalRegularOpen),
      let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := { obj := fun i => {
        M := (Jτ (rho (k i))).terminalRegularOpen
        basepoint := x i
        metric := scaleMetric (O (rho (k i))).scale (O (rho (k i))).scale_pos (Lτ (rho (k i))).metric } }
      let Pτ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := { P with
        metric := Diffeomorph.pullbackMetricCross (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm }
      RiemannianMetricComplete Pτ.metric ∧
        (∀ y : Pτ.M, 0 < metricScalarAt Pτ.metric y ∧ metricScalarAt Pτ.metric y ≤ 1) ∧
        Diffeomorph.pullbackMetricCross Pτ.metric e =
          (scaleMetric (2 * (1 - v)) (mul_pos (by norm_num) (sub_pos.mpr ((hv.2.trans hb).trans (by norm_num : (0 : ℝ) < 1))))
            (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod (euclideanMetric (E := ℝ)) ∧
        ∃ (ell : ℕ → ℕ), StrictMono ell ∧
          ∃ maps : PointedRiemannianConvergenceMaps X Pτ ell,
            (∀ i (z : neckBuffer (δ (ell i))),
              ∃ hprec : eps (rho (k (ell i))) ≤ δ (ell i),
              ∃ A : BackwardPointTrace (H (rho (k (ell i)))) (first (rho (k (ell i))))
                  (last (rho (k (ell i)))) ((hf (rho (k (ell i)))).trans (hl (rho (k (ell i)))))
                  (((O (rho (k (ell i)))).monoDelta hprec (hδ1 (ell i))).chart z).val,
                (maps.map i (e z)).val = A.point (reset (rho (k (ell i))))
                  (hf (rho (k (ell i)))) (hl (rho (k (ell i))))) ∧
            ∃ C : MetricConvergenceData maps,
              ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i := by
  obtain ⟨v, hv, reset, hf, hl, Jτ, Lτ, hinitτ, hregτ, htermτ, hsourceτ,
    psi, hpsi, hinj, hpoint, rho, hrho, hconv⟩ :=
    exists_actual_cylindrical_source_reset H last first hle s J L hinit δ hδ hδ1 hδlim
      eps order O heps horder offset hoffset hprecision Footprint htrace hinside T hT hstart
      C qPhysical hq hscale hderivative hfinal hphi hpinching hpinchFinal ha hab hb
  have hv0 : v ≤ 0 := (hv.2.trans hb).le
  have hpoint' : ∀ n i (z : neckBuffer (δ n)),
      ∃ A : BackwardPointTrace (H (i + offset n)) (first (i + offset n)) (last (i + offset n))
          ((hf (i + offset n)).trans (hl (i + offset n)))
          (((O (i + offset n)).monoDelta (hprecision n i) (hδ1 n)).chart z).val,
        (psi n i z).val = A.point (reset (i + offset n)) (hf (i + offset n)) (hl (i + offset n)) :=
    hpoint
  obtain ⟨k, hk, x, hc, hscalar, hproduct, ell, hell, maps, hmap, conv, hcanonical⟩ :=
    exists_canonical_actual_reset_convergence Jτ psi hf hl J L O hδ hδ1 hmono hδlim
      hprecision hpsi hinj hpoint' Lτ rho hrho mark hv0 hconv P e hmark
  exact ⟨v, hv, reset, hf, hl, Jτ, Lτ, hinitτ, hregτ, htermτ, hsourceτ, rho, hrho,
    k, hk, x, hc, hscalar, hproduct, ell, hell, maps, hmap, conv, hcanonical⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}} {first middle last : Fin (H.eventCount + 1)}
  {hmid : middle ≤ last} {endpoint : (H.stage last).Carrier}

private def concat (A : BackwardPointTrace H middle last hmid endpoint) (hfirst : first ≤ middle)
    (B : BackwardPointTrace H first middle hfirst (A.point middle le_rfl hmid)) :
    BackwardPointTrace H first last (hfirst.trans hmid) endpoint where
  point j hf hl := if hj : j ≤ middle then B.point j hf hj
    else A.point j (le_of_lt (lt_of_not_ge hj)) hl
  endpoint_eq := by
    split_ifs with hle
    · have he : middle = last := le_antisymm hmid hle
      subst middle
      exact B.endpoint_eq.trans A.endpoint_eq
    · exact A.endpoint_eq
  crossing i hf hl := by
    by_cases hi : i.succ ≤ middle
    · simpa only [dite_eq_left hi,dite_eq_left (i.castSucc_lt_succ.le.trans hi)] using B.crossing i hf hi
    · have hmiddle : middle ≤ i.castSucc := by
        have hh : middle < i.succ := lt_of_not_ge hi
        exact Nat.le_of_lt_succ hh
      by_cases he : i.castSucc = middle
      · have hpoint : B.point i.castSucc hf (he.le) = A.point i.castSucc hmiddle
            (i.castSucc_lt_succ.le.trans hl) := by
          subst middle
          exact B.endpoint_eq
        simpa only [dite_eq_left he.le,dite_eq_right hi,hpoint] using A.crossing i hmiddle hl
      · have hi' : ¬ i.castSucc ≤ middle := not_le.mpr (lt_of_le_of_ne hmiddle (Ne.symm he))
        simpa only [dite_eq_right hi,dite_eq_right hi'] using A.crossing i hmiddle hl

@[simp] theorem concat_point_before
    (A : BackwardPointTrace H middle last hmid endpoint) (hfirst : first ≤ middle)
    (B : BackwardPointTrace H first middle hfirst (A.point middle le_rfl hmid))
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hj : j ≤ middle) :
    (A.concat hfirst B).point j hf (hj.trans hmid) = B.point j hf hj := by
  simp only [concat,dite_eq_left hj]

@[simp] theorem concat_point_after
    (A : BackwardPointTrace H middle last hmid endpoint) (hfirst : first ≤ middle)
    (B : BackwardPointTrace H first middle hfirst (A.point middle le_rfl hmid))
    (j : Fin (H.eventCount + 1)) (hj : middle ≤ j) (hl : j ≤ last) :
    (A.concat hfirst B).point j (hfirst.trans hj) hl = A.point j hj hl := by
  by_cases he : j = middle
  · subst j
    simp only [concat,dite_eq_left le_rfl,B.endpoint_eq]
  · have hn : ¬ j ≤ middle := not_le.mpr (lt_of_le_of_ne hj (Ne.symm he))
    simp only [concat,dite_eq_right hn]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩


private theorem exists_uniform_trace_extension_from_cylindrical_reset
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i),
    Tendsto Q atTop atTop → ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i => {
          M := (G i).terminalRegularOpen
          basepoint := x i
          metric := scaleMetric (Q i) (hQ i) (L i).metric } };
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (subseq : ℕ → ℕ), StrictMono subseq →
    ∀ (Phi : PointedRiemannianConvergenceMaps X P subseq) (Cm : MetricConvergenceData Phi),
    (∀ i, Cm.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) →
    ∀ (e : NeckCylinder ≃ₘ⟮NeckCylinderModel,ThreeModel⟯ P.M) (v : ℝ), v ≤ 0 →
    Diffeomorph.pullbackMetricCross P.metric e = PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v →
    ∀ (K : Set P.M), IsCompact K →
    ∀ (later : ∀ i, Fin ((H i).eventCount + 1)) (hlater : ∀ i, last i ≤ later i)
      (endpoint : ∀ i, P.M → ((H i).stage (later i)).Carrier),
    (∀ᶠ i in atTop, ∀ y ∈ K,
      ∃ A : BackwardPointTrace (H (subseq i)) (last (subseq i)) (later (subseq i))
          (hlater (subseq i)) (endpoint (subseq i) y),
        (Phi.map i y).val = A.point (last (subseq i)) le_rfl (hlater (subseq i))) →
    ∀ (originalTime : ℕ → ℝ) (T : ℝ),
    (∀ i, s i = originalTime i + v / Q i) →
    v < -T + θ / 2 →
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ᶠ i in atTop, ∃ first : Fin ((H (subseq i)).eventCount + 1),
      ∃ hle : first ≤ later (subseq i),
        (H (subseq i)).time first < originalTime (subseq i) - (T + θ/2) / Q (subseq i) ∧
        ∀ y ∈ K, Nonempty (BackwardPointTrace (H (subseq i)) first (later (subseq i)) hle
          (endpoint (subseq i) y)) := by
  obtain ⟨theta,eps0,delta0,htheta,heps0,hdelta0,hwindow⟩ :=
    exists_uniform_backward_trace_window_of_cylindrical_limit D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨theta,eps0,delta0,htheta,heps0,hdelta0,?_⟩
  intro H last s G L hinit x Q hQ hQlim a ha hsa X P subseq hsubseq Phi Cm hcanonical e v hv he K hK
    later hlater endpoint hpoint originalTime T htime hvT parameters records hfixed hlower
    hdelta haccuracy hmargin hm q0 hq0 hderiv hfinal hcap center precision order d w Jbig hJbig hzero hmark
  have htraces := hwindow H last s G L hinit x Q hQ hQlim ha hsa P subseq hsubseq Phi Cm hcanonical
    e v hv he K hK parameters records hfixed hlower hdelta haccuracy hmargin hm q0 hq0 hderiv hfinal hcap
    center precision order d w Jbig hJbig hzero hmark
  filter_upwards [hpoint,htraces] with i hpointi htracesi
  obtain ⟨first,hle,hfirst,_,hbefore⟩ := htracesi
  have hgain : s (subseq i) - theta / Q (subseq i) <
      originalTime (subseq i) - (T + theta/2) / Q (subseq i) := by
    rw [htime]
    have hdiv := div_lt_div_of_pos_right hvT (hQ (subseq i))
    have heq : (-T + theta/2) / Q (subseq i) - theta / Q (subseq i) =
        -(T + theta/2) / Q (subseq i) := by ring
    rw [neg_div] at heq
    linarith
  refine ⟨first,hle.trans (hlater (subseq i)),hfirst.trans_lt hgain,?_⟩
  intro y hy
  obtain ⟨A,hA⟩ := hpointi y hy
  obtain ⟨B⟩ := hbefore y hy
  have B' : BackwardPointTrace (H (subseq i)) first (last (subseq i)) hle
      (A.point (last (subseq i)) le_rfl (hlater (subseq i))) := by
    rw [← hA]
    exact B
  exact ⟨A.concat hle B'⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false

open Set
open scoped NNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem scalar_deriv_bound_at_actual_source_reset
    (H : ObservedHistory.{u}) (reset last : Fin (H.eventCount + 1))
    {s τ : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (J : (H.stage reset).IncomingSlab (H.time reset) τ)
    (hsource :
      (reset = last ∧ τ < s ∧ ∀ t, HEq (J.flow.base.metric t) (G.flow.base.metric t)) ∨
        ∃ j : Fin H.eventCount, reset = j.castSucc ∧ j.succ ≤ last ∧ τ < H.time j.succ ∧
          ∀ t, HEq (J.flow.base.metric t) (H.stageMetric j.castSucc t))
    {q : ℝ} {C : ℝ≥0}
    (hderiv : ∀ (j : Fin H.eventCount), j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) :
    ∀ y, ∀ t ∈ Ioo (H.time reset) τ, q < J.flow.scalar t y →
      |derivWithin (fun v => J.flow.scalar v y) (Iic t) t| ≤ C * J.flow.scalar t y ^ 2 := by
  rcases hsource with ⟨rfl,hτ,hmetric⟩ | ⟨j,rfl,hjl,hτ,hmetric⟩
  · have hscalar : J.flow.scalar = G.flow.scalar := by
      funext t y
      change metricScalarAt (J.flow.base.metric t) y = metricScalarAt (G.flow.base.metric t) y
      rw [eq_of_heq (hmetric t)]
    intro y t ht hhigh
    rw [hscalar] at hhigh ⊢
    exact hfinal y t ⟨ht.1,ht.2.trans hτ⟩ hhigh
  · have hscalar : J.flow.scalar = (H.event j).incoming.flow.scalar := by
      funext t y
      change metricScalarAt (J.flow.base.metric t) y =
        metricScalarAt ((H.event j).incoming.flow.base.metric t) y
      have hm := eq_of_heq (hmetric t)
      simpa only [stageMetric,Fin.lastCases_castSucc] using congrArg (fun g => metricScalarAt g y) hm
    intro y t ht hhigh
    rw [hscalar] at hhigh ⊢
    exact hderiv j hjl y t ⟨ht.1,ht.2.trans hτ⟩ hhigh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

section
open Set

private theorem reset_time_bounds_of_scale_lower_bound
    {a s T v Q : ℝ} (ha : 0 < a) (hsa : a ≤ s) (hQ : 0 < Q)
    (hscale : 2 * T / a ≤ Q) (hv : v ∈ Ioo (-T) 0) :
    a / 2 < s + v / Q ∧ s + v / Q < s := by
  have htime : T / Q ≤ a / 2 := by
    apply (div_le_iff₀ hQ).mpr
    have hh := (div_le_iff₀ ha).mp hscale
    nlinarith
  have hlo := div_lt_div_of_pos_right hv.1 hQ
  rw [neg_div] at hlo
  have hhi := div_neg_of_neg_of_pos hv.2 hQ
  constructor <;> linarith
end

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private def selectedChartExtension
    {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    {G : (H.stage last).IncomingSlab (H.time last) s} {L : G.TerminalLimitMetric}
    {eps : ℝ} {k : ℕ} (O : NormalizedNeck L.metric eps k) (z : NeckCylinder) :
    G.terminalRegularOpen := by
  classical
  exact if hz : z ∈ neckBuffer eps then O.chart ⟨z,hz⟩ else O.center

private theorem selectedChartExtension_apply
    {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    {G : (H.stage last).IncomingSlab (H.time last) s} {L : G.TerminalLimitMetric}
    {eps : ℝ} {k : ℕ} (O : NormalizedNeck L.metric eps k) (z : neckBuffer eps) :
    selectedChartExtension O z = O.chart z := by
  simp only [selectedChartExtension,dite_eq_left z.property]

private theorem actual_reset_point_trace_on_compact_of_selected_chart
    (H : ℕ → ObservedHistory.{u}) (first reset last : ∀ i, Fin ((H i).eventCount + 1))
    (hf : ∀ i, first i ≤ reset i) (hl : ∀ i, reset i ≤ last i)
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric) (eps δ : ℕ → ℝ) (order : ℕ → ℕ)
    (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
    (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1) (hδlim : Tendsto δ atTop (𝓝 0))
    (resetMap : ∀ i, NeckCylinder → ((H i).stage (reset i)).Carrier)
    (hpoint : ∀ i (z : neckBuffer (δ i)), ∃ hprec : eps i ≤ δ i,
      ∃ A : BackwardPointTrace (H i) (first i) (last i) ((hf i).trans (hl i))
          (((O i).monoDelta hprec (hδ1 i)).chart z).val,
        resetMap i z.val = A.point (reset i) (hf i) (hl i))
    (K : Set NeckCylinder) (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∀ z ∈ K,
      ∃ A : BackwardPointTrace (H i) (first i) (last i) ((hf i).trans (hl i))
          (selectedChartExtension (O i) z).val,
        resetMap i z = A.point (reset i) (hf i) (hl i) := by
  obtain ⟨B,hB⟩ := hK.bddAbove_image continuous_snd.abs.continuousOn
  have hsmall := hδlim.eventually (Iio_mem_nhds (show 0 < (max B 0 + 2)⁻¹ by positivity))
  filter_upwards [hsmall] with i hi z hz
  have habs : |z.2| ≤ max B 0 := (hB ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  have hrad : max B 0 + 2 < (δ i)⁻¹ := lt_inv_of_lt_inv₀ (hδ i) hi
  have hzin : z ∈ neckBuffer (δ i) := by
    have hh := abs_le.mp habs
    constructor <;> linarith [hh.1,hh.2]
  obtain ⟨hprec,A,hA⟩ := hpoint i ⟨z,hzin⟩
  have he : selectedChartExtension (O i) z = ((O i).monoDelta hprec (hδ1 i)).chart ⟨z,hzin⟩ := by
    rw [selectedChartExtension,dite_eq_left (neckBuffer_le_of_le (O i).delta_pos hprec hzin)]
    rfl
  rw [he]
  exact ⟨A,hA⟩

private theorem selected_chart_image_trace_of_extended_points
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    {eps : ℝ} {k : ℕ} (O : NormalizedNeck L.metric eps k) (R : ℝ)
    (htrace : ∀ z ∈ (univ ×ˢ Icc (-R) R : Set NeckCylinder),
      Nonempty (BackwardPointTrace H first last hle (selectedChartExtension O z).val)) :
    ∀ x ∈ O.chart '' {z | -R ≤ z.val.2 ∧ z.val.2 ≤ R},
      Nonempty (BackwardPointTrace H first last hle x.val) := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := hx
  simpa only [selectedChartExtension_apply] using htrace z.val ⟨mem_univ _,hz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


private local instance (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

variable (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (hinit : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
  (hprecision0 : ∀ i, eps i ≤ (1 / 2 : ℝ))
  (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
  (hfit0 : ∀ i, (3 : ℝ) ≤ radius i)
  (htrace : ∀ i x, x ∈ (O i).chart ''
    {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
    Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) x.val))
  (T : ℝ) (hT : 0 < T)
  (hstart : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (C : ℝ≥0) (qPhysical : ℕ → ℝ)
  (hq : ∀ᶠ i in atTop, qPhysical i / (O i).scale ≤ 1)
  (hscale : Tendsto (fun i => (O i).scale) atTop atTop)
  (hderivative : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      qPhysical i < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (hfinal : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    qPhysical i < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hpinching : ∀ i (j : Fin (H i).eventCount), first i ≤ j.castSucc → j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)


include heps hprecision0 hradius hfit0 in
private theorem exists_neck_restrictions_in_growing_source_slabs :
    ∃ (δ : ℕ → ℝ) (hδ1 : ∀ n, δ n < 1),
      δ 0 = (1 / 2 : ℝ) ∧ (∀ n, 0 < δ n) ∧ Antitone δ ∧
        Tendsto δ atTop (𝓝 0) ∧
      ∃ (offset : ℕ → ℕ)
        (hprecision : ∀ n j, eps (j + offset n) ≤ δ n),
        offset 0 = 0 ∧
        (∀ n j, (δ n)⁻¹ + 1 ≤ radius (j + offset n)) ∧
        ∀ n j,
          range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
            interior ((O (j + offset n)).chart ''
              {z | -(radius (j + offset n)) ≤ z.val.2 ∧
                z.val.2 ≤ radius (j + offset n)}) := by
  let d : ℕ → ℝ := fun n => (1 / 2 : ℝ) / ((n : ℝ) + 1)
  have hd : ∀ n, 0 < d n := by
    intro n
    dsimp [d]
    positivity
  have hmono : Antitone d := by
    intro m n hmn
    dsimp [d]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hd0 : d 0 = (1 / 2 : ℝ) := by
    norm_num [d]
  have hd1 : ∀ n, d n < 1 := by
    intro n
    calc
      d n ≤ d 0 := hmono (Nat.zero_le n)
      _ < 1 := by norm_num [d]
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    exact hh.const_div_atTop (1 / 2 : ℝ)
  have htail (n : ℕ) : ∃ m : ℕ, ∀ j, m ≤ j →
      eps j ≤ d n ∧ (d n)⁻¹ + 1 ≤ radius j := by
    have hp : ∀ᶠ j in atTop, eps j ≤ d n :=
      (heps.eventually (Iio_mem_nhds (hd n))).mono fun j hj => hj.le
    have hr : ∀ᶠ j in atTop, (d n)⁻¹ + 1 ≤ radius j :=
      hradius.eventually (eventually_ge_atTop _)
    exact eventually_atTop.1 (hp.and hr)
  choose tail htail using htail
  let offset : ℕ → ℕ := fun n => Nat.casesOn n 0 (fun m => tail (m + 1))
  have hoffset : offset 0 = 0 := rfl
  have hprecision : ∀ n j, eps (j + offset n) ≤ d n := by
    intro n j
    cases n with
    | zero => simpa [offset, d] using hprecision0 j
    | succ n => exact (htail (n + 1) (j + offset (n + 1))
        (by dsimp [offset]; omega)).1
  have hfit : ∀ n j, (d n)⁻¹ + 1 ≤ radius (j + offset n) := by
    intro n j
    cases n with
    | zero =>
      norm_num [offset, d]
      exact hfit0 j
    | succ n => exact (htail (n + 1) (j + offset (n + 1))
        (by dsimp [offset]; omega)).2
  let Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen :=
    fun n j => (O (j + offset n)).chart ''
      {z | -(radius (j + offset n)) ≤ z.val.2 ∧
        z.val.2 ≤ radius (j + offset n)}
  have hinside : ∀ n j,
      range ((O (j + offset n)).monoDelta (hprecision n j) (hd1 n)).chart ⊆
        interior (Footprint n j) := by
    intro n j x hx
    obtain ⟨z, rfl⟩ := hx
    dsimp [Footprint]
    rw [(O (j + offset n)).interior_image_closedSlab]
    refine ⟨TopologicalSpace.Opens.inclusion
      (neckBuffer_le_of_le (O (j + offset n)).delta_pos (hprecision n j)) z, ?_, rfl⟩
    constructor <;> dsimp <;> linarith [z.property.1, z.property.2, hfit n j]
  exact ⟨d, hd1, hd0, hd, hmono, hdlim, offset, hprecision, hoffset, hfit, hinside⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


private local instance (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace J.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel J.terminalRegularOpen.isOpen)

private theorem exists_selected_neck_trace_extension
    (D r tol a₀ : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (_ : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (δ : ℕ → ℝ) (_ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n < 1)
  (_ : Tendsto δ atTop (𝓝 0))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (_ : Tendsto eps atTop (𝓝 0)) (_ : Tendsto order atTop atTop)
  (offset : ℕ → ℕ) (_ : offset 0 = 0)
  (hprecision : ∀ n j, eps (j + offset n) ≤ δ n)
  (Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen)
  (_ : ∀ n j x, x ∈ Footprint n j → Nonempty (BackwardPointTrace
    (H (j + offset n)) (first (j + offset n)) (last (j + offset n))
    (hle (j + offset n)) x.val))
  (_ : ∀ n j, range ((O (j + offset n)).monoDelta (hprecision n j) (hδ1 n)).chart ⊆
    interior (Footprint n j))
  (T : ℝ) (_ : 0 < T)
  (_ : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (q0 : ℝ) (_ : 0 < q0)
  (_ : Tendsto (fun i => (O i).scale) atTop atTop)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q0 < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (_ : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    q0 < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (_ : Perelman.AdmissiblePinchingFunction phi)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (_ : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)
    (_ : Antitone δ)
    {a : ℝ} (_ : 0 < a) (_ : ∀ i, a ≤ s i)
    (_ : ∀ i, 2 * T / a ≤ (O i).scale)
    (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (mark : Sphere 2)
    (_ : e (mark, 0) = P.basepoint),
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈tol⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∃ ind : ℕ → ℕ, StrictMono ind ∧
      ∀ K : Set NeckCylinder, IsCompact K → ∀ᶠ i in atTop,
        ∃ earlier : Fin ((H (ind i)).eventCount + 1), ∃ he : earlier ≤ last (ind i),
          (H (ind i)).time earlier < s (ind i) - (T + θ / 2) / (O (ind i)).scale ∧
          ∀ z ∈ K, Nonempty (BackwardPointTrace (H (ind i)) earlier (last (ind i)) he
            (selectedChartExtension (O (ind i)) z).val) := by
  obtain ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, hwindow⟩ :=
    exists_uniform_trace_extension_from_cylindrical_reset D r tol a₀ C ha₀ htol htolsmall hr hfit
  refine ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, ?_⟩
  intro H last first hle s J L hinit δ hδ hδ1 hδlim eps order O heps horder offset hoffset
    hprecision Footprint htrace hinside T hT hstart q0 hq0 hscale hderivative hfinal
    phi hphi hpinching hpinchFinal hmono a ha hsa hQLower P e mark hmark
    parameters records hfixed hlower hdelta haccuracy hmargin hm hcap
    center precision capOrder d w Jbig hJbig hzero hcapmark
  have hq : ∀ᶠ i in atTop, q0 / (O i).scale ≤ 1 := by
    filter_upwards [hscale.eventually_ge_atTop q0] with i hi
    exact (div_le_one (O i).scale_pos).mpr hi
  let η := min T θ
  have hη : 0 < η := lt_min hT hθ
  have hηT : η ≤ T := min_le_left _ _
  have hηθ : η ≤ θ := min_le_right _ _
  have hleft : -T < -T + η / 4 := by linarith
  have hmid : -T + η / 4 < -T + η / 2 := by linarith
  have hright : -T + η / 2 < 0 := by linarith
  obtain ⟨v, hv, reset, hf, hl, Jτ, Lτ, hinitτ, hregτ, htermτ, hsourceτ,
    rho, hrho, k, hk, x, hc, hscalar, hproduct, ell, hell, maps, hmap, Cm, hcanonical⟩ :=
    exists_actual_reset_pointed_convergence H last first hle s J L hinit δ hδ hδ1 hδlim
      eps order O heps horder offset hoffset hprecision Footprint htrace hinside T hT hstart
      C (fun _ => q0) hq hscale
      (fun i j _ hj => hderivative i j hj) hfinal hphi
      (fun i j _ hj => hpinching i j hj) hpinchFinal hmono P e mark hmark hleft hmid hright
  let p := rho ∘ k
  have hp : StrictMono p := hrho.comp hk
  let τ := fun i => s i + v / (O i).scale
  have hv0 : v < 0 := hv.2.trans hright
  have hvT : -T < v := hleft.trans hv.1
  have hvGain : v < -T + θ / 2 := hv.2.trans_le (by linarith)
  have hτa (i) : a / 2 ≤ τ i :=
    (reset_time_bounds_of_scale_lower_bound ha (hsa i) (O i).scale_pos (hQLower i) ⟨hvT,hv0⟩).1.le
  let Pτ : PointedRiemannianManifold.{u, 0, 0} ThreeModel := { P with
    metric := Diffeomorph.pullbackMetricCross (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm }
  have he : Diffeomorph.pullbackMetricCross Pτ.metric e =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl
  have hfinalτ (i) : ∀ y, ∀ t ∈ Ioo ((H i).time (reset i)) (τ i),
      q0 < (Jτ i).flow.scalar t y →
      |derivWithin (fun v => (Jτ i).flow.scalar v y) (Iic t) t| ≤ C * (Jτ i).flow.scalar t y ^ 2 :=
    ObservedHistory.scalar_deriv_bound_at_actual_source_reset (H i) (reset i) (last i)
      (J i) (Jτ i) (hsourceτ i) (hderivative i) (hfinal i)
  refine ⟨p ∘ ell, hp.comp hell, ?_⟩
  intro K hK
  have hpointK := actual_reset_point_trace_on_compact_of_selected_chart
    (fun i => H (p (ell i))) (fun i => first (p (ell i))) (fun i => reset (p (ell i)))
    (fun i => last (p (ell i))) (fun i => hf (p (ell i))) (fun i => hl (p (ell i)))
    (fun i => s (p (ell i))) (fun i => J (p (ell i))) (fun i => L (p (ell i)))
    (fun i => eps (p (ell i))) (fun i => δ (ell i)) (fun i => order (p (ell i)))
    (fun i => O (p (ell i))) (fun i => hδ (ell i)) (fun i => hδ1 (ell i))
    (hδlim.comp hell.tendsto_atTop) (fun i z => (maps.map i (e z)).val) hmap K hK
  have hpointP : ∀ᶠ i in atTop, ∀ y ∈ e '' K,
      ∃ A : BackwardPointTrace (H (p (ell i))) (reset (p (ell i))) (last (p (ell i)))
          (hl (p (ell i))) (selectedChartExtension (O (p (ell i))) (e.symm y)).val,
        (maps.map i y).val = A.point (reset (p (ell i))) le_rfl (hl (p (ell i))) := by
    filter_upwards [hpointK] with i hi y hy
    obtain ⟨z,hz,rfl⟩ := hy
    obtain ⟨A,hA⟩ := hi z hz
    have hA' : ∃ A' : BackwardPointTrace (H (p (ell i))) (reset (p (ell i))) (last (p (ell i)))
        (hl (p (ell i))) (selectedChartExtension (O (p (ell i))) z).val,
        (maps.map i (e z)).val = A'.point (reset (p (ell i))) le_rfl (hl (p (ell i))) :=
      ⟨A.restrictFirst (hf _) (hl _), hA⟩
    have hzEq : e.symm (e z) = z := e.symm_apply_apply z
    exact hzEq.symm ▸ hA'
  have hdeltaτ : ∀ᶠ i in atTop, ∀ j : Fin (H (p i)).eventCount, j.succ ≤ reset (p i) →
      ∀ b, (records (p i) j).delta b ≤ δ₀ :=
    (hp.tendsto_atTop.eventually hdelta).mono fun i hi j hj => hi j (hj.trans (hl (p i)))
  have hresult := hwindow (fun i => H (p i)) (fun i => reset (p i)) (fun i => τ (p i))
    (fun i => Jτ (p i)) (fun i => Lτ (p i)) (fun i => hinitτ (p i)) x
    (fun i => (O (p i)).scale) (fun i => (O (p i)).scale_pos)
    (hscale.comp hp.tendsto_atTop) (half_pos ha) (fun i => hτa (p i))
    Pτ ell hell maps Cm hcanonical e v hv0.le he (e '' K) (hK.image e.continuous)
    (fun i => last (p i)) (fun i => hl (p i))
    (fun i y => (selectedChartExtension (O (p i)) (e.symm y)).val) hpointP
    (fun i => s (p i)) T (fun _ => rfl) hvGain
    (fun i => parameters (p i)) (fun i => records (p i))
    (fun i => hfixed (p i)) (fun i => hlower (p i)) hdeltaτ
    (hp.tendsto_atTop.eventually haccuracy) (fun i => hmargin (p i)) (fun i => hm (p i)) q0 hq0
    (fun i j hj => hderivative (p i) j (hj.trans (hl (p i))))
    (fun i => hfinalτ (p i)) (fun i j hj => hcap (p i) j (hj.trans (hl (p i))))
    (fun i j hj => center (p i) j (hj.trans (hl (p i))))
    (fun i j hj => precision (p i) j (hj.trans (hl (p i))))
    (fun i j hj => capOrder (p i) j (hj.trans (hl (p i))))
    (fun i j hj => d (p i) j (hj.trans (hl (p i))))
    (fun i j hj => w (p i) j (hj.trans (hl (p i))))
    (fun i j hj => Jbig (p i) j (hj.trans (hl (p i))))
    (fun i j hj => hJbig (p i) j (hj.trans (hl (p i))))
    (fun i j hj => hzero (p i) j (hj.trans (hl (p i))))
    (fun i j hj => hcapmark (p i) j (hj.trans (hl (p i))))
  filter_upwards [hresult] with i hi
  obtain ⟨earlier, hle', htime, htraces⟩ := hi
  refine ⟨earlier, hle', htime, ?_⟩
  intro z hz
  have hh := htraces (e z) ⟨z,hz,rfl⟩
  simpa only [e.symm_apply_apply, Function.comp_apply] using! hh


private theorem exists_selected_neck_trace_extension_of_growing_source_traces
    (D r tol a₀ : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ θ ε₀ δ₀ : ℝ, 0 < θ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
  (first : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, first i ≤ last i)
  (s : ℕ → ℝ)
  (J : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
  (L : ∀ i, (J i).TerminalLimitMetric)
  (_ : ∀ i, (J i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
  (eps : ℕ → ℝ) (order : ℕ → ℕ)
  (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
  (_ : Tendsto eps atTop (𝓝 0)) (_ : Tendsto order atTop atTop)
  (_ : ∀ i, eps i ≤ (1 / 2 : ℝ))
  (radius : ℕ → ℝ) (_ : Tendsto radius atTop atTop) (_ : ∀ i, (3 : ℝ) ≤ radius i)
  (_ : ∀ i x, x ∈ (O i).chart '' {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
    Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) x.val))
  (T : ℝ) (_ : 0 < T)
  (_ : ∀ i, (H i).time (first i) ≤ s i - T / (O i).scale)
  (q0 : ℝ) (_ : 0 < q0)
  (_ : Tendsto (fun i => (O i).scale) atTop atTop)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    ∀ x : ((H i).stage j.castSucc).Carrier,
    ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q0 < ((H i).event j).incoming.flow.scalar t x →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t x ^ 2)
  (_ : ∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
    q0 < (J i).flow.scalar t x →
    |derivWithin (fun v => (J i).flow.scalar v x) (Iic t) t| ≤ C * (J i).flow.scalar t x ^ 2)
  {phi : ℝ → ℝ} (_ : Perelman.AdmissiblePinchingFunction phi)
  (_ : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
    Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi)
  (_ : ∀ i, Perelman.PhiAlmostNonnegative (J i).flow
    (Ico ((H i).time (last i)) (s i)) phi)
    {a : ℝ} (_ : 0 < a) (_ : ∀ i, a ≤ s i)
    (_ : ∀ i, 2 * T / a ≤ (O i).scale)
    (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (mark : Sphere 2)
    (_ : e (mark, 0) = P.basepoint),
    ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈tol⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∃ ind : ℕ → ℕ, StrictMono ind ∧
      ∀ K : Set NeckCylinder, IsCompact K → ∀ᶠ i in atTop,
        ∃ earlier : Fin ((H (ind i)).eventCount + 1), ∃ he : earlier ≤ last (ind i),
          (H (ind i)).time earlier < s (ind i) - (T + θ / 2) / (O (ind i)).scale ∧
          ∀ z ∈ K, Nonempty (BackwardPointTrace (H (ind i)) earlier (last (ind i)) he
            (selectedChartExtension (O (ind i)) z).val) := by
  obtain ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, hstep⟩ :=
    exists_selected_neck_trace_extension D r tol a₀ C ha₀ htol htolsmall hr hfit
  refine ⟨θ, ε₀, δ₀, hθ, hε₀, hδ₀, ?_⟩
  intro H last first hle s J L hinit eps order O heps horder hprecision0 radius hradius hfit0
    htrace T hT hstart q0 hq0 hscale hderivative hfinal phi hphi hpinching hpinchFinal
    a ha hsa hQLower P e mark hmark parameters records hfixed hlower hdelta haccuracy hmargin hm hcap
    center precision capOrder d w Jbig hJbig hzero hcapmark
  obtain ⟨δ, hδ1, _, hδ, hmono, hδlim, offset, hprecision, hoffset, _, hinside⟩ :=
    exists_neck_restrictions_in_growing_source_slabs H last s J L eps order O heps
      hprecision0 radius hradius hfit0
  let Footprint : ∀ n j, Set (J (j + offset n)).terminalRegularOpen :=
    fun n j => (O (j + offset n)).chart ''
      {z | -(radius (j + offset n)) ≤ z.val.2 ∧ z.val.2 ≤ radius (j + offset n)}
  exact hstep H last first hle s J L hinit δ hδ hδ1 hδlim eps order O heps horder offset hoffset
    hprecision Footprint (fun n j => htrace (j + offset n)) hinside T hT hstart
    q0 hq0 hscale hderivative hfinal hphi hpinching hpinchFinal hmono ha hsa hQLower
    P e mark hmark parameters records hfixed hlower hdelta haccuracy hmargin hm hcap
    center precision capOrder d w Jbig hJbig hzero hcapmark

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
open Set Filter
open scoped Topology

private theorem exists_strict_subsequence_satisfying_finite_prefix
    (P : ℕ → ℕ → Prop) (hP : ∀ n, ∀ᶠ i in atTop, P n i) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i n, n ≤ i → P n (f i) := by
  classical
  have hfinite (i : ℕ) : ∀ᶠ j in atTop, ∀ n ≤ i, P n j := by
    have hh := (Finset.range (i+1)).finite_toSet.eventually_all.mpr
      (fun n _ => hP n)
    simpa only [Finset.mem_coe,Finset.mem_range,Nat.lt_succ_iff] using hh
  choose bound hbound using fun i => eventually_atTop.mp (hfinite i)
  let f : ℕ → ℕ := fun i => i + (Finset.range (i+1)).sup bound
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hm : (Finset.range (i+1)).sup bound ≤ (Finset.range (i+1+1)).sup bound :=
      Finset.sup_mono (Finset.range_mono (by omega))
    dsimp [f]
    omega
  refine ⟨f,hf,?_⟩
  intro i n hn
  have hi : bound i ≤ f i := by
    have hh : bound i ≤ (Finset.range (i+1)).sup bound :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    dsimp [f]
    omega
  exact hbound i (f i) hi n hn
end

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem exists_growing_selected_neck_trace_subsequence
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (eps : ℕ → ℝ) (order : ℕ → ℕ)
    (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
    (heps : Tendsto eps atTop (𝓝 0)) (horder : Tendsto order atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (T : ℝ)
    (htrace : ∀ n : ℕ, ∀ᶠ i in atTop,
      ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
        (H i).time first ≤ s i - T / (O i).scale ∧
        ∀ x ∈ (O i).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
          Nonempty (BackwardPointTrace (H i) first (last i) hle x.val)) :
    ∃ (f : ℕ → ℕ) (_ : StrictMono f)
      (first : ∀ i, Fin ((H (f i)).eventCount + 1))
      (hle : ∀ i, first i ≤ last (f i)) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop ∧
      (∀ i, 0 < radius i) ∧
      (∀ i, δ⁻¹ + 1 ≤ radius i) ∧
      (∀ i, radius i < (eps (f i))⁻¹) ∧
      (∀ i, (univ ×ˢ Icc (-(radius i)) (radius i) : Set NeckCylinder) ⊆
        neckBuffer (eps (f i))) ∧
      (∀ i, ((O (f i)).chart ''
        {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i}).Nonempty) ∧
      (∀ i, eps (f i) ≤ δ) ∧
      (∀ i, k ≤ order (f i)) ∧
      (∀ i, (H (f i)).time (first i) ≤ s (f i) - T / (O (f i)).scale) ∧
      (∀ i x, x ∈ (O (f i)).chart ''
          {z | -(radius i) ≤ z.val.2 ∧ z.val.2 ≤ radius i} →
        Nonempty (BackwardPointTrace (H (f i)) (first i) (last (f i)) (hle i) x.val)) := by
  let B : ℕ := ⌈δ⁻¹ + 1⌉₊ + 1
  have hB : δ⁻¹ + 1 ≤ (B : ℝ) := by
    have hh : δ⁻¹ + 1 ≤ (⌈δ⁻¹ + 1⌉₊ : ℝ) := Nat.le_ceil _
    dsimp [B]
    push_cast
    linarith
  have hBpos : 0 < (B : ℝ) := by dsimp [B]; positivity
  let radius : ℕ → ℝ := fun i => (i : ℝ) + B
  let P : ℕ → ℕ → Prop := fun n i =>
    radius n < (eps i)⁻¹ ∧ eps i ≤ δ ∧ k ≤ order i ∧
      ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
        (H i).time first ≤ s i - T / (O i).scale ∧
        ∀ x ∈ (O i).chart '' {z | -(radius n) ≤ z.val.2 ∧ z.val.2 ≤ radius n},
          Nonempty (BackwardPointTrace (H i) first (last i) hle x.val)
  have hP : ∀ n, ∀ᶠ i in atTop, P n i := by
    intro n
    have hr : 0 < radius n := by dsimp [radius]; positivity
    have hsmall := heps.eventually (Iio_mem_nhds (inv_pos.mpr hr))
    have hprec := heps.eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall,hprec,horder.eventually (eventually_ge_atTop k),htrace (n+B)]
      with i hsmalli hpreci hki htr
    refine ⟨?_,hpreci.le,hki,?_⟩
    · exact lt_inv_of_lt_inv₀ (O i).delta_pos hsmalli
    · simpa only [Nat.cast_add] using htr
  obtain ⟨f,hf,hfP⟩ := exists_strict_subsequence_satisfying_finite_prefix P hP
  have hi := fun i => hfP i i le_rfl
  choose first hle hstart htr using fun i => (hi i).2.2.2
  refine ⟨f,hf,first,hle,radius,?_,?_,?_,?_,?_,?_,?_,?_,hstart,htr⟩
  · exact tendsto_atTop_add_const_right _ (B : ℝ) tendsto_natCast_atTop_atTop
  · intro i
    dsimp [radius]
    positivity
  · intro i
    exact hB.trans (by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i])
  · exact fun i => (hi i).1
  · intro i z hz
    constructor <;> linarith [hz.2.1,hz.2.2,(hi i).1]
  · intro i
    let z : neckBuffer (eps (f i)) :=
      ⟨((O (f i)).sphereMark,0),by
        constructor <;> dsimp <;> linarith [inv_pos.mpr (O (f i)).delta_pos]⟩
    refine ⟨(O (f i)).chart z,z,?_,rfl⟩
    change -(radius i) ≤ (0 : ℝ) ∧ 0 ≤ radius i
    have hr : 0 < radius i := by dsimp [radius]; positivity
    exact ⟨by linarith,hr.le⟩
  · exact fun i => (hi i).2.1
  · exact fun i => (hi i).2.2.1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem selected_neck_slab_traces_mono_depth
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric) (eps : ℕ → ℝ) (order : ℕ → ℕ)
    (O : ∀ i, NormalizedNeck (L i).metric (eps i) (order i))
    {T U : ℝ} (hTU : T ≤ U)
    (htrace : ∀ n : ℕ, ∀ᶠ i in atTop,
      ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
        (H i).time first ≤ s i - U / (O i).scale ∧
        ∀ x ∈ (O i).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
          Nonempty (BackwardPointTrace (H i) first (last i) hle x.val)) :
    ∀ n : ℕ, ∀ᶠ i in atTop,
      ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
        (H i).time first ≤ s i - T / (O i).scale ∧
        ∀ x ∈ (O i).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
          Nonempty (BackwardPointTrace (H i) first (last i) hle x.val) := by
  intro n
  filter_upwards [htrace n] with i hi
  obtain ⟨first,hle,htime,hpoints⟩ := hi
  refine ⟨first,hle,htime.trans ?_,hpoints⟩
  exact sub_le_sub_left (div_le_div_of_nonneg_right hTU (O i).scale_pos.le) _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩


private theorem exists_selected_neck_traces_at_arbitrary_depth_of_cylindrical_reference
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
    ∀ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (_ : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) (_ : Sphere 2),
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (last i)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ target : ℝ, ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ n : ℕ, ∀ᶠ i in atTop,
        ∃ (first : Fin ((H (f i)).eventCount + 1)) (hle : first ≤ last (f i)),
          (H (f i)).time first ≤ s (f i) - target / (O (f i)).scale ∧
          ∀ x ∈ (O (f i)).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
            Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val) := by
  classical
  obtain ⟨theta0,eps0,delta0,htheta0,heps0,hdelta0,hbase⟩ :=
    exists_uniform_initial_trace_window_of_selected_necks D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  obtain ⟨theta1,eps1,delta1,htheta1,heps1,hdelta1,hstep⟩ :=
    exists_selected_neck_trace_extension_of_growing_source_traces D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨min eps0 eps1,min delta0 delta1,lt_min heps0 heps1,lt_min hdelta0 hdelta1,?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa P e mark
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark target
  let Pmark := P.repoint (e (mark,0))
  have hmarkP : e (mark,0) = Pmark.basepoint := rfl
  let depth := fun n : ℕ => theta0 + (n : ℝ) * (theta1 / 2)
  have hdepth : ∀ n, 0 < depth n := by intro n; dsimp [depth]; positivity
  let Traces := fun (T : ℝ) (f : ℕ → ℕ) => ∀ n : ℕ, ∀ᶠ i in atTop,
    ∃ (first : Fin ((H (f i)).eventCount + 1)) (hle : first ≤ last (f i)),
      (H (f i)).time first ≤ s (f i) - T / (O (f i)).scale ∧
      ∀ x ∈ (O (f i)).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
        Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val)
  have hdelta0' := hdelta.mono fun i hi j hj b => (hi j hj b).trans (min_le_left _ _)
  have haccuracy0 := haccuracy.mono fun i hi => hi.trans (min_le_left _ _)
  obtain ⟨f0,hf0,hfirst⟩ := hbase H last s G L hinit eta m O heta hm hscale ha hsa Pmark e mark
  have hbaseP : Traces (depth 0) f0 := by
    intro n
    have hh := hfirst (univ ×ˢ Icc (-(n : ℝ)) n) (isCompact_univ.prod isCompact_Icc)
      parameters records hfixed hlower hdelta0' haccuracy0 hmargin horder q0 hq0 hderiv hfinal hcap
      center precision order d w Jbig hJbig hzero hmark
    filter_upwards [hh] with i hi
    obtain ⟨first,hle,htime,_,hpoints⟩ := hi
    refine ⟨first,hle,?_,?_⟩
    · simpa [depth] using htime
    · simpa only [mem_prod,mem_univ,true_and,mem_Icc] using hpoints
  have hind : ∀ n : ℕ, ∃ f : ℕ → ℕ, StrictMono f ∧ Traces (depth n) f := by
    intro n
    induction n with
    | zero => exact ⟨f0,hf0,hbaseP⟩
    | succ n ih =>
      obtain ⟨f,hf,htraces⟩ := ih
      have hscaleF := hscale.comp hf.tendsto_atTop
      obtain ⟨N,hN⟩ := eventually_atTop.mp (hscaleF.eventually_ge_atTop (2 * depth n / a))
      let f' := fun i => f (i+N)
      have hf' : StrictMono f' := hf.comp (strictMono_nat_of_lt_succ fun _ => by omega)
      have htraces' : Traces (depth n) f' := by
        intro j
        exact (tendsto_add_atTop_nat N).eventually (htraces j)
      obtain ⟨g,hg,first,hle,radius,hradius,_,hfit0,_,_,_,hprec,hord,hstart,htrace⟩ :=
        exists_growing_selected_neck_trace_subsequence
          (fun i => H (f' i)) (fun i => last (f' i)) (fun i => s (f' i))
          (fun i => G (f' i)) (fun i => L (f' i)) (fun i => eta (f' i)) (fun i => m (f' i))
          (fun i => O (f' i)) (heta.comp hf'.tendsto_atTop) (hm.comp hf'.tendsto_atTop)
          (by norm_num : 0 < (1/2 : ℝ)) 0 (depth n) htraces'
      let p := f' ∘ g
      have hp : StrictMono p := hf'.comp hg
      have hfit0' : ∀ i, 3 ≤ radius i := by norm_num at hfit0 ⊢; exact hfit0
      have hQLower : ∀ i, 2 * depth n / a ≤ (O (p i)).scale := by
        intro i
        exact hN (g i + N) (by omega)
      have hdelta1' := (hp.tendsto_atTop.eventually hdelta).mono
        fun i hi j hj b => (hi j hj b).trans (min_le_right _ _)
      have haccuracy1 := (hp.tendsto_atTop.eventually haccuracy).mono
        fun i hi => hi.trans (min_le_right _ _)
      obtain ⟨ell,hell,hext⟩ := hstep
        (fun i => H (p i)) (fun i => last (p i)) first hle (fun i => s (p i))
        (fun i => G (p i)) (fun i => L (p i)) (fun i => hinit (p i))
        (fun i => eta (p i)) (fun i => m (p i)) (fun i => O (p i))
        (heta.comp hp.tendsto_atTop) (hm.comp hp.tendsto_atTop) hprec radius hradius hfit0'
        htrace (depth n) (hdepth n) hstart q0 hq0 (hscale.comp hp.tendsto_atTop)
        (fun i => hderiv (p i)) (fun i => hfinal (p i)) hphi
        (fun i => hpinch (p i)) (fun i => hpinchFinal (p i)) ha (fun i => hsa (p i)) hQLower
        Pmark e mark hmarkP (fun i => parameters (p i)) (fun i => records (p i))
        (fun i => hfixed (p i)) (fun i => hlower (p i)) hdelta1' haccuracy1
        (fun i => hmargin (p i)) (fun i => horder (p i))
        (fun i => hcap (p i)) (fun i => center (p i)) (fun i => precision (p i))
        (fun i => order (p i)) (fun i => d (p i)) (fun i => w (p i))
        (fun i => Jbig (p i)) (fun i => hJbig (p i)) (fun i => hzero (p i)) (fun i => hmark (p i))
      refine ⟨p ∘ ell,hp.comp hell,?_⟩
      intro j
      have hh := hext (univ ×ˢ Icc (-(j : ℝ)) j) (isCompact_univ.prod isCompact_Icc)
      filter_upwards [hh] with i hi
      obtain ⟨earlier,hle',htime,hpoints⟩ := hi
      refine ⟨earlier,hle',?_,?_⟩
      · have hdepthsucc : depth (n+1) = depth n + theta1/2 := by dsimp [depth]; push_cast; ring
        simpa only [hdepthsucc,Function.comp_apply] using htime.le
      · exact selected_chart_image_trace_of_extended_points (H (p (ell i))) earlier
          (last (p (ell i))) hle' (G (p (ell i))) (L (p (ell i))) (O (p (ell i))) j hpoints
  obtain ⟨n,hn⟩ := exists_nat_gt ((target - theta0) / (theta1/2))
  have htarget : target ≤ depth n := by
    have hh := (div_lt_iff₀ (by positivity : 0 < theta1/2)).mp hn
    dsimp [depth]
    linarith
  obtain ⟨f,hf,htraces⟩ := hind n
  refine ⟨f,hf,?_⟩
  exact selected_neck_slab_traces_mono_depth (fun i => H (f i)) (fun i => last (f i))
    (fun i => s (f i)) (fun i => G (f i)) (fun i => L (f i))
    (fun i => eta (f i)) (fun i => m (f i)) (fun i => O (f i)) htarget htraces

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem exists_threeModel_cylinder :
    ∃ P : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
      Nonempty (NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M) := by
  let Q := PDE.RicciFlow.cylinderReferenceCopy.Q
  let _ : ChartedSpace ThreeSpace (ULift.{u} Q) :=
    DifferentialGeometry.Topology.uliftChartedSpace ThreeSpace Q
  let _ : IsManifold ThreeModel ∞ (ULift.{u} Q) :=
    DifferentialGeometry.Topology.isManifold_ulift ThreeModel Q
  let d : Q ≃ₘ⟮ThreeModel, ThreeModel⟯ ULift.{u} Q :=
    DifferentialGeometry.Topology.uliftDiffeomorph ThreeModel Q
  let P : PointedRiemannianManifold.{u, 0, 0} ThreeModel := {
    M := ULift.{u} Q
    basepoint := d PDE.RicciFlow.cylinderPointedReference.basepoint
    metric := Diffeomorph.pullbackMetricCross PDE.RicciFlow.cylinderReferenceMetric d.symm }
  exact ⟨P,⟨PDE.RicciFlow.cylinderReferenceCopy.equiv.trans d⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
set_option autoImplicit false

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩


theorem exists_selected_neck_traces_at_arbitrary_depth
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (last i)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ target : ℝ, ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ n : ℕ, ∀ᶠ i in atTop,
        ∃ (first : Fin ((H (f i)).eventCount + 1)) (hle : first ≤ last (f i)),
          (H (f i)).time first ≤ s (f i) - target / (O (f i)).scale ∧
          ∀ x ∈ (O (f i)).chart '' {z | -(n : ℝ) ≤ z.val.2 ∧ z.val.2 ≤ (n : ℝ)},
            Nonempty (BackwardPointTrace (H (f i)) first (last (f i)) hle x.val) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, h⟩ :=
    exists_selected_neck_traces_at_arbitrary_depth_of_cylindrical_reference
      D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa
  obtain ⟨P, ⟨e⟩⟩ := exists_threeModel_cylinder.{u}
  exact h H last s G L hinit eta m O heta hm hscale ha hsa P e spherePoint

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_prospective_neck_convergence_of_improving_necks
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric),
    (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (L i).metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (s i), q₀ < (G i).flow.scalar t y →
      |derivWithin (fun v => (G i).flow.scalar v y) (Iic t) t| ≤ Ctime * (G i).flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (G i).flow
      (Ico ((H i).time (last i)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ last i)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ last i →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
    ∃ (first : ∀ i, Fin ((H (ind i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (ind i))
      (hprecision : ∀ i, eta (ind i) ≤ δ) (horder : ∀ i, k ≤ m (ind i)),
    let N := fun i => ((O (ind i)).monoDelta (hprecision i) hδ1).lowerOrder (horder i)
    (∀ i, (H (ind i)).time (first i) ≤ s (ind i) - 2 / (O (ind i)).scale) ∧
    ∃ (K : ∀ i, Set (G (ind i)).terminalRegularOpen)
      (Phi : ∀ i, neckBuffer δ → (H (ind i)).backwardSurvivorIncomingFootprint
        (first i) (last (ind i)) (hle i) (G (ind i)) (K i))
      (hPhi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (Phi i))
      (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H (ind i)).backwardSurvivorIncomingFootprint (first i) (last (ind i)) (hle i) (G (ind i)) (K i)))
      (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed (-2) 0 (by norm_num)))
      (rho : ℕ → ℕ),
      StrictMono rho ∧
      (∀ i, (H (ind i)).backwardSurvivorIncomingFootprintMap
        (first i) (last (ind i)) (hle i) (G (ind i)) (K i) ∘ Phi i = (N i).chart) ∧
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, (S i).base.metric 0 = (N i).normalizedMetric) ∧
      (∀ i t, (S i).base.metric t = localPullMetric
        (scaleMetric (N i).scale (N i).scale_pos (gflow i (s (ind i) + t / (N i).scale)))
        (Phi i) (hPhi i)) ∧
      (∀ i (j : Fin (H (ind i)).eventCount) (hf : first i ≤ j.castSucc) (hl : j.succ ≤ last (ind i)),
        ∀ t ∈ Icc ((H (ind i)).time j.castSucc) ((H (ind i)).time j.succ),
          gflow i t = (((H (ind i)).backwardSurvivorSlabMetric (first i) (last (ind i))
            (hle i) j hf hl t).restrictOpen
            ((H (ind i)).backwardSurvivorIncomingDomain (first i) (last (ind i)) (hle i) (G (ind i)))).restrictOpen
              ((H (ind i)).backwardSurvivorIncomingFootprint (first i) (last (ind i)) (hle i) (G (ind i)) (K i))) ∧
      (∀ i t, t ∈ Icc ((H (ind i)).time (last (ind i))) (s (ind i)) →
        gflow i t = ((H (ind i)).backwardSurvivorIncomingMetric
          (first i) (last (ind i)) (hle i) (G (ind i)) (L (ind i)) t).restrictOpen
          ((H (ind i)).backwardSurvivorIncomingFootprint (first i) (last (ind i)) (hle i) (G (ind i)) (K i))) ∧
      (∀ A : Set (neckBuffer δ), IsCompact A → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(3 / 2 : ℝ)) 0,
          metricDerivNormSupOn A p ((S (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer δ)) (roundCylinderMetric.restrictOpen (neckBuffer δ)) < η) ∧
      ∀ᶠ i in atTop,
        ∃ Z : (b : ℕ) → Icc (-1 : ℝ) 0 →
          Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
          (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
            metricTensorField ((S (rho i)).base.metric t) x -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                  (neckBuffer δ)) x) (Icc (-1 : ℝ) 0) v.1) ∧
          ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
            ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
              let g := (shrinkingCylinderMetric
                ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
              Real.sqrt (normSq0S g x (r + 2)
                (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hiter⟩ :=
    exists_selected_neck_traces_at_arbitrary_depth D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H last s G L hinit eta m O heta hm hscale a ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark δ hδ hδ1 k
  obtain ⟨f, hf, htraces⟩ := hiter H last s G L hinit eta m O heta hm hscale ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
    hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark 2
  obtain ⟨g, hg, first, hle, radius, hradius, _, hfit0, _, _, _, hprec, hord, hstart, htrace⟩ :=
    exists_growing_selected_neck_trace_subsequence
      (fun i => H (f i)) (fun i => last (f i)) (fun i => s (f i))
      (fun i => G (f i)) (fun i => L (f i))
      (fun i => eta (f i)) (fun i => m (f i)) (fun i => O (f i))
      (heta.comp hf.tendsto_atTop) (hm.comp hf.tendsto_atTop) hδ k 2 htraces
  let ind := f ∘ g
  have hind : StrictMono ind := hf.comp hg
  let N := fun i => ((O (ind i)).monoDelta (hprec i) hδ1).lowerOrder (hord i)
  refine ⟨ind, hind, first, hle, hprec, hord, hstart, ?_⟩
  exact exists_prospective_neck_convergence_of_growing_source_traces
    (fun i => H (ind i)) (fun i => last (ind i)) first hle
    (fun i => s (ind i)) (fun i => G (ind i)) (fun i => L (ind i)) (fun i => hinit (ind i))
    hδ hδ1 (fun i => eta (ind i)) (fun i => m (ind i)) (fun i => O (ind i))
    (heta.comp hind.tendsto_atTop) (hm.comp hind.tendsto_atTop) hprec hord N (fun _ => rfl)
    radius hradius hfit0 htrace hstart Ctime q0 (hscale.comp hind.tendsto_atTop)
    (fun i j _ hj => hderiv (ind i) j hj) (fun i => hfinal (ind i)) hphi
    (fun i j _ hj => hpinch (ind i) j hj) (fun i => hpinchFinal (ind i))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q (H.time (Fin.last H.eventCount)) s) :
    SigmaCompactSpace E.incoming.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

private theorem exists_subsequence_selected_neck_append_backward
    (D r eps a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (s : ℕ → ℝ) (Qstage : ℕ → OrientedThreeStage.{u})
      (E : ∀ i, MetricCutCapEvent ((H i).stage (Fin.last (H i).eventCount)) (Qstage i)
        ((H i).time (Fin.last (H i).eventCount)) (s i)),
    ∀ hinit : ∀ i, (E i).incoming.flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount),
    ∀ (eta : ℕ → ℝ) (m : ℕ → ℕ)
      (O : ∀ i, NormalizedNeck (E i).terminal.metric (eta i) (m i)),
    Tendsto eta atTop (𝓝 0) → Tendsto m atTop atTop →
    Tendsto (fun i => (O i).scale) atTop atTop →
    ∀ {a : ℝ}, 0 < a → (∀ i, a ≤ s i) →
      ∀ (parameters : ℕ → CutoffParameters)
      (records : ∀ i, ∀ j : Fin (H i).eventCount, GeometricCutoffRecord (H i) j (parameters i)),
    (∀ i y, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ y) →
    (∀ i y, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) y) →
    (∀ᶠ i in atTop, ∀ j : Fin (H i).eventCount, j.succ ≤ Fin.last (H i).eventCount → ∀ b, (records i j).delta b ≤ δ₀) →
    (∀ᶠ i in atTop, (parameters i).modelAccuracy ≤ ε₀) →
    (∀ i, D + 1 ≤ (parameters i).modelRadius) →
    (∀ i, ⌈eps⁻¹⌉₊ + 2 ≤ (parameters i).modelOrder) →
    ∀ (q₀ : ℝ), 0 < q₀ →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).event j).incoming.flow.scalar t y ^ 2) →
    (∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (s i), q₀ < (E i).incoming.flow.scalar t y →
      |derivWithin (fun v => (E i).incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * (E i).incoming.flow.scalar t y ^ 2) →
    ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      Perelman.PhiAlmostNonnegative ((H i).event j).incoming.flow
        (Ico ((H i).time j.castSucc) ((H i).time j.succ)) phi) →
    (∀ i, Perelman.PhiAlmostNonnegative (E i).incoming.flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (s i)) phi) →
    (∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤ metricScalarAt ((records i j).static b).witness.metric
          (((records i j).static b).witness.cap z)) →
    ∀ (center : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ((H i).event j).incoming.terminalRegularOpen)
      (precision : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        normalizedDatum ((H i).event j).terminal.metric (center i j hj b) (precision i j hj b) (order i j hj b))
      (w : ∀ i (j : Fin (H i).eventCount) (hj : j.succ ≤ Fin.last (H i).eventCount)
        (b : ((H i).event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d i j hj b)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos (parameters i).modelRadius
          (parameters i).modelOrder (parameters i).modelAccuracy)
      (Jbig : ∀ i (j : Fin (H i).eventCount), j.succ ≤ Fin.last (H i).eventCount →
        ((H i).event j).RetainedBoundaryIndex → standardCapWindow (parameters i).modelRadius → ((H i).stage j.succ).Carrier),
    (∀ i j hj b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig i j hj b)) →
    (∀ i j hj b y (v z : TangentSpace ThreeModel y), (w i j hj b).windowMetric.inner y v z =
      ((records i j).static b).neck.scale * ((H i).initialMetric j.succ).inner (Jbig i j hj b y)
        (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y v) (mfderiv ThreeModel ThreeModel (Jbig i j hj b) y z)) →
    (∀ i j hj b z, ∃ u : standardCapWindow (parameters i).modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig i j hj b u = ((records i j).static b).inclusion (((records i j).static b).witness.cap z)) →
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∃ (ind : ℕ → ℕ), StrictMono ind ∧
      ∃ (hprecision : ∀ i, eta (ind i) ≤ δ) (horder : ∀ i, k ≤ m (ind i)),
      let N := fun i => ((O (ind i)).monoDelta (hprecision i) hδ1).lowerOrder (horder i)
      ∀ᶠ i in atTop,
        ∃ N' : NormalizedNeck (((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i))
          (hinit (ind i))).event (Fin.last (H (ind i)).eventCount)).terminal.metric δ k,
          HEq N' (N i) ∧ Nonempty (IncomingBackwardNeck
            ((H (ind i)).appendEvent (E (ind i)).incoming.lt (E (ind i)) (hinit (ind i)))
            (Fin.last (H (ind i)).eventCount) N' (Real.sqrt (N i).scale⁻¹)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hrec⟩ :=
    exists_prospective_neck_convergence_of_improving_necks D r eps a₀ Ctime ha₀ heps hepssmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro H s Qstage E hinit eta m O heta hm hscale a ha hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
    phi hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark δ hδ hδ1 k
  obtain ⟨ind, hind, first, hle, hprec, hord, hstart, K, Phi, hPhi, gflow, S, rho, hrho,
    hmap, hS, hterminal, hmetric, hslabs, hlast, _, hjets⟩ :=
    hrec H (fun i => Fin.last (H i).eventCount) s (fun i => (E i).incoming)
      (fun i => (E i).terminal) hinit eta m O heta hm hscale ha hsa
      parameters records hfixed hlower hdelta haccuracy hmargin horder q0 hq0 hderiv hfinal
      hphi hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark hδ hδ1 k
  let N := fun i => ((O (ind i)).monoDelta (hprec i) hδ1).lowerOrder (hord i)
  refine ⟨ind ∘ rho, hind.comp hrho, (fun i => hprec (rho i)), (fun i => hord (rho i)), ?_⟩
  filter_upwards [hjets] with i hi
  obtain ⟨Z, hZ, eta', heta', hclose⟩ := hi
  have hclock : (H (ind (rho i))).time (first (rho i)) ≤ s (ind (rho i)) - (N (rho i)).scale⁻¹ := by
    apply (hstart (rho i)).trans
    have hscale : (N (rho i)).scale = (O (ind (rho i))).scale := rfl
    rw [hscale, inv_eq_one_div]
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (O (ind (rho i))).scale_pos.le
  obtain ⟨N', hN', B, _, _⟩ := NormalizedNeck.exists_incomingBackwardNeck_appendEvent
    (H (ind (rho i))) (first (rho i)) (hle (rho i)) (E (ind (rho i))) (hinit (ind (rho i)))
    (N (rho i)) (K (rho i)) (Phi (rho i)) (hPhi (rho i)) (hmap (rho i)) (gflow (rho i))
    (by norm_num : (1 : ℝ) < 2) (S (rho i)) (hS (rho i)) (hterminal (rho i))
    (fun t _ => hmetric (rho i) t) (hslabs (rho i)) (hlast (rho i)) hclock Z hZ ⟨eta', heta', hclose⟩
  exact ⟨N', hN', ⟨B⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q (H.time (Fin.last H.eventCount)) s) :
    SigmaCompactSpace E.incoming.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

private theorem exists_selected_neck_append_backward_threshold
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ (a q₀ : ℝ), 0 < a → 0 < q₀ →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ ηstar : ℝ, ∃ mstar : ℕ, ∃ Qmin : ℝ,
      0 < ηstar ∧ ηstar ≤ δ ∧ k ≤ mstar ∧ 0 < Qmin ∧
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v) (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    η ≤ ηstar → mstar ≤ m → Qmin ≤ O.scale →
    ∀ (hprec : η ≤ δ) (hord : k ≤ m),
    let N := (O.monoDelta hprec hδ1).lowerOrder hord
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹)) := by
  classical
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hseq⟩ :=
    exists_subsequence_selected_neck_append_backward D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a q0 ha hq0 phi hphi
  by_contra hnot
  push Not at hnot
  have hfail (n : ℕ) := hnot (min (δ / 2) (1 / ((n : ℝ) + 1))) (k + n) ((n : ℝ) + 1)
    (lt_min (half_pos hδ) (by positivity))
    ((min_le_left _ _).trans (half_le_self hδ.le)) (Nat.le_add_right k n) (by positivity)
  choose H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale hprec hord hbad using hfail
  have hηlim : Tendsto η atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (O n).delta_pos.le)
      (fun n => (hη n).trans (min_le_right _ _))
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hmlim : Tendsto m atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_add_atTop_nat k)
    intro n
    have hn := hm n
    omega
  have hscaleLim : Tendsto (fun n => (O n).scale) atTop atTop :=
    tendsto_atTop_mono hscale
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨ind, hind, hprecision, horder', hsuccess⟩ :=
    hseq H s Qstage E hinit η m O hηlim hmlim hscaleLim ha hsa parameters records
      hfixed hlower (Eventually.of_forall fun i j _ => hdelta i j)
      (Eventually.of_forall haccuracy) hmargin horder q0 hq0
      (fun i j _ => hderiv i j) hfinal hphi (fun i j _ => hpinch i j) hpinchFinal
      (fun i j _ => hcap i j)
      (fun i j _ => center i j) (fun i j _ => precision i j) (fun i j _ => order i j)
      (fun i j _ => d i j) (fun i j _ => w i j) (fun i j _ => Jbig i j)
      (fun i j _ => hJbig i j) (fun i j _ => hzero i j) (fun i j _ => hmark i j)
      hδ hδ1 k
  obtain ⟨n, hn⟩ := hsuccess.exists
  obtain ⟨N', hN', hB⟩ := hn
  exact hbad (ind n) ⟨N', hN', hB⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance (H : ObservedHistory.{u})
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q (H.time (Fin.last H.eventCount)) s) :
    SigmaCompactSpace E.incoming.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

theorem exists_uniform_selected_neck_append_backward
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ (a q₀ : ℝ), 0 < a → 0 < q₀ →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Qmin : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Qmin ∧
    ∀ (H : ObservedHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        (H.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        normalizedDatum (H.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v) (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Qmin ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ N' : NormalizedNeck ((H.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hthreshold⟩ :=
    exists_selected_neck_append_backward_threshold D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a q0 ha hq0 phi hphi
  obtain ⟨ηstar, mstar, Qmin, hηstar, hηδ, hkm, hQmin, hmain⟩ :=
    hthreshold hδ hδ1 k a q0 ha hq0 phi hphi
  refine ⟨ηstar, mstar, Qmin, hηδ, hkm, hηstar, hQmin, ?_⟩
  intro H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale
  exact hmain H s Qstage E hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale (hη.trans hηδ) (hkm.trans hm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end

section
noncomputable section
open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance {Q : OrientedThreeStage.{u}} {a s : ℝ} (G : Q.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_selected_neck_append_backward_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (D Dbig r tol : ℝ) (Ctime : ℝ≥0)
    (hmargin : D + 1 ≤ Dbig) (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ q₀ : ℝ, 0 < q₀ →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Qmin : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Qmin ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ε₀ →
    ∀ (H : RetainedCoreHistory.{u}), InitialIdentification P g H.toHistory →
    ∀ ρ : ℝ, H.hasCanonicalCutoffRecords p₀ δ₀ ρ →
    ∀ (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    E.incoming.SingularEndpoint →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck E.terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Qmin ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    ∃ N' : NormalizedNeck ((H.toHistory.appendEvent E.incoming.lt E hinit).event
      (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ Nonempty (IncomingBackwardNeck (H.toHistory.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹)) := by
  classical
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  obtain ⟨Phi, hPhi, hpinch⟩ := Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P g
  obtain ⟨a, ha, htime⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P g
  obtain ⟨εback, δ₀, hεback, hδ₀, hback⟩ := exists_uniform_selected_neck_append_backward
    D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  have hDbig : StandardCap.transitionEnd < Dbig := by
    have := StandardCap.transitionEnd_pos
    have := inv_pos.mpr htol
    linarith
  obtain ⟨εscalar, hεscalar, hscalar⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window Dbig hDbig
  refine ⟨min εback εscalar, δ₀, lt_min hεback hεscalar, hδ₀, ?_⟩
  intro δ hδ hδ1 k q₀ hq₀
  obtain ⟨ηstar,mstar,Qmin,hηδ,hkm,hηstar,hQmin,hmain⟩ := hback hδ hδ1 k a q₀ ha hq₀ Phi hPhi
  refine ⟨ηstar,mstar,Qmin,hηδ,hkm,hηstar,hQmin,?_⟩
  intro p₀ hpD hpm hpε H A ρ hInv s Qstage E hinit hsing hderiv hfinal η m O hη hm hscale
  obtain ⟨p,_,hmodel,horder,haccuracy,_,records,hcanonical,hδold,_⟩ := hInv
  have hstart := hinitial H.toHistory A
  have hs := htime H.toHistory A (fun j => (records j).singular) (Fin.last H.eventCount) s E.incoming hinit hsing
  have hcap : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤
        metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z) := by
    intro j b z
    have hh := hscalar (H.toHistory.event j) (fixed := p.fixed) (m := p.modelOrder) (ε := p.modelAccuracy)
    rw [← hpD, ← hmodel] at hh
    exact hh (haccuracy.trans_le (hpε.trans (min_le_right _ _))) (by omega) ((records j).static b)
      (hcanonical j b) z
  choose center precision order datum w hdatum hmetric hmark using hcanonical
  have hzero (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (y : standardCapWindow p.modelRadius) (v z : TangentSpace ThreeModel y) :
      (w j b).windowMetric.inner y v z = ((records j).static b).neck.scale *
        (H.initialMetric j.succ).inner (((records j).static b).window y)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window y v)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window y z) := by
    have he : (H.toHistory.event j).outputMetric = H.initialMetric j.succ := H.event_output j
    have hh := hmetric j b y v z
    rw [he] at hh
    exact hh
  exact hmain H.toHistory s Qstage E hinit hs p records hstart.1 hstart.2
    (fun j b => ((records j).delta_le b).trans (hδold j))
    (haccuracy.trans_le (hpε.trans (min_le_left _ _)))
    (by rw [hmodel,hpD]; exact hmargin) (by omega) hderiv hfinal
    (fun j => hpinch H.toHistory A p records j.castSucc (H.time j.succ)
      (H.toHistory.event j).incoming (H.toHistory.event_initial j))
    (hpinch H.toHistory A p records (Fin.last H.eventCount) s E.incoming hinit)
    hcap center precision order datum w (fun j b => ((records j).static b).window)
    (fun j b => ((records j).static b).window_smooth) hzero hmark η m O hη hm hscale

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
end
end
