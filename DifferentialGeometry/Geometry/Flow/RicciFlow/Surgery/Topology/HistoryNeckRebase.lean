import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckRebaseStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions.SumProd

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u uE uJ uX

open private slabMetric_restrict_eq_localPull incomingMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  (K : Set G.terminalRegularOpen)
  (gflow : ℝ → SmoothRiemannianMetric ThreeModel
    (H.backwardSurvivorIncomingFootprint first last hle G K))
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {J : Type uJ} [TopologicalSpace J] {I : ModelWithCorners ℝ E J} [I.Boundaryless]
  {X : Type uX} [TopologicalSpace X] [ChartedSpace J X] [IsManifold I ∞ X] [T2Space X]
  (Phi : X → H.backwardSurvivorIncomingFootprint first last hle G K)
  (hPhi : IsLocalDiffeomorph I ThreeModel ∞ Phi)

private theorem footprint_scalar_of_incoming_metric
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {t : ℝ} (ht : t ∈ Ico (H.time last) s)
    (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
    metricScalarAt (gflow t) z = G.flow.scalar t
      (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl z) := by
  rw [hlast t ⟨ht.1, ht.2.le⟩,
    incomingMetric_restrict_eq_localPull H first last hle G L K ht.2,
    metricScalarAt_localPull]
  rfl

private theorem normalized_scalar_eq_incoming_scalar
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := X) D)
    {Q t : ℝ} (hQ : 0 < Q)
    (hmetric : S.base.metric t = localPullMetric
      (scaleMetric Q hQ (gflow (s + t / Q))) Phi hPhi)
    (ht : s + t / Q ∈ Ico (H.time last) s) (x : X) :
    G.flow.scalar (s + t / Q)
      (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi x)) =
        Q * S.scalar t x := by
  change _ = Q * metricScalarAt (S.base.metric t) x
  rw [hmetric, metricScalarAt_localPull, metricScalarAt_scaleMetric,
    footprint_scalar_of_incoming_metric H first last hle G L K gflow hlast ht]
  rw [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]

private theorem rebased_clock {Q q s t v : ℝ} (hQ : Q ≠ 0) (hq : q ≠ 0) :
    s + (t + v / q) / Q = (s + t / Q) + v / (Q * q) := by
  field_simp
  ring

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

open private slabMetric_restrict_eq_localPull incomingMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

private theorem normalized_footprint_stage_realization
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ : ℝ}
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
    (hinj : Injective Phi)
    {Q : ℝ} (hQ : 0 < Q) (origin : ℝ) {D : RealTimeInterval}
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric Q hQ (gflow (origin + v / Q))) Phi hPhi) :
    let F := fun (j : H.StageInterval first last) =>
      H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.val j.property.1 j.property.2 ∘ Phi;
    (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j)) ∧
    (∀ j, Injective (F j)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (x : neckBuffer δ),
      (H.event j).RegularCrossing
        (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
        (F ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩ x)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (v : ℝ),
      origin + v / Q ∈ Ico (H.time j.castSucc) (H.time j.succ) →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (S.base.metric v).inner x u w = Q * ((H.event j).incoming.flow.base.metric (origin + v / Q)).inner
          (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x w)) ∧
    (∀ v : ℝ, origin + v / Q ∈ Ico (H.time last) s →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (S.base.metric v).inner x u w = Q * (G.flow.base.metric (origin + v / Q)).inner
          (F ⟨last, hle, le_rfl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x w)) := by
  intro F
  have hF (j : H.StageInterval first last) : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j) :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
        j.val j.property.1 j.property.2) hPhi
  refine ⟨hF, ?_, ?_, ?_, ?_⟩
  · intro j
    have hs : Injective (H.backwardSurvivorIncomingFootprintStageMap first last hle G K
        j.val j.property.1 j.property.2) :=
      (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
        (Subtype.val_injective.comp Subtype.val_injective)
    exact hs.comp hinj
  · intro j hf hl x
    exact H.backwardSurvivorIncomingFootprintStageMap_crossing first last hle G K j hf hl (Phi x)
  · intro j hf hl v hv x u w
    rw [hmetric v, hslabs j hf hl _ ⟨hv.1, hv.2.le⟩,
      slabMetric_restrict_eq_localPull H first last hle G K j hf hl hv.2,
      localPullMetric_inner, scaleMetric_inner, localPullMetric_inner]
    have heq := mfderiv_comp x
      ((H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
        j.castSucc hf (j.castSucc_lt_succ.le.trans hl)).mdifferentiable (by simp) (Phi x))
      (hPhi.mdifferentiable (by simp) x)
    rw [heq]
    rfl
  · intro v hv x u w
    rw [hmetric v, hlast _ ⟨hv.1, hv.2.le⟩,
      incomingMetric_restrict_eq_localPull H first last hle G L K hv.2,
      localPullMetric_inner, scaleMetric_inner, localPullMetric_inner]
    have heq := mfderiv_comp x
      ((H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
        last hle le_rfl).mdifferentiable (by simp) (Phi x))
      (hPhi.mdifferentiable (by simp) x)
    rw [heq]
    rfl


private theorem rebased_localPullMetric_eq
    {M : Type*}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {δ ε : ℝ}
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel M)
    (Phi : neckBuffer δ → M) (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
    (f : neckBuffer ε → neckBuffer δ)
    (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f)
    {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q) (s t v : ℝ) :
    localPullMetric (scaleMetric q hq
      (localPullMetric (scaleMetric Q hQ (gflow (s + (t + v / q) / Q))) Phi hPhi)) f hf =
      localPullMetric (scaleMetric (Q * q) (mul_pos hQ hq)
        (gflow ((s + t / Q) + v / (Q * q)))) (Phi ∘ f)
        (DifferentialGeometry.isLocalDiffeomorph_comp hPhi hf) := by
  have htime : s + (t + v / q) / Q = (s + t / Q) + v / (Q * q) :=
    rebased_clock hQ.ne' hq.ne'
  rw [htime]
  apply SmoothRiemannianMetric.ext_inner
  intro x u w
  rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner, scaleMetric_inner,
    localPullMetric_inner, scaleMetric_inner,
    mfderiv_comp x (hPhi.mdifferentiable (by simp) (f x)) (hf.mdifferentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
  ring

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem rebased_footprint_metric_and_scalar
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ ε : ℝ}
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
    (f : neckBuffer ε → neckBuffer δ)
    (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f)
    {Q t : ℝ} (hQ : 0 < Q)
    {D : RealTimeInterval} (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric Q hQ (gflow (s + v / Q))) Phi hPhi)
    (z : neckBuffer δ) (hq : 0 < S.scalar t z)
    (ht : s + t / Q ∈ Ico (H.time last) s)
    {D' : RealTimeInterval} (T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε) D')
    (hTmetric : ∀ v, T.base.metric v = localPullMetric
      (scaleMetric (S.scalar t z) hq (S.base.metric (t + v / S.scalar t z))) f hf) :
    let p := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi z);
    let R := G.flow.scalar (s + t / Q) p;
    ∃ hR : 0 < R, ∀ v, T.base.metric v = localPullMetric
      (scaleMetric R hR (gflow ((s + t / Q) + v / R))) (Phi ∘ f)
      (DifferentialGeometry.isLocalDiffeomorph_comp hPhi hf) := by
  intro p R
  have hscale : R = Q * S.scalar t z :=
    normalized_scalar_eq_incoming_scalar H first last hle G L K gflow Phi hPhi hlast S hQ (hmetric t) ht z
  have hR : 0 < R := hscale.symm ▸ mul_pos hQ hq
  refine ⟨hR, ?_⟩
  intro v
  rw [hTmetric, hmetric]
  have heq := rebased_localPullMetric_eq gflow Phi hPhi f hf hQ hq s t v
  rw [heq]
  apply congrArg (fun g => localPullMetric g (Phi ∘ f)
    (DifferentialGeometry.isLocalDiffeomorph_comp hPhi hf))
  apply SmoothRiemannianMetric.ext_inner
  intro x u w
  simp only [scaleMetric_inner]
  rw [hscale]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem rebased_incomingFootprint_stage_maps
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ ε : ℝ}
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi) (hPhiinj : Injective Phi)
    (f : neckBuffer ε → neckBuffer δ)
    (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f) (hfinj : Injective f)
    {Q t : ℝ} (hQ : 0 < Q) {D : RealTimeInterval}
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric Q hQ (gflow (s + v / Q))) Phi hPhi)
    (z : neckBuffer δ) (y : neckBuffer ε) (hcenter : f y = z) (hq : 0 < S.scalar t z)
    (ht : s + t / Q ∈ Ico (H.time last) s)
    {D' : RealTimeInterval} (T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε) D')
    (hTmetric : ∀ v, T.base.metric v = localPullMetric
      (scaleMetric (S.scalar t z) hq (S.base.metric (t + v / S.scalar t z))) f hf) :
    let p := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi z);
    let R := G.flow.scalar (s + t / Q) p;
    let F := fun (j : H.StageInterval first last) =>
      H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.val j.property.1 j.property.2 ∘ (Phi ∘ f);
    R = Q * S.scalar t z ∧ 0 < R ∧ F ⟨last, hle, le_rfl⟩ y = p ∧ T.scalar 0 y = 1 ∧
    (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j)) ∧
    (∀ j, Injective (F j)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (x : neckBuffer ε),
      (H.event j).RegularCrossing
        (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
        (F ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩ x)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (v : ℝ),
      (s + t / Q) + v / R ∈ Ico (H.time j.castSucc) (H.time j.succ) →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * ((H.event j).incoming.flow.base.metric ((s + t / Q) + v / R)).inner
          (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x w)) ∧
    (∀ v : ℝ, (s + t / Q) + v / R ∈ Ico (H.time last) s →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * (G.flow.base.metric ((s + t / Q) + v / R)).inner
          (F ⟨last, hle, le_rfl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x w)) := by
  intro p R F
  have hscale : R = Q * S.scalar t z :=
    normalized_scalar_eq_incoming_scalar H first last hle G L K gflow Phi hPhi hlast S hQ (hmetric t) ht z
  obtain ⟨hR, hTphysical⟩ := rebased_footprint_metric_and_scalar H first last hle G L K
    gflow hlast Phi hPhi f hf hQ S hmetric z hq ht T hTmetric
  have hbase : T.scalar 0 y = 1 := by
    change metricScalarAt (T.base.metric 0) y = 1
    rw [hTmetric, metricScalarAt_localPull, metricScalarAt_scaleMetric]
    simp only [zero_div, add_zero]
    rw [hcenter]
    exact inv_mul_cancel₀ hq.ne'
  refine ⟨hscale, hR, ?_, hbase, ?_⟩
  · change H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi (f y)) = p
    rw [hcenter]
  · exact normalized_footprint_stage_realization H first last hle G L K gflow hslabs hlast
      (Phi ∘ f) (DifferentialGeometry.isLocalDiffeomorph_comp hPhi hf) (hPhiinj.comp hfinj)
      hR (s + t / Q) T hTphysical

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end
end
end

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem NormalizedNeck.normalizedMetric_scalar_center
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k) :
    metricScalarAt N.normalizedMetric ⟨(N.sphereMark, 0), by
      have h := inv_pos.mpr N.delta_pos
      constructor <;> linarith⟩ = 1 := by
  have hlocal : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ N.chart :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv N.chart
      N.chart_smooth.contMDiff
      (fun x => (N.chart_smooth.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
      (by simp [ThreeSpace])
  have heq : N.normalizedMetric = localPullMetric (scaleMetric N.scale N.scale_pos g) N.chart hlocal := by
    apply SmoothRiemannianMetric.ext_inner
    intro x u v
    rw [localPullMetric_inner, scaleMetric_inner]
    exact N.normalized_inner x u v
  rw [heq, metricScalarAt_localPull, DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, N.marked, ← N.scale_scalar]
  exact inv_mul_cancel₀ N.scale_pos.ne'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem eventually_exists_rebased_incomingFootprint_strongNeckWitness
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi) (hPhiinj : Injective Phi)
    {Q : ℝ} (hQ : 0 < Q)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric Q hQ (gflow (s + v / Q))) Phi hPhi)
    (x : neckBuffer δ) (haxial : x.val.2 = 0) (hscalar : S.scalar 0 x = 1)
    (Z : ℕ → Icc (-(5 / 4 : ℝ)) 0 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v y, Z q v y = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) y - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) y) (Icc (-(5 / 4 : ℝ)) 0) v.1)
    (hbound : ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ ⌈ε⁻¹⌉₊ →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ η) :
    ∀ᶠ z : neckBuffer δ × ℝ in 𝓝[univ ×ˢ Iio 0] (x, 0),
      s + z.2 / Q ∈ Ioo (H.time last) s ∧
      ∃ (hq : 0 < S.scalar z.2 z.1) (f : neckBuffer ε → neckBuffer δ)
        (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
        (∀ y : neckBuffer ε, (f y).val = (y.val.1, y.val.2 + z.1.val.2)) ∧
        f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
        MapsTo (parabolicTime z.2 (S.scalar z.2 z.1)) (Icc (-(9 / 8 : ℝ)) 0)
          (Ioc (-(5 / 4 : ℝ)) 0) ∧
        ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
          (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
          IsSolutionOn T ∧
          (∀ v, T.base.metric v = localPullMetric
            (scaleMetric (S.scalar z.2 z.1) hq (S.base.metric (z.2 + v / S.scalar z.2 z.1))) f hf) ∧
          ∃ W : Perelman.KappaSolutions.StrongNeckWitness S z.1.val.1 z.1 z.2 ε,
            (∀ y : neckBuffer ε, W.embedding y = f y) ∧
            (∀ r ∈ Icc (-1 : ℝ) 0, W.jet 0 r = metricTensorField (T.base.metric r) -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min r 0, (min_le_right r 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))) ∧
            let center : neckBuffer ε := ⟨(z.1.val.1, 0), by
              have hi := inv_pos.mpr (hδ.trans hδε)
              constructor <;> linarith⟩;
            let p := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi z.1);
            let R := G.flow.scalar (s + z.2 / Q) p;
            let F := fun (j : H.StageInterval first last) =>
              H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.val j.property.1 j.property.2 ∘ (Phi ∘ f);
    R = Q * S.scalar z.2 z.1 ∧ 0 < R ∧ F ⟨last, hle, le_rfl⟩ center = p ∧ T.scalar 0 center = 1 ∧
    (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j)) ∧
    (∀ j, Injective (F j)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (x : neckBuffer ε),
      (H.event j).RegularCrossing
        (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
        (F ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩ x)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (v : ℝ),
      (s + z.2 / Q) + v / R ∈ Ico (H.time j.castSucc) (H.time j.succ) →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * ((H.event j).incoming.flow.base.metric ((s + z.2 / Q) + v / R)).inner
          (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x w)) ∧
    (∀ v : ℝ, (s + z.2 / Q) + v / R ∈ Ico (H.time last) s →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * (G.flow.base.metric ((s + z.2 / Q) + v / R)).inner
          (F ⟨last, hle, le_rfl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x w)) := by
  have hsource := eventually_exists_strongNeckWitness_of_reserved_time_jets hδ hδε hε1 S hS x haxial hscalar Z hZ hbound
  have hfilter : 𝓝[univ ×ˢ Iio (0 : ℝ)] (x, 0) ≤ 𝓝[univ ×ˢ Iic (0 : ℝ)] (x, 0) :=
    nhdsWithin_mono _ (prod_mono Subset.rfl Iio_subset_Iic_self)
  have htime : ∀ᶠ z : neckBuffer δ × ℝ in 𝓝[univ ×ˢ Iio (0 : ℝ)] (x, 0),
      H.time last < s + z.2 / Q := by
    have hc : ContinuousAt (fun z : neckBuffer δ × ℝ => s + z.2 / Q) (x, 0) := by fun_prop
    have hbase : H.time last < s + (0 : ℝ) / Q := by simpa only [zero_div, add_zero] using G.lt
    exact (hc.eventually (Ioi_mem_nhds hbase)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsource.filter_mono hfilter, htime, self_mem_nhdsWithin] with z hz hzt hmem
  obtain ⟨hq, f, hf, hemb, hval, hcapture, hwindow, T, hT, hTmetric, hbase, W, hembed, hjet⟩ := hz
  have hphys : s + z.2 / Q ∈ Ioo (H.time last) s :=
    ⟨hzt, add_lt_of_neg_right s (div_neg_of_neg_of_pos hmem.2 hQ)⟩
  refine ⟨hphys, hq, f, hf, hemb, hval, hcapture, hwindow, T, hT, hTmetric, W, hembed, hjet, ?_⟩
  intro center p R F
  have hcenter : f center = z.1 := by
    apply Subtype.ext
    have hh := hval center
    change (f center).val = (z.1.val.1, 0 + z.1.val.2) at hh
    simpa only [zero_add, Prod.mk.eta] using hh
  exact rebased_incomingFootprint_stage_maps H first last hle G L K gflow hslabs hlast
    Phi hPhi hPhiinj f hf hemb.isEmbedding.injective hQ S hmetric z.1 center hcenter hq ⟨hphys.1.le, hphys.2⟩ T hTmetric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
theorem eventually_exists_rebased_incomingFootprint_strongNeckWitness_of_normalizedNeck
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
    {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hmap : H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Phi = N.chart)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric N.scale N.scale_pos (gflow (s + v / N.scale))) Phi hPhi)
    (hzero : S.base.metric 0 = N.normalizedMetric)
    (Z : ℕ → Icc (-(5 / 4 : ℝ)) 0 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v y, Z q v y = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) y - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) y) (Icc (-(5 / 4 : ℝ)) 0) v.1)
    (hbound : ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ ⌈ε⁻¹⌉₊ →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ η) :
    let x : neckBuffer δ := ⟨(N.sphereMark, 0), by
      have h := inv_pos.mpr N.delta_pos
      constructor <;> linarith⟩;
    ∀ᶠ z : neckBuffer δ × ℝ in 𝓝[univ ×ˢ Iio 0] (x, 0),
      s + z.2 / N.scale ∈ Ioo (H.time last) s ∧
      ∃ (hq : 0 < S.scalar z.2 z.1) (f : neckBuffer ε → neckBuffer δ)
        (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
        (∀ y : neckBuffer ε, (f y).val = (y.val.1, y.val.2 + z.1.val.2)) ∧
        f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
        MapsTo (parabolicTime z.2 (S.scalar z.2 z.1)) (Icc (-(9 / 8 : ℝ)) 0)
          (Ioc (-(5 / 4 : ℝ)) 0) ∧
        ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
          (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
          IsSolutionOn T ∧
          (∀ v, T.base.metric v = localPullMetric
            (scaleMetric (S.scalar z.2 z.1) hq (S.base.metric (z.2 + v / S.scalar z.2 z.1))) f hf) ∧
          ∃ W : Perelman.KappaSolutions.StrongNeckWitness S z.1.val.1 z.1 z.2 ε,
            (∀ y : neckBuffer ε, W.embedding y = f y) ∧
            (∀ r ∈ Icc (-1 : ℝ) 0, W.jet 0 r = metricTensorField (T.base.metric r) -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min r 0, (min_le_right r 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))) ∧
            let center : neckBuffer ε := ⟨(z.1.val.1, 0), by
              have hi := inv_pos.mpr (hδ.trans hδε)
              constructor <;> linarith⟩;
            let p := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi z.1);
            let R := G.flow.scalar (s + z.2 / N.scale) p;
            let F := fun (j : H.StageInterval first last) =>
              H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.val j.property.1 j.property.2 ∘ (Phi ∘ f);
    R = N.scale * S.scalar z.2 z.1 ∧ 0 < R ∧ F ⟨last, hle, le_rfl⟩ center = p ∧ T.scalar 0 center = 1 ∧
    (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j)) ∧
    (∀ j, Injective (F j)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (x : neckBuffer ε),
      (H.event j).RegularCrossing
        (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
        (F ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩ x)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (v : ℝ),
      (s + z.2 / N.scale) + v / R ∈ Ico (H.time j.castSucc) (H.time j.succ) →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * ((H.event j).incoming.flow.base.metric ((s + z.2 / N.scale) + v / R)).inner
          (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x w)) ∧
    (∀ v : ℝ, (s + z.2 / N.scale) + v / R ∈ Ico (H.time last) s →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * (G.flow.base.metric ((s + z.2 / N.scale) + v / R)).inner
          (F ⟨last, hle, le_rfl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x w)) := by
  intro x
  have hPhiinj : Injective Phi := by
    intro a b hab
    apply N.chart_smooth.isEmbedding.injective
    have h := congrArg (H.backwardSurvivorIncomingFootprintMap first last hle G K) hab
    change (H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Phi) a =
      (H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Phi) b at h
    rwa [hmap] at h
  have hscalar : S.scalar 0 x = 1 := by
    change metricScalarAt (S.base.metric 0) x = 1
    rw [hzero]
    exact NormalizedNeck.normalizedMetric_scalar_center N
  exact H.eventually_exists_rebased_incomingFootprint_strongNeckWitness first last hle G L K gflow
    hslabs hlast hδ hδε hε1 Phi hPhi hPhiinj N.scale_pos S hS hmetric x rfl hscalar Z hZ hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

section
open Set Filter Topology

private theorem eventually_exists_lift_nhdsWithin
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} {S : Set X} {T : Set Y} {P : X → Prop}
    (hopen : 𝓝 (f x) ≤ Filter.map f (𝓝 x))
    (hpre : f ⁻¹' T ⊆ S) (hP : ∀ᶠ z in 𝓝[S] x, P z) :
    ∀ᶠ w in 𝓝[T] (f x), ∃ z, f z = w ∧ z ∈ S ∧ P z := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hP with ⟨U, hU, hUP⟩
  have himage : f '' U ∈ 𝓝 (f x) := hopen (Filter.image_mem_map hU)
  apply eventually_nhdsWithin_iff.mpr
  refine Filter.mem_of_superset himage ?_
  rintro w ⟨z, hz, rfl⟩ hw
  exact ⟨z, rfl, hpre hw, hUP ⟨hz, hpre hw⟩⟩

private theorem eventually_exists_lift_before_of_nhds_le
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} (hf : 𝓝 (f x) ≤ Filter.map f (𝓝 x))
    {s q : ℝ} (hq : 0 < q)
    {P : X × ℝ → Prop} (hP : ∀ᶠ z in 𝓝[univ ×ˢ Iio 0] (x, 0), P z) :
    ∀ᶠ w in 𝓝[univ ×ˢ Iio s] (f x, s),
      ∃ z : X × ℝ, f z.1 = w.1 ∧ s + z.2 / q = w.2 ∧ z.2 < 0 ∧ P z := by
  have hclock : IsOpenMap (fun t : ℝ => s + t / q) := by
    simpa only [Function.comp_def, div_eq_mul_inv, Homeomorph.coe_mulRight₀] using
      (isOpenMap_add_left s).comp
        (Homeomorph.mulRight₀ q⁻¹ (inv_ne_zero (ne_of_gt hq))).isOpenMap
  have hmap : 𝓝 (Prod.map f (fun t : ℝ => s + t / q) (x, 0)) ≤
      Filter.map (Prod.map f (fun t : ℝ => s + t / q)) (𝓝 (x, 0)) := by
    rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq']
    exact Filter.prod_mono hf (hclock.nhds_le 0)
  have hpre : Prod.map f (fun t : ℝ => s + t / q) ⁻¹' (univ ×ˢ Iio s) ⊆
      univ ×ˢ Iio 0 := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    have hz' : s + z.2 / q < s := hz.2
    have hdiv : z.2 / q < 0 := (add_lt_iff_neg_left s).mp hz'
    exact (div_lt_iff₀ hq).mp hdiv |>.trans_eq (zero_mul q)
  have h := eventually_exists_lift_nhdsWithin hmap hpre hP
  simp only [Prod.map_apply, zero_div, add_zero] at h
  exact h.mono fun w ⟨z, hz, hzS, hzP⟩ =>
    ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz, hzS.2, hzP⟩

private theorem eventually_exists_lift_before_of_isOpenMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpenMap f) {x : X} {s q : ℝ} (hq : 0 < q)
    {P : X × ℝ → Prop} (hP : ∀ᶠ z in 𝓝[univ ×ˢ Iio 0] (x, 0), P z) :
    ∀ᶠ w in 𝓝[univ ×ˢ Iio s] (f x, s),
      ∃ z : X × ℝ, f z.1 = w.1 ∧ s + z.2 / q = w.2 ∧ z.2 < 0 ∧ P z :=
  eventually_exists_lift_before_of_nhds_le (hf.nhds_le x) hq hP

end

noncomputable section
open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem eventually_exists_rebased_strongNeckWitness_at_incoming_points
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi) (hPhiinj : Injective Phi)
    {Q : ℝ} (hQ : 0 < Q)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric Q hQ (gflow (s + v / Q))) Phi hPhi)
    (x : neckBuffer δ) (haxial : x.val.2 = 0) (hscalar : S.scalar 0 x = 1)
    (Z : ℕ → Icc (-(5 / 4 : ℝ)) 0 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v y, Z q v y = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) y - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) y) (Icc (-(5 / 4 : ℝ)) 0) v.1)
    (hbound : ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ ⌈ε⁻¹⌉₊ →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ η) :
    ∀ᶠ pt : (H.stage last).Carrier × ℝ in 𝓝[univ ×ˢ Iio s]
      (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi x), s),
      ∃ z : neckBuffer δ × ℝ,
        H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi z.1) = pt.1 ∧
        s + z.2 / Q = pt.2 ∧ z.2 < 0 ∧
      pt.2 ∈ Ioo (H.time last) s ∧
      ∃ (hq : 0 < S.scalar z.2 z.1) (f : neckBuffer ε → neckBuffer δ)
        (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
        (∀ y : neckBuffer ε, (f y).val = (y.val.1, y.val.2 + z.1.val.2)) ∧
        f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
        MapsTo (parabolicTime z.2 (S.scalar z.2 z.1)) (Icc (-(9 / 8 : ℝ)) 0)
          (Ioc (-(5 / 4 : ℝ)) 0) ∧
        ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
          (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
          IsSolutionOn T ∧
          (∀ v, T.base.metric v = localPullMetric
            (scaleMetric (S.scalar z.2 z.1) hq (S.base.metric (z.2 + v / S.scalar z.2 z.1))) f hf) ∧
          ∃ W : Perelman.KappaSolutions.StrongNeckWitness S z.1.val.1 z.1 z.2 ε,
            (∀ y : neckBuffer ε, W.embedding y = f y) ∧
            (∀ r ∈ Icc (-1 : ℝ) 0, W.jet 0 r = metricTensorField (T.base.metric r) -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min r 0, (min_le_right r 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))) ∧
            let center : neckBuffer ε := ⟨(z.1.val.1, 0), by
              have hi := inv_pos.mpr (hδ.trans hδε)
              constructor <;> linarith⟩;
            let p := pt.1;
            let R := G.flow.scalar pt.2 p;
            let F := fun (j : H.StageInterval first last) =>
              H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.val j.property.1 j.property.2 ∘ (Phi ∘ f);
    R = Q * S.scalar z.2 z.1 ∧ 0 < R ∧ F ⟨last, hle, le_rfl⟩ center = p ∧ T.scalar 0 center = 1 ∧
    (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j)) ∧
    (∀ j, Injective (F j)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (x : neckBuffer ε),
      (H.event j).RegularCrossing
        (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
        (F ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩ x)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (v : ℝ),
      pt.2 + v / R ∈ Ico (H.time j.castSucc) (H.time j.succ) →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * ((H.event j).incoming.flow.base.metric (pt.2 + v / R)).inner
          (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x w)) ∧
    (∀ v : ℝ, pt.2 + v / R ∈ Ico (H.time last) s →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * (G.flow.base.metric (pt.2 + v / R)).inner
          (F ⟨last, hle, le_rfl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x w)) := by
  let Ψ := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl ∘ Phi
  have hΨ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Ψ :=
    isLocalDiffeomorph_comp
      (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
        last hle le_rfl) hPhi
  have hlocal := H.eventually_exists_rebased_incomingFootprint_strongNeckWitness first last hle
    G L K gflow hslabs hlast hδ hδε hε1 Phi hPhi hPhiinj hQ S hS hmetric
    x haxial hscalar Z hZ hbound
  have hpush := eventually_exists_lift_before_of_isOpenMap (s := s) hΨ.isOpenMap hQ hlocal
  filter_upwards [hpush] with w hw
  obtain ⟨z, hpoint, htime, hnegative, hz⟩ := hw
  refine ⟨z, hpoint, htime, hnegative, ?_⟩
  simpa only [← htime, ← hpoint, Ψ, Function.comp_apply] using hz


theorem eventually_exists_rebased_strongNeckWitness_at_incoming_points_of_normalizedNeck
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.backwardSurvivorSlabMetric first last hle j hf hl v).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ v ∈ Icc (H.time last) s,
      gflow v = (H.backwardSurvivorIncomingMetric first last hle G L v).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (Phi : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hPhi : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Phi)
    {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hmap : H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Phi = N.chart)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-2) 0 (by norm_num))) (hS : IsSolutionOn S)
    (hmetric : ∀ v, S.base.metric v = localPullMetric
      (scaleMetric N.scale N.scale_pos (gflow (s + v / N.scale))) Phi hPhi)
    (hzero : S.base.metric 0 = N.normalizedMetric)
    (Z : ℕ → Icc (-(5 / 4 : ℝ)) 0 →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ q v y, Z q v y = iteratedDerivWithin q (fun t =>
      metricTensorField (S.base.metric t) y - metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
          (neckBuffer δ)) y) (Icc (-(5 / 4 : ℝ)) 0) v.1)
    (hbound : ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ ⌈ε⁻¹⌉₊ →
      ∀ v : Icc (-(5 / 4 : ℝ)) 0, ∀ y ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g y (r + 2)
          (cylinderTensorCovDeriv g (Z q v) r y)) ≤ η) :
    ∀ᶠ pt : (H.stage last).Carrier × ℝ in 𝓝[univ ×ˢ Iio s] (N.center.val, s),
      ∃ z : neckBuffer δ × ℝ,
        H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl (Phi z.1) = pt.1 ∧
        s + z.2 / N.scale = pt.2 ∧ z.2 < 0 ∧
      pt.2 ∈ Ioo (H.time last) s ∧
      ∃ (hq : 0 < S.scalar z.2 z.1) (f : neckBuffer ε → neckBuffer δ)
        (hf : IsLocalDiffeomorph NeckCylinderModel NeckCylinderModel ∞ f),
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f ∧
        (∀ y : neckBuffer ε, (f y).val = (y.val.1, y.val.2 + z.1.val.2)) ∧
        f '' neckClosedTest ε ⊆ neckClosedTest δ ∧
        MapsTo (parabolicTime z.2 (S.scalar z.2 z.1)) (Icc (-(9 / 8 : ℝ)) 0)
          (Ioc (-(5 / 4 : ℝ)) 0) ∧
        ∃ T : SolutionOn (I := NeckCylinderModel) (M := neckBuffer ε)
          (RealTimeInterval.closed (-(9 / 8 : ℝ)) 0 (by norm_num)),
          IsSolutionOn T ∧
          (∀ v, T.base.metric v = localPullMetric
            (scaleMetric (S.scalar z.2 z.1) hq (S.base.metric (z.2 + v / S.scalar z.2 z.1))) f hf) ∧
          ∃ W : Perelman.KappaSolutions.StrongNeckWitness S z.1.val.1 z.1 z.2 ε,
            (∀ y : neckBuffer ε, W.embedding y = f y) ∧
            (∀ r ∈ Icc (-1 : ℝ) 0, W.jet 0 r = metricTensorField (T.base.metric r) -
              metricTensorField ((shrinkingCylinderMetric
                ⟨min r 0, (min_le_right r 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer ε))) ∧
            let center : neckBuffer ε := ⟨(z.1.val.1, 0), by
              have hi := inv_pos.mpr (hδ.trans hδε)
              constructor <;> linarith⟩;
            let p := pt.1;
            let R := G.flow.scalar pt.2 p;
            let F := fun (j : H.StageInterval first last) =>
              H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.val j.property.1 j.property.2 ∘ (Phi ∘ f);
    R = N.scale * S.scalar z.2 z.1 ∧ 0 < R ∧ F ⟨last, hle, le_rfl⟩ center = p ∧ T.scalar 0 center = 1 ∧
    (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (F j)) ∧
    (∀ j, Injective (F j)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (x : neckBuffer ε),
      (H.event j).RegularCrossing
        (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
        (F ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩ x)) ∧
    (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last) (v : ℝ),
      pt.2 + v / R ∈ Ico (H.time j.castSucc) (H.time j.succ) →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * ((H.event j).incoming.flow.base.metric (pt.2 + v / R)).inner
          (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩) x w)) ∧
    (∀ v : ℝ, pt.2 + v / R ∈ Ico (H.time last) s →
      ∀ x (u w : TangentSpace NeckCylinderModel x),
        (T.base.metric v).inner x u w = R * (G.flow.base.metric (pt.2 + v / R)).inner
          (F ⟨last, hle, le_rfl⟩ x)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x u)
          (mfderiv NeckCylinderModel ThreeModel (F ⟨last, hle, le_rfl⟩) x w)) := by
  let x : neckBuffer δ := ⟨(N.sphereMark, 0), by
    have hi := inv_pos.mpr N.delta_pos
    constructor <;> linarith⟩
  let Ψ := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl ∘ Phi
  have hΨ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Ψ :=
    isLocalDiffeomorph_comp
      (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
        last hle le_rfl) hPhi
  have hcenter : Ψ x = N.center.val := by
    dsimp only [Ψ, Function.comp_apply]
    rw [H.backwardSurvivorIncomingFootprintStageMap_last]
    have h := congrFun hmap x
    exact congrArg Subtype.val (h.trans N.marked)
  have hlocal := H.eventually_exists_rebased_incomingFootprint_strongNeckWitness_of_normalizedNeck
    first last hle G L K gflow hslabs hlast hδ hδε hε1 Phi hPhi N hmap S hS hmetric hzero Z hZ hbound
  have hpush := eventually_exists_lift_before_of_isOpenMap (s := s) hΨ.isOpenMap N.scale_pos hlocal
  rw [hcenter] at hpush
  filter_upwards [hpush] with w hw
  obtain ⟨z, hpoint, htime, hnegative, hz⟩ := hw
  refine ⟨z, hpoint, htime, hnegative, ?_⟩
  simpa only [← htime, ← hpoint, Ψ, Function.comp_apply] using hz


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
