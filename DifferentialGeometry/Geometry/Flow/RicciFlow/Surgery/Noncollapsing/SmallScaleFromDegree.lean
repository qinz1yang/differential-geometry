import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.HistoryDegreeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmallScaleNoncollapsingThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StageBallVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StageComponentSimplyConnected
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowPointScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionThreshold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerNoncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {N : ℕ}
open GC.GeneralFlow

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u})

private theorem time_lt_succ_of_activeStage_eq (t : Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.toHistory.activeStage_before_next t hval
  have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.toHistory.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

private theorem isParabolicallyRmControlledBall_of_scalar_le_of_castSucc
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan M c Dcap Dstar θcap r₀ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / 2 ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (2 + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (hqM : qcan ≤ M) (hM : 1 ≤ 4 * M)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius) (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap)
    (hr₀ : 0 < r₀) (hr₀c : r₀ ≤ c / Real.sqrt M)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (htM : c ^ 2 / M ≤ t)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow
          t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v)) :
    H.toHistory.isParabolicallyRmControlledBall t y r₀ := by
  have hMpos : 0 < M := by linarith
  let u : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨t - c ^ 2 / M, sub_nonneg.mpr htM, (sub_le_self _ (by positivity)).trans t.2.2⟩
  have hut : u ≤ t := show (t : ℝ) - c ^ 2 / M ≤ t from sub_le_self _ (by positivity)
  rcases H.exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le records hcan
      hscale hacc hphi hpinch t i hi y hqM hM hyM hc hcgrad hctime hcpinch hut rfl hslabs
      hcurrent hgrad hDstar hDmodel hθ hwin with h | h
  · exact h.mono_radius H.toHistory hr₀ hr₀c
  · exact absurd h (H.not_capWindowPoint_of_scalar_le records hqM one_le_two hwinScale hbig t i
      hi y hyM hslabs hcurrent)

private theorem isParabolicallyRmControlledBall_of_scalar_le_of_last
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan M c Dcap Dstar θcap r₀ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / 2 ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (2 + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (hqM : qcan ≤ M) (hM : 1 ≤ 4 * M)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius) (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap)
    (hr₀ : 0 < r₀) (hr₀c : r₀ ≤ c / Real.sqrt M)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (htM : c ^ 2 / M ≤ t)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hgrad : ∀ w, qcan < (H.finalSlab h).flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.finalSlab h).flow t w v| ≤
          Cgrad * (H.finalSlab h).flow.scalar t w *
            Real.sqrt ((H.finalSlab h).flow.scalar t w) *
            Real.sqrt (((H.finalSlab h).flow.base.metric t).inner w v v)) :
    H.toHistory.isParabolicallyRmControlledBall t y r₀ := by
  have hMpos : 0 < M := by linarith
  let u : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨t - c ^ 2 / M, sub_nonneg.mpr htM, (sub_le_self _ (by positivity)).trans t.2.2⟩
  have hut : u ≤ t := show (t : ℝ) - c ^ 2 / M ≤ t from sub_le_self _ (by positivity)
  have hor :=
    H.exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le_of_activeStage_eq_last
      records hcan hscale hacc hphi hpinch t h hlastA hfinalPinch y hqM hM hyM hc hcgrad hctime
      hcpinch hut rfl hslabs hfinal hgrad hDstar hDmodel hθ hwin
  rcases hor with hb | hb
  · exact hb.mono_radius H.toHistory hr₀ hr₀c
  · exact absurd hb (H.not_capWindowPoint_of_scalar_le_of_activeStage_eq_last records hqM
      one_le_two hwinScale hbig t h hlastA y hyM hslabs hfinal)

private theorem ball_volume_of_spatialCanonicalWitness {κW ε C1 C2 : ℝ} (hκW : 0 ≤ κW)
    (hW : ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      StageFiniteDegreeBound P N → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κW * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r))
    (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ)
    (hsc : StageFiniteDegreeBound (H.toHistory.stageAt t) N)
    (hwit : ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
      ε C1 C2 p, W.capTubeHasNeckChart ε)
    (hball : H.toHistory.isParabolicallyRmControlledBall t p r) :
    ENNReal.ofReal κW * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) := by
  obtain ⟨W, hW'⟩ := hwit
  have hr : 0 < r := hball.1
  have hp : p ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hv := hW W hW' hsc r hr (hball.terminal_curvature_bound H.toHistory p hp)
  rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul hκW]
  exact hv

private theorem exists_spatialCanonicalWitness_of_castSucc {ε C1 C2 qs t₁ : ℝ}
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (hSC : (H.toHistory.event i).incoming.SpatiallyCanonicalBefore ε C1 C2 qs t₁)
    (ht : (t : ℝ) ∈ Ioo (H.time i.castSucc) t₁) :
    ∀ p : (H.toHistory.stageAt t).Carrier,
      qs < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p →
      ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        ε C1 C2 p, W.capTubeHasNeckChart ε := by
  change ∀ p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier, _
  rw [hi]
  intro p hp
  rw [ObservedHistory.stageMetric_castSucc_apply] at hp ⊢
  exact hSC p t ht hp

private theorem exists_spatialCanonicalWitness_of_last {ε C1 C2 qs t₁ : ℝ}
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hSC : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).SpatiallyCanonicalBefore ε C1 C2
      qs t₁)
    (ht : (t : ℝ) ∈ Ioo (H.time (Fin.last H.eventCount)) t₁) :
    ∀ p : (H.toHistory.stageAt t).Carrier,
      qs < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p →
      ∃ W : SpatialCanonicalWitness (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        ε C1 C2 p, W.capTubeHasNeckChart ε := by
  change ∀ p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier, _
  rw [hlastA]
  intro p hp
  rw [ObservedHistory.stageMetric_last_of_lt (h := h)] at hp ⊢
  exact hSC p t ht hp

private theorem exists_eventSlab_bounds_of_castSucc_lt {Ctime Cgrad : ℝ≥0} {qcan qs ε C1 C2 : ℝ}
    {k : Fin (H.eventCount + 1)} (hder : H.EventSlabsDerivative Ctime qcan k)
    (hgrad : H.EventSlabsGradient Cgrad qcan k)
    (hspat : H.EventSlabsSpatiallyCanonical ε C1 C2 qs k)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (hreg : ∀ i : Fin (H.eventCount + 1), H.time i ≠ t)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) (hik : i.castSucc < k) :
    ∃ t₁ : ℝ, (t : ℝ) ∈ Ioo (H.time i.castSucc) t₁ ∧
      H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t) ∧
      (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t₁ ∧
      (H.toHistory.event i).incoming.GradientBoundBefore Cgrad qcan t₁ ∧
      (H.toHistory.event i).incoming.SpatiallyCanonicalBefore ε C1 C2 qs t₁ := by
  have hle := H.toHistory.activeStage_time_le t
  rw [hi] at hle
  refine ⟨H.time i.succ, ⟨lt_of_le_of_ne hle (hreg _), H.time_lt_succ_of_activeStage_eq t i hi⟩,
    fun j hj => hder j ((hi ▸ hj).trans hik), hder i hik, hgrad i hik, hspat i hik⟩

private theorem noncollapsedAtRegularTimesBefore_of_slab_supply
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan qs M c Dcap Dstar θcap r₀ η ε C1 C2 κ₁ κW κ₀ cBG t₀ : ℝ}
    {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / 2 ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (2 + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (hqM : qcan ≤ M) (hsM : qs ≤ M) (hM : 1 ≤ 4 * M)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius) (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap)
    (hr₀ : 0 < r₀) (hr₀c : r₀ ≤ c / Real.sqrt M) (hr₀ε : r₀ ≤ ε) (hr₀1 : r₀ ≤ 1)
    (hcη : c ^ 2 / M ≤ η) (hcBG : 0 ≤ cBG) (hκ₁ : 0 ≤ κ₁)
    (hBG : ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p : P.Carrier) {r R : ℝ},
      0 < r → r ≤ R →
      (∀ x ∈ riemannianBallOf g p R, R ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) →
      ENNReal.ofReal (cBG * (r / R) ^ 3) *
          riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p R) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r))
    (hκW : 0 ≤ κW)
    (hW : ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      StageFiniteDegreeBound P N → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κW * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r))
    (hdegree : ∀ t : Icc (0 : ℝ) H.toHistory.horizon,
      StageFiniteDegreeBound (H.toHistory.stageAt t) N)
    (habove : H.NoncollapsedAboveBefore κ₁ r₀ ε t₀)
    (hinit : ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier)
      (r : ℝ), (t : ℝ) ≤ η → r ≤ 1 → H.toHistory.isParabolicallyRmControlledBall t p r →
      ENNReal.ofReal κ₀ * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
          (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r))
    (hsupply : ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < t₀ →
      (∀ i : Fin (H.eventCount + 1), H.time i ≠ t) →
      (∃ i : Fin H.eventCount, H.toHistory.activeStage t = i.castSucc ∧ ∃ t₁ : ℝ,
        (t : ℝ) ∈ Ioo (H.time i.castSucc) t₁ ∧
        H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t) ∧
        (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t₁ ∧
        (H.toHistory.event i).incoming.GradientBoundBefore Cgrad qcan t₁ ∧
        (H.toHistory.event i).incoming.SpatiallyCanonicalBefore ε C1 C2 qs t₁) ∨
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        H.toHistory.activeStage t = Fin.last H.eventCount ∧
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi ∧
        ∃ t₁ : ℝ, (t : ℝ) ∈ Ioo (H.time (Fin.last H.eventCount)) t₁ ∧
        H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t) ∧
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t₁ ∧
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).GradientBoundBefore Cgrad qcan t₁ ∧
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).SpatiallyCanonicalBefore ε C1 C2 qs
          t₁) :
    H.NoncollapsedAtRegularTimesBefore (min (min (cBG * κ₁) κW) κ₀) r₀ t₀ := by
  refine H.noncollapsedAtRegularTimesBefore_of_cases (M := M) hr₀ε hr₀1 hcBG hκ₁ hBG habove ?_ ?_
    hinit
  · intro t y ht hreg hηt hyM
    have htM : c ^ 2 / M ≤ t := hcη.trans hηt.le
    rcases hsupply t ht hreg with ⟨i, hi, t₁, ht₁, hslabs, hder, hgrad, -⟩ |
      ⟨h, hlastA, hfp, t₁, ht₁, hslabs, hder, hgrad, -⟩
    · exact H.isParabolicallyRmControlledBall_of_scalar_le_of_castSucc records hcan hscale hacc
        hphi hpinch hwinScale hbig hqM hM hc hcgrad hctime hcpinch hDstar hDmodel hθ hwin hr₀
        hr₀c t i hi y hyM htM hslabs
        ((H.toHistory.event i).incoming.derivativeBoundBefore_mono ht₁.2.le hder)
        (fun w hw v => hgrad w t ht₁ hw v)
    · exact H.isParabolicallyRmControlledBall_of_scalar_le_of_last records hcan hscale hacc
        hphi hpinch hwinScale hbig hqM hM hc hcgrad hctime hcpinch hDstar hDmodel hθ hwin hr₀
        hr₀c t h hlastA hfp y hyM htM hslabs
        (((H.finalSlab h).restrictIncoming le_rfl h le_rfl).derivativeBoundBefore_mono
          ht₁.2.le hder)
        (fun w hw v => hgrad w t ht₁ hw v)
  · intro t y r ht hreg hyM hball
    have hq : qs < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y :=
      hsM.trans_lt hyM
    refine H.ball_volume_of_spatialCanonicalWitness hκW hW t y r (hdegree t) ?_ hball
    rcases hsupply t ht hreg with ⟨i, hi, t₁, ht₁, -, -, -, hSC⟩ |
      ⟨h, hlastA, -, t₁, ht₁, -, -, -, hSC⟩
    · exact H.exists_spatialCanonicalWitness_of_castSucc t i hi hSC ht₁ y hq
    · exact H.exists_spatialCanonicalWitness_of_last t h hlastA hSC ht₁ y hq

end RetainedCoreHistory

private theorem exists_cutoff_record_bounds (Dcw K : ℝ) (hK : 0 < K)
    (hDcw : StandardCap.transitionEnd < Dcw) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (H : RetainedCoreHistory.{u})
      {p₀ : CutoffParameters} {δbound ρbound : ℝ},
      H.hasCanonicalCutoffRecords p₀ δbound ρbound → p₀.recenterConstant * δbound ≤ 1 / 2 →
      p₀.modelAccuracy ≤ ε₀ → Dcw + 2 ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder →
      ρbound ≤ (Real.sqrt (4 * K))⁻¹ →
      ∃ (p : CutoffParameters) (records : ∀ i : Fin H.eventCount,
        GeometricCutoffRecord H.toHistory i p),
        (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
        (∀ i b z, ((records i).static b).neck.scale / 2 ≤
          metricScalarAt ((records i).static b).witness.metric
            (((records i).static b).witness.cap z)) ∧
        p.modelAccuracy ≤ 1 / 2 ∧ Dcw + 2 ≤ p.modelRadius ∧
        (∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcw + 1 →
          ((records j).static b).neck.scale / 2 ≤
            metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x)) ∧
        ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
          K < ((records j).static b).neck.scale := by
  obtain ⟨εs, hεs, hsc⟩ :=
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u} (Dcw + 2)
      (by linarith)
  obtain ⟨εw, hεw, hwin⟩ :=
    RetainedCoreHistory.exists_window_scalar_lower_bound.{u} Dcw (Dcw + 2) (by linarith)
  refine ⟨min (1 / 2) (min εs εw), lt_min (by norm_num) (lt_min hεs hεw), ?_⟩
  intro H p₀ δbound ρbound hrec hΛδ hacc hD hm hρ
  obtain ⟨p, records, hfam⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mp
      hrec
  have hcan := hfam.2.2.2.2.2.1
  have hradius : Dcw + 2 ≤ p.modelRadius := by
    rw [hfam.2.1]
    exact hD
  have hord : 2 ≤ p.modelOrder := by
    rw [hfam.2.2.1]
    exact hm
  have hacc' : p.modelAccuracy = p₀.modelAccuracy := hfam.2.2.2.1
  have haccs : p.modelAccuracy ≤ εs := by
    rw [hacc']
    exact hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haccw : p.modelAccuracy ≤ εw := by
    rw [hacc']
    exact hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨p, records, hcan, fun i b z => hsc (H.toHistory.event i) hradius haccs hord
    ((records i).static b) (hcan i b) z, by rw [hacc']; exact hacc.trans (min_le_left _ _),
    hradius, hwin H records hcan hradius haccw hord, fun j b => ?_⟩
  have h1 := hfam.inv_two_mul_sq_lt_static_scale hΛδ j b
  have hρpos : 0 < ρbound :=
    (p.neckRadius_pos _ (H.toHistory.time_nonneg _)).trans_le (hfam.2.2.2.2.2.2.2 j)
  have h2 : ρbound ^ 2 ≤ (4 * K)⁻¹ := by
    have := pow_le_pow_left₀ hρpos.le hρ 2
    rwa [inv_pow, Real.sq_sqrt (by positivity)] at this
  have h3 : 2 * K ≤ (2 * ρbound ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) (by positivity)]
    calc 2 * ρbound ^ 2 ≤ 2 * (4 * K)⁻¹ := by gcongr
      _ = (2 * K)⁻¹ := by field_simp; ring
  linarith

namespace ObservedHistory

private theorem ball_volume_lower_bound_of_closedSlab_stage_zero
    {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}
    (A : InitialIdentification P g H) {τ ρ κ : ℝ}
    (hbound : ∀ {Q : OrientedThreeStage.{u}} {b : ℝ} (G : Q.ClosedSlab 0 b)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
        (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
          (G.flow.base.metric 0).inner (φ x)
            (mfderiv ThreeModel ThreeModel φ x v)
            (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
        ∀ t ∈ Icc (0 : ℝ) b, t ≤ τ → ∀ x : Q.Carrier,
          ∀ r : ℝ, 0 < r → r ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
              riemannianVolumeMeasure ThreeModel Q.Carrier (G.flow.base.metric t)
                (riemannianBallOf (G.flow.base.metric t) x r))
    (k : Fin (H.eventCount + 1)) (hk : k = 0) {a b : ℝ} (ha : a = H.time k)
    (G : (H.stage k).ClosedSlab a b) (hG : G.flow.base.metric a = H.initialMetric k)
    (t : ℝ) (ht : t ∈ Icc a b) (htτ : t ≤ τ) (x : (H.stage k).Carrier)
    (r : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (G.flow.base.metric t)
        (riemannianBallOf (G.flow.base.metric t) x r) := by
  subst hk
  rw [H.time_zero] at ha
  subst ha
  refine hbound G A.map (fun y v w => ?_) t ht htτ x r hr hrρ
  rw [hG]
  exact A.metric_eq y v w

end ObservedHistory

private theorem exists_initial_layer_noncollapsed_of_initialIdentification
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ κ η : ℝ, 0 < κ ∧ 0 < η ∧
      ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      (∀ j : Fin H.eventCount, (H.toHistory.event j).incoming.SingularEndpoint) →
      ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
        (t : ℝ) ≤ η → r ≤ 1 → H.toHistory.isParabolicallyRmControlledBall t p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
            (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) := by
  obtain ⟨τ, ρ, κ, hτ, hρ, hκ, hbound⟩ :=
    exists_uniform_initial_closedSlab_ball_volume_lower_bound P₀ g₀
  obtain ⟨a₁, ha₁, hsing⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  set m := min ρ 1 with hm
  have hm0 : 0 < m := lt_min hρ one_pos
  refine ⟨κ * m ^ 3, min τ (a₁ / 2), by positivity, lt_min hτ (half_pos ha₁), ?_⟩
  intro H hA hsingular t p r htη hr1 hball
  have hr : 0 < r := hball.1
  have hrt : r ^ 2 ≤ (t : ℝ) := hball.radius_sq_le_time H.toHistory
  have ht0 : 0 < (t : ℝ) := (pow_pos hr 2).trans_le hrt
  have A := hA.some
  have hfirst : ∀ k : Fin (H.eventCount + 1), H.time k ≤ (t : ℝ) → k = 0 := by
    intro k hk
    by_contra hk0
    have hpos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk0 (Fin.ext h))
    let j : Fin H.eventCount := ⟨0, by omega⟩
    have hjk : j.succ ≤ k := by
      change 1 ≤ k.val
      omega
    have hle := hsing H.toHistory A hsingular j.castSucc
      (H.time j.succ) (H.toHistory.event j).incoming (H.toHistory.event_initial j)
      (hsingular j)
    have hmono : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hjk
    have : a₁ ≤ (t : ℝ) := hle.trans (hmono.trans hk)
    have : (t : ℝ) ≤ a₁ / 2 := htη.trans (min_le_right _ _)
    linarith
  have hk : H.toHistory.activeStage t = 0 := hfirst _ (H.toHistory.activeStage_time_le t)
  have hlt : H.toHistory.time (H.toHistory.activeStage t) < (t : ℝ) := by
    rw [hk, H.toHistory.time_zero]
    exact ht0
  set s := min r ρ with hs
  have hs0 : 0 < s := lt_min hr hρ
  have hv := ObservedHistory.ball_volume_lower_bound_of_closedSlab_stage_zero A hbound
    (H.toHistory.activeStage t) hk rfl (H.toHistory.closedPrefixAt t hlt)
    (H.toHistory.closedPrefixAt_initial t hlt) t ⟨(H.toHistory.activeStage_time_le t), le_rfl⟩
    (htη.trans (min_le_left _ _)) p s hs0 (min_le_right _ _)
  rw [H.toHistory.closedPrefixAt_metric] at hv
  have hmr : m * r ≤ s := le_min
    (mul_le_of_le_one_left hr.le (min_le_right _ _))
    ((mul_le_of_le_one_right hm0.le hr1).trans (min_le_left _ _))
  calc ENNReal.ofReal (κ * m ^ 3) * ENNReal.ofReal r ^ 3
      = ENNReal.ofReal κ * ENNReal.ofReal (m * r) ^ 3 := by
        rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_mul hm0.le, ENNReal.ofReal_pow hm0.le,
          mul_pow, mul_assoc]
    _ ≤ ENNReal.ofReal κ * ENNReal.ofReal s ^ 3 := by
        gcongr
    _ ≤ _ := hv
    _ ≤ _ := MeasureTheory.measure_mono (riemannianBallOf_mono _ _ (min_le_left _ _))

theorem smallScaleNoncollapsingThroughSurgery_of_historyDegreeBound
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (N : ℕ) (hN : 0 < N)
    (hdegree : UniformHistoryDegreeBound P₀ g₀ N) :
    SmallScaleNoncollapsingThroughSurgery P₀ g₀ := by
  intro B ε C1 C2 C1s C2s τmin Ctime Cgrad phi κ₁ hB hε hε' hC1 hC2 hC1s hC2s hτ hphi hκ₁
  obtain ⟨cBG, hcBG, hBG⟩ := exists_riemannianVolumeMeasure_ball_ge_of_rm_le.{u}
  obtain ⟨κW, hκW, hW⟩ :=
    canonicalBallConsumer_of_stage_degree.{u} ε C1s C2s N hN
  obtain ⟨κ₀, η, hκ₀, hη, hinit⟩ :=
    exists_initial_layer_noncollapsed_of_initialIdentification P₀ g₀
  obtain ⟨cT, hcT, -, hS0⟩ := exists_noncollapsedBefore_of_regularTimes.{u}
  have hCg : (0 : ℝ) ≤ Cgrad := Cgrad.2
  have hCt : (0 : ℝ) ≤ Ctime := Ctime.2
  set L : ℝ := 1 + (Cgrad : ℝ) + 8 * (Ctime : ℝ) + 3072 * (1 + phi 1 + phi 0) ^ 2 with hLdef
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (1 + phi 1 + phi 0)]
  set c : ℝ := 1 / (4 * L) with hcdef
  have hc : 0 < c := by positivity
  have hLc : L * c = 1 / 4 := by
    rw [hcdef]
    field_simp
  have hc4 : c ≤ 1 / 4 := by nlinarith
  have hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4 := by nlinarith
  have hctime : 8 * (Ctime : ℝ) * c ^ 2 ≤ 1 := by
    have h1 : 8 * (Ctime : ℝ) * c ^ 2 ≤ L * c ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (1 + phi 1 + phi 0)]) (sq_nonneg c)
    nlinarith
  have hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1 := by
    have h1 : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ L * c ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : L * c ^ 4 = c ^ 3 / 4 := by
      rw [show L * c ^ 4 = L * c * c ^ 3 by ring, hLc]
      ring
    have h3 : c ^ 3 ≤ 1 := pow_le_one₀ hc.le (by linarith)
    linarith
  have hκpos : 0 < min (min (cBG * κ₁) κW) κ₀ := lt_min (lt_min (mul_pos hcBG hκ₁) hκW) hκ₀
  refine ⟨cT * min (min (cBG * κ₁) κW) κ₀, mul_pos hcT hκpos, ?_⟩
  intro qcan qs hqcan hqs
  set M : ℝ := max (max qs (1 / 4)) (c ^ 2 / η) with hMdef
  have hqsM : qs ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM4 : 1 ≤ 4 * M := by
    have := (le_max_right qs (1 / 4)).trans (le_max_left _ (c ^ 2 / η))
    linarith
  have hMpos : 0 < M := by linarith
  have hqM : qcan ≤ M := hqs.trans hqsM
  have hcη : c ^ 2 / M ≤ η := by
    rw [div_le_iff₀ hMpos]
    have h := le_max_right (max qs (1 / 4)) (c ^ 2 / η)
    calc c ^ 2 = c ^ 2 / η * η := by field_simp
      _ ≤ M * η := mul_le_mul_of_nonneg_right h hη.le
      _ = η * M := mul_comm _ _
  set r₀ : ℝ := min (min ε (c / Real.sqrt M)) 1 with hr₀def
  have hr₀ : 0 < r₀ := lt_min (lt_min hε (div_pos hc (Real.sqrt_pos.mpr hMpos))) one_pos
  have hr₀ε : r₀ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hr₀c : r₀ ≤ c / Real.sqrt M := (min_le_left _ _).trans (min_le_right _ _)
  have hr₀1 : r₀ ≤ 1 := min_le_right _ _
  set Dcw : ℝ := 2 * StandardCap.transitionEnd +
    Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) + 1
    with hDcwdef
  have hTE := StandardCap.transitionEnd_pos
  have hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcw := by
    rw [hDcwdef]
    linarith
  have hDcw : StandardCap.transitionEnd < Dcw := by
    have : 0 ≤ Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) :=
      by positivity
    linarith
  set K : ℝ := (2 + Ctime * (16 * c ^ 2)) * M with hKdef
  have hK : 0 < K := by positivity
  obtain ⟨ε₀, hε₀, hrecords⟩ := exists_cutoff_record_bounds.{u} Dcw K hK hDcw
  refine ⟨r₀, 1, (Real.sqrt (4 * K))⁻¹, ε₀, Dcw + 2, 2, hr₀, one_pos, by positivity, hε₀,
    by linarith, ?_⟩
  intro p₀ δbound ρbound hacc₀ hD₀ hm₀ _ hρ₀ H hH hpinch
  have hstages : ∀ k : Fin (H.eventCount + 1), StageFiniteDegreeBound (H.stage k) N :=
    hdegree H hH
  refine ⟨?_, ?_⟩
  · intro j _ hder hgrad hspat t₀ ht₀ _ hdb hgb hsb habove
    obtain ⟨p, records, hcan, hscale, hacc, hradius, hwinScale, hbig⟩ :=
      hrecords H hH.2.2.2.1 hH.2.2.2.2 hacc₀ hD₀ hm₀ hρ₀
    refine hS0 H hκpos ?_
    refine H.noncollapsedAtRegularTimesBefore_of_slab_supply records hcan hscale hacc hphi hpinch
      hwinScale hbig hqM hqsM hM4 hc hcgrad hctime hcpinch (by linarith : Dcw ≤ Dcw + 2) hradius
      le_rfl hwin hr₀ hr₀c hr₀ε hr₀1 hcη hcBG.le hκ₁.le hBG hκW.le hW
      (fun t => hstages _) habove (hinit H hH.1 (fun i => (records i).singular)) ?_
    intro t ht hreg
    left
    have hk : H.toHistory.activeStage t ≠ Fin.last H.eventCount := by
      intro hk
      have h1 := H.toHistory.activeStage_time_le t
      rw [hk] at h1
      have h2 : H.time j.succ ≤ H.time (Fin.last H.eventCount) :=
        H.time_strictMono.monotone (Fin.le_last _)
      have h3 : H.time (Fin.last H.eventCount) ≤ (t : ℝ) := h1
      linarith [ht₀.2]
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hk
    have hle := H.toHistory.activeStage_time_le t
    rw [← hi] at hle
    have hle' : H.time i.castSucc ≤ (t : ℝ) := hle
    have hij : i ≤ j := by
      by_contra hji
      have hlt : j < i := lt_of_not_ge hji
      have : H.time j.succ ≤ H.time i.castSucc :=
        H.time_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith [ht₀.2]
    refine ⟨i, hi.symm, ?_⟩
    rcases hij.lt_or_eq with hlt | rfl
    · exact H.exists_eventSlab_bounds_of_castSucc_lt hder hgrad hspat t hreg i hi.symm
        (Fin.castSucc_lt_castSucc_iff.mpr hlt)
    · refine ⟨t₀, ⟨lt_of_le_of_ne hle' (hreg _), ht⟩, fun j' hj' => hder j' ?_, hdb, hgb, hsb⟩
      rw [← hi] at hj'
      exact hj'
  · intro s G hG hpG _ hder hgrad hspat t₀ _ _ hdb hgb hsb habove T hT hTs hTt
    have hHT : H.horizon ≤ T := hH.2.1 ▸ hT.le
    have hrec' :=
      RetainedCoreHistory.hasCanonicalCutoffRecords_extendHorizon hH.2.2.2.1 T hHT
      (G.closedPrefix T hT hTs) hG.2
    obtain ⟨p, records, hcan, hscale, hacc, hradius, hwinScale, hbig⟩ :=
      hrecords _ hrec' hH.2.2.2.2 hacc₀ hD₀ hm₀ hρ₀
    refine hS0 _ hκpos ?_
    refine RetainedCoreHistory.noncollapsedAtRegularTimesBefore_of_slab_supply _ records hcan
      hscale hacc hphi (H.eventSlabsPinched_extendHorizon hpinch hHT _ hG.2) hwinScale hbig hqM
      hqsM hM4 hc hcgrad hctime hcpinch (by linarith : Dcw ≤ Dcw + 2) hradius le_rfl hwin hr₀
      hr₀c hr₀ε hr₀1 hcη hcBG.le hκ₁.le hBG hκW.le hW (fun t => hstages _)
      (habove T hT hTs hTt)
      (hinit _ (hH.1.elim fun A => ⟨⟨A.map, A.positive, A.metric_eq⟩⟩)
        (fun i => (records i).singular)) ?_
    intro t ht hreg
    by_cases hlastA :
        (H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG.2).toHistory.activeStage t =
          Fin.last H.eventCount
    · right
      obtain ⟨h, hfp⟩ := RetainedCoreHistory.extendHorizon_finalSlab_phiAlmostNonnegative (H := H)
        (G := G) (hG := hG.2) (T := T) (hHT := hHT) (hT := hT) (hTs := hTs) hpG
      have hle :=
        (H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG.2).toHistory.activeStage_time_le t
      rw [hlastA] at hle
      refine ⟨h, hlastA, hfp, T, ⟨lt_of_le_of_ne hle (hreg _), ht⟩, ?_,
        RetainedCoreHistory.extendHorizon_finalSlab_derivativeBoundBefore hdb hTt h,
        RetainedCoreHistory.extendHorizon_finalSlab_gradientBoundBefore hgb hTt h,
        fun y v hv hq => hsb y v ⟨hv.1, hv.2.trans_le hTt⟩ hq⟩
      rw [hlastA]
      exact H.eventSlabsDerivative_extendHorizon hder hHT _ hG.2
    · left
      obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hlastA
      exact ⟨i, hi.symm, RetainedCoreHistory.exists_eventSlab_bounds_of_castSucc_lt _
        (H.eventSlabsDerivative_extendHorizon hder hHT _ hG.2)
        (H.eventSlabsGradient_extendHorizon hgrad hHT _ hG.2) hspat t hreg i hi.symm
        (Fin.castSucc_lt_last i)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
