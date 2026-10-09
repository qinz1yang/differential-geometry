import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact


theorem metricSourceCapture_of_convergesOn
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (I := I3) ((ancientFlowSequence X).atTime 0)
      (L.atTime (I := I3) 0) f)
    (hcomplete : RiemannianMetricComplete (I := I3) (L.S.base.metric 0))
    (hconv : ConvergesOn F L.S) :
    MetricSourceCapture F := by
  intro r hr
  set R : ℝ := 2 * r + 1 with hRdef
  have hR : 0 < R := by positivity
  have hK : IsCompact (riemannianClosedBallOf (I := I3) (L.S.base.metric 0) L.basepoint R) :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I3) hcomplete L.basepoint R
  have hIcc : Icc (0 : ℝ) 0 ⊆ ancientTimeInterval.carrier := by
    intro s hs
    rw [ancientTimeInterval_carrier]
    exact hs.2
  have hev := hconv _ hK 0 0 le_rfl hIcc 0 (1 / 2) (by norm_num)
  filter_upwards [hev] with i hi
  obtain ⟨-, hsrc, ⟨C⟩⟩ := hi
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hlower : ∀ y ∈ riemannianClosedBallOf (I := I3) (L.S.base.metric 0) L.basepoint R,
      ∀ v : TangentSpace I3 y,
        (L.S.base.metric 0).inner y v v ≤
          Real.sqrt 2 ^ 2 * ((X (f i)).S.base.metric 0).inner (F.partialDiffeomorph i y)
            (mfderiv I3 I3 (F.partialDiffeomorph i) y v)
            (mfderiv I3 I3 (F.partialDiffeomorph i) y v) := by
    intro y hy v
    have hh := (C.equivalence 0 ⟨le_rfl, le_rfl⟩ y hy v).1
    rw [C.pullback_eq 0 y hy (fun _ => v)] at hh
    have hh' : (1 - 1 / 2) * (L.S.base.metric 0).inner y v v ≤
        ((X (f i)).S.base.metric 0).inner (F.partialDiffeomorph i y)
          (mfderiv I3 I3 (F.partialDiffeomorph i) y v)
          (mfderiv I3 I3 (F.partialDiffeomorph i) y v) := hh
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hcap := ball_subset_image_of_metric_lower_crossModel (L.S.base.metric 0)
    ((X (f i)).S.base.metric 0) (F.partialDiffeomorph i) L.basepoint hR hsqrt hK hsrc hlower
  have hbase : F.partialDiffeomorph i L.basepoint = (X (f i)).basepoint := F.basepoint_map i
  have hr' : r ≤ R / Real.sqrt 2 := by
    rw [le_div_iff₀ hsqrt, hRdef]
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    nlinarith [hr.le, h2]
  change riemannianBallOf (I := I3) ((X (f i)).S.base.metric 0) (X (f i)).basepoint r ⊆
    F.partialDiffeomorph i '' (F.partialDiffeomorph i).source
  intro y hy
  have hy' : y ∈ riemannianBallOf (I := I3) ((X (f i)).S.base.metric 0)
      (F.partialDiffeomorph i L.basepoint) (R / Real.sqrt 2) := by
    rw [hbase]
    exact riemannianBallOf_mono _ _ hr' hy
  obtain ⟨z, hz, hzy⟩ := hcap hy'
  exact ⟨z, hsrc hz, hzy⟩


theorem exists_ancientKappa_fixed_kappa_compactness_captured {kappa : ℝ}
    (hkappa : 0 < kappa)
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hX : ∀ i, IsAncientKappaSolution (I := I3) kappa (X i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (f : ℕ → ℕ),
      StrictMono f ∧ IsAncientKappaSolution (I := I3) kappa L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        ∃ F : PointedRiemannianConvergenceMaps (I := I3) ((ancientFlowSequence X).atTime 0)
          (L.atTime (I := I3) 0) f, MetricSourceCapture F ∧ ConvergesOn F L.S := by
  refine ancientKappa_fixed_kappa_compactness_of_capture hkappa X hX hbase ?_
  intro L f F hL hconv
  have h0 : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr le_rfl
  have hcomplete : RiemannianMetricComplete (I := I3) (L.S.base.metric 0) :=
    ⟨MetricComplete.complete _ (hL.complete 0 h0)⟩
  exact metricSourceCapture_of_convergesOn X L F hcomplete hconv

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
