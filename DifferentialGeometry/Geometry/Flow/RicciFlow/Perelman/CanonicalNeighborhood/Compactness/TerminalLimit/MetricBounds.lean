import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.QuadraticBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

section

set_option autoImplicit false
noncomputable section
open scoped Topology _root_.Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.eventually_metric_uniformly_equivalent_on_compact
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {K : Set L.space.M} (hK : IsCompact K) {width : ℝ}
    (hw : 0 < width) (hwd : width < depthBound) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop,
      K ⊆ (L.maps.partialDiffeomorph i).source ∧
      ∀ t ∈ Set.Icc (-width) 0, ∀ x ∈ K, ∀ v : TangentSpace I3 x,
        B⁻¹ * L.space.metric.inner x v v ≤
          ((X.term (L.subseq i)).S.base.metric t).inner (L.maps.map i x)
            (mfderiv I3 I3 (L.maps.map i) x v) (mfderiv I3 I3 (L.maps.map i) x v) ∧
        ((X.term (L.subseq i)).S.base.metric t).inner (L.maps.map i x)
            (mfderiv I3 I3 (L.maps.map i) x v) (mfderiv I3 I3 (L.maps.map i) x v) ≤
          B * L.space.metric.inner x v v := by
  obtain ⟨C, hC⟩ := L.slab_bounds K hK width hw hwd
  let A : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let Bt : ℝ := Real.exp (2 * A * width)
  have hBt : 1 ≤ Bt := Real.one_le_exp (by positivity)
  have hBt0 : 0 ≤ Bt := zero_le_one.trans hBt
  have hconv : metricSourceConvergesOn (I := I3) L.maps
      (CanonicalMetricCompactness.canonicalSourceData L.maps) K 0 := by
    have h := L.converges.converges K hK 0
    rwa [show L.converges.domain = CanonicalMetricCompactness.canonicalSourceData L.maps
      from funext L.canonical_domains] at h
  refine ⟨2 * Bt, by linarith, ?_⟩
  filter_upwards [hC, pointed_metric_eventually_quadratic_bounds hK hconv
    (epsilon := 1 / 2) (by norm_num)] with i hcurv hinit
  refine ⟨hinit.1, ?_⟩
  let U : Set (X.term (L.subseq i)).M := L.maps.map i '' K
  have hquad := twoTensorQuadBound_of_solutions (I := I3)
    (fun _ => (X.term (L.subseq i)).S) U (-width) 0 C
    (fun _ t ht y hy => by
      obtain ⟨x, hx, rfl⟩ := hy
      exact hcurv t ht x hx)
  have hEq := metric_uniform_equivalent_on_closed_interval_of_solution
    (X.term (L.subseq i)).S (X.term (L.subseq i)).isSolution
    (show -width < 0 by linarith) (L.window_subset_carrier hwd.le (L.subseq i))
    (L.open_window_subset_regular hwd.le (L.subseq i))
    (show (0 : ℝ) ∈ Set.Icc (-width) 0 from ⟨by linarith, le_rfl⟩)
    hA (fun t ht y hy v => hquad.2 0 t ht y hy v)
  intro t ht x hx v
  have hfactor : metricEquivalenceFactor 1 A t 0 ≤ Bt := by
    simp only [metricEquivalenceFactor, one_mul, sub_zero]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨ht.1, ht.2.trans hw.le⟩)
      (mul_nonneg (by norm_num) hA)
  have htime := (metricUniformEquivalentOn_of_le (hEq 0 t ht) hfactor).2
    (L.maps.map i x) (Set.mem_image_of_mem _ hx) (mfderiv I3 I3 (L.maps.map i) x v)
  have hstart := hinit.2 x hx v
  have hnn : 0 ≤ L.space.metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (L.space.metric.pos x v hv).le
  constructor
  · calc
      _ = Bt⁻¹ * ((1 - (1 / 2 : ℝ)) * L.space.metric.inner x v v) := by
        rw [mul_inv_rev]
        ring
      _ ≤ Bt⁻¹ * (((X.term (L.subseq i)).S.base.metric 0).inner (L.maps.map i x)
          (mfderiv I3 I3 (L.maps.map i) x v) (mfderiv I3 I3 (L.maps.map i) x v)) :=
        mul_le_mul_of_nonneg_left hstart.1 (inv_nonneg.mpr hBt0)
      _ ≤ _ := htime.1
  · calc
      _ ≤ Bt * (((X.term (L.subseq i)).S.base.metric 0).inner (L.maps.map i x)
          (mfderiv I3 I3 (L.maps.map i) x v) (mfderiv I3 I3 (L.maps.map i) x v)) := htime.2
      _ ≤ Bt * ((1 + (1 / 2 : ℝ)) * L.space.metric.inner x v v) :=
        mul_le_mul_of_nonneg_left hstart.2 hBt0
      _ ≤ _ := by nlinarith [mul_nonneg hBt0 hnn]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.eventually_metric_lower_bound_on_compact
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (G : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M)
    {K : Set L.space.M} (hK : IsCompact K)
    (hG : ∀ᶠ i in atTop, ∀ t ∈ Icc (-width) 0, ∀ x ∈ K,
      ∀ v : TangentSpace I3 x,
        (G i t).inner x v v = ((X.term (L.subseq i)).S.base.metric t).inner
          (L.maps.partialDiffeomorph i x)
          (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
          (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc (-width) 0,
      ∀ x ∈ K, ∀ v : TangentSpace I3 x,
        c * L.space.metric.inner x v v ≤ (G i t).inner x v v := by
  obtain ⟨B, hB, hBeq⟩ := L.eventually_metric_uniformly_equivalent_on_compact hK hw hwd
  refine ⟨B⁻¹, inv_pos.mpr (lt_of_lt_of_le zero_lt_one hB), ?_⟩
  filter_upwards [hBeq, hG] with i hi hg
  intro t ht x hx v
  rw [hg t ht x hx v]
  exact (hi.2 t ht x hx v).1

theorem StaticTerminalLimit.eventually_metric_lower_bound_of_local_pullbacks
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (G : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M)
    (hG : ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.space.M, IsOpen U ∧ K ⊆ U ∧
        U ⊆ (L.maps.partialDiffeomorph i).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
          (G i t).inner x v w = ((X.term (L.subseq i)).S.base.metric t).inner
            (L.maps.partialDiffeomorph i x)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x w)) :
    ∀ K : Set L.space.M, IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc (-width) 0,
        ∀ x ∈ K, ∀ v : TangentSpace I3 x,
          c * L.space.metric.inner x v v ≤ (G i t).inner x v v := by
  intro K hK
  apply L.eventually_metric_lower_bound_on_compact hw hwd G hK
  filter_upwards [hG K hK] with i hi
  obtain ⟨U, _hUopen, hKU, _hUsource, hpair⟩ := hi
  exact fun t _ht x hx v => hpair t x (hKU hx) v v

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
