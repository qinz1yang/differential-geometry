import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

theorem CylinderReference.closedBall_subset_slab (C : CylinderReference)
    (p : Cylinder) {R : ℝ} (hR : 0 ≤ R) :
    riemannianClosedBallOf (C.metric 0) p R ⊆ univ ×ˢ Icc (p.2 - R) (p.2 + R) := by
  intro y hy
  have hheight : |p.2 - y.2| ≤ R :=
    (ENNReal.ofReal_le_ofReal_iff hR).mp ((C.height_edist_le p y).trans hy)
  have habs := abs_le.mp hheight
  exact ⟨mem_univ _, by constructor <;> linarith⟩

theorem CylinderReference.isCompact_closedBall (C : CylinderReference)
    (p : Cylinder) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (riemannianClosedBallOf (C.metric 0) p R) := by
  have hslab : IsCompact (univ ×ˢ Icc (p.2 - R) (p.2 + R) : Set Cylinder) :=
    (isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod isCompact_Icc
  exact hslab.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist (C.metric 0) p) continuous_const)
    (C.closedBall_subset_slab p hR)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem collar_ball_subset_image (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : univ ×ˢ Icc (-R) R ⊆ U)
    (p : Sphere 2) :
    riemannianBallOf (g 0) (F (p, 0)) (R / 2) ⊆ F '' (univ ×ˢ Icc (-R) R) := by
  have hball : riemannianClosedBallOf (C.metric 0) (p, 0) R ⊆
      univ ×ˢ Icc (-R) R := by
    simpa only [zero_sub, zero_add] using C.closedBall_subset_slab (p, 0) hR.le
  apply (ball_subset_image_of_metric_lower_crossModel (C.metric 0) (g 0) F (p, 0)
    (L := 2) hR (by norm_num) (C.isCompact_closedBall (p, 0) hR.le)
    (hball.trans (hslab.trans hsource)) ?_).trans (image_mono hball)
  intro y hy v
  have hlower := (cmp.equivalence 0 hzero y (hslab (hball hy)) v).1
  rw [hmetric, cmp.pullback_eq 0 y (hslab (hball hy))] at hlower
  have hh := inner_self_nonneg (I := IC) (C.metric 0) y v
  have hg := inner_self_nonneg (I := I3) (g 0) (F y) (mfderiv IC I3 (F : Cylinder → M) y v)
  nlinarith [mul_nonneg (sub_nonneg.mpr heps) hh]

theorem collar_isCompact_closedBall (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R r : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R) (hr : r < R / 2)
    (hsource : U ⊆ F.source) (hslab : univ ×ˢ Icc (-R) R ⊆ U)
    (p : Sphere 2) :
    IsCompact (riemannianClosedBallOf (g 0) (F (p, 0)) r) := by
  have hcpt : IsCompact (F '' (univ ×ˢ Icc (-R) R)) :=
    ((isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod isCompact_Icc).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hslab.trans hsource))
  apply hcpt.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist (g 0) (F (p, 0))) continuous_const)
  intro y hy
  apply collar_ball_subset_image C g F cmp hmetric heps hzero hR hsource hslab p
  exact lt_of_le_of_lt hy
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < R / 2)).mpr hr)

theorem collar_short_curve_stays (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : univ ×ˢ Icc (-R) R ⊆ U)
    (p : Sphere 2) {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc a b))
    (hstart : gamma a = F (p, 0))
    (hlen : metricPathELength (g 0) gamma a b < ENNReal.ofReal (R / 2)) :
    ∀ s ∈ Icc a b, gamma s ∈ F '' (univ ×ˢ Icc (-R) R) := by
  intro s hs
  apply collar_ball_subset_image C g F cmp hmetric heps hzero hR hsource hslab p
  have hdist := edistOf_le_metricPathELength (g 0) hs.1
    (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
  rw [hstart] at hdist
  exact (hdist.trans (metricPathELength_mono (g 0) gamma le_rfl hs.2)).trans_lt hlen

theorem collar_length_lower_of_leaves (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : univ ×ˢ Icc (-R) R ⊆ U)
    (p : Sphere 2) {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc a b))
    (hstart : gamma a = F (p, 0))
    (hleave : ∃ s ∈ Icc a b, gamma s ∉ F '' (univ ×ˢ Icc (-R) R)) :
    ENNReal.ofReal (R / 2) ≤ metricPathELength (g 0) gamma a b := by
  apply le_of_not_gt
  intro hshort
  obtain ⟨s, hs, hnot⟩ := hleave
  exact hnot (collar_short_curve_stays C g F cmp hmetric heps hzero hR hsource hslab
    p hgamma hstart hshort s hs)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
