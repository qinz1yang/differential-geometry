import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture

noncomputable section

open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem collar_ball_subset_image_of_eps_lt_one (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : eps < 1) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : univ ×ˢ Icc (-R) R ⊆ U)
    (p : Sphere 2) :
    riemannianBallOf (g 0) (F (p, 0)) (Real.sqrt (1 - eps) * R) ⊆
      F '' (univ ×ˢ Icc (-R) R) := by
  have hminus : 0 < 1 - eps := sub_pos.mpr heps
  have hsqrt : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr hminus
  have hball : riemannianClosedBallOf (C.metric 0) (p, 0) R ⊆
      univ ×ˢ Icc (-R) R := by
    simpa only [zero_sub, zero_add] using C.closedBall_subset_slab (p, 0) hR.le
  have hcapture := ball_subset_image_of_metric_lower_crossModel (C.metric 0) (g 0) F (p, 0)
    (L := (Real.sqrt (1 - eps))⁻¹) hR (inv_pos.mpr hsqrt)
    (C.isCompact_closedBall (p, 0) hR.le) (hball.trans (hslab.trans hsource))
    (by
      intro y hy v
      have hlow := (cmp.equivalence 0 hzero y (hslab (hball hy)) v).1
      rw [hmetric, cmp.pullback_eq 0 y (hslab (hball hy)) (fun _ => v)] at hlow
      have hh := mul_le_mul_of_nonneg_left hlow (inv_pos.mpr hminus).le
      rw [← mul_assoc, inv_mul_cancel₀ hminus.ne', one_mul] at hh
      simpa only [inv_pow, Real.sq_sqrt hminus.le] using hh)
  rw [div_inv_eq_mul, mul_comm R] at hcapture
  exact hcapture.trans (image_mono hball)

theorem StrongNeck.sqrt_one_sub_mul_le_edistOf_of_height
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J}
    {eps : ℝ} {x : M} {t : ℝ} (neck : StrongNeck S eps x t)
    {R : ℝ} (hR : 0 < R) {q : Sphere 2} {l : ℝ}
    (hRl : R < |l|) (hl : |l| < eps⁻¹) :
    ENNReal.ofReal (Real.sqrt (1 - eps) * R) ≤
      riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) x
        (neck.map (q, l)) := by
  have hRe : R < eps⁻¹ := hRl.trans hl
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-R) R ⊆
      (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    rintro ⟨y, c⟩ ⟨_, hc⟩
    exact ⟨mem_univ _, by constructor <;> linarith [hc.1, hc.2]⟩
  have hcapture := collar_ball_subset_image_of_eps_lt_one neck.cylinder
    (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map neck.comparison rfl
    (by linarith [neck.eps_small]) ⟨by norm_num, le_rfl⟩ hR neck.domain hslab neck.center
  rw [neck.center_eq] at hcapture
  by_contra hnot
  have hmem : neck.map (q, l) ∈
      riemannianBallOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) x
        (Real.sqrt (1 - eps) * R) := not_le.mp hnot
  obtain ⟨z, hz, hzeq⟩ := hcapture hmem
  have hqsrc : ((q, l) : Cylinder) ∈ neck.map.source :=
    neck.domain ⟨mem_univ _, abs_lt.mp hl⟩
  have hzsrc : z ∈ neck.map.source := neck.domain (hslab hz)
  have hzq : z = (q, l) := by
    have hleft := neck.map.left_inv' hzsrc
    rw [hzeq] at hleft
    exact hleft.symm.trans (neck.map.left_inv' hqsrc)
  rw [hzq] at hz
  have hh : |l| ≤ R := abs_le.mpr ⟨hz.2.1, hz.2.2⟩
  exact (not_lt_of_ge hh) hRl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
