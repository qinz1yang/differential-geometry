import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# CH12-S63 G1 (s1): static canonical-neighbourhood scalar-spread lemma

If every point of scalar curvature `> N` has a `SpatialCanonicalWitness` (radius `≥ R^{-1/2}`, scalar
curvature comparable within `C2` on its domain) and `R(x) ≤ Mb` with `N ≤ Mb`, then
`R < 2 C2 Mb` on the ball `B(x, (2 C2 Mb)^{-1/2})`.  Clopen argument in the path-connected ball:
at a point `y` with `R y = 2 C2 Mb` the witness domain contains `B(y, (2 C2 Mb)^{-1/2})` and has
`R ≥ 2 Mb > R x` there, so `x` is not in it.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- (s1) Static CN lemma: scalar curvature stays `< 2 C2 Mb` on `B(x, (2 C2 Mb)^{-1/2})`. -/
theorem cn_scalar_spread_S63 {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I3 M) {ε C1 C2 : ℝ} (hC2 : 1 ≤ C2) {N : ℝ}
    (hcn : ∀ y, N < metricScalarAt g y → Nonempty (SpatialCanonicalWitness g ε C1 C2 y))
    (x : M) {Mb : ℝ} (hMb : 0 < Mb) (hNM : N ≤ Mb) (hx : metricScalarAt g x ≤ Mb) :
    ∀ y ∈ riemannianBallOf g x (Real.sqrt (2 * C2 * Mb))⁻¹,
      metricScalarAt g y < 2 * C2 * Mb := by
  set L : ℝ := 2 * C2 * Mb with hLdef
  have hL2 : 2 * Mb ≤ L := by rw [hLdef]; nlinarith
  have hLpos : 0 < L := by linarith
  have hNL : N < L := by linarith
  have hρ : 0 < (Real.sqrt L)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hLpos)
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  have hBconn : IsPreconnected (riemannianBallOf g x (Real.sqrt L)⁻¹) :=
    (isPathConnected_riemannianBallOf g x hρ).isConnected.isPreconnected
  have hu : IsOpen {y | metricScalarAt g y < L} := isOpen_lt hcont continuous_const
  have hxB : x ∈ riemannianBallOf g x (Real.sqrt L)⁻¹ := by
    change riemannianEDistOf g x x < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hne : (riemannianBallOf g x (Real.sqrt L)⁻¹ ∩ {y | metricScalarAt g y < L}).Nonempty :=
    ⟨x, hxB, show metricScalarAt g x < L by linarith⟩
  have hcl : closure {y | metricScalarAt g y < L} ∩ riemannianBallOf g x (Real.sqrt L)⁻¹ ⊆
      {y | metricScalarAt g y < L} := by
    rintro y ⟨hyc, hyB⟩
    have hle : metricScalarAt g y ≤ L :=
      closure_lt_subset_le hcont continuous_const hyc
    by_contra hnot
    have heq : metricScalarAt g y = L := le_antisymm hle (not_lt.mp hnot)
    obtain ⟨W⟩ := hcn y (by rw [heq]; exact hNL)
    have hrad : (Real.sqrt L)⁻¹ ≤ W.radius := by
      have := W.radius_lower
      rwa [heq] at this
    have hxout : x ∉ riemannianBallOf g y W.radius := by
      intro hxin
      have hxd := W.ball_inside hxin
      have h1 := (W.scalar_bounds x hxd).1
      rw [heq] at h1
      have hC2pos : 0 < C2 := by linarith
      have h2 : C2⁻¹ * L = 2 * Mb := by
        rw [hLdef]; field_simp
      rw [h2] at h1
      linarith
    have hxy : ENNReal.ofReal W.radius ≤ riemannianEDistOf g y x := not_lt.mp hxout
    have hyx : riemannianEDistOf g y x < ENNReal.ofReal (Real.sqrt L)⁻¹ := by
      rw [riemannianEDistOf_comm]; exact hyB
    have := hxy.trans_lt hyx
    rw [ENNReal.ofReal_lt_ofReal_iff hρ] at this
    linarith
  exact hBconn.subset_of_closure_inter_subset hu hne hcl

end GC.LongTime.Ch12
