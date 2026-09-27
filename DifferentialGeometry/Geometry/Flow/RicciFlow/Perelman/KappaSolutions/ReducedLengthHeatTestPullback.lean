import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHeatTest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobiPullback
import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Geometry.Operator.Scaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
set_option autoImplicit false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
  [T2Space M] [BoundarylessManifold J M]

theorem ancient_redLength_time_deriv_add_laplacian_lower_test_pullback
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (phi : ℝ × M → ℝ)
    (hphi : ContMDiffAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) 2 phi (theta, x))
    (hmin : IsLocalMin (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z) (theta, x)) :
    deriv (fun t => phi (t, x)) theta + laplacian (LeviCivita g) g (fun y => phi (theta, y)) x ≤
      ((Module.finrank ℝ E' : ℝ) / 2 - redLength F.S 0 p (Φ x) (c * theta)) / theta := by
  let psi : ℝ × F.M → ℝ := fun z => phi (z.1 / c, Φ.symm z.2)
  have hleft : Φ.symm (Φ x) = x := Φ.left_inv' hx
  have hcancel : c * theta / c = theta := mul_div_cancel_left₀ theta hc.ne'
  have hinv : ContMDiffAt I J 2 Φ.symm (Φ x) :=
    (Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds (Φ.map_source' hx))).of_le (by decide)
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) 2
      (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2)) (c * theta, Φ x) := by
    have hdiv : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun z : ℝ × F.M => z.1 / c) (c * theta, Φ x) := by
      simp only [div_eq_mul_inv]
      exact contMDiffAt_fst.mul contMDiffAt_const
    exact hdiv.prodMk (hinv.comp (c * theta, Φ x) contMDiffAt_snd)
  have hpsi : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 psi (c * theta, Φ x) := by
    apply ContMDiffAt.comp (c * theta, Φ x) _ hmap
    simpa only [hcancel, hleft] using hphi
  have htend : Tendsto (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2))
      (𝓝 (c * theta, Φ x)) (𝓝 (theta, x)) := by
    simpa only [hcancel, hleft] using hmap.continuousAt.tendsto
  have hcontact : IsLocalMin (fun z : ℝ × F.M => redLength F.S 0 p z.2 z.1 - psi z)
      (c * theta, Φ x) := by
    have htarget : ∀ᶠ z : ℝ × F.M in 𝓝 (c * theta, Φ x), z.2 ∈ Φ.target :=
      continuous_snd.continuousAt.tendsto.eventually (Φ.open_target.mem_nhds (Φ.map_source' hx))
    filter_upwards [htend.eventually hmin, htarget] with z hz hzt
    have hright : Φ (Φ.symm z.2) = z.2 := Φ.right_inv' hzt
    change redLength F.S 0 p (Φ x) (c * theta) - phi (theta, x) ≤
      redLength F.S 0 p (Φ (Φ.symm z.2)) (c * (z.1 / c)) - phi (z.1 / c, Φ.symm z.2) at hz
    change redLength F.S 0 p (Φ x) (c * theta) - psi (c * theta, Φ x) ≤
      redLength F.S 0 p z.2 z.1 - psi z
    simpa only [psi, hcancel, hleft, hright, mul_div_cancel₀ _ hc.ne'] using hz
  have ht : DifferentiableAt ℝ (fun t => phi (t, x)) theta :=
    (hphi.comp theta (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by norm_num) |>.differentiableAt
  have hdt : deriv (fun t => psi (t, Φ x)) (c * theta) = deriv (fun t => phi (t, x)) theta / c := by
    have hout : HasDerivAt (fun t => phi (t, x)) (deriv (fun t => phi (t, x)) theta) (c * theta / c) :=
      hcancel.symm ▸ ht.hasDerivAt
    simpa only [psi, hleft, Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using
      (hout.comp (c * theta) ((hasDerivAt_id (c * theta)).div_const c)).deriv
  have hs : ContMDiffAt J 𝓘(ℝ, ℝ) 2 (fun y => phi (theta, y)) x :=
    hphi.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  have hg' : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace J y,
      g.inner y v w = (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w) := by
    filter_upwards [hg] with y hy
    intro v w
    rw [scaleMetric_inner]
    exact hy v w
  have hlap := laplacian_comp_symm_eq_of_partialDiffeomorph_inner g
    (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))) Φ (x := x) hx hg' hs
  have hspace : ContMDiffAt I 𝓘(ℝ, ℝ) 2 ((fun y => phi (theta, y)) ∘ Φ.symm) (Φ x) := by
    apply ContMDiffAt.comp (Φ x) _ hinv
    simpa only [hleft] using hs
  have hgrad := (gradientFun_contMDiffAt_one (F.S.base.metric (-(c * theta))) hspace).mdifferentiableAt (by norm_num)
  change laplacian (leviCivitaConnectionOfMetric (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))))
    (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))) _ _ = _ at hlap
  rw [lcConn_scaleMetric, laplacian_scaleMetric _ _ _ _ hgrad, inv_inv] at hlap
  have hn : Module.finrank ℝ E' = Module.finrank ℝ E :=
    ((Φ.isLocalDiffeomorphAt J I ∞ hx).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq
  have hh := ancient_redLength_time_deriv_add_laplacian_lower_test F hF (mul_pos hc htheta) p (Φ x) psi hpsi hcontact
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  rw [hdt] at hm
  simp only [psi, hcancel] at hm
  have hscale : c * (((Module.finrank ℝ E : ℝ) / 2 - redLength F.S 0 p (Φ x) (c * theta)) / (c * theta)) =
      ((Module.finrank ℝ E : ℝ) / 2 - redLength F.S 0 p (Φ x) (c * theta)) / theta := by field_simp
  rw [mul_add, mul_div_cancel₀ _ hc.ne', hscale] at hm
  rw [hn]
  exact hlap ▸ hm

theorem ancient_redLength_conjugate_heat_lower_test_pullback
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (phi : ℝ × M → ℝ)
    (hphi : ContMDiffAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) 2 phi (theta, x))
    (hmin : IsLocalMin (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z) (theta, x)) :
    0 ≤ deriv (fun t => phi (t, x)) theta - laplacian (LeviCivita g) g (fun y => phi (theta, y)) x +
      normGradSqFun g (fun y => phi (theta, y)) x - c * F.S.scalar (-(c * theta)) (Φ x) +
      (Module.finrank ℝ E' : ℝ) / (2 * theta) := by
  have hheat := ancient_redLength_time_deriv_add_laplacian_lower_test_pullback F hF p Φ hx hc htheta g hg phi hphi hmin
  have hHJ := ancient_redLength_hamilton_jacobi_lower_test_pullback F hF p Φ hx hc htheta g hg.self_of_nhds
    (fun t y => phi (t, y)) (hphi.mdifferentiableAt (by norm_num)) hmin
  have halgebra : ((Module.finrank ℝ E' : ℝ) / 2 - redLength F.S 0 p (Φ x) (c * theta)) / theta +
      2 * (redLength F.S 0 p (Φ x) (c * theta) / (2 * theta)) =
      (Module.finrank ℝ E' : ℝ) / (2 * theta) := by ring
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
