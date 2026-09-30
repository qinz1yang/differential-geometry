import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import Mathlib.Analysis.Calculus.LocalExtr.Basic


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_lCost_hamilton_jacobi_eq_of_mdifferentiableAt
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {b : ℝ} (hb : 0 < b) (p q : F.M)
    (hdiff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ lCost F.S 0 p z.2 (z.1 ^ 2)) (b, q)) :
    deriv (fun a ↦ lCost F.S 0 p q (a ^ 2)) b +
        (1 / 2 : ℝ) * (F.S.base.metric (-(b ^ 2))).inner q
          (gradientFun (F.S.base.metric (-(b ^ 2)))
            (fun y ↦ lCost F.S 0 p y (b ^ 2)) q)
          (gradientFun (F.S.base.metric (-(b ^ 2)))
            (fun y ↦ lCost F.S 0 p y (b ^ 2)) q) -
        2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q = 0 := by
  let g := F.S.base.metric (-(b ^ 2))
  let w := gradientFun g (fun y ↦ lCost F.S 0 p y (b ^ 2)) q
  let dt := deriv (fun a ↦ lCost F.S 0 p q (a ^ 2)) b
  have hupper : dt + (1 / 2 : ℝ) * g.inner q w w -
      2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q ≤ 0 := by
    exact ancient_lCost_hamilton_jacobi_upper_test_terminal F hF hb p q
      (fun a y ↦ lCost F.S 0 p y (a ^ 2)) hdiff rfl
      (Filter.Eventually.of_forall fun _ ↦ le_rfl)
  obtain ⟨alpha, halpha, hstart, hend, _, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q (sq_pos_of_pos hb)
  have hsqrt : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb.le
  rw [hsqrt] at hend hcost
  have hlag : Continuous (fun a ↦ lRegularizedLagrangian F.S 0 alpha a) := by
    have h := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
    exact h.comp_continuous (continuous_const.prodMk continuous_id)
      (fun a ↦ by change 0 - a ^ 2 ≤ 0; nlinarith [sq_nonneg a])
  have hact : HasDerivAt (fun a ↦ lRegularizedAction F.S 0 alpha 0 a)
      (lRegularizedLagrangian F.S 0 alpha b) b :=
    intervalIntegral.integral_hasDerivAt_right (hlag.intervalIntegrable 0 b)
      hlag.stronglyMeasurable.stronglyMeasurableAtFilter hlag.continuousAt
  have htime : HasDerivAt (fun a ↦ lCost F.S 0 p (alpha b) (a ^ 2)) dt b := by
    rw [hend]
    exact (hdiff.comp b (mdifferentiableAt_id.prodMk
      mdifferentiableAt_const)).differentiableAt.hasDerivAt
  have hcurve := DifferentialGeometry.Analysis.Calculus.hasDerivAt_along_curve g
    (F := fun a y ↦ lCost F.S 0 p y (a ^ 2)) (gamma := alpha) (t := b)
    (by simpa only [hend] using hdiff)
    (halpha.mdifferentiableAt (by simp)) htime
  have hbound : ∀ᶠ a in 𝓝 b,
      lCost F.S 0 p (alpha a) (a ^ 2) ≤ lRegularizedAction F.S 0 alpha 0 a := by
    filter_upwards [eventually_gt_nhds hb] with a ha
    have hscalar : ∀ s ∈ Icc (0 : ℝ) (a ^ 2), ∀ y : F.M,
        0 ≤ F.S.scalar (0 - s) y := by
      obtain ⟨C, hC⟩ := hF.globalScalarBound
      intro s hs y
      exact (hC (0 - s) (by change 0 - s ≤ 0; linarith [hs.1]) y).1
    simpa only [Real.sqrt_sq ha.le, hstart] using
      lCost_le_lRegularizedAction_of_scalar_nonneg F.S (sq_nonneg a)
        hscalar alpha halpha
  have hmin : IsLocalMin
      (fun a ↦ lRegularizedAction F.S 0 alpha 0 a -
        lCost F.S 0 p (alpha a) (a ^ 2)) b := by
    change ∀ᶠ a in 𝓝 b,
      lRegularizedAction F.S 0 alpha 0 b - lCost F.S 0 p (alpha b) (b ^ 2) ≤
        lRegularizedAction F.S 0 alpha 0 a - lCost F.S 0 p (alpha a) (a ^ 2)
    rw [hcost, sub_self]
    exact hbound.mono fun _ ha ↦ sub_nonneg.mpr ha
  have hcontact := hmin.hasDerivAt_eq_zero (hact.sub hcurve)
  let v : TangentSpace I q := lVelocity (I := I) alpha b
  have hpair : dt + g.inner q w v =
      (1 / 2 : ℝ) * g.inner q v v + 2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q := by
    have hmetric : g.inner (alpha b) = g.inner q := congrArg _ hend
    have hgrad : (gradientFun g (fun y ↦ lCost F.S 0 p y (b ^ 2)) (alpha b) : E) = w :=
      congrArg (fun y ↦ (gradientFun g (fun z ↦ lCost F.S 0 p z (b ^ 2)) y : E)) hend
    simp only [lRegularizedLagrangian, zero_sub, hend] at hcontact
    change (1 / 2 : ℝ) * g.inner (alpha b) v v +
      2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q -
      (dt + g.inner (alpha b)
        (gradientFun g (fun y ↦ lCost F.S 0 p y (b ^ 2)) (alpha b)) v) = 0 at hcontact
    rw [hmetric, hgrad] at hcontact
    change (1 / 2 : ℝ) * g.inner q v v + 2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q -
      (dt + g.inner q w v) = 0 at hcontact
    linarith
  have hnonneg := DifferentialGeometry.metric_inner_self_nonneg g q (v - w)
  have hsymm : g.inner q v w = g.inner q w v := g.symm q v w
  simp only [map_sub, sub_apply, hsymm] at hnonneg
  change dt + (1 / 2 : ℝ) * g.inner q w w -
    2 * b ^ 2 * F.S.scalar (-(b ^ 2)) q = 0
  linarith

theorem ancient_redLength_hamilton_jacobi_eq_of_mdifferentiableAt
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M)
    (hdiff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ redLength F.S 0 p z.2 z.1) (tau, q)) :
    deriv (fun a ↦ redLength F.S 0 p q a) tau +
        (1 / 2 : ℝ) * (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (fun y ↦ redLength F.S 0 p y tau) q)
          (gradientFun (F.S.base.metric (-tau)) (fun y ↦ redLength F.S 0 p y tau) q) -
        (1 / 2 : ℝ) * F.S.scalar (-tau) q + redLength F.S 0 p q tau / (2 * tau) = 0 := by
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  let phi : ℝ → F.M → ℝ := fun a y ↦ redLength F.S 0 p y a
  let psi : ℝ → F.M → ℝ := fun a y ↦ 2 * a * phi (a ^ 2) y
  have hmap : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (fun z : ℝ × F.M ↦ (z.1 ^ 2, z.2)) (b, q) :=
    (mdifferentiableAt_fst.pow 2).prodMk mdifferentiableAt_snd
  have hcomp : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ phi (z.1 ^ 2) z.2) (b, q) :=
    hdiff.comp_of_eq (b, q) hmap (by rw [hb2])
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M ↦ psi z.1 z.2) (b, q) :=
    (mdifferentiableAt_const.mul mdifferentiableAt_fst).mul hcomp
  have hscale (a : ℝ) (ha : 0 < a) (y : F.M) :
      lCost F.S 0 p y (a ^ 2) = psi a y := by
    change lCost F.S 0 p y (a ^ 2) = 2 * a * redLength F.S 0 p y (a ^ 2)
    simp only [redLength, Real.sqrt_sq ha.le]
    field_simp
  have hcostPsi : (fun z : ℝ × F.M ↦ lCost F.S 0 p z.2 (z.1 ^ 2))
      =ᶠ[𝓝 (b, q)] (fun z ↦ psi z.1 z.2) := by
    have hpos : ∀ᶠ z : ℝ × F.M in 𝓝 (b, q), 0 < z.1 :=
      continuous_fst.continuousAt.tendsto.eventually (eventually_gt_nhds hb)
    exact hpos.mono fun z hz ↦ hscale z.1 hz z.2
  have hcostMD := hpsi.congr_of_eventuallyEq hcostPsi
  have hHJ := ancient_lCost_hamilton_jacobi_eq_of_mdifferentiableAt F hF hb p q hcostMD
  have htime : HasDerivAt (fun a ↦ phi a q) (deriv (fun a ↦ phi a q) tau) tau := by
    have htmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun a ↦ phi a q) tau :=
      hdiff.comp tau (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    exact htmd.differentiableAt.hasDerivAt
  have hpsitime : HasDerivAt (fun a ↦ psi a q)
      (2 * phi tau q + 4 * tau * deriv (fun a ↦ phi a q) tau) b := by
    have htimeb : HasDerivAt (fun a ↦ phi a q) (deriv (fun a ↦ phi a q) tau) (b ^ 2) := by
      rw [hb2]
      exact htime
    have hsq : HasDerivAt (fun a : ℝ ↦ a ^ 2) (2 * b) b := by
      simpa using hasDerivAt_pow 2 b
    have h := ((hasDerivAt_id b).const_mul 2).mul (htimeb.comp b (h := fun a : ℝ ↦ a ^ 2) hsq)
    apply h.congr_deriv
    simp only [id_eq, Function.comp_apply, hb2, mul_one]
    calc
      2 * phi tau q + 2 * b * (deriv (fun a ↦ phi a q) tau * (2 * b)) =
          2 * phi tau q + 4 * b ^ 2 * deriv (fun a ↦ phi a q) tau := by ring
      _ = _ := by rw [hb2]
  have hcostTime : HasDerivAt (fun a ↦ lCost F.S 0 p q (a ^ 2))
      (2 * phi tau q + 4 * tau * deriv (fun a ↦ phi a q) tau) b :=
    hpsitime.congr_of_eventuallyEq
      ((eventually_gt_nhds hb).mono fun a ha ↦ hscale a ha q)
  have hspace : MDifferentiableAt I 𝓘(ℝ, ℝ) (phi tau) q :=
    hdiff.comp q (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hgrad : gradientFun (F.S.base.metric (-(b ^ 2)))
      (fun y ↦ lCost F.S 0 p y (b ^ 2)) q =
      (2 * b) • gradientFun (F.S.base.metric (-tau)) (phi tau) q := by
    have hfun : (fun y ↦ lCost F.S 0 p y (b ^ 2)) = psi b :=
      funext (hscale b hb)
    rw [hfun, hb2]
    change gradientFun (F.S.base.metric (-tau)) ((2 * b) • phi (b ^ 2)) q = _
    rw [hb2, gradientFun_const_smul _ _ hspace]
  rw [hcostTime.deriv, hgrad, hb2,
    DifferentialGeometry.SmoothRiemannianMetric.metric_inner_smul_self] at hHJ
  have halgebra : 4 * tau *
      (deriv (fun a ↦ phi a q) tau +
        (1 / 2 : ℝ) * (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q)
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q) -
        (1 / 2 : ℝ) * F.S.scalar (-tau) q + phi tau q / (2 * tau)) =
      2 * phi tau q + 4 * tau * deriv (fun a ↦ phi a q) tau +
        (1 / 2 : ℝ) * (2 * b) ^ 2 * (F.S.base.metric (-tau)).inner q
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q)
          (gradientFun (F.S.base.metric (-tau)) (phi tau) q) -
        2 * tau * F.S.scalar (-tau) q := by
    have hs : (2 * b) ^ 2 = 4 * tau := by nlinarith [hb2]
    rw [hs]
    field_simp
    ring
  have hzero := halgebra.trans (by simpa only [mul_assoc] using hHJ)
  exact (mul_eq_zero.mp hzero).resolve_left (by positivity)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
