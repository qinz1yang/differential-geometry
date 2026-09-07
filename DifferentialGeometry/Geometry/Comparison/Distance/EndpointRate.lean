import DifferentialGeometry.Geometry.Exponential.GaussLemma.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Calculus (psd_sqrt_lipschitz)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space (TangentBundle I M)] in
private lemma riemannianEDistOf_comm
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y = riemannianEDistOf (I := I) g y x := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  simpa only [riemannianEDistOf] using
    (Manifold.riemannianEDist_comm (I := I) (x := x) (y := y))

theorem riemannianEDistOf_div_tendsto_speed
    (g : SmoothRiemannianMetric I M) (gamma : Real → M) (tau : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau) :
    Tendsto
      (fun h : Real ↦
        (riemannianEDistOf (I := I) g (gamma (tau + h)) (gamma tau)).toReal / h)
      (nhdsWithin (0 : Real) (Ioi 0))
      (nhds (Real.sqrt
        (g.inner (gamma tau)
          (mfderiv 𝓘(Real, Real) I gamma tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma tau (1 : Real))))) := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let p : M := gamma tau
  let psi := NormalCoordinates.normalChartAt (I := I) g p
  let c : Real → E := fun s ↦ psi (gamma s)
  let v : E := mfderiv 𝓘(Real, Real) I gamma tau (1 : Real)
  let B : E →L[Real] E →L[Real] Real := g.inner p
  let nE : E → Real := fun w ↦ Real.sqrt (B w w)
  have hpSrc : p ∈ psi.source := by
    exact NormalCoordinates.normalChartAt_source (I := I) g p
  have hpsi : MDifferentiableAt I 𝓘(Real, E) psi p :=
    ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
      one_ne_zero p hpSrc).mdifferentiableAt
        ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds hpSrc)
  have hc : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) c tau := by
    exact hpsi.comp tau hgamma
  have hc0 : c tau = 0 := by
    simpa only [c, p] using NormalCoordinates.normalChartAt_centre (I := I) g p
  have hcv : mfderiv 𝓘(Real, Real) 𝓘(Real, E) c tau (1 : Real) = v := by
    rw [show c = psi ∘ gamma from rfl, mfderiv_comp tau hpsi hgamma]
    rw [show gamma tau = p from rfl,
      NormalCoordinates.mfderiv_normalChartAt_self (I := I) g p]
    rfl
  have hcDeriv : HasDerivAt c v tau := by
    have hmf := hc.hasMFDerivAt
    rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
    have hda := @HasFDerivAt.hasDerivAt Real _ E _ _ _ c tau
      IsBoundedSMul.continuousSMul _ hmf
    exact hda.congr_deriv hcv
  have hBsym : ∀ w z : E, B w z = B z w := fun w z ↦ g.symm p w z
  have hBnn : ∀ w : E, 0 ≤ B w w := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp only [map_zero]
      exact le_rfl
    · exact (g.pos p w hw).le
  have hnCont : Continuous nE :=
    (psd_sqrt_lipschitz B hBsym hBnn).continuous
  have hnSmul : ∀ {a : Real}, 0 ≤ a → ∀ w : E, nE (a • w) = a * nE w := by
    intro a ha w
    change Real.sqrt (g.inner p (a • (show TangentSpace I p from w))
      (a • (show TangentSpace I p from w))) =
      a * Real.sqrt (g.inner p (show TangentSpace I p from w)
        (show TangentSpace I p from w))
    simpa only [abs_of_nonneg ha] using
      sqrt_inner_smul (I := I) g p a (show TangentSpace I p from w)
  have hspeed : nE v = Real.sqrt (g.inner p v v) := rfl
  change Tendsto
    (fun h : Real ↦
      (riemannianEDistOf (I := I) g (gamma (tau + h)) p).toReal / h)
    (nhdsWithin (0 : Real) (Ioi 0)) (nhds (nE v))
  have hslope : Tendsto
      (fun h : Real ↦ h⁻¹ • (c (tau + h) - c tau))
      (nhdsWithin (0 : Real) (Ioi 0)) (nhds v) :=
    hcDeriv.tendsto_slope_zero_right
  have hnSlope : Tendsto
      (fun h : Real ↦ nE (h⁻¹ • (c (tau + h) - c tau)))
      (nhdsWithin (0 : Real) (Ioi 0)) (nhds (nE v)) :=
    hnCont.continuousAt.tendsto.comp hslope
  have hadd : Tendsto (fun h : Real ↦ tau + h) (nhds 0) (nhds tau) := by
    simpa only [id_eq, add_zero] using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun h : Real ↦ tau + h) (nhds 0) (nhds (tau + 0)))
  have harg : Tendsto (fun h : Real ↦ gamma (tau + h)) (nhds 0) (nhds p) := by
    exact hgamma.continuousAt.tendsto.comp hadd
  have hsrc : ∀ᶠ h in nhds 0, gamma (tau + h) ∈ psi.source :=
    harg.eventually
      ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds hpSrc)
  have hcArg : Tendsto (fun h : Real ↦ c (tau + h)) (nhds 0) (nhds 0) := by
    simpa only [hc0, Function.comp_def] using hc.continuousAt.tendsto.comp hadd
  have hnArg : Tendsto (fun h : Real ↦ nE (c (tau + h))) (nhds 0) (nhds 0) := by
    simpa only [nE, map_zero, Real.sqrt_zero, Function.comp_def] using
      hnCont.continuousAt.tendsto.comp hcArg
  have hrad : ∀ᶠ h in nhds 0,
      nE (c (tau + h)) < metricCoerciveExpRadius (I := I) g p :=
    hnArg.eventually (Iio_mem_nhds (metricCoerciveExpRadius_pos (I := I) g p))
  refine hnSlope.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    hsrc.filter_mono inf_le_left, hrad.filter_mono inf_le_left] with h hh hs hr
  have hhpos : 0 < h := hh
  have hhne : h ≠ 0 := ne_of_gt hhpos
  have hcTarget : c (tau + h) ∈ psi.target := psi.map_source hs
  have hgammaExp : gamma (tau + h) =
      expMap (I := I) g p (show TangentSpace I p from c (tau + h)) := by
    calc
      gamma (tau + h) = psi.symm (c (tau + h)) := (psi.left_inv hs).symm
      _ = expMap (I := I) g p
          (show TangentSpace I p from c (tau + h)) :=
        NormalCoordinates.normalChartAt_symm_apply (I := I) g p hcTarget
  have hdist : riemannianEDistOf (I := I) g (gamma (tau + h)) p =
      ENNReal.ofReal (nE (c (tau + h))) := by
    calc
      riemannianEDistOf (I := I) g (gamma (tau + h)) p =
          riemannianEDistOf (I := I) g p (gamma (tau + h)) := by
        exact riemannianEDistOf_comm (I := I) g _ _
      _ = ENNReal.ofReal (nE (c (tau + h))) := by
        rw [hgammaExp]
        change riemannianEDistOf (I := I) g p
            (expMap (I := I) g p
              (show TangentSpace I p from c (tau + h))) =
          ENNReal.ofReal (Real.sqrt (g.inner p (c (tau + h)) (c (tau + h))))
        exact edist_exp_eq_radius_of_metric (I := I) g p hr
  have hnnonneg : 0 ≤ nE (c (tau + h)) := by
    dsimp only [nE]
    exact Real.sqrt_nonneg _
  rw [hdist, ENNReal.toReal_ofReal hnnonneg, hc0, sub_zero]
  rw [hnSmul (inv_nonneg.mpr hhpos.le)]
  field_simp

end DifferentialGeometry.Geometry.Riemannian

end
