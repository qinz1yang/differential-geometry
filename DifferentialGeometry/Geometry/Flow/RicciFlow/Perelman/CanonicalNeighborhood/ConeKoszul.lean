import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance angularOneNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance angularOneNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance angularTwoNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  inferInstance
local instance angularTwoNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance productOneNormedAddCommGroup : NormedAddCommGroup ((ℝ × V) →L[ℝ] ℝ) :=
  inferInstance
local instance productOneNormedSpace : NormedSpace ℝ ((ℝ × V) →L[ℝ] ℝ) := inferInstance
local instance productTwoNormedAddCommGroup :
    NormedAddCommGroup ((ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ) := inferInstance
local instance productTwoNormedSpace :
    NormedSpace ℝ ((ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ) := inferInstance


def coneAngularForm (B : V →L[ℝ] V →L[ℝ] ℝ) :
    (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.snd ℝ ℝ V)).comp
    (B.comp (ContinuousLinearMap.snd ℝ ℝ V))

@[simp] theorem coneAngularForm_apply (B : V →L[ℝ] V →L[ℝ] ℝ)
    (v w : ℝ × V) : coneAngularForm B v w = B v.2 w.2 := by
  rfl


def coneForm (h : V → V →L[ℝ] V →L[ℝ] ℝ) (z : ℝ × V) :
    (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).smulRight (ContinuousLinearMap.fst ℝ ℝ V) +
    z.1 ^ 2 • coneAngularForm (h z.2)

@[simp] theorem coneForm_apply (h : V → V →L[ℝ] V →L[ℝ] ℝ)
    (z v w : ℝ × V) :
    coneForm h z v w = v.1 * w.1 + z.1 ^ 2 * h z.2 v.2 w.2 := by
  rfl

theorem coneForm_differentiableAt
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) : DifferentiableAt ℝ (coneForm h) z := by
  have ha : DifferentiableAt ℝ (fun y : ℝ × V => coneAngularForm (h y.2)) z :=
    (differentiableAt_const _).clm_comp
      ((hh.comp z differentiableAt_snd).clm_comp (differentiableAt_const _))
  exact (differentiableAt_const _).add ((differentiableAt_fst.pow 2).smul ha)


theorem fderiv_coneForm_apply
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) (v w u : ℝ × V) :
    fderiv ℝ (coneForm h) z v w u =
      2 * z.1 * v.1 * h z.2 w.2 u.2 +
        z.1 ^ 2 * fderiv ℝ h z.2 v.2 w.2 u.2 := by
  have hw : HasFDerivAt (fun _ : ℝ × V => w) 0 z :=
    hasFDerivAt_const (𝕜 := ℝ) w z
  have hu : HasFDerivAt (fun _ : ℝ × V => u) 0 z :=
    hasFDerivAt_const (𝕜 := ℝ) u z
  have heval := ((coneForm_differentiableAt hh).hasFDerivAt.clm_apply hw).clm_apply hu
  have heq : fderiv ℝ (fun y : ℝ × V => coneForm h y w u) z v =
      fderiv ℝ (coneForm h) z v w u := by
    simpa using DFunLike.congr_fun heval.fderiv v
  have hc : HasFDerivAt (fun y : ℝ × V => h y.2)
      ((fderiv ℝ h z.2).comp (ContinuousLinearMap.snd ℝ ℝ V)) z :=
    hh.hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hfirst := hc.clm_apply (hasFDerivAt_const (𝕜 := ℝ) w.2 z)
  have hangular := hfirst.clm_apply (hasFDerivAt_const (𝕜 := ℝ) u.2 z)
  have hformula := (hasFDerivAt_const (𝕜 := ℝ) (w.1 * u.1) z).add
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).pow 2).mul hangular)
  simp only [coneForm_apply] at heq
  erw [hformula.fderiv] at heq
  simpa [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, add_comm] using heq.symm


theorem koszulCov_coneForm_radial
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) (v u : ℝ × V) :
    MetricKoszul.koszulCov (fderiv ℝ (coneForm h) z) v (1, 0) u =
      z.1 * h z.2 v.2 u.2 := by
  rw [MetricKoszul.koszul_cov_apply]
  simp only [fderiv_coneForm_apply hh, map_zero,
    zero_apply, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  ring

theorem koszulCov_coneForm_radial_eq
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) (hr : z.1 ≠ 0) (v : ℝ × V) :
    MetricKoszul.koszulCov (fderiv ℝ (coneForm h) z) v (1, 0) =
      coneForm h z (0, z.1⁻¹ • v.2) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [koszulCov_coneForm_radial hh, coneForm_apply]
  simp only [zero_mul, zero_add, map_smul, smul_apply, smul_eq_mul]
  field_simp [hr]

variable [FiniteDimensional ℝ V]

theorem leviCivita_radial_of_coneForm
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : DifferentiableAt ℝ h z.2) (hr : z.1 ≠ 0) (v : ℝ × V) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z
      ((leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
        (constantModelVectorField (1, 0)) z)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z).symm v)) =
      (0, z.1⁻¹ • v.2) := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z
  let a := (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
    (constantModelVectorField (1, 0)) z) (e.symm v)
  have hflat := const_flat_eq_nhds g (coneForm h) hmetric
    (coneForm_differentiableAt hh) v (1, 0)
  rw [koszulCov_coneForm_radial_eq hh hr] at hflat
  have hmetric0 := hmetric.self_of_nhds
  have ha : a = e.symm (0, z.1⁻¹ • v.2) := by
    apply tangentFlatLinear_injective_gen (I := 𝓘(ℝ, ℝ × V)) g z
    ext w
    have hpair := DFunLike.congr_fun hflat (e w)
    rw [← hmetric0, tangentBilinearFormToModel_apply,
      tangentBilinearFormToModel_apply] at hpair
    simpa only [e, a, ContinuousLinearEquiv.symm_apply_apply,
      tangentFlatLinear_apply_gen] using hpair
  change e a = _
  rw [ha, e.apply_symm_apply]


def coneEulerField (z : ℝ × V) : TangentSpace 𝓘(ℝ, ℝ × V) z :=
  z.1 • constantModelVectorField (1, 0) z

omit [FiniteDimensional ℝ V] in
theorem coneEulerField_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ × V).tangent) ∞
      (T% (coneEulerField (V := V))) := by
  apply contMDiff_vectorSpace_iff_contDiff.mpr
  exact contDiff_fst.smul contDiff_const


theorem leviCivita_coneEuler_of_coneForm
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : DifferentiableAt ℝ h z.2) (hr : z.1 ≠ 0)
    (v : TangentSpace 𝓘(ℝ, ℝ × V) z) :
    (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
      (coneEulerField (V := V)) z) v = v := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z
  let vModel : ℝ × V := e v
  have hrad : ContMDiff 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ × V).tangent) ∞
      (T% (constantModelVectorField (𝕜 := ℝ) ((1 : ℝ), (0 : V)))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hleib :=
    (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g).isCovariantDerivativeOnUniv.leibniz
      (x := z) (g := fun y : ℝ × V => y.1)
      (hrad.contMDiffAt.mdifferentiableAt (by simp))
      (differentiableAt_fst.mdifferentiableAt)
  have hradial : (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
      (constantModelVectorField (1, 0)) z) v = e.symm (0, z.1⁻¹ • vModel.2) := by
    apply e.injective
    simpa only [vModel, e, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply] using
      leviCivita_radial_of_coneForm g hmetric hh hr vModel
  have hdf : mvfderiv (I := 𝓘(ℝ, ℝ × V)) (fun y : ℝ × V => y.1) z v = vModel.1 := by
    rw [mvfderiv_model_apply_eq_fderiv, (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).fderiv]
    rfl
  have hEuler : coneEulerField (V := V) =
      (fun y : ℝ × V => y.1) • constantModelVectorField ((1 : ℝ), (0 : V)) := rfl
  rw [hEuler, hleib]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hdf]
  rw [hradial]
  apply e.injective
  simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  change z.1 • (0, z.1⁻¹ • vModel.2) + vModel.1 • (1, (0 : V)) = vModel
  ext <;> simp [smul_smul, hr]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
