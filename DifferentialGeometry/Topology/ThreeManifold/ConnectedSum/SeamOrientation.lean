import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SmoothStructure
import Mathlib.Analysis.InnerProductSpace.Calculus
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Intrinsic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Manifold ContDiff Topology InnerProductSpace
open Module
open Set Function Manifold Metric
noncomputable section

namespace DifferentialGeometry.Topology
namespace ConnectedSumQuotient

private local instance csFact : Fact (Module.finrank ℝ csModel = 2 + 1) := ⟨by simp⟩

private theorem hasFDerivAt_norm_aux {y : csModel} (hy : y ≠ 0) :
    HasFDerivAt (fun x : csModel => ‖x‖) (innerSL ℝ ((‖y‖)⁻¹ • y)) y := by
  have hsq : HasFDerivAt (fun x : csModel => ‖x‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖y‖ ^ 2))) (‖y‖ ^ 2) :=
    Real.hasDerivAt_sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy))
  have hcomp := hsqrt.hasFDerivAt.comp y hsq
  have hfun : (Real.sqrt ∘ fun x : csModel => ‖x‖ ^ 2) = fun x : csModel => ‖x‖ := by
    funext x
    exact Real.sqrt_sq (norm_nonneg x)
  rw [hfun] at hcomp
  have hf' : ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖y‖ ^ 2))) ∘SL
      (2 • innerSL ℝ y) = innerSL ℝ ((‖y‖)⁻¹ • y) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      innerSL_apply_apply, real_inner_smul_left, smul_apply]
    rw [Real.sqrt_sq (norm_nonneg y), nsmul_eq_mul, smul_eq_mul]
    field_simp
    ring
  rw [hf'] at hcomp
  exact hcomp

private noncomputable def radialDeriv (y : csModel) : csModel →L[ℝ] csModel :=
  (‖y‖)⁻¹ • ContinuousLinearMap.id ℝ csModel +
    (((innerSL ℝ ((‖y‖)⁻¹ • y)).smulRight (-((‖y‖)⁻¹)^2)).smulRight y)

private theorem hasFDerivAt_radial {y : csModel} (hy : y ≠ 0) :
    HasFDerivAt (fun x : csModel => (‖x‖)⁻¹ • x) (radialDeriv y) y := by
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-((‖y‖)⁻¹)^2) ‖y‖ := by
    have h := hasDerivAt_inv (x := ‖y‖) (norm_ne_zero_iff.mpr hy)
    simpa [inv_pow] using h
  have hcomp := hinv.hasFDerivAt.comp y (hasFDerivAt_norm_aux hy)
  have hc : HasFDerivAt (fun x : csModel => (‖x‖)⁻¹)
      ((innerSL ℝ ((‖y‖)⁻¹ • y)).smulRight (-((‖y‖)⁻¹)^2)) y := by
    rw [ContinuousLinearMap.toSpanSingleton_comp] at hcomp
    exact hcomp
  have hf : HasFDerivAt (fun x : csModel => x) (ContinuousLinearMap.id ℝ csModel) y :=
    hasFDerivAt_id y
  have h := hc.smul hf
  have hfun : ((fun x : csModel => (‖x‖)⁻¹) • (fun x : csModel => x)) =
      fun x : csModel => (‖x‖)⁻¹ • x := by
    funext x
    rfl
  exact h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)

private theorem radial_norm_inv_self {y : csModel} (hy : y ≠ 0) :
    ‖((‖y‖)⁻¹ • y : csModel)‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

theorem fderiv_radial_self {y : csModel} (hy : y ≠ 0) :
    fderiv ℝ (fun x : csModel => (‖x‖)⁻¹ • x) y ((‖y‖)⁻¹ • y) = 0 := by
  rw [(hasFDerivAt_radial hy).fderiv]
  have hinner : ⟪((‖y‖)⁻¹ • y : csModel), ((‖y‖)⁻¹ • y : csModel)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, radial_norm_inv_self hy, mul_one]
  simp only [radialDeriv, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [hinner]
  simp only [one_smul]
  rw [smul_smul]
  rw [show (‖y‖)⁻¹ * (‖y‖)⁻¹ = ((‖y‖)⁻¹)^2 from by ring]
  rw [neg_smul, add_neg_cancel]

theorem fderiv_radial_eq_of_orthogonal {y v : csModel} (hy : y ≠ 0)
    (hv : ⟪(‖y‖)⁻¹ • y, v⟫_ℝ = 0) :
    fderiv ℝ (fun x : csModel => (‖x‖)⁻¹ • x) y v = (‖y‖)⁻¹ • v := by
  rw [(hasFDerivAt_radial hy).fderiv]
  simp only [radialDeriv, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [hv]
  simp

theorem unitVecFun_coe_eventuallyEq {y : csModel} (hy : y ≠ 0) :
    ((↑) : csSphere → csModel) ∘ unitVecFun =ᶠ[𝓝 y] (fun x : csModel => (‖x‖)⁻¹ • x) := by
  refine Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hy) fun x hx => ?_
  rw [Function.comp_apply, unitVecFun_of_ne hx]
  rfl

theorem mvfderiv_unitVecFun_eq_radial {y : csModel} (hy : y ≠ 0) (v : csModel) :
    Geometry.dIncl (n := 2) (unitVecFun y) (mfderiv (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y v)
      = fderiv ℝ (fun x : csModel => (‖x‖)⁻¹ • x) y v := by
  have hu : MDifferentiableAt (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y :=
    (contMDiffAt_unitVecFun_self y hy).mdifferentiableAt (by simp)
  have hincl : MDifferentiableAt (𝓡 2) (𝓡 3) ((↑) : csSphere → csModel) (unitVecFun y) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply (x := y) hincl hu v
  rw [Filter.EventuallyEq.mfderiv_eq (unitVecFun_coe_eventuallyEq hy)] at hc
  rw [mfderiv_eq_fderiv] at hc
  change mfderiv (𝓡 2) (𝓡 3) ((↑) : csSphere → csModel) (unitVecFun y)
      (mfderiv (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y v)
      = fderiv ℝ (fun x : csModel => (‖x‖)⁻¹ • x) y v
  exact hc.symm

theorem dIncl_unitVecFun_injective (y : csModel) :
    Function.Injective (Geometry.dIncl (n := 2) (unitVecFun y)) := by
  have h := injective_mvfderiv_subtypeVal_sphere (n := 2) (unitVecFun y)
  have hd : Geometry.dIncl (n := 2) (unitVecFun y)
      = mvfderiv (𝓡 2) ((↑) : csSphere → csModel) (unitVecFun y) := rfl
  rwa [hd]

theorem coe_unitVecFun_eq {y : csModel} (hy : y ≠ 0) :
    ((unitVecFun y : csSphere) : csModel) = (‖y‖)⁻¹ • y := by
  rw [unitVecFun_of_ne hy]
  rfl

theorem mfderiv_unitVecFun_self {y : csModel} (hy : y ≠ 0) :
    mfderiv (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y ((‖y‖)⁻¹ • y) = 0 := by
  refine dIncl_unitVecFun_injective y ?_
  rw [map_zero, mvfderiv_unitVecFun_eq_radial hy, fderiv_radial_self hy]

theorem mfderiv_unitVecFun_eq_smul {y : csModel} (hy : y ≠ 0)
    (b : TangentSpace (𝓡 2) (unitVecFun y)) :
    mfderiv (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y (Geometry.dIncl (n := 2) (unitVecFun y) b)
      = (‖y‖)⁻¹ • b := by
  refine dIncl_unitVecFun_injective y ?_
  rw [mvfderiv_unitVecFun_eq_radial hy,
    fderiv_radial_eq_of_orthogonal hy (v := Geometry.dIncl (n := 2) (unitVecFun y) b) ?_,
    map_smul]
  rw [← coe_unitVecFun_eq hy]
  exact DifferentialGeometry.Geometry.dIncl_orth (n := 2) (unitVecFun y) b

variable (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)

private noncomputable def pushCoe : csModel → csModel :=
  fun x => ((a (unitVecFun x) : csSphere) : csModel)

theorem mfderiv_pushCoe_apply {y : csModel} (hy : y ≠ 0) (v : csModel) :
    mfderiv (𝓘(ℝ, csModel)) (𝓡 3) (pushCoe a) y v =
      Geometry.dIncl (n := 2) (a (unitVecFun y))
        (mfderiv (𝓡 2) (𝓡 2) a (unitVecFun y)
          (mfderiv (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y v)) := by
  have hu : MDifferentiableAt (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y :=
    (contMDiffAt_unitVecFun_self y hy).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt (𝓡 2) (𝓡 2) a (unitVecFun y) :=
    a.contMDiff.mdifferentiableAt (by simp)
  have hincl : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : csSphere → csModel)
      (a (unitVecFun y)) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have h1 := mfderiv_comp_apply (x := y) hincl (ha.comp y hu) v
  have h2 := mfderiv_comp_apply (x := y) ha hu v
  rw [h2] at h1
  have hfun : (Subtype.val : csSphere → csModel) ∘ (a ∘ unitVecFun) = pushCoe a := rfl
  rw [hfun] at h1
  exact h1

theorem fderiv_pushCoe_self {y : csModel} (hy : y ≠ 0) :
    fderiv ℝ (pushCoe a) y ((‖y‖)⁻¹ • y) = 0 := by
  have h := mfderiv_pushCoe_apply a hy ((‖y‖)⁻¹ • y)
  rw [mfderiv_unitVecFun_self hy, map_zero] at h
  simp only [mfderiv_eq_fderiv, map_zero] at h
  exact h

theorem fderiv_pushCoe_dIncl {y : csModel} (hy : y ≠ 0)
    (b : TangentSpace (𝓡 2) (unitVecFun y)) :
    fderiv ℝ (pushCoe a) y (Geometry.dIncl (n := 2) (unitVecFun y) b) =
      (‖y‖)⁻¹ • Geometry.dIncl (n := 2) (a (unitVecFun y))
        (mfderiv (𝓡 2) (𝓡 2) a (unitVecFun y) b) := by
  have h := mfderiv_pushCoe_apply a hy (Geometry.dIncl (n := 2) (unitVecFun y) b)
  rw [mfderiv_unitVecFun_eq_smul hy b] at h
  simp only [mfderiv_eq_fderiv, map_smul] at h
  exact h

theorem differentiableAt_pushCoe {y : csModel} (hy : y ≠ 0) :
    DifferentiableAt ℝ (pushCoe a) y := by
  have hu : MDifferentiableAt (𝓘(ℝ, csModel)) (𝓡 2) unitVecFun y :=
    (contMDiffAt_unitVecFun_self y hy).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt (𝓡 2) (𝓡 2) a (unitVecFun y) :=
    a.contMDiff.mdifferentiableAt (by simp)
  have hincl : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : csSphere → csModel)
      (a (unitVecFun y)) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have hmd : MDifferentiableAt (𝓘(ℝ, csModel)) (𝓡 3) (pushCoe a) y :=
    hincl.comp y (ha.comp y hu)
  rwa [mdifferentiableAt_iff_differentiableAt] at hmd

theorem hasFDerivAt_pushCoe {y : csModel} (hy : y ≠ 0) :
    HasFDerivAt (pushCoe a) (fderiv ℝ (pushCoe a) y) y :=
  (differentiableAt_pushCoe a hy).hasFDerivAt

theorem hasFDerivAt_reflectMap {y : csModel} (hy : y ≠ 0) :
    HasFDerivAt (reflectMap a.toHomeomorph)
      ((2 - ‖y‖) • fderiv ℝ (pushCoe a) y +
        (-(innerSL ℝ ((‖y‖)⁻¹ • y))).smulRight (pushCoe a y)) y := by
  have h1 : HasFDerivAt (fun x : csModel => 2 - ‖x‖) (-(innerSL ℝ ((‖y‖)⁻¹ • y))) y := by
    have h := (hasFDerivAt_const (c := (2 : ℝ)) y).sub (hasFDerivAt_norm_aux hy)
    rw [zero_sub] at h
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext x
    rfl
  have h2 := hasFDerivAt_pushCoe a hy
  have h := h1.smul h2
  have hfun : ((fun x : csModel => 2 - ‖x‖) • pushCoe a) = reflectMap a.toHomeomorph := by
    funext x
    rw [reflectMap]
    rfl
  exact h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)

theorem fderiv_reflectMap_self {y : csModel} (hy : y ≠ 0) :
    fderiv ℝ (reflectMap a.toHomeomorph) y ((‖y‖)⁻¹ • y) = - pushCoe a y := by
  have hinner : ⟪((‖y‖)⁻¹ • y : csModel), ((‖y‖)⁻¹ • y : csModel)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, radial_norm_inv_self hy, mul_one]
  rw [(hasFDerivAt_reflectMap a hy).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, neg_apply, fderiv_pushCoe_self a hy, smul_zero, zero_add, hinner,
    neg_one_smul]

theorem fderiv_reflectMap_dIncl {y : csModel} (hy : y ≠ 0)
    (b : TangentSpace (𝓡 2) (unitVecFun y)) :
    fderiv ℝ (reflectMap a.toHomeomorph) y (Geometry.dIncl (n := 2) (unitVecFun y) b) =
      ((2 - ‖y‖) * (‖y‖)⁻¹) • Geometry.dIncl (n := 2) (a (unitVecFun y))
        (mfderiv (𝓡 2) (𝓡 2) a (unitVecFun y) b) := by
  have hinner : ⟪((‖y‖)⁻¹ • y : csModel), Geometry.dIncl (n := 2) (unitVecFun y) b⟫_ℝ = 0 := by
    rw [← coe_unitVecFun_eq hy]
    exact DifferentialGeometry.Geometry.dIncl_orth (n := 2) (unitVecFun y) b
  rw [(hasFDerivAt_reflectMap a hy).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, neg_apply, fderiv_pushCoe_dIncl a hy b, hinner, neg_zero, zero_smul,
    add_zero, smul_smul]

private noncomputable def stdBasis : Module.Basis (Fin 3) ℝ csModel :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem det_stdBasis_apply (v : Fin 3 → csModel) :
    (stdBasis).det v = Matrix.det (fun i j : Fin 3 => (v j) i) :=
  Module.Basis.det_apply (e := stdBasis) v


theorem sphereOutwardDeterminant_ne_zero_aux (x : csSphere)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    sphereOutwardDeterminant 2 x b ≠ 0 := by
  classical
  have hne : (x : csModel) ≠ 0 := by
    intro h
    have hmem := x.2
    rw [h] at hmem
    simp at hmem
  have hnorm : ‖(x : csModel)‖ = 1 := by
    have h := Metric.mem_sphere.mp x.2
    simpa only [dist_zero_right] using h
  let frame : Fin 3 → csModel := fun j =>
    Fin.cases (x : csModel) (fun k => Geometry.dIncl (n := 2) x (b k)) j
  let Φ : csModel →ₗ[ℝ] csModel := stdBasis.constr ℝ frame
  have hΦ : ∀ j, Φ (stdBasis j) = frame j := fun j => stdBasis.constr_basis ℝ frame j
  have hdet : stdBasis.det frame = LinearMap.det Φ := by
    have h := Module.Basis.det_comp stdBasis Φ stdBasis
    rw [show (Φ ∘ stdBasis) = frame from funext fun j => hΦ j,
      Module.Basis.det_self, mul_one] at h
    exact h
  have hdet2 : sphereOutwardDeterminant 2 x b = LinearMap.det Φ := by
    rw [← hdet, det_stdBasis_apply]
    congr 1
  rw [hdet2]
  intro hzero
  have hker : LinearMap.ker Φ ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot (f := Φ)).mp hzero
  apply hker
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hrepr : u = ∑ i : Fin 3, (stdBasis.repr u) i • stdBasis i :=
    (stdBasis.sum_repr u).symm
  have hΦu : Φ u = (stdBasis.repr u) 0 • (x : csModel) +
      Geometry.dIncl (n := 2) x
        (∑ k : Fin 2, (stdBasis.repr u) (Fin.succ k) • b k) := by
    calc Φ u = Φ (∑ i : Fin 3, (stdBasis.repr u) i • stdBasis i) := by conv_lhs => rw [hrepr]
      _ = ∑ i : Fin 3, (stdBasis.repr u) i • Φ (stdBasis i) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      _ = (stdBasis.repr u) 0 • (x : csModel) +
            ∑ k : Fin 2, (stdBasis.repr u) (Fin.succ k) •
              Geometry.dIncl (n := 2) x (b k) := by
            rw [Fin.sum_univ_succ]
            simp only [hΦ, frame, Fin.cases_zero, Fin.cases_succ]
      _ = (stdBasis.repr u) 0 • (x : csModel) +
            Geometry.dIncl (n := 2) x
              (∑ k : Fin 2, (stdBasis.repr u) (Fin.succ k) • b k) := by
            rw [map_sum]
            simp only [map_smul]
  have hzero' : (stdBasis.repr u) 0 • (x : csModel) +
      Geometry.dIncl (n := 2) x
        (∑ k : Fin 2, (stdBasis.repr u) (Fin.succ k) • b k) = 0 := by
    rw [← hΦu, hu]
  have h0 : (stdBasis.repr u) 0 = 0 := by
    have h := congrArg (fun z : csModel => ⟪(x : csModel), z⟫_ℝ) hzero'
    simp only [inner_add_right, inner_smul_right] at h
    rw [real_inner_self_eq_norm_mul_norm, hnorm, mul_one,
      DifferentialGeometry.Geometry.dIncl_orth (n := 2) x, add_zero] at h
    simpa using h
  have htail : ∑ k : Fin 2, (stdBasis.repr u) (Fin.succ k) • b k = 0 := by
    have hz : Geometry.dIncl (n := 2) x
        (∑ k : Fin 2, (stdBasis.repr u) (Fin.succ k) • b k) = 0 := by
      have h := hzero'
      rw [h0, zero_smul, zero_add] at h
      exact h
    exact injective_mvfderiv_subtypeVal_sphere (n := 2) x (by rw [map_zero]; exact hz)
  have hall : ∀ k : Fin 2, (stdBasis.repr u) (Fin.succ k) = 0 := by
    intro k
    have hmap := congrArg (fun w => b.repr w k) htail
    rw [map_sum, map_zero] at hmap
    simp only [map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul] at hmap
    have hval : (∑ l : Fin 2, (stdBasis.repr u) (Fin.succ l) *
        (Finsupp.single l (1 : ℝ)) k) = (stdBasis.repr u) (Fin.succ k) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        rw [Finsupp.single_eq_of_ne hl.symm, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hval] at hmap
    simpa using hmap
  rw [hrepr, Fin.sum_univ_succ, h0, zero_smul, zero_add]
  exact Finset.sum_eq_zero fun k _ => by rw [hall k, zero_smul]

theorem det_fderiv_reflectMap_pos (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (ha : a.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hrpos : 0 < ‖y‖) (hy2 : ‖y‖ < 2) :
    0 < LinearMap.det (fderiv ℝ (reflectMap a.toHomeomorph) y : csModel →ₗ[ℝ] csModel) := by
  classical
  have hy : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hrpos)
  have h2r : 0 < 2 - ‖y‖ := by linarith
  set o : ManifoldOrientation (𝓡 2) csSphere 2 := sphereOrientation 2 (by decide) with ho
  have hfin : Module.Finite ℝ (TangentSpace (𝓡 2) (unitVecFun y)) := by
    change Module.Finite ℝ (EuclideanSpace ℝ (Fin 2))
    infer_instance
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace (𝓡 2) (unitVecFun y)) := by
    change Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
    simp
  let b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (unitVecFun y)) :=
    Orientation.someBasis (o.orientation (unitVecFun y)) hcard
  have hb : b.orientation = o.orientation (unitVecFun y) := Orientation.someBasis_orientation _ _
  have hpos : 0 < sphereOutwardDeterminant 2 (unitVecFun y) b :=
    (sphereOrientation_characterization 2 (by decide) (unitVecFun y) b).mp hb
  let A : TangentSpace (𝓡 2) (unitVecFun y) ≃ₗ[ℝ] TangentSpace (𝓡 2) (a (unitVecFun y)) :=
    (a.mfderivToContinuousLinearEquiv (by simp) (unitVecFun y)).toLinearEquiv
  let c : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (a (unitVecFun y))) := b.map A
  have hc : ∀ k : Fin 2, c k = mfderiv (𝓡 2) (𝓡 2) a (unitVecFun y) (b k) := by
    intro k
    rw [show c k = A (b k) from Module.Basis.map_apply b A k]
    exact congrArg (fun (L : TangentSpace (𝓡 2) (unitVecFun y) →L[ℝ]
      TangentSpace (𝓡 2) (a (unitVecFun y))) => L (b k))
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe a (by simp))
  have hmapc : Orientation.map (Fin 2) A (o.orientation (unitVecFun y)) = c.orientation := by
    rw [← hb]
    exact (Module.Basis.orientation_map b A).symm
  have hne : c.orientation ≠ o.orientation (a (unitVecFun y)) := by
    rw [← hmapc, ha (unitVecFun y)]
    exact fun h => Module.Ray.ne_neg_self (o.orientation (a (unitVecFun y))) h.symm
  have hneg : sphereOutwardDeterminant 2 (a (unitVecFun y)) c < 0 := by
    have hnot : ¬ 0 < sphereOutwardDeterminant 2 (a (unitVecFun y)) c := fun h =>
      hne ((sphereOrientation_characterization 2 (by decide) (a (unitVecFun y)) c).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt hnot)
      (sphereOutwardDeterminant_ne_zero_aux (a (unitVecFun y)) c)
  let xframe : Fin 3 → csModel := fun j => Fin.cases ((unitVecFun y : csSphere) : csModel)
    (fun k => NormedSpace.fromTangentSpace (((unitVecFun y : csSphere) : csModel))
      (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : csSphere → csModel) (unitVecFun y) (b k))) j
  let rframe : Fin 3 → csModel := fun j => Fin.cases ((a (unitVecFun y) : csSphere) : csModel)
    (fun k => NormedSpace.fromTangentSpace (((a (unitVecFun y) : csSphere) : csModel))
      (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : csSphere → csModel) (a (unitVecFun y)) (c k))) j
  have hxdet : stdBasis.det xframe = sphereOutwardDeterminant 2 (unitVecFun y) b := by
    rw [det_stdBasis_apply]
    rfl
  have hrdet : stdBasis.det rframe = sphereOutwardDeterminant 2 (a (unitVecFun y)) c := by
    rw [det_stdBasis_apply]
    rfl
  let d : Fin 3 → ℝ := Fin.cases (-1) (fun _ => (2 - ‖y‖) * (‖y‖)⁻¹)
  have hframe : ((fderiv ℝ (reflectMap a.toHomeomorph) y : csModel →ₗ[ℝ] csModel)) ∘ xframe =
      fun j => d j • rframe j := by
    funext j
    refine Fin.cases ?_ ?_ j
    · change (fderiv ℝ (reflectMap a.toHomeomorph) y)
          (((unitVecFun y : csSphere) : csModel)) =
        d 0 • ((a (unitVecFun y) : csSphere) : csModel)
      rw [coe_unitVecFun_eq hy, fderiv_reflectMap_self a hy]
      simp [d, pushCoe]
    · intro k
      change (fderiv ℝ (reflectMap a.toHomeomorph) y)
          (Geometry.dIncl (n := 2) (unitVecFun y) (b k)) =
        d (Fin.succ k) • Geometry.dIncl (n := 2) (a (unitVecFun y)) (c k)
      rw [fderiv_reflectMap_dIncl a hy (b k), ← hc k]
      simp only [d, Fin.cases_succ]
  have hprod : (∏ j : Fin 3, d j) = -(((2 - ‖y‖) * (‖y‖)⁻¹)) ^ 2 := by
    simp only [d, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  have hkey : LinearMap.det (fderiv ℝ (reflectMap a.toHomeomorph) y : csModel →ₗ[ℝ] csModel) * stdBasis.det xframe =
      -(((2 - ‖y‖) * (‖y‖)⁻¹)) ^ 2 * stdBasis.det rframe := by
    rw [← Module.Basis.det_comp stdBasis
      (fderiv ℝ (reflectMap a.toHomeomorph) y : csModel →ₗ[ℝ] csModel) xframe, hframe,
      AlternatingMap.map_smul_univ, hprod]
    rfl
  have hcpos : 0 < (2 - ‖y‖) * (‖y‖)⁻¹ := mul_pos h2r (inv_pos.mpr hrpos)
  have hP : 0 < stdBasis.det xframe := by rw [hxdet]; exact hpos
  have hR : stdBasis.det rframe < 0 := by rw [hrdet]; exact hneg
  have hrhs : 0 < -(((2 - ‖y‖) * (‖y‖)⁻¹)) ^ 2 * stdBasis.det rframe := by
    have h1 : -(((2 - ‖y‖) * (‖y‖)⁻¹)) ^ 2 < 0 := by
      have h2 : 0 < ((2 - ‖y‖) * (‖y‖)⁻¹) ^ 2 := pow_pos hcpos 2
      linarith
    exact mul_pos_of_neg_of_neg h1 hR
  have := (mul_pos_iff_of_pos_right hP).mp (by rw [hkey]; exact hrhs)
  exact this

theorem reflectMapInv_eq_reflectMap_symm (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    reflectMapInv a.toHomeomorph = reflectMap a.symm.toHomeomorph := by
  funext x
  simp [reflectMap, reflectMapInv]

theorem det_fderiv_reflectMapInv_pos (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (ha : a.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hrpos : 0 < ‖y‖) (hy2 : ‖y‖ < 2) :
    0 < LinearMap.det (fderiv ℝ (reflectMapInv a.toHomeomorph) y : csModel →ₗ[ℝ] csModel) := by
  have hsymm : a.symm.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)).opposite := by
    have h1 : a.symm.preservesOrientation (sphereOrientation 2 (by decide)).opposite
        (sphereOrientation 2 (by decide)) :=
      _root_.Diffeomorph.preservesOrientation_symm ha
    have h2 := _root_.Diffeomorph.preservesOrientation_opposite h1
    intro x
    have hx := h2 x
    simpa [ManifoldOrientation.opposite_opposite] using hx
  rw [reflectMapInv_eq_reflectMap_symm a]
  exact det_fderiv_reflectMap_pos a.symm hsymm hrpos hy2

theorem det_fderiv_reflectMap_pos_of_shell (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (ha : a.preservesOrientation (sphereOrientation 2 (by decide))
      (sphereOrientation 2 (by decide)).opposite)
    {y : csModel} (hy : y ∈ SeamShell) :
    0 < LinearMap.det (fderiv ℝ (reflectMap a.toHomeomorph) y : csModel →ₗ[ℝ] csModel) :=
  det_fderiv_reflectMap_pos a ha (lt_trans (by norm_num) hy.1) (by linarith [hy.2])

end ConnectedSumQuotient
end DifferentialGeometry.Topology
