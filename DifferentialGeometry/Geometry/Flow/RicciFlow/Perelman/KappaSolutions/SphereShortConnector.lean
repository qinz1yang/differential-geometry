import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderMetric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Intrinsic
import DifferentialGeometry.Geometry.Metric.Sphere.Polar.Basic
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance shortSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem sphere2_exists_unit_orthogonal (p : SpatialNeckSphere) :
    ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 ∧ ⟪(p : EuclideanSpace ℝ (Fin 3)), v⟫ = 0 := by
  let w : TangentSpace (𝓡 2) p := EuclideanSpace.single (0 : Fin 2) 1
  have hw : w ≠ 0 := by
    intro hw
    have hc := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hw
    change (1 : ℝ) = 0 at hc
    exact one_ne_zero hc
  let a : EuclideanSpace ℝ (Fin 3) := dIncl (n := 2) p w
  have ha : a ≠ 0 := by
    intro ha
    apply hw
    apply injective_mvfderiv_subtypeVal_sphere p
    exact ha.trans (map_zero (dIncl (n := 2) p)).symm
  refine ⟨‖a‖⁻¹ • a, norm_smul_inv_norm ha, ?_⟩
  rw [real_inner_smul_right, dIncl_orth, mul_zero]

theorem sphere2_greatCircle_rescaled_speed
    (p : SpatialNeckSphere) (v : EuclideanSpace ℝ (Fin 3))
    (hv : ‖v‖ = 1) (hpv : ⟪(p : EuclideanSpace ℝ (Fin 3)), v⟫ = 0)
    (L t : ℝ) :
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
        (greatCircle p v hv hpv (L * t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s => greatCircle p v hv hpv (L * s)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s => greatCircle p v hv hpv (L * s)) t 1) =
      L ^ 2 := by
  let c := greatCircle p v hv hpv
  have hc := (greatCircle_smooth (n := 2) p v hv hpv).mdifferentiableAt
    (x := L * t) (by decide)
  have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => L * s) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have hdlin : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => L * s) t 1 = L := by
    rw [mfderiv_eq_fderiv]
    change (fderiv ℝ (fun s : ℝ => L * s) t) (1 : ℝ) = L
    have hd := (hasDerivAt_id t).const_mul L
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, mul_one, id_eq] using
      congrArg (fun D : ℝ →L[ℝ] ℝ => D 1) hd.hasFDerivAt.fderiv
  have hd : (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s => c (L * s)) t 1 :
      EuclideanSpace ℝ (Fin 2)) =
      L • mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t) 1 := by
    have hcomp := mfderiv_comp_apply t hc
      (hlin.mdifferentiableAt (by decide)) (1 : ℝ)
    have hsmul : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t) L =
        L • mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t) 1 := by
      let D : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t)
      change D L = L • D (1 : ℝ)
      exact (congrArg D (mul_one L).symm).trans (map_smul D L (1 : ℝ))
    exact hcomp.trans ((congrArg
      (fun a : ℝ => mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t) a) hdlin).trans hsmul)
  have hinner := congrArg₂
    (fun V Z : EuclideanSpace ℝ (Fin 2) =>
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner (c (L * t)) V Z)
    hd hd
  apply hinner.trans
  have hspeed : (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
      (c (L * t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t) 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c (L * t) 1) = 1 :=
    greatCircle_speed p v hv hpv (L * t)
  exact (gInner_smul_self _ _ L _).trans
    ((congrArg (fun a : ℝ => L ^ 2 * a) hspeed).trans (mul_one _))

theorem sphere2_exists_short_constant_speed_curve (p q : SpatialNeckSphere) :
    ∃ (L : ℝ) (γ : ℝ → SpatialNeckSphere),
      L ∈ Icc 0 Real.pi ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ ∧
      γ 0 = p ∧ γ 1 = q ∧
      ∀ t : ℝ, (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
        (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = L ^ 2 := by
  classical
  by_cases hpq : p = q
  · refine ⟨0, fun _ => p, ⟨le_rfl, Real.pi_pos.le⟩, contMDiff_const,
      rfl, hpq, ?_⟩
    intro t
    simp only [mfderiv_const, zero_apply, map_zero]
    norm_num
  have hdata : ∃ (L : ℝ) (v : EuclideanSpace ℝ (Fin 3))
      (hv : ‖v‖ = 1) (hpv : ⟪(p : EuclideanSpace ℝ (Fin 3)), v⟫ = 0),
      L ∈ Icc 0 Real.pi ∧ greatCircle p v hv hpv L = q := by
    by_cases hanti : q = -p
    · obtain ⟨v, hv, hpv⟩ := sphere2_exists_unit_orthogonal p
      refine ⟨Real.pi, v, hv, hpv, ⟨Real.pi_pos.le, le_rfl⟩, ?_⟩
      apply Subtype.ext
      simp only [greatCircle_val, Real.cos_pi, Real.sin_pi, neg_one_smul,
        zero_smul, add_zero, hanti, coe_neg_sphere]
    · have hqp : (q : EuclideanSpace ℝ (Fin 3)) ≠ (p : EuclideanSpace ℝ (Fin 3)) :=
        fun heq => hpq (Subtype.ext heq).symm
      have hqnp : (q : EuclideanSpace ℝ (Fin 3)) ≠ -(p : EuclideanSpace ℝ (Fin 3)) :=
        fun heq => hanti (Subtype.ext heq)
      obtain ⟨hL, hpv, hv, heq⟩ := polar_decomp
        (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere q) hqp hqnp
      refine ⟨Real.arccos ⟪(p : EuclideanSpace ℝ (Fin 3)),
        (q : EuclideanSpace ℝ (Fin 3))⟫, _, hv, hpv, ⟨hL.1.le, hL.2.le⟩, ?_⟩
      exact Subtype.ext heq
  obtain ⟨L, v, hv, hpv, hL, hend⟩ := hdata
  let γ : ℝ → SpatialNeckSphere := fun t => greatCircle p v hv hpv (L * t)
  have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => L * s) :=
    (contDiff_const.mul contDiff_id).contMDiff
  refine ⟨L, γ, hL, (greatCircle_smooth (n := 2) p v hv hpv).comp hlin, ?_, ?_, ?_⟩
  · simp only [γ, mul_zero, greatCircle_zero]
  · simpa only [γ, mul_one] using hend
  · intro t
    exact sphere2_greatCircle_rescaled_speed p v hv hpv L t

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
