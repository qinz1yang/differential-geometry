import DifferentialGeometry.Geometry.Metric.Sphere.Round.Area
import DifferentialGeometry.Topology.Manifold.SphereDirection
import DifferentialGeometry.Geometry.Metric.LinearAlgebra.NormalFixedVector
import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option autoImplicit false
noncomputable section

open Bundle Manifold Metric Set Module MeasureTheory
open DifferentialGeometry.Integral.Measure (paramDensity paramGramMatrix paramGramMatrix_apply
  modelHaar riemannianVolumeMeasure)
open scoped Manifold ContDiff RealInnerProductSpace ENNReal Topology Matrix

namespace DifferentialGeometry.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp⟩

private local instance : MeasurableSpace E2 := borel E2
private local instance : BorelSpace E2 := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E3) 1) := borel _
private local instance : BorelSpace (sphere (0 : E3) 1) := ⟨rfl⟩

local notation "sphereVolume" =>
  riemannianVolumeMeasure (I := 𝓡 2) (M := sphere (0 : E3) 1)
    (roundMetric (E := E3) (n := 2))

private theorem coe_ne_zero_of_isometryEquiv {base : sphere (0 : E3) 1}
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) {y : E2} (hy : y ≠ 0) : (R y : E3) ≠ 0 := by
  intro h
  have hzero : R y = 0 := Subtype.ext h
  exact hy (R.injective (by simpa using hzero))

private def equatorialDirection (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) : E2 → sphere (0 : E3) 1 :=
  fun y => DifferentialGeometry.Topology.Manifold.sphereDirection base (R y : E3)

private theorem contMDiffOn_equatorialDirection (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) :
    ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ (equatorialDirection base R) ({0}ᶜ : Set E2) := by
  have hR : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ (fun y : E2 => (R y : E3)) ({0}ᶜ : Set E2) :=
    ((Submodule.subtypeL (ℝ ∙ (base : E3))ᗮ).contDiff.comp R.contDiff).contDiffOn.contMDiffOn
  have hsd := DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection
    (E := E3) (n := 2) base
  have hmaps : ({0}ᶜ : Set E2) ⊆ (fun y : E2 => (R y : E3)) ⁻¹' ({0}ᶜ : Set E3) :=
    fun y hy => coe_ne_zero_of_isometryEquiv R (Set.mem_compl_singleton_iff.mp hy)
  exact (hsd.comp hR hmaps).congr (fun y _ => rfl)

private theorem equatorialDirection_smul (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) {y : E2} (hy : y ≠ 0) {s : ℝ} (hs : 0 < s) :
    equatorialDirection base R (s • y) = equatorialDirection base R y := by
  have hRy : (R y : E3) ≠ 0 := coe_ne_zero_of_isometryEquiv R hy
  have h1 : (R (s • y) : E3) =
      (s * ‖(R y : E3)‖) •
        ((DifferentialGeometry.Topology.Manifold.sphereDirection base (R y : E3) : E3)) := by
    rw [map_smul, Submodule.coe_smul]
    conv_lhs => rw [← DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection base hRy]
    rw [smul_smul]
  simp only [equatorialDirection]
  rw [h1]
  exact DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul base
    (DifferentialGeometry.Topology.Manifold.sphereDirection base (R y : E3))
    (mul_pos hs (norm_pos_iff.mpr hRy))

private theorem mfderiv_equatorialDirection_self (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) {y : E2} (hy : y ≠ 0) :
    mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y y = 0 := by
  have hyc : y ∈ ({0}ᶜ : Set E2) := Set.mem_compl_singleton_iff.mpr hy
  have hMd : MDifferentiableAt 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y :=
    ((contMDiffOn_equatorialDirection base R).contMDiffAt
      (isOpen_compl_singleton.mem_nhds hyc)).mdifferentiableAt (by decide)
  let c : ℝ → E2 := fun s => s • y
  have hc1 : c 1 = y := by simp [c]
  have hderiv : HasDerivAt c y 1 := by
    simpa [c] using (hasDerivAt_id (1 : ℝ)).smul_const y
  have hcMd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) c 1 :=
    mdifferentiableAt_iff_differentiableAt.mpr hderiv.differentiableAt
  have hMd' : MDifferentiableAt 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) (c 1) := by
    simpa [hc1] using hMd
  have hev : ((equatorialDirection base R) ∘ c) =ᶠ[𝓝 (1 : ℝ)]
      (fun _ => equatorialDirection base R y) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)] with s hs
    exact equatorialDirection_smul base R hy hs
  have hzero : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ((equatorialDirection base R) ∘ c) 1 = 0 := by
    rw [hev.mfderiv_eq]
    exact mfderiv_const
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E2)) (I'' := 𝓡 2)
    (f := c) (g := equatorialDirection base R) 1 hMd' hcMd (1 : ℝ)
  have hcderiv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) c 1) (1 : ℝ) = y := by
    have hd : deriv c 1 = y := by simpa using hderiv.deriv
    have hfd : (fderiv ℝ c 1) (1 : ℝ) = deriv c 1 := rfl
    have hmd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) c 1 = fderiv ℝ c 1 := mfderiv_eq_fderiv
    rw [hmd]
    exact hfd.trans hd
  have hL : (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ((equatorialDirection base R) ∘ c) 1) (1 : ℝ) = 0 := by
    rw [hzero]; rfl
  rw [hL, hcderiv, hc1] at hcomp
  exact hcomp.symm

private theorem paramDensity_equatorialDirection_eq_zero (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) {y : E2} (hy : y ≠ 0) :
    paramDensity (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
      (equatorialDirection base R) y = 0 := by
  let B := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2
  let t : Fin (Module.finrank ℝ E2) → ℝ := B.repr y
  let A : Fin (Module.finrank ℝ E2) → E3 := fun i =>
    dIncl (n := 2) (equatorialDirection base R y)
      (mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (B i))
  have ht_ne : t ≠ 0 := by
    intro h
    have hy0 : y = 0 := by
      conv_lhs => rw [← B.sum_repr y]
      simp [t, h]
    exact hy hy0
  have hsum : ∑ i, t i • mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (B i) =
      mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y y := by
    have h1 : ∑ i, t i • mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (B i) =
        ∑ i, mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (t i • B i) :=
      Finset.sum_congr rfl (fun i _ =>
        (map_smul (mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y) (t i) (B i)).symm)
    have h2 : ∑ i, mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (t i • B i) =
        mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (∑ i, t i • B i) :=
      (map_sum (mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y)
        (fun i => t i • B i) Finset.univ).symm
    rw [h1, h2]
    congr 1
    exact B.sum_repr y
  have hmul : (paramGramMatrix (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
      (equatorialDirection base R) y).mulVec t = 0 := by
    funext j
    rw [Matrix.mulVec_apply, dotProduct]
    calc ∑ i, paramGramMatrix (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
            (equatorialDirection base R) y j i * t i
        = ∑ i, ⟪A j, A i⟫ * t i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [paramGramMatrix_apply, roundMetric_inner]
      _ = ∑ i, ⟪A j, t i • A i⟫ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [real_inner_smul_right]
          ring
      _ = ⟪A j, ∑ i, t i • A i⟫ := (inner_sum _ _ _).symm
      _ = ⟪A j, dIncl (n := 2) (equatorialDirection base R y)
            (∑ i, t i • mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (B i))⟫ := by
          congr 1
          exact (Finset.sum_congr rfl (fun i _ =>
            (map_smul (dIncl (n := 2) (equatorialDirection base R y)) (t i)
              (mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (B i))).symm)).trans
            (map_sum (dIncl (n := 2) (equatorialDirection base R y))
              (fun i => t i • mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y (B i))
              Finset.univ).symm
      _ = ⟪A j, dIncl (n := 2) (equatorialDirection base R y)
            (mfderiv 𝓘(ℝ, E2) (𝓡 2) (equatorialDirection base R) y y)⟫ :=
          congrArg (fun z => ⟪A j, dIncl (n := 2) (equatorialDirection base R y) z⟫) hsum
      _ = ⟪A j, (0 : E3)⟫ := by
          rw [mfderiv_equatorialDirection_self base R hy, map_zero]
      _ = 0 := inner_zero_right _
  have hdet : (paramGramMatrix (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
      (equatorialDirection base R) y).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨t, ht_ne, hmul⟩
  rw [paramDensity, hdet, Real.sqrt_zero]

private theorem equatorialDirection_image_eq (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) :
    equatorialDirection base R '' sphere (0 : E2) 1 =
      {x : sphere (0 : E3) 1 | ⟪(x : E3), (base : E3)⟫ = 0} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hyne : y ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
    have hRy : (R y : E3) ≠ 0 := coe_ne_zero_of_isometryEquiv R hyne
    change ⟪(DifferentialGeometry.Topology.Manifold.sphereDirection base (R y : E3) : E3),
      (base : E3)⟫ = 0
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection base hRy,
      real_inner_smul_left,
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (R y).property, mul_zero]
  · intro hx
    have hp : (x : E3) ∈ (ℝ ∙ (base : E3))ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hx
    have hx1 : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    refine ⟨R.symm ⟨(x : E3), hp⟩, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      have hnorm : ‖R.symm ⟨(x : E3), hp⟩‖ = ‖(x : E3)‖ := by
        simp [(R.symm).norm_map ⟨(x : E3), hp⟩]
      rw [hnorm, hx1]
    · apply Subtype.ext
      have hRy : (R (R.symm ⟨(x : E3), hp⟩) : E3) = (x : E3) :=
        congrArg Subtype.val (R.apply_symm_apply ⟨(x : E3), hp⟩)
      have hne : (R (R.symm ⟨(x : E3), hp⟩) : E3) ≠ 0 := by
        rw [hRy]; intro h; rw [h, norm_zero] at hx1; norm_num at hx1
      simp only [equatorialDirection]
      rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection base hne, hRy, hx1,
        inv_one, one_smul]

theorem riemannianVolumeMeasure_roundMetric_equator_eq_zero (base : sphere (0 : E3) 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (base : E3))ᗮ) :
    riemannianVolumeMeasure (I := 𝓡 2) (M := sphere (0 : E3) 1) (roundMetric (E := E3) (n := 2))
      {x : sphere (0 : E3) 1 | ⟪(x : E3), (base : E3)⟫ = 0} = 0 := by
  have himg := equatorialDirection_image_eq base R
  have hmeas : MeasurableSet (equatorialDirection base R '' sphere (0 : E2) 1) := by
    rw [himg]
    exact (isClosed_eq (continuous_subtype_val.inner continuous_const)
      continuous_const).measurableSet
  have hsub : {x : sphere (0 : E3) 1 | ⟪(x : E3), (base : E3)⟫ = 0} ⊆
      equatorialDirection base R '' sphere (0 : E2) 1 := by
    rw [himg]
  have hKU : sphere (0 : E2) 1 ⊆ ({0}ᶜ : Set E2) := by
    intro y hy h
    have hn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    rw [h, norm_zero] at hn
    norm_num at hn
  have hf : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) 1 (equatorialDirection base R)
      ({0}ᶜ : Set E2) :=
    (contMDiffOn_equatorialDirection base R).of_le (by simp)
  have hbound : riemannianVolumeMeasure (I := 𝓡 2) (M := sphere (0 : E3) 1)
        (roundMetric (E := E3) (n := 2))
        {x : sphere (0 : E3) 1 | ⟪(x : E3), (base : E3)⟫ = 0} ≤
      ∫⁻ y in sphere (0 : E2) 1,
        ENNReal.ofReal (paramDensity (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
          (equatorialDirection base R) y) ∂modelHaar (E := E2) :=
    le_trans (measure_mono hsub)
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_image_le (I := 𝓡 2)
        (M := sphere (0 : E3) 1) (roundMetric (E := E3) (n := 2))
        (f := equatorialDirection base R) (U := {0}ᶜ) (K := sphere (0 : E2) 1)
        isOpen_compl_singleton isClosed_sphere.measurableSet hKU hf hmeas)
  have hzero : ∫⁻ y in sphere (0 : E2) 1,
        ENNReal.ofReal (paramDensity (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
          (equatorialDirection base R) y) ∂modelHaar (E := E2) = 0 := by
    have hpt : ∀ y ∈ sphere (0 : E2) 1,
        ENNReal.ofReal (paramDensity (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
          (equatorialDirection base R) y) = (0 : ℝ≥0∞) := by
      intro y hy
      have hn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
      have hyne : y ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
      rw [paramDensity_equatorialDirection_eq_zero base R hyne, ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun isClosed_sphere.measurableSet hpt]
    simp
  exact le_antisymm (hbound.trans_eq hzero) zero_le

theorem sphereGraphParametrization_image_eq_openHemisphere {v : E3} (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    sphereGraphParametrization hv R '' ball (0 : E2) 1 =
      {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    change 0 < ⟪(sphereGraphParametrization hv R y : E3), v⟫
    rw [coe_sphereGraphParametrization hv R hy, sphereGraphMap_inner_base hv R y]
    exact Real.sqrt_pos.mpr (by
      have := mem_ball_zero_iff.mp hy
      nlinarith [norm_nonneg y])
  · intro x hx
    have hxnorm : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    set p : E3 := (x : E3) - ⟪(x : E3), v⟫ • v with hp
    have hpv : ⟪p, v⟫ = 0 := by
      rw [hp, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hv, mul_one]
      ring
    have hpmem : p ∈ (ℝ ∙ v)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hpv
    set y : E2 := R.symm ⟨p, hpmem⟩ with hy
    have hRy : (R y : E3) = p := by
      have h1 : R y = (⟨p, hpmem⟩ : (ℝ ∙ v)ᗮ) := R.apply_symm_apply ⟨p, hpmem⟩
      exact congrArg Subtype.val h1
    have hynorm : ‖y‖ = ‖p‖ := by
      rw [← R.norm_map y]
      exact congrArg (fun z : E3 => ‖z‖) hRy
    have hdecomp : (x : E3) = p + ⟪(x : E3), v⟫ • v := by
      rw [hp]; abel
    have hinner : ⟪p, ⟪(x : E3), v⟫ • v⟫ = 0 := by
      rw [real_inner_smul_right, hpv, mul_zero]
    have hsq : 1 = ‖y‖ ^ 2 + ⟪(x : E3), v⟫ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        p (⟪(x : E3), v⟫ • v) hinner
      rw [← hdecomp] at h
      rw [← hynorm] at h
      rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_pos hx] at h
      nlinarith [h, hxnorm]
    have hlt : ‖y‖ < 1 := by
      have hpos : 0 < ⟪(x : E3), v⟫ ^ 2 := pow_pos hx 2
      nlinarith [norm_nonneg y]
    have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = ⟪(x : E3), v⟫ := by
      have h1 : 1 - ‖y‖ ^ 2 = ⟪(x : E3), v⟫ ^ 2 := by linarith [hsq]
      rw [h1, Real.sqrt_sq hx.le]
    refine ⟨y, mem_ball_zero_iff.mpr hlt, ?_⟩
    refine Subtype.ext ?_
    rw [coe_sphereGraphParametrization hv R (mem_ball_zero_iff.mpr hlt), sphereGraphMap, hRy, hsqrt]
    exact hdecomp.symm

private noncomputable def roundSphereBasis : OrthonormalBasis (Fin 3) ℝ E3 :=
  (stdOrthonormalBasis ℝ E3).reindex
    (finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)))

private noncomputable def roundSphereBasePoint : sphere (0 : E3) 1 :=
  ⟨roundSphereBasis 0, mem_sphere_zero_iff_norm.mpr (roundSphereBasis.orthonormal.1 0)⟩

private noncomputable def sphereFrameFor (v : E3) (hv : v ≠ 0) :
    E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ :=
  ((stdOrthonormalBasis ℝ ((ℝ ∙ v)ᗮ)).reindex
    (finCongr (by rw [finrank_normal hv, finrank_euclideanSpace_fin]))).repr.symm

private theorem riemannianVolumeMeasure_roundMetric_sphere_univ_eq_of_frame {v : E3}
    (hv : ‖v‖ = 1) (hv' : ‖(-v : E3)‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (R' : E2 ≃ₗᵢ[ℝ] (ℝ ∙ (-v : E3))ᗮ) :
    sphereVolume (univ : Set (sphere (0 : E3) 1)) = ENNReal.ofReal (4 * Real.pi) := by
  have hAeq : sphereVolume {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} =
      ENNReal.ofReal (2 * Real.pi) := by
    rw [← sphereGraphParametrization_image_eq_openHemisphere hv R]
    exact riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq_two_pi hv R
  have hBeq : sphereVolume {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫} =
      ENNReal.ofReal (2 * Real.pi) := by
    rw [← sphereGraphParametrization_image_eq_openHemisphere hv' R']
    exact riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_neg_eq_two_pi hv' R'
  have hCeq : sphereVolume {x : sphere (0 : E3) 1 | ⟪(x : E3), v⟫ = 0} = 0 :=
    riemannianVolumeMeasure_roundMetric_equator_eq_zero
      ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩ R
  have hsum4 : ENNReal.ofReal (2 * Real.pi) + ENNReal.ofReal (2 * Real.pi) =
      ENNReal.ofReal (4 * Real.pi) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hcover : (univ : Set (sphere (0 : E3) 1)) ⊆
      {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} ∪
        {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫} ∪
          {x : sphere (0 : E3) 1 | ⟪(x : E3), v⟫ = 0} := by
    intro x _
    rcases lt_trichotomy ⟪(x : E3), v⟫ 0 with h | h | h
    · refine Or.inl (Or.inr ?_)
      change 0 < ⟪(x : E3), (-v : E3)⟫
      rw [inner_neg_right]
      linarith
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hupper_meas : MeasurableSet {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} :=
    (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).measurableSet
  have hlower_meas : MeasurableSet {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫} :=
    (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).measurableSet
  have hdisj : Disjoint {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫}
      {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫} := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hxv : 0 < ⟪(x : E3), v⟫ := hx
    have hyv : 0 < ⟪(x : E3), (-v : E3)⟫ := hy
    rw [inner_neg_right] at hyv
    linarith
  have hub : sphereVolume (univ : Set (sphere (0 : E3) 1)) ≤ ENNReal.ofReal (4 * Real.pi) := by
    refine le_trans (measure_mono hcover) ?_
    calc sphereVolume ({x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} ∪
          {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫} ∪
            {x : sphere (0 : E3) 1 | ⟪(x : E3), v⟫ = 0})
        ≤ sphereVolume ({x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} ∪
            {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫}) +
          sphereVolume {x : sphere (0 : E3) 1 | ⟪(x : E3), v⟫ = 0} :=
          measure_union_le _ _
      _ ≤ (sphereVolume {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} +
            sphereVolume {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫}) +
          sphereVolume {x : sphere (0 : E3) 1 | ⟪(x : E3), v⟫ = 0} :=
          add_le_add (measure_union_le _ _) le_rfl
      _ = ENNReal.ofReal (4 * Real.pi) := by
          rw [hAeq, hBeq, hCeq, add_zero, hsum4]
  have hlb : ENNReal.ofReal (4 * Real.pi) ≤ sphereVolume (univ : Set (sphere (0 : E3) 1)) := by
    have h1 : sphereVolume ({x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} ∪
        {x : sphere (0 : E3) 1 | 0 < ⟪(x : E3), (-v : E3)⟫}) ≤
        sphereVolume (univ : Set (sphere (0 : E3) 1)) :=
      measure_mono (Set.subset_univ _)
    rw [measure_union hdisj hlower_meas, hAeq, hBeq, hsum4] at h1
    exact h1
  exact le_antisymm hub hlb

theorem riemannianVolumeMeasure_roundMetric_sphere_univ_eq :
    sphereVolume (univ : Set (sphere (0 : E3) 1)) = ENNReal.ofReal (4 * Real.pi) := by
  have hv : ‖((roundSphereBasePoint : E3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp roundSphereBasePoint.property
  have hvne : (roundSphereBasePoint : E3) ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; norm_num at hv
  have hv' : ‖(-(roundSphereBasePoint : E3))‖ = 1 := by rw [norm_neg]; exact hv
  have hvne' : (-(roundSphereBasePoint : E3)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hv'; norm_num at hv'
  exact riemannianVolumeMeasure_roundMetric_sphere_univ_eq_of_frame hv hv'
    (sphereFrameFor _ hvne) (sphereFrameFor _ hvne')

theorem riemannianVolumeMeasure_roundMetric_sphere_univ_real_eq :
    Measure.real sphereVolume (univ : Set (sphere (0 : E3) 1)) = 4 * Real.pi := by
  rw [Measure.real_def, riemannianVolumeMeasure_roundMetric_sphere_univ_eq,
    ENNReal.toReal_ofReal (by positivity)]

end DifferentialGeometry.Geometry
