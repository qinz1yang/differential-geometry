import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeBallChartDictionary
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev CapE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CapE4 := EuclideanSpace ℝ (Fin 4)
private abbrev CapS3 := Metric.sphere (0 : CapE4) 1

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

attribute [local instance] threeBallChartedSpace threeBall_isManifold

open private isEmbedding_standardNeckCapFun
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance

private def capE4Embed (v : CapE3) : CapE4 :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => v.ofLp i) 0)

private theorem capE4Embed_ofLp_last (v : CapE3) :
    (capE4Embed v).ofLp (Fin.last 3) = 0 := by
  rw [capE4Embed, WithLp.ofLp_toLp, snocR_last]

private theorem capE4Embed_ofLp_castSucc (v : CapE3) (i : Fin 3) :
    (capE4Embed v).ofLp i.castSucc = v.ofLp i := by
  rw [capE4Embed, WithLp.ofLp_toLp, snocR_castSucc]

private theorem capE4Embed_add (u v : CapE3) :
    capE4Embed (u + v) = capE4Embed u + capE4Embed v := by
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [capE4Embed_ofLp_last, PiLp.add_apply, capE4Embed_ofLp_last, capE4Embed_ofLp_last, add_zero]
  · rw [capE4Embed_ofLp_castSucc, PiLp.add_apply, PiLp.add_apply,
      capE4Embed_ofLp_castSucc, capE4Embed_ofLp_castSucc]

private theorem capE4Embed_smul (c : ℝ) (v : CapE3) :
    capE4Embed (c • v) = c • capE4Embed v := by
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [capE4Embed_ofLp_last, PiLp.smul_apply, capE4Embed_ofLp_last, smul_zero]
  · rw [capE4Embed_ofLp_castSucc, PiLp.smul_apply, PiLp.smul_apply,
      capE4Embed_ofLp_castSucc]

private theorem capE4Embed_norm_sq (v : CapE3) : ‖capE4Embed v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_castSucc (fun i : Fin 4 => ‖(capE4Embed v).ofLp i‖ ^ 2)]
  have h1 : (∑ i : Fin 3, ‖(capE4Embed v).ofLp i.castSucc‖ ^ 2) =
      ∑ i : Fin 3, ‖v.ofLp i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [capE4Embed_ofLp_castSucc]
  rw [h1, capE4Embed_ofLp_last, norm_zero]
  ring

private def capE4Unit : CapE4 := EuclideanSpace.single (Fin.last 3) (1 : ℝ)

private theorem capE4Unit_ofLp_last : capE4Unit.ofLp (Fin.last 3) = 1 := by
  simp [capE4Unit]

private theorem capE4Unit_ofLp_castSucc (i : Fin 3) : capE4Unit.ofLp i.castSucc = 0 := by
  rw [capE4Unit, PiLp.single_apply]
  rw [if_neg (Fin.castSucc_ne_last i)]

private theorem capE4Unit_norm : ‖capE4Unit‖ = 1 := by
  rw [capE4Unit]
  simp

private def capPole : CapS3 :=
  -⟨capE4Unit, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero, capE4Unit_norm]⟩

private theorem capPole_coe : (capPole : CapE4) = -capE4Unit := rfl

private theorem capPole_ofLp_last : (capPole : CapE4).ofLp (Fin.last 3) = -1 := by
  rw [capPole_coe, PiLp.neg_apply, capE4Unit_ofLp_last]

private theorem capPole_ofLp_castSucc (i : Fin 3) : (capPole : CapE4).ofLp i.castSucc = 0 := by
  rw [capPole_coe, PiLp.neg_apply, capE4Unit_ofLp_castSucc, neg_zero]

private def capBasis : (ℝ ∙ (capPole : CapE4))ᗮ ≃ₗᵢ[ℝ] CapE3 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere capPole)).repr

private theorem capE4Embed_mem (v : CapE3) : capE4Embed v ∈ (ℝ ∙ (capPole : CapE4))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [capPole_coe, inner_neg_left, neg_eq_zero]
  rw [capE4Unit, EuclideanSpace.inner_single_left]
  simpa using capE4Embed_ofLp_last v

private def capEmbedLinear : CapE3 →ₗ[ℝ] (ℝ ∙ (capPole : CapE4))ᗮ where
  toFun v := ⟨capE4Embed v, capE4Embed_mem v⟩
  map_add' u v := Subtype.ext (capE4Embed_add u v)
  map_smul' c v := Subtype.ext (capE4Embed_smul c v)

private theorem capEmbedLinear_injective : Function.Injective capEmbedLinear := by
  intro u v huv
  have h : capE4Embed u = capE4Embed v := congrArg Subtype.val huv
  have h2 : ∀ i : Fin 3, u.ofLp i = v.ofLp i := by
    intro i
    have := congrArg (fun w : CapE4 => w.ofLp i.castSucc) h
    simpa only [capE4Embed_ofLp_castSucc] using this
  exact WithLp.ofLp_injective 2 (funext h2)

private theorem capE4_mem_orthogonal_last {y : CapE4} (hy : y ∈ (ℝ ∙ (capPole : CapE4))ᗮ) :
    y.ofLp (Fin.last 3) = 0 := by
  have h : inner ℝ (capPole : CapE4) y = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hy
  rw [capPole_coe, inner_neg_left, neg_eq_zero, capE4Unit,
    EuclideanSpace.inner_single_left] at h
  simpa using h

private theorem capEmbedLinear_surjective : Function.Surjective capEmbedLinear := by
  intro y
  refine ⟨WithLp.toLp 2 (fun i : Fin 3 => (y : CapE4).ofLp i.castSucc), ?_⟩
  apply Subtype.ext
  change capE4Embed (WithLp.toLp 2 fun i : Fin 3 => (y : CapE4).ofLp i.castSucc) = (y : CapE4)
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [capE4Embed_ofLp_last, capE4_mem_orthogonal_last y.2]
  · rw [capE4Embed_ofLp_castSucc]

private def capEmbedEquiv : CapE3 ≃ₗ[ℝ] (ℝ ∙ (capPole : CapE4))ᗮ :=
  LinearEquiv.ofBijective capEmbedLinear ⟨capEmbedLinear_injective, capEmbedLinear_surjective⟩

private def capEmbedCLE : CapE3 ≃L[ℝ] (ℝ ∙ (capPole : CapE4))ᗮ :=
  capEmbedEquiv.toContinuousLinearEquiv

private def capScaleFactor : ℝ := 2 * standardNeckCapAmbientRadius

private theorem capScaleFactor_ne_zero : capScaleFactor ≠ 0 :=
  mul_ne_zero two_ne_zero (ne_of_gt standardNeckCapRadius_pos)

private def capScaleCLE : CapE3 ≃L[ℝ] CapE3 :=
  (LinearEquiv.smulOfNeZero ℝ CapE3 capScaleFactor capScaleFactor_ne_zero).toContinuousLinearEquiv

private def capStereoEquiv : CapE3 ≃L[ℝ] CapE3 :=
  capScaleCLE.trans (capEmbedCLE.trans capBasis.toContinuousLinearEquiv)

private theorem capStereoEquiv_apply (v : CapE3) :
    (capStereoEquiv v : CapE3) =
      capBasis ⟨capE4Embed (capScaleFactor • v), capE4Embed_mem _⟩ := rfl

private theorem capStereoEquiv_scale (v : CapE3) :
    (capStereoEquiv v : CapE3) = capBasis ⟨capE4Embed (capScaleFactor • v), capE4Embed_mem _⟩ :=
  capStereoEquiv_apply v

private theorem capBasis_symm_capStereoEquiv (v : CapE3) :
    capBasis.symm (capStereoEquiv v) =
      ⟨capE4Embed (capScaleFactor • v), capE4Embed_mem _⟩ := by
  rw [capStereoEquiv_scale]
  exact LinearIsometryEquiv.symm_apply_apply _ _

private theorem capEmbed_scale_norm_sq (v : CapE3) :
    ‖capE4Embed (capScaleFactor • v)‖ ^ 2 = capScaleFactor ^ 2 * ‖v‖ ^ 2 := by
  rw [capE4Embed_norm_sq, norm_smul, mul_pow,
    Real.norm_of_nonneg (le_of_lt (by
      rw [capScaleFactor]
      exact mul_pos (by norm_num) standardNeckCapRadius_pos))]

private theorem capScaleFactor_sq : capScaleFactor ^ 2 = 20 / 3 := by
  rw [capScaleFactor, mul_pow, standardNeckCapRadius_sq]
  norm_num

private theorem capAmbientDen_pos (v : CapE3) :
    0 < 1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2 := by positivity

private theorem standardNeckCapAmbientRadius_nonneg : 0 ≤ standardNeckCapAmbientRadius :=
  Real.sqrt_nonneg _

private theorem capONB_eq_capBasis :
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere capPole)).repr = capBasis := rfl

private theorem capStereographicSymm_apply (x : CapE3) :
    ((stereographic' 3 capPole).symm x : CapE4) =
      (‖((capBasis.symm x : (ℝ ∙ (capPole : CapE4))ᗮ) : CapE4)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) •
          ((capBasis.symm x : (ℝ ∙ (capPole : CapE4))ᗮ) : CapE4) +
        (‖((capBasis.symm x : (ℝ ∙ (capPole : CapE4))ᗮ) : CapE4)‖ ^ 2 + 4)⁻¹ •
          (‖((capBasis.symm x : (ℝ ∙ (capPole : CapE4))ᗮ) : CapE4)‖ ^ 2 - 4) •
            (capPole : CapE4) := by
  simp only [stereographic'_symm_apply]
  rw [capONB_eq_capBasis]

private theorem standardNeckCapDenAmbient_eq_radius (v : CapE3) :
    standardNeckCapDenAmbient v = 1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2 := by
  rw [standardNeckCapDenAmbient, standardNeckCapWAmbient, norm_smul,
    Real.norm_of_nonneg standardNeckCapAmbientRadius_nonneg, mul_pow]

private theorem standardNeckCapUAmbient_ofLp (v : CapE3) (j : Fin 3) :
    (standardNeckCapUAmbient v).ofLp j =
      (2 * standardNeckCapAmbientRadius * v.ofLp j) /
        (1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) := by
  rw [standardNeckCapUAmbient, standardNeckCapDenAmbient_eq_radius, standardNeckCapWAmbient,
    PiLp.smul_apply, PiLp.smul_apply]
  ring

private theorem standardNeckCapCAmbient_eq_radius (v : CapE3) :
    standardNeckCapCAmbient v =
      (1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) /
        (1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) := by
  rw [standardNeckCapCAmbient, standardNeckCapDenAmbient_eq_radius, standardNeckCapWAmbient,
    norm_smul, Real.norm_of_nonneg standardNeckCapAmbientRadius_nonneg, mul_pow]

private theorem capStereographicLast_algebra (t : ℝ) :
    (20 / 3 * t ^ 2 + 4)⁻¹ * (4 - 20 / 3 * t ^ 2) =
      (1 - 5 / 3 * t ^ 2) / (1 + 5 / 3 * t ^ 2) := by
  have h : (1 + 5 / 3 * t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem capStereographicCoord_algebra (a t : ℝ) :
    (20 / 3 * t ^ 2 + 4)⁻¹ * (4 * a) = a / (1 + 5 / 3 * t ^ 2) := by
  have h : (1 + 5 / 3 * t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private def capPoleTrue : CapS3 :=
  ⟨capE4Unit, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero, capE4Unit_norm]⟩

private theorem capPoleTrue_coe : (capPoleTrue : CapE4) = capE4Unit := rfl

private theorem capPoleTrue_ofLp_last : (capPoleTrue : CapE4).ofLp (Fin.last 3) = 1 := by
  rw [capPoleTrue_coe]
  exact capE4Unit_ofLp_last

private theorem capPoleTrue_ofLp_castSucc (i : Fin 3) :
    (capPoleTrue : CapE4).ofLp i.castSucc = 0 := by
  rw [capPoleTrue_coe]
  exact capE4Unit_ofLp_castSucc i

private def capBasisTrue : (ℝ ∙ (capPoleTrue : CapE4))ᗮ ≃ₗᵢ[ℝ] CapE3 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere capPoleTrue)).repr

private theorem capE4Embed_memTrue (v : CapE3) :
    capE4Embed v ∈ (ℝ ∙ (capPoleTrue : CapE4))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, capPoleTrue_coe, capE4Unit,
    EuclideanSpace.inner_single_left]
  simpa using capE4Embed_ofLp_last v

private def capEmbedLinearTrue : CapE3 →ₗ[ℝ] (ℝ ∙ (capPoleTrue : CapE4))ᗮ where
  toFun v := ⟨capE4Embed v, capE4Embed_memTrue v⟩
  map_add' u v := Subtype.ext (capE4Embed_add u v)
  map_smul' c v := Subtype.ext (capE4Embed_smul c v)

private theorem capEmbedLinearTrue_injective : Function.Injective capEmbedLinearTrue := by
  intro u v huv
  have h : capE4Embed u = capE4Embed v := congrArg Subtype.val huv
  have h2 : ∀ i : Fin 3, u.ofLp i = v.ofLp i := by
    intro i
    have := congrArg (fun w : CapE4 => w.ofLp i.castSucc) h
    simpa only [capE4Embed_ofLp_castSucc] using this
  exact WithLp.ofLp_injective 2 (funext h2)

private theorem capE4_mem_orthogonal_lastTrue {y : CapE4}
    (hy : y ∈ (ℝ ∙ (capPoleTrue : CapE4))ᗮ) : y.ofLp (Fin.last 3) = 0 := by
  have h : inner ℝ (capPoleTrue : CapE4) y = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hy
  rw [capPoleTrue_coe, capE4Unit, EuclideanSpace.inner_single_left] at h
  simpa using h

private theorem capEmbedLinearTrue_surjective : Function.Surjective capEmbedLinearTrue := by
  intro y
  refine ⟨WithLp.toLp 2 (fun i : Fin 3 => (y : CapE4).ofLp i.castSucc), ?_⟩
  apply Subtype.ext
  change capE4Embed (WithLp.toLp 2 fun i : Fin 3 => (y : CapE4).ofLp i.castSucc) = (y : CapE4)
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [capE4Embed_ofLp_last, capE4_mem_orthogonal_lastTrue y.2]
  · rw [capE4Embed_ofLp_castSucc]

private def capEmbedEquivTrue : CapE3 ≃ₗ[ℝ] (ℝ ∙ (capPoleTrue : CapE4))ᗮ :=
  LinearEquiv.ofBijective capEmbedLinearTrue
    ⟨capEmbedLinearTrue_injective, capEmbedLinearTrue_surjective⟩

private def capEmbedCLETrue : CapE3 ≃L[ℝ] (ℝ ∙ (capPoleTrue : CapE4))ᗮ :=
  capEmbedEquivTrue.toContinuousLinearEquiv

private def capStereoEquivTrue : CapE3 ≃L[ℝ] CapE3 :=
  capScaleCLE.trans (capEmbedCLETrue.trans capBasisTrue.toContinuousLinearEquiv)

private theorem capStereoEquivTrue_apply (v : CapE3) :
    (capStereoEquivTrue v : CapE3) =
      capBasisTrue ⟨capE4Embed (capScaleFactor • v), capE4Embed_memTrue _⟩ := rfl

private theorem capBasisTrue_symm_capStereoEquivTrue (v : CapE3) :
    capBasisTrue.symm (capStereoEquivTrue v) =
      ⟨capE4Embed (capScaleFactor • v), capE4Embed_memTrue _⟩ := by
  rw [capStereoEquivTrue_apply]
  exact LinearIsometryEquiv.symm_apply_apply _ _

private theorem capONBTrue_eq_capBasisTrue :
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere capPoleTrue)).repr = capBasisTrue := rfl

private theorem capStereographicSymmTrue_apply (x : CapE3) :
    ((stereographic' 3 capPoleTrue).symm x : CapE4) =
      (‖((capBasisTrue.symm x : (ℝ ∙ (capPoleTrue : CapE4))ᗮ) : CapE4)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) •
          ((capBasisTrue.symm x : (ℝ ∙ (capPoleTrue : CapE4))ᗮ) : CapE4) +
        (‖((capBasisTrue.symm x : (ℝ ∙ (capPoleTrue : CapE4))ᗮ) : CapE4)‖ ^ 2 + 4)⁻¹ •
          (‖((capBasisTrue.symm x : (ℝ ∙ (capPoleTrue : CapE4))ᗮ) : CapE4)‖ ^ 2 - 4) •
            (capPoleTrue : CapE4) := by
  simp only [stereographic'_symm_apply]
  rw [capONBTrue_eq_capBasisTrue]

private theorem capStereographicLastTrue_algebra (t : ℝ) :
    (20 / 3 * t ^ 2 + 4)⁻¹ * (20 / 3 * t ^ 2 - 4) =
      -((1 - 5 / 3 * t ^ 2) / (1 + 5 / 3 * t ^ 2)) := by
  have h : (1 + 5 / 3 * t ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem stereographicSymm_capStereoEquivTrue_coe (v : CapE3) :
    ((stereographic' 3 capPoleTrue).symm (capStereoEquivTrue v) : CapE4) =
      standardNeckCapPointAmbient true v := by
  rw [capStereographicSymmTrue_apply]
  have hcoe : ((capBasisTrue.symm (capStereoEquivTrue v) :
      (ℝ ∙ (capPoleTrue : CapE4))ᗮ) : CapE4) = capE4Embed (capScaleFactor • v) := by
    rw [capBasisTrue_symm_capStereoEquivTrue]
  rw [hcoe, capEmbed_scale_norm_sq]
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,
      capE4Embed_ofLp_last, capPoleTrue_ofLp_last, snocR_last, if_true, smul_zero]
    rw [standardNeckCapCAmbient_eq_radius, standardNeckCapRadius_sq, capScaleFactor_sq, zero_add]
    simp only [smul_eq_mul, mul_one]
    exact capStereographicLastTrue_algebra ‖v‖
  · simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,
      capE4Embed_ofLp_castSucc, capPoleTrue_ofLp_castSucc, snocR_castSucc, if_true, smul_zero]
    rw [standardNeckCapUAmbient_ofLp, standardNeckCapRadius_sq, capScaleFactor_sq,
      show capScaleFactor = 2 * standardNeckCapAmbientRadius from rfl, add_zero]
    simp only [smul_eq_mul]
    exact capStereographicCoord_algebra (2 * standardNeckCapAmbientRadius * v.ofLp j) ‖v‖

private theorem stereographicSymm_capStereoEquiv_coe (v : CapE3) :
    ((stereographic' 3 capPole).symm (capStereoEquiv v) : CapE4) =
      standardNeckCapPointAmbient false v := by
  rw [capStereographicSymm_apply]
  have hcoe : ((capBasis.symm (capStereoEquiv v) : (ℝ ∙ (capPole : CapE4))ᗮ) : CapE4) =
      capE4Embed (capScaleFactor • v) := by
    rw [capBasis_symm_capStereoEquiv]
  rw [hcoe, capEmbed_scale_norm_sq]
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,
      capE4Embed_ofLp_last, capPole_ofLp_last, snocR_last, Bool.false_eq_true, if_false,
      smul_zero]
    rw [standardNeckCapCAmbient_eq_radius, standardNeckCapRadius_sq, capScaleFactor_sq]
    rw [zero_add]
    simp only [smul_eq_mul]
    convert capStereographicLast_algebra ‖v‖ using 2
    ring
  · simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,
      capE4Embed_ofLp_castSucc, capPole_ofLp_castSucc, snocR_castSucc, Bool.false_eq_true,
      if_false, smul_zero]
    rw [standardNeckCapUAmbient_ofLp, standardNeckCapRadius_sq, capScaleFactor_sq]
    rw [show capScaleFactor = 2 * standardNeckCapAmbientRadius from rfl]
    rw [add_zero]
    simp only [smul_eq_mul]
    exact capStereographicCoord_algebra (2 * standardNeckCapAmbientRadius * v.ofLp j) ‖v‖

private theorem standardNeckCapFun_false_eq_stereographic (v : ThreeBall) :
    ((stereographic' 3 capPole).symm (capStereoEquiv (v : CapE3)) : CapS3) =
      standardNeckCapFun false v := by
  apply Subtype.ext
  rw [standardNeckCapFun_val_eq_ambient]
  exact stereographicSymm_capStereoEquiv_coe (v : CapE3)

private theorem standardNeckCapFun_true_eq_stereographic (v : ThreeBall) :
    ((stereographic' 3 capPoleTrue).symm (capStereoEquivTrue (v : CapE3)) : CapS3) =
      standardNeckCapFun true v := by
  apply Subtype.ext
  rw [standardNeckCapFun_val_eq_ambient]
  exact stereographicSymm_capStereoEquivTrue_coe (v : CapE3)

private theorem capStereoEquiv_isImmersion :
    IsImmersion (𝓡 3) (𝓡 3) ∞ (⇑capStereoEquiv) := by
  have hid : IsImmersion (𝓡 3) (𝓡 3) ∞ (id : CapE3 → CapE3) := IsImmersion.id
  have h := IsImmersion.continuousLinearEquiv_comp hid capStereoEquiv
  simpa using h

private theorem capStereoEquivTrue_isImmersion :
    IsImmersion (𝓡 3) (𝓡 3) ∞ (⇑capStereoEquivTrue) := by
  have hid : IsImmersion (𝓡 3) (𝓡 3) ∞ (id : CapE3 → CapE3) := IsImmersion.id
  have h := IsImmersion.continuousLinearEquiv_comp hid capStereoEquivTrue
  simpa using h

private theorem capStereographicInverse_isImmersion :
    IsImmersion (𝓡 3) (𝓡 3) ∞ (⇑(stereographic' 3 capPole).symm) :=
  DifferentialGeometry.Topology.Manifold.isImmersion_of_isLocalDiffeomorph
    (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph capPole)

private theorem capStereographicInverseTrue_isImmersion :
    IsImmersion (𝓡 3) (𝓡 3) ∞ (⇑(stereographic' 3 capPoleTrue).symm) :=
  DifferentialGeometry.Topology.Manifold.isImmersion_of_isLocalDiffeomorph
    (DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph capPoleTrue)

private theorem capStereographicMap_isImmersion :
    IsImmersion (𝓡 3) (𝓡 3) ∞
      (⇑(stereographic' 3 capPole).symm ∘ ⇑capStereoEquiv) :=
  IsImmersion.comp capStereoEquiv_isImmersion capStereographicInverse_isImmersion (by simp)

private theorem capStereographicMapTrue_isImmersion :
    IsImmersion (𝓡 3) (𝓡 3) ∞
      (⇑(stereographic' 3 capPoleTrue).symm ∘ ⇑capStereoEquivTrue) :=
  IsImmersion.comp capStereoEquivTrue_isImmersion capStereographicInverseTrue_isImmersion (by simp)

private theorem standardNeckCapFun_false_isImmersion :
    IsImmersion (𝓡∂ 3) (𝓡 3) ∞ (standardNeckCapFun false) := by
  have h := IsImmersion.comp_of_smoothBoundary
    (isSmoothEmbedding_threeBall_inclusion.isImmersion) capStereographicMap_isImmersion
  refine IsImmersion.congr h ?_
  funext v
  exact standardNeckCapFun_false_eq_stereographic v

private theorem standardNeckCapFun_true_isImmersion :
    IsImmersion (𝓡∂ 3) (𝓡 3) ∞ (standardNeckCapFun true) := by
  have h := IsImmersion.comp_of_smoothBoundary
    (isSmoothEmbedding_threeBall_inclusion.isImmersion) capStereographicMapTrue_isImmersion
  refine IsImmersion.congr h ?_
  funext v
  exact standardNeckCapFun_true_eq_stereographic v

theorem standardNeckCapIsImmersion (side : Bool) :
    IsImmersion (𝓡∂ 3) (𝓡 3) ∞ (standardNeckCapFun side) := by
  cases side
  · exact standardNeckCapFun_false_isImmersion
  · exact standardNeckCapFun_true_isImmersion

theorem standardNeckCapFun_isSmoothEmbedding (side : Bool) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (standardNeckCapFun side) :=
  ⟨standardNeckCapIsImmersion side, isEmbedding_standardNeckCapFun side⟩

theorem standardNeckCapping_cap_isSmoothEmbedding :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
    ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (standardNeckCapping.cap b) := by
  intro b
  have hb : b = standardNeckBoundaryFalse ∨ b = standardNeckBoundaryTrue := by
    obtain ⟨a, s⟩ := b
    obtain ⟨⟩ := a
    cases s <;> simp [standardNeckBoundaryFalse, standardNeckBoundaryTrue]
  rcases hb with rfl | rfl
  · simpa only [standardNeckCapping_cap_false] using
      IsSmoothEmbedding.comp_of_smoothBoundary (IsSmoothEmbedding.sumInl (I := ThreeModel)
        (M := Sphere 3) (M' := Sphere 3))
        (standardNeckCapFun_isSmoothEmbedding false)
  · simpa only [standardNeckCapping_cap_true] using
      IsSmoothEmbedding.comp_of_smoothBoundary (IsSmoothEmbedding.sumInr (I := ThreeModel)
        (M := Sphere 3) (M' := Sphere 3))
        (standardNeckCapFun_isSmoothEmbedding true)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
