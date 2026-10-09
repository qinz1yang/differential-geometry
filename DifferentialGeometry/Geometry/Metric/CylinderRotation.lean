import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Submodule Module TopologicalSpace Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff RealInnerProductSpace ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]

private theorem det_hyperplane_reflection {v : E} (hv : v ≠ 0) :
    LinearMap.det ((ℝ ∙ v)ᗮ.reflection.toLinearMap) = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal]
  rw [finrank_span_singleton hv]
  norm_num

theorem exists_sphereDiffeo_det_one (hn : 0 < n)
    (p q : Metric.sphere (0 : E) 1) :
    ∃ e : E ≃ₗᵢ[ℝ] E, LinearMap.det e.toLinearMap = 1 ∧ sphereDiffeo (n := n) e p = q := by
  classical
  by_cases hpq : p = q
  · refine ⟨LinearIsometryEquiv.refl ℝ E, ?_, ?_⟩
    · simp
    · exact hpq
  have hp : (p : E) ≠ 0 := by
    have hp1 := mem_sphere_zero_iff_norm.mp p.property
    intro he
    rw [he, norm_zero] at hp1
    norm_num at hp1
  have hdim : finrank ℝ (ℝ ∙ (p : E))ᗮ = n :=
    Submodule.finrank_orthogonal_span_singleton hp
  have : Nontrivial (ℝ ∙ (p : E))ᗮ := Module.nontrivial_of_finrank_pos (hdim ▸ hn)
  obtain ⟨u, hu⟩ := exists_ne (0 : (ℝ ∙ (p : E))ᗮ)
  have hu0 : (u : E) ≠ 0 := by
    intro he
    apply hu
    exact Subtype.ext he
  have hdiff : (p : E) - q ≠ 0 := by
    intro he
    exact hpq (Subtype.ext (sub_eq_zero.mp he))
  let R := (ℝ ∙ (u : E))ᗮ.reflection
  let S := (ℝ ∙ ((p : E) - q))ᗮ.reflection
  have hRp : R (p : E) = p := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have horth := u.property
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at horth
    exact horth
  refine ⟨R.trans S, ?_, ?_⟩
  · change LinearMap.det (S.toLinearMap.comp R.toLinearMap) = 1
    rw [LinearMap.det_comp, det_hyperplane_reflection hdiff, det_hyperplane_reflection hu0]
    norm_num
  · apply Subtype.ext
    change S (R (p : E)) = (q : E)
    rw [hRp]
    exact Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp p.property).trans
        (mem_sphere_zero_iff_norm.mp q.property).symm)

def roundCylinderDiffeomorph (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) :
    (Metric.sphere (0 : E) 1 × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯
      (Metric.sphere (0 : E) 1 × ℝ) :=
  ((sphereDiffeo (n := n) e).prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)).trans
    (cylinderAxialDiffeomorph (I := 𝓡 n) a 1 (by norm_num))

@[simp] theorem roundCylinderDiffeomorph_apply (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    roundCylinderDiffeomorph (n := n) e a x = (sphereDiffeo (n := n) e x.1, a + x.2) := by
  change (sphereDiffeo (n := n) e x.1, a + 1 * x.2) = _
  rw [one_mul]

@[simp] theorem roundCylinderDiffeomorph_symm_apply (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    (roundCylinderDiffeomorph (n := n) e a).symm x =
      (sphereDiffeo (n := n) e.symm x.1, x.2 - a) := by
  change (sphereDiffeo (n := n) e.symm x.1, 1 * (x.2 - a)) = _
  rw [one_mul]

theorem roundCylinderDiffeomorph_mfderiv (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (x : Metric.sphere (0 : E) 1 × ℝ) (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
      (roundCylinderDiffeomorph (n := n) e a) x v =
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x.1 v.1, v.2) := by
  let P := (sphereDiffeo (n := n) e).prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let T := cylinderAxialDiffeomorph (I := 𝓡 n) (M := Metric.sphere (0 : E) 1) a 1 (by norm_num)
  change mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) (T ∘ P) x v = _
  rw [mfderiv_comp x (T.contMDiff.mdifferentiableAt (by decide))
    (P.contMDiff.mdifferentiableAt (by decide)), ContinuousLinearMap.comp_apply]
  rw [cylinderAxialDiffeomorph_mfderiv]
  change ((mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
    (Prod.map (sphereDiffeo (n := n) e) (id : ℝ → ℝ)) x v).1,
    1 * (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
    (Prod.map (sphereDiffeo (n := n) e) (id : ℝ → ℝ)) x v).2) = _
  rw [mfderiv_prodMap ((sphereDiffeo (n := n) e).contMDiff.mdifferentiableAt (by decide))
    mdifferentiableAt_id, mfderiv_id]
  change (_, 1 * v.2) = _
  rw [one_mul]
  rfl

theorem pullback_roundCylinderMetric_roundCylinderDiffeomorph
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) :
    Diffeomorph.pullbackMetric (roundCylinderMetric (E := E) (n := n))
      (roundCylinderDiffeomorph (n := n) e a) = roundCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  calc
    _ = 2 * inner ℝ
        (dIncl (roundCylinderDiffeomorph (n := n) e a x).1
          (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
            (roundCylinderDiffeomorph (n := n) e a) x v).1)
        (dIncl (roundCylinderDiffeomorph (n := n) e a x).1
          (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
            (roundCylinderDiffeomorph (n := n) e a) x w).1) +
        (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
          (roundCylinderDiffeomorph (n := n) e a) x v).2 *
        (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
          (roundCylinderDiffeomorph (n := n) e a) x w).2 := roundCylinderMetric_inner _ _ _
    _ = 2 * inner ℝ (dIncl x.1 v.1) (dIncl x.1 w.1) + v.2 * w.2 := by
      rw [roundCylinderDiffeomorph_mfderiv, roundCylinderDiffeomorph_mfderiv,
        roundCylinderDiffeomorph_apply]
      have hv := mfderiv_incl_sphereDiffeo (n := n) e x.1 v.1
      have hw := mfderiv_incl_sphereDiffeo (n := n) e x.1 w.1
      change 2 * inner ℝ
        (dIncl (sphereDiffeo (n := n) e x.1)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x.1 v.1))
        (dIncl (sphereDiffeo (n := n) e x.1)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x.1 w.1)) + v.2 * w.2 = _
      rw [hv, hw, e.inner_map_map]
    _ = (roundCylinderMetric (E := E) (n := n)).inner x v w :=
      (roundCylinderMetric_inner x v w).symm

theorem metricDerivNorm_pullback_roundCylinderDiffeomorph
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (gk gInf : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))
    (j : ℕ) (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricDerivNorm j
      (Diffeomorph.pullbackMetric gk (roundCylinderDiffeomorph (n := n) e a))
      (Diffeomorph.pullbackMetric gInf (roundCylinderDiffeomorph (n := n) e a))
      roundCylinderMetric x =
    metricDerivNorm j gk gInf roundCylinderMetric (roundCylinderDiffeomorph (n := n) e a x) := by
  simpa only [pullback_roundCylinderMetric_roundCylinderDiffeomorph] using
    metricDerivNorm_pullback gk gInf roundCylinderMetric (roundCylinderDiffeomorph (n := n) e a) j x

theorem metricDerivENormSupOn_pullback_roundCylinderDiffeomorph
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (gk gInf : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))
    (K : Set (Metric.sphere (0 : E) 1 × ℝ)) (p : ℕ) :
    metricDerivENormSupOn K p
      (Diffeomorph.pullbackMetric gk (roundCylinderDiffeomorph (n := n) e a))
      (Diffeomorph.pullbackMetric gInf (roundCylinderDiffeomorph (n := n) e a))
      roundCylinderMetric =
    metricDerivENormSupOn (roundCylinderDiffeomorph (n := n) e a '' K) p
      gk gInf roundCylinderMetric := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pullback_roundCylinderDiffeomorph, iSup_image]

def roundCylinderImage (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) : Opens (Metric.sphere (0 : E) 1 × ℝ) :=
  ⟨roundCylinderDiffeomorph (n := n) e a '' (U : Set (Metric.sphere (0 : E) 1 × ℝ)),
    (roundCylinderDiffeomorph (n := n) e a).toHomeomorph.isOpenMap _ U.isOpen⟩

@[simp] theorem mem_roundCylinderImage (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) (x : Metric.sphere (0 : E) 1 × ℝ) :
    x ∈ roundCylinderImage (n := n) e a U ↔
      (sphereDiffeo (n := n) e.symm x.1, x.2 - a) ∈ U := by
  change x ∈ roundCylinderDiffeomorph (n := n) e a '' (U : Set (Metric.sphere (0 : E) 1 × ℝ)) ↔ _
  rw [Diffeomorph.image_eq_preimage_symm]
  change (roundCylinderDiffeomorph (n := n) e a).symm x ∈ U ↔ _
  rw [roundCylinderDiffeomorph_symm_apply]

def roundCylinderRestrict (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) :
    U ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯ roundCylinderImage (n := n) e a U :=
  PartialDiffeomorph.toOpensDiffeo
    (roundCylinderDiffeomorph (n := n) e a).toPartialDiffeomorph
    (fun _ _ => mem_univ _)

@[simp] theorem roundCylinderRestrict_apply (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) (x : U) :
    (roundCylinderRestrict (n := n) e a U x : Metric.sphere (0 : E) 1 × ℝ) =
      (sphereDiffeo (n := n) e x.val.1, a + x.val.2) :=
  roundCylinderDiffeomorph_apply e a (x : Metric.sphere (0 : E) 1 × ℝ)

@[simp] theorem roundCylinderRestrict_symm_apply (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) (x : roundCylinderImage (n := n) e a U) :
    ((roundCylinderRestrict (n := n) e a U).symm x : Metric.sphere (0 : E) 1 × ℝ) =
      (sphereDiffeo (n := n) e.symm x.val.1, x.val.2 - a) :=
  roundCylinderDiffeomorph_symm_apply e a (x : Metric.sphere (0 : E) 1 × ℝ)

theorem roundCylinderRestrict_mfderiv (e : E ≃ₗᵢ[ℝ] E) (a : ℝ)
    (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) (x : U)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
      (roundCylinderRestrict (n := n) e a U) x v =
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x.val.1 v.1, v.2) :=
  (PartialDiffeomorph.mfderiv_toOpensDiffeo
    (roundCylinderDiffeomorph (n := n) e a).toPartialDiffeomorph
    (fun _ _ => mem_univ _) x v).trans
      (roundCylinderDiffeomorph_mfderiv e a (x : Metric.sphere (0 : E) 1 × ℝ) v)

theorem pullback_roundCylinderMetric_roundCylinderRestrict
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) (U : Opens (Metric.sphere (0 : E) 1 × ℝ)) :
    Diffeomorph.pullbackMetric
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen (roundCylinderImage (n := n) e a U))
      (roundCylinderRestrict (n := n) e a U) =
      (roundCylinderMetric (E := E) (n := n)).restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hglobal := congrArg
    (fun k : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ) =>
      k.inner (x : Metric.sphere (0 : E) 1 × ℝ) v w)
    (pullback_roundCylinderMetric_roundCylinderDiffeomorph (n := n) e a)
  have hambient := (Diffeomorph.pullbackMetric_inner roundCylinderMetric
    (roundCylinderDiffeomorph (n := n) e a) (x : Metric.sphere (0 : E) 1 × ℝ) v w).symm.trans hglobal
  rw [Diffeomorph.pullbackMetric_inner]
  change (roundCylinderMetric (E := E) (n := n)).inner
    (roundCylinderDiffeomorph (n := n) e a (x : Metric.sphere (0 : E) 1 × ℝ))
    (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) (roundCylinderRestrict (n := n) e a U) x v)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) (roundCylinderRestrict (n := n) e a U) x w) =
    (roundCylinderMetric (E := E) (n := n)).inner (x : Metric.sphere (0 : E) 1 × ℝ) v w
  have hdv : mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
      (roundCylinderRestrict (n := n) e a U) x v =
      mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
        (roundCylinderDiffeomorph (n := n) e a) (x : Metric.sphere (0 : E) 1 × ℝ) v :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo
      (roundCylinderDiffeomorph (n := n) e a).toPartialDiffeomorph
      (fun _ _ => mem_univ _) x v
  have hdw : mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
      (roundCylinderRestrict (n := n) e a U) x w =
      mfderiv ((𝓡 n).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ))
        (roundCylinderDiffeomorph (n := n) e a) (x : Metric.sphere (0 : E) 1 × ℝ) w :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo
      (roundCylinderDiffeomorph (n := n) e a).toPartialDiffeomorph
      (fun _ _ => mem_univ _) x w
  rw [hdv, hdw]
  exact hambient

theorem metricDerivNorm_pullback_roundCylinderRestrict
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) (U : Opens (Metric.sphere (0 : E) 1 × ℝ))
    (gk gInf : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (roundCylinderImage (n := n) e a U))
    (j : ℕ) (x : U) :
    metricDerivNorm j
      (Diffeomorph.pullbackMetric gk (roundCylinderRestrict (n := n) e a U))
      (Diffeomorph.pullbackMetric gInf (roundCylinderRestrict (n := n) e a U))
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) x =
    metricDerivNorm j gk gInf
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen (roundCylinderImage (n := n) e a U))
      (roundCylinderRestrict (n := n) e a U x) := by
  simpa only [pullback_roundCylinderMetric_roundCylinderRestrict] using
    metricDerivNorm_pullback gk gInf
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen (roundCylinderImage (n := n) e a U))
      (roundCylinderRestrict (n := n) e a U) j x

theorem metricDerivENormSupOn_pullback_roundCylinderRestrict
    (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) (U : Opens (Metric.sphere (0 : E) 1 × ℝ))
    (gk gInf : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (roundCylinderImage (n := n) e a U))
    (K : Set U) (p : ℕ) :
    metricDerivENormSupOn K p
      (Diffeomorph.pullbackMetric gk (roundCylinderRestrict (n := n) e a U))
      (Diffeomorph.pullbackMetric gInf (roundCylinderRestrict (n := n) e a U))
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) =
    metricDerivENormSupOn (roundCylinderRestrict (n := n) e a U '' K) p gk gInf
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen (roundCylinderImage (n := n) e a U)) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pullback_roundCylinderRestrict, iSup_image]

end DifferentialGeometry.Geometry.Metric
