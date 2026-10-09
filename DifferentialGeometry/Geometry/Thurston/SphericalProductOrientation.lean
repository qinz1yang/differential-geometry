import DifferentialGeometry.Geometry.Thurston.SphericalProductQuotient
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation
import DifferentialGeometry.Topology.Manifold.OpenSphereCylinder
import DifferentialGeometry.Topology.Manifold.Orientation.TopForm
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Product isometries commuting with a local diffeomorphism into an oriented manifold

Chapter 7, packet P8b. If `f : S² × ℝ → M` is a local diffeomorphism into an oriented
`3`-manifold and `f ∘ cylinderAct γ = f`, then `γ = (A, b)` preserves orientation:
`det A = lineSign b` (`det_eq_lineSign_of_comp_eq`).

The cylinder is identified with `ℝ³ ∖ {0}` by `(x, t) ↦ eᵗ x`
(`sphereProdRealDiffeomorphPunctured`), where `cylinderAct γ` becomes `x ↦ e^c A x` if `b` is a
translation and `x ↦ e^c A (x / |x|²)` if `b` is a reflection. Whether `f` carries the standard
orientation of `ℝ³` to the orientation of `M` is locally constant
(`IsLocalDiffeomorph.orientation_agreement_isLocallyConstant`), hence constant on the connected
punctured space, so the conjugated map has positive Jacobian; at a unit vector its derivative is
`e^c A`, respectively `e^c A` composed with a reflection.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CI" => SpatialNeckCylinderModel
local notation "U3" => puncturedSpace (EuclideanSpace ℝ (Fin 3))

private local instance orientationSphereDimension :
    Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def lineDiffeo (b : LineIsometry) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toEquiv := b.toHomeomorph.toEquiv
  contMDiff_toFun := by
    have h : (b : ℝ → ℝ) = fun s => lineSign b * s + b 0 := funext (line_apply b)
    change ContMDiff _ _ _ (b : ℝ → ℝ)
    rw [h]
    exact ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff
  contMDiff_invFun := by
    have h : (b.symm : ℝ → ℝ) = fun s => lineSign b.symm * s + b.symm 0 :=
      funext (line_apply b.symm)
    change ContMDiff _ _ _ (b.symm : ℝ → ℝ)
    rw [h]
    exact ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff

def cylinderActDiffeo (γ : CylinderIsometry) :
    SpatialNeckCylinder ≃ₘ⟮CI, CI⟯ SpatialNeckCylinder :=
  (sphereDiffeo (n := 2) γ.1).prodCongr (lineDiffeo γ.2)

theorem cylinderActDiffeo_apply (γ : CylinderIsometry) (p : SpatialNeckCylinder) :
    cylinderActDiffeo γ p = cylinderAct γ p := rfl

private def cylinderBasePoint : SpatialNeckSphere :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

def puncturedCylinderAct (γ : CylinderIsometry) : U3 ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ U3 :=
  ((sphereProdRealDiffeomorphPunctured (n := 2) cylinderBasePoint).symm.trans
    (cylinderActDiffeo γ)).trans (sphereProdRealDiffeomorphPunctured (n := 2) cylinderBasePoint)

def puncturedCylinderMap (γ : CylinderIsometry) (x : E3) : E3 :=
  Real.exp (γ.2 (Real.log ‖x‖)) • γ.1 (sphereDirection cylinderBasePoint x : E3)

theorem puncturedCylinderAct_coe (γ : CylinderIsometry) (u : U3) :
    (puncturedCylinderAct γ u : E3) = puncturedCylinderMap γ u := rfl

def puncturedCylinderDeriv (γ : CylinderIsometry) (u : U3) : E3 →L[ℝ] E3 :=
  mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (puncturedCylinderAct γ) u

def standardOrientation : Orientation ℝ E3 (Fin 3) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation

private instance puncturedSpaceConnected : ConnectedSpace U3 := by
  have h : IsConnected ({0}ᶜ : Set E3) := isConnected_compl_singleton_of_one_lt_rank (by
    rw [← Module.finrank_eq_rank]
    simp) 0
  exact isConnected_iff_connectedSpace.mp h

section Orientation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  (o : ManifoldOrientation (𝓡 3) M 3) {f : SpatialNeckCylinder → M}
  (hf : IsLocalDiffeomorph CI (𝓡 3) ∞ f)

include hf in
theorem det_mfderiv_puncturedCylinderAct_pos (o : ManifoldOrientation (𝓡 3) M 3)
    (γ : CylinderIsometry) (hγ : ∀ p, f (cylinderAct γ p) = f p) (u : U3) :
    0 < LinearMap.det (puncturedCylinderDeriv γ u : E3 →ₗ[ℝ] E3) := by
  let Θ := sphereProdRealDiffeomorphPunctured (n := 2) cylinderBasePoint
  let F : U3 → M := f ∘ Θ.symm
  have hF : IsLocalDiffeomorph 𝓘(ℝ, E3) (𝓡 3) ∞ F :=
    isLocalDiffeomorph_comp hf Θ.symm.isLocalDiffeomorph
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_compatibleOrientation 𝓘(ℝ, E3) (n := 3)
    (by simp) (fun x : E3 => standardOrientation)
    (DifferentialGeometry.Manifold.Orientation.isCompatibleOrientation_model standardOrientation)
  let OU := O.restrictOpen U3
  have hOU : ∀ v : U3, OU.orientation v = standardOrientation := fun v => by
    rw [ManifoldOrientation.restrictOpen_orientation, hO]
  let ψ := puncturedCylinderAct γ
  have hFψ : F ∘ ψ = F := funext fun v => by
    change f (Θ.symm (Θ (cylinderActDiffeo γ (Θ.symm v)))) = f (Θ.symm v)
    rw [Θ.symm_apply_apply, cylinderActDiffeo_apply, hγ]
  let ℓ : U3 → (E3 ≃ₗ[ℝ] E3) := fun v =>
    ((hF v).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let oM : M → Orientation ℝ E3 (Fin 3) := fun p => o.orientation p
  let ori : U3 → Orientation ℝ E3 (Fin 3) := fun v => oM (F v)
  have hloc : IsLocallyConstant fun v : U3 =>
      Orientation.map (Fin 3) (ℓ v) standardOrientation = ori v := by
    have h := hF.orientation_agreement_isLocallyConstant OU o
    have heq : (fun v : U3 => Orientation.map (Fin 3) (ℓ v) standardOrientation = ori v) =
        (fun v : U3 => Orientation.map (Fin 3)
          ((hF v).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv (OU.orientation v) =
            o.orientation (F v)) := by
      funext v
      rw [hOU v]
      rfl
    rw [heq]
    exact h
  have hconst := hloc.apply_eq_of_preconnectedSpace u (ψ u)
  let D : E3 ≃ₗ[ℝ] E3 := (ψ.mfderivToContinuousLinearEquiv (by simp) u).toLinearEquiv
  have hchain : ℓ u = D.trans (ℓ (ψ u)) := by
    apply LinearEquiv.ext
    intro v
    change mfderiv 𝓘(ℝ, E3) (𝓡 3) F u v =
      mfderiv 𝓘(ℝ, E3) (𝓡 3) F (ψ u) (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) ψ u v)
    rw [← mfderiv_comp_apply u (hF.mdifferentiable (by simp) (ψ u))
      (ψ.mdifferentiable (by simp) u) v, hFψ]
  have hFu : ori (ψ u) = ori u := by
    change oM (F (ψ u)) = oM (F u)
    rw [show F (ψ u) = F u from congrFun hFψ u]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  rcases Orientation.eq_or_eq_neg (Orientation.map (Fin 3) D standardOrientation)
    standardOrientation hcard with hpos | hneg
  · exact (Orientation.map_eq_iff_det_pos _ D hcard).mp hpos
  exfalso
  have hmapu : Orientation.map (Fin 3) (ℓ u) standardOrientation =
      -Orientation.map (Fin 3) (ℓ (ψ u)) standardOrientation := by
    rw [hchain, orientation_map_trans_fin, hneg, Orientation.map_neg]
  rw [hFu] at hconst
  generalize Orientation.map (Fin 3) (ℓ u) standardOrientation = a at hmapu hconst
  generalize Orientation.map (Fin 3) (ℓ (ψ u)) standardOrientation = b at hmapu hconst
  generalize ori u = c at hconst
  rcases Orientation.eq_or_eq_neg a c hcard with h1 | h1
  · have h2 : b = c := hconst ▸ h1
    rw [hmapu, h2] at h1
    exact Module.Ray.ne_neg_self c h1.symm
  · rcases Orientation.eq_or_eq_neg b c hcard with h2 | h2
    · have h3 : a = c := hconst.symm ▸ h2
      rw [h3] at h1
      exact Module.Ray.ne_neg_self c h1
    · rw [hmapu, h2] at h1
      exact Module.Ray.ne_neg_self (-c) h1.symm

private def unitPoint : U3 :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    change EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∈ ({0}ᶜ : Set E3)
    rw [Set.mem_compl_singleton_iff]
    exact fun h => one_ne_zero (congrArg (fun v : E3 => v 0) h)⟩

private theorem unitPoint_norm : ‖(unitPoint : E3)‖ = 1 := by
  change ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1
  simp only [PiLp.norm_single, norm_one]

private theorem unitPoint_ne_zero : (unitPoint : E3) ≠ 0 := unitPoint.2

private theorem mfderiv_puncturedCylinderAct_eq (γ : CylinderIsometry) (u : U3)
    {L : E3 →L[ℝ] E3} (hL : HasFDerivAt (puncturedCylinderMap γ) L (u : E3)) :
    puncturedCylinderDeriv γ u = L := by
  unfold puncturedCylinderDeriv
  rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, E3)) (J := 𝓘(ℝ, E3)) U3]
  have hcomp : (Subtype.val ∘ (puncturedCylinderAct γ : U3 → U3)) =
      puncturedCylinderMap γ ∘ (Subtype.val : U3 → E3) := rfl
  rw [hcomp, mfderiv_comp u hL.differentiableAt.mdifferentiableAt
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := 𝓘(ℝ, E3)) U3 u).mdifferentiableAt,
    DifferentialGeometry.mfderiv_subtype_val (I := 𝓘(ℝ, E3)) U3 u, mfderiv_eq_fderiv,
    hL.fderiv]
  rfl

private theorem puncturedCylinderMap_of_lineSign_one (γ : CylinderIsometry)
    (hγ : lineSign γ.2 = 1) {x : E3} (hx : x ≠ 0) :
    puncturedCylinderMap γ x = Real.exp (γ.2 0) • γ.1 x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [puncturedCylinderMap, coe_sphereDirection _ hx, line_apply_of_lineSign_one hγ,
    Real.exp_add, Real.exp_log hn, map_smul, smul_smul]
  congr 1
  field_simp

private theorem puncturedCylinderMap_of_lineSign_neg (γ : CylinderIsometry)
    (hγ : lineSign γ.2 = -1) {x : E3} (hx : x ≠ 0) :
    puncturedCylinderMap γ x =
      Real.exp (γ.2 0) • γ.1 (EuclideanGeometry.inversion (0 : E3) 1 x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [puncturedCylinderMap, coe_sphereDirection _ hx, line_apply_of_lineSign_neg hγ,
    Real.exp_sub, Real.exp_log hn, EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub,
    sub_zero, vadd_eq_add, add_zero, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  field_simp

private theorem det_sq_eq_one (A : E3 ≃ₗᵢ[ℝ] E3) :
    LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) *
      LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hadj : LinearMap.det (LinearMap.adjoint (A.toLinearEquiv : E3 →ₗ[ℝ] E3)) =
      LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) := by
    rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis
      (A.toLinearEquiv : E3 →ₗ[ℝ] E3), LinearMap.toMatrix_adjoint b b,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose]
  have hsymm : LinearMap.adjoint (A.toLinearEquiv : E3 →ₗ[ℝ] E3) =
      (A.symm.toLinearEquiv : E3 →ₗ[ℝ] E3) := A.adjoint_toLinearMap_eq_symm
  have hcomp : (A.symm.toLinearEquiv : E3 →ₗ[ℝ] E3) ∘ₗ (A.toLinearEquiv : E3 →ₗ[ℝ] E3) =
      LinearMap.id := by
    ext v
    simp
  calc LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) *
        LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) =
        LinearMap.det (LinearMap.adjoint (A.toLinearEquiv : E3 →ₗ[ℝ] E3)) *
          LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) := by rw [hadj]
    _ = 1 := by rw [hsymm, ← LinearMap.det_comp, hcomp, LinearMap.det_id]

include hf in
theorem det_eq_lineSign_of_comp_eq (o : ManifoldOrientation (𝓡 3) M 3) (γ : CylinderIsometry)
    (hγ : ∀ p, f (cylinderAct γ p) = f p) :
    LinearMap.det (γ.1.toLinearEquiv : E3 →ₗ[ℝ] E3) = lineSign γ.2 := by
  have hmap := det_mfderiv_puncturedCylinderAct_pos hf o γ hγ unitPoint
  have hsq := det_sq_eq_one γ.1
  set d := LinearMap.det (γ.1.toLinearEquiv : E3 →ₗ[ℝ] E3) with hd
  have hne : ∀ᶠ x in nhds (unitPoint : E3), x ≠ 0 :=
    isOpen_compl_singleton.mem_nhds unitPoint_ne_zero
  let A : E3 →L[ℝ] E3 := γ.1.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : LinearMap.det (A : E3 →ₗ[ℝ] E3) = d := rfl
  have hexp : 0 < Real.exp (γ.2 0) := Real.exp_pos _
  rcases lineSign_eq_one_or_neg_one γ.2 with hs | hs
  · have hL : HasFDerivAt (puncturedCylinderMap γ) (Real.exp (γ.2 0) • A) (unitPoint : E3) := by
      refine (A.hasFDerivAt.const_smul (Real.exp (γ.2 0))).congr_of_eventuallyEq ?_
      filter_upwards [hne] with x hx
      exact puncturedCylinderMap_of_lineSign_one γ hs hx
    have hder := mfderiv_puncturedCylinderAct_eq γ unitPoint hL
    have hdet : LinearMap.det (puncturedCylinderDeriv γ unitPoint : E3 →ₗ[ℝ] E3) =
        Real.exp (γ.2 0) ^ 3 * d := by
      rw [hder, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul, hA]
      simp
    rw [hdet] at hmap
    rw [hs]
    have hd0 : 0 < d := pos_of_mul_pos_right hmap (by positivity)
    nlinarith
  · have hL : HasFDerivAt (puncturedCylinderMap γ)
        (Real.exp (γ.2 0) • (A.comp ((1 / dist (unitPoint : E3) 0) ^ 2 •
          ((ℝ ∙ ((unitPoint : E3) - 0))ᗮ.reflection : E3 →L[ℝ] E3)))) (unitPoint : E3) := by
      refine ((A.hasFDerivAt.comp _ (EuclideanGeometry.hasFDerivAt_inversion
        unitPoint_ne_zero)).const_smul (Real.exp (γ.2 0))).congr_of_eventuallyEq ?_
      filter_upwards [hne] with x hx
      exact puncturedCylinderMap_of_lineSign_neg γ hs hx
    have hder := mfderiv_puncturedCylinderAct_eq γ unitPoint hL
    have hrefl : LinearMap.det (((ℝ ∙ ((unitPoint : E3) - 0))ᗮ.reflection : E3 →L[ℝ] E3) :
        E3 →ₗ[ℝ] E3) = -1 := by
      change LinearMap.det (ℝ ∙ ((unitPoint : E3) - 0))ᗮ.reflection.toLinearMap = -1
      rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
        finrank_span_singleton (by simpa using unitPoint_ne_zero)]
      norm_num
    have hdet : LinearMap.det (puncturedCylinderDeriv γ unitPoint : E3 →ₗ[ℝ] E3) =
        -(Real.exp (γ.2 0) ^ 3 * d) := by
      rw [hder, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
        ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
        ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul, hrefl, dist_zero_right,
        unitPoint_norm, hA]
      simp
    rw [hdet] at hmap
    rw [hs]
    have hd0 : d < 0 := by
      by_contra h
      push Not at h
      have : 0 ≤ Real.exp (γ.2 0) ^ 3 * d := by positivity
      linarith
    nlinarith

end Orientation

end GC.Geometry.SphericalProduct
