import DifferentialGeometry.Geometry.Exponential.Flat.ExpCovering
import DifferentialGeometry.Geometry.Exponential.Flat.PlaneIsometry
import DifferentialGeometry.Topology.Covering.DeckDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SF4(b), core: the deck group of a flat orientable surface consists of translations

* `smoothOrientation_model_apply_eq`: a smooth orientation of a model vector space is constant.
* `det_mfderiv_pos_of_comp_eq`: if `F : E → M` is a smooth map with bijective differentials into an
  oriented manifold and `γ : E → E` satisfies `F ∘ γ = F`, then `γ` preserves orientation.
* `flat_deck_apply_eq_add`: for a complete flat orientable surface, every deck transformation of
  `exp_p` (the tree's `coveringDeckGroup`) is a translation `z ↦ z + c`.

Route: a deck map is smooth with derivative a `g_p`-isometry (RadialFlat); conjugated by a
`g_p`-orthonormal coordinate map it is an affine isometry of the Euclidean plane (mean value and
Mazur–Ulam); it is fixed-point free (free deck action) and orientation preserving (pull-back of the
orientation of `M` is constant on the plane), hence a translation.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A smooth orientation of a (connected) model vector space is constant. -/
theorem smoothOrientation_model_apply_eq (O : SmoothOrientation 𝓘(ℝ, E) E) (z w : E) :
    O.val z = O.val w := by
  have h := O.property 0
  have hfun : (fun x : (chartAt E (0 : E)).source =>
      Orientation.map (Fin (Module.finrank ℝ E))
        (preferredChartTangentEquiv 𝓘(ℝ, E) 0 x.val x.property).toLinearEquiv (O.val x.val)) =
      fun x => O.val x.val := by
    funext x
    rw [preferredChartTangentEquiv_model]
    change Orientation.map _ (LinearEquiv.refl ℝ E) (O.val x.val) = O.val x.val
    rw [Orientation.map_refl]
    rfl
  rw [hfun] at h
  let ι : E → (chartAt E (0 : E)).source := fun x => ⟨x, by simp⟩
  have hι : Continuous ι := continuous_id.subtype_mk _
  exact (h.comp_continuous hι).apply_eq_of_preconnectedSpace z w

/-- A self-map of the model space commuting with a smooth map with bijective differentials into an
oriented manifold preserves orientation. -/
theorem det_mfderiv_pos_of_comp_eq {F : E → M} (hF : ContMDiff 𝓘(ℝ, E) I ∞ F)
    (hbij : ∀ z, Bijective (mfderiv 𝓘(ℝ, E) I F z)) (oM : SmoothOrientation I M)
    {γ : E → E} (hγ : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) γ) (hγF : ∀ z, F (γ z) = F z) (z : E) :
    0 < LinearMap.det ((fderiv ℝ γ z : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  classical
  set D : E →L[ℝ] E := fderiv ℝ γ z with hD
  have hcomp : F ∘ γ = F := funext hγF
  have hchain : ∀ v, mfderiv 𝓘(ℝ, E) I F (γ z) (D v) = mfderiv 𝓘(ℝ, E) I F z v := by
    intro v
    have h := mfderiv_comp z ((hF (γ z)).mdifferentiableAt (by simp)) (hγ z)
    rw [hcomp] at h
    rw [h]
    exact congrArg (mfderiv 𝓘(ℝ, E) I F (γ z))
      (congrArg (fun L : E →L[ℝ] E => L v) (mfderiv_eq_fderiv (f := γ) (x := z))).symm
  have hinj : Injective D := by
    intro a b hab
    apply (hbij z).1
    rw [← hchain a, ← hchain b, hab]
  have hsurj : Surjective (D : E →ₗ[ℝ] E) := LinearMap.injective_iff_surjective.mp hinj
  let G : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩
  let dF := differentialEquivOfBijective 𝓘(ℝ, E) I F hbij
  let O := pullbackSmoothOrientation 𝓘(ℝ, E) I F hF hbij oM
  have hO : ∀ w, O.val w = tangentOrientationEquiv (dF w).symm.toLinearEquiv (oM.val (F w)) :=
    fun w => pullbackSmoothOrientation_apply 𝓘(ℝ, E) I F hF hbij oM w
  have hdiff : (dF z).symm.toLinearEquiv = (dF (γ z)).symm.toLinearEquiv.trans G.symm := by
    apply LinearEquiv.ext
    intro w
    apply (dF z).injective
    change dF z ((dF z).symm w) = dF z (G.symm ((dF (γ z)).symm w))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change w = mfderiv 𝓘(ℝ, E) I F z (G.symm ((dF (γ z)).symm w))
    rw [← hchain]
    have hG : D (G.symm ((dF (γ z)).symm w)) = (dF (γ z)).symm w :=
      G.apply_symm_apply ((dF (γ z)).symm w)
    rw [hG]
    exact ((dF (γ z)).apply_symm_apply w).symm
  have hkey : O.val z = Orientation.map _ G.symm (O.val (γ z)) := by
    rw [hO z, hO (γ z), hdiff, tangentOrientationEquiv_trans, tangentOrientationEquiv_self, hγF z]
  have hconst : O.val (γ z) = O.val z := smoothOrientation_model_apply_eq O (γ z) z
  rw [hconst] at hkey
  have hfix : Orientation.map (Fin (Module.finrank ℝ E)) G (O.val z) = O.val z := by
    conv_lhs => rw [hkey]
    rw [← Orientation.map_symm]
    exact Equiv.apply_symm_apply _ _
  have hpos := (Orientation.map_eq_iff_det_pos (O.val z) G (by simp)).mp hfix
  have hGD : (G : E →ₗ[ℝ] E) = (D : E →ₗ[ℝ] E) := rfl
  rwa [hGD] at hpos

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.FlatSurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A deck transformation of a flat `exp_p` has `g_p`-isometric derivative. -/
theorem flat_deck_inner_mfderiv (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (γ : coveringDeckGroup
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)))
    (x v w : E) :
    inner ℝ (show TangentSpace I p from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => γ • y) x v)
        (show TangentSpace I p from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => γ • y) x w) =
      inner ℝ (show TangentSpace I p from v) (show TangentSpace I p from w) := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ F :=
    expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero (I := I) g hEnorm hR p
  have hΓ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : E => γ • y) := coveringDeckGroup_contMDiff hloc γ
  have hΓF : F ∘ (fun y : E => γ • y) = F := funext fun y => coveringDeckGroup_map γ y
  have hchain : ∀ u, mfderiv 𝓘(ℝ, E) I F (γ • x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => γ • y) x u) = mfderiv 𝓘(ℝ, E) I F x u := by
    intro u
    have h := mfderiv_comp x ((hloc.contMDiff (γ • x)).mdifferentiableAt (by simp))
      ((hΓ x).mdifferentiableAt (by simp))
    rw [hΓF] at h
    rw [h]
    rfl
  have hflat := fun u a b =>
    expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero (I := I) g hEnorm hR p u a b
  have hbase : F (γ • x) = F x := coveringDeckGroup_map γ x
  have key : ∀ (q q' : M) (a b a' b' : E), q = q' → a = a' → b = b' →
      g.inner q a b = g.inner q' a' b' := by
    rintro q q' a b a' b' rfl rfl rfl
    rfl
  refine (hflat (γ • x) _ _).trans ((key _ _ _ _ _ _ hbase (hchain v) (hchain w)).trans
    (hflat x v w).symm)

/-- SF4(b) core: on a complete flat orientable surface every deck transformation of `exp_p` is a
translation. -/
theorem flat_deck_apply_eq_add (hdim : Module.finrank ℝ E = 2) [ConnectedSpace M]
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (γ : coveringDeckGroup
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)))
    (z : E) : γ • z = z + γ • (0 : E) := by
  classical
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ F :=
    expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero (I := I) g hEnorm hR p
  have hcov : IsCoveringMap F :=
    expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero (I := I) g hEnorm hR p
  have hbij : ∀ w, Bijective (mfderiv 𝓘(ℝ, E) I F w) := fun w => by
    obtain ⟨L, hL⟩ := (hloc w).isInvertible_mfderiv (by simp)
    rw [← hL]
    exact L.bijective
  let o' : DifferentialGeometry.ManifoldOrientation I M (Module.finrank ℝ E) := hdim ▸ o
  let oM : SmoothOrientation I M := smoothOrientationOfManifoldOrientation I o'
  -- the deck map and its inverse
  let Γ : E → E := fun y => γ • y
  let Γi : E → E := fun y => γ⁻¹ • y
  have hΓ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Γ := coveringDeckGroup_contMDiff hloc γ
  have hΓi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Γi := coveringDeckGroup_contMDiff hloc γ⁻¹
  have hΓd : Differentiable ℝ Γ :=
    (contMDiff_iff_contDiff.mp hΓ).differentiable (by simp)
  have hΓid : Differentiable ℝ Γi :=
    (contMDiff_iff_contDiff.mp hΓi).differentiable (by simp)
  have hdet : ∀ x, 0 < LinearMap.det ((fderiv ℝ Γ x : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    intro x
    exact det_mfderiv_pos_of_comp_eq hloc.contMDiff hbij oM
      (hΓ.mdifferentiable (by simp)) (fun y => coveringDeckGroup_map γ y) x
  have hinnerΓ : ∀ (δ : coveringDeckGroup F) (x v : E),
      ‖(show TangentSpace I p from fderiv ℝ (fun y : E => δ • y) x v)‖ =
        ‖(show TangentSpace I p from v)‖ := by
    intro δ x v
    have h := flat_deck_inner_mfderiv (I := I) g hEnorm hR p δ x v v
    rw [mfderiv_eq_fderiv] at h
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    exact h
  -- orthonormal coordinates for g_p
  let e := (stdOrthonormalBasis ℝ (TangentSpace I p)).repr
  let T := EuclideanSpace ℝ (Fin (Module.finrank ℝ (TangentSpace I p)))
  let eL : E ≃ₗ[ℝ] T := e.toLinearEquiv
  let eE : E ≃L[ℝ] T := eL.toContinuousLinearEquiv
  have heE : ∀ x : E, ‖eE x‖ = ‖(show TangentSpace I p from x)‖ := fun x => e.norm_map x
  have hT : Module.finrank ℝ T = 2 := by
    simp only [T, finrank_euclideanSpace_fin]
    exact hdim
  let φ : T ≃ T :=
    { toFun := fun y => eE (Γ (eE.symm y))
      invFun := fun y => eE (Γi (eE.symm y))
      left_inv := fun y => by
        simp only [Γ, Γi, ContinuousLinearEquiv.symm_apply_apply, inv_smul_smul,
          ContinuousLinearEquiv.apply_symm_apply]
      right_inv := fun y => by
        simp only [Γ, Γi, ContinuousLinearEquiv.symm_apply_apply, smul_inv_smul,
          ContinuousLinearEquiv.apply_symm_apply] }
  have hφderiv : ∀ (ψ : E → E), Differentiable ℝ ψ → ∀ y,
      HasFDerivAt (fun y => eE (ψ (eE.symm y)))
        ((eE : E →L[ℝ] T).comp ((fderiv ℝ ψ (eE.symm y)).comp (eE.symm : T →L[ℝ] E))) y := by
    intro ψ hψ y
    exact (eE : E →L[ℝ] T).hasFDerivAt.comp y
      ((hψ (eE.symm y)).hasFDerivAt.comp y (eE.symm : T →L[ℝ] E).hasFDerivAt)
  have hnorm' : ∀ (δ : coveringDeckGroup F), ∀ y v : T,
      ‖(eE : E →L[ℝ] T).comp ((fderiv ℝ (fun y : E => δ • y) (eE.symm y)).comp
        (eE.symm : T →L[ℝ] E)) v‖ = ‖v‖ := by
    intro δ y v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [heE, hinnerΓ δ, ← heE, ContinuousLinearEquiv.apply_symm_apply]
  have hφd : Differentiable ℝ φ := fun y => (hφderiv Γ hΓd y).differentiableAt
  have hφsd : Differentiable ℝ φ.symm := fun y => (hφderiv Γi hΓid y).differentiableAt
  have hφn : ∀ y v, ‖fderiv ℝ φ y v‖ ≤ ‖v‖ := fun y v => by
    rw [show fderiv ℝ φ y = _ from (hφderiv Γ hΓd y).fderiv, hnorm' γ y v]
  have hφsn : ∀ y v, ‖fderiv ℝ φ.symm y v‖ ≤ ‖v‖ := fun y v => by
    rw [show fderiv ℝ φ.symm y = _ from (hφderiv Γi hΓid y).fderiv, hnorm' γ⁻¹ y v]
  obtain ⟨A, hA⟩ := exists_affineIsometryEquiv_of_fderiv_norm_le φ hφd hφn hφsd hφsn
  -- linear part of A = conjugate of DΓ
  set L := A.linearIsometryEquiv
  have hAfd : ∀ y, HasFDerivAt (⇑A) ((L : T ≃L[ℝ] T) : T →L[ℝ] T) y := by
    intro y
    have hAeq : (⇑A) = fun x => L x + A 0 := funext fun x => by simpa using A.map_vadd (0 : T) x
    rw [hAeq]
    exact ((L : T ≃L[ℝ] T) : T →L[ℝ] T).hasFDerivAt.add_const _
  have hLeq : ((L : T ≃L[ℝ] T) : T →L[ℝ] T) =
      (eE : E →L[ℝ] T).comp ((fderiv ℝ Γ (eE.symm 0)).comp (eE.symm : T →L[ℝ] E)) := by
    have h1 := hAfd 0
    rw [hA] at h1
    exact h1.unique (hφderiv Γ hΓd 0)
  have hLdet : 0 < LinearMap.det ((L : T ≃ₗ[ℝ] T) : T →ₗ[ℝ] T) := by
    have hc : ((L : T ≃ₗ[ℝ] T) : T →ₗ[ℝ] T) = (eL : E →ₗ[ℝ] T) ∘ₗ
        ((fderiv ℝ Γ (eE.symm 0) : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ (eL.symm : T →ₗ[ℝ] E) := by
      apply LinearMap.ext
      intro v
      have := congrArg (fun f : T →L[ℝ] T => f v) hLeq
      exact this
    rw [hc, LinearMap.det_conj]
    exact hdet _
  by_cases hγ1 : γ = 1
  · subst hγ1
    simp
  have hfree : ∀ y, A y ≠ y := by
    intro y hy
    rw [hA] at hy
    change eE (Γ (eE.symm y)) = y at hy
    have hfix : γ • (eE.symm y) = eE.symm y := by
      have := congrArg eE.symm hy
      simpa [Γ] using this
    exact hγ1 (coveringDeckGroup_eq_one_of_apply_eq hcov γ _ hfix)
  have htr := apply_eq_add_of_fixedPoint_free hT A hLdet hfree (eE z)
  rw [hA] at htr
  change eE (Γ (eE.symm (eE z))) = eE z + eE (Γ (eE.symm 0)) at htr
  rw [ContinuousLinearEquiv.symm_apply_apply, map_zero, ← map_add] at htr
  exact eE.injective htr

end DifferentialGeometry.Geometry.Riemannian.Exponential
