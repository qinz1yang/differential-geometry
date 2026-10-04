import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceSolid
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClass
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Orientation sign of linear filling extensions

The derivative of the linear boundary map is conjugate to its real matrix under the torus
cover. A genuine product collar germ transfers this determinant to the actual solid extension.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

open AnnulusStraightening

def fillingLinearPlane (A : GL (Fin 2) ℤ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  ((A.val 0 0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (A.val 0 1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((A.val 1 0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (A.val 1 1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem fillingLinearPlane_det (A : GL (Fin 2) ℤ) :
    LinearMap.det (fillingLinearPlane A).toLinearMap = ((Matrix.det A.val : ℤ) : ℝ) := by
  classical
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  have hM : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (fillingLinearPlane A).toLinearMap = fun i j => (A.val i j : ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, fillingLinearPlane, Module.Basis.finTwoProd]
  rw [hM]
  calc
    Matrix.det (fun (i j : Fin 2) => ((A.val : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)) =
        (A.val 0 0 : ℝ) * A.val 1 1 - (A.val 0 1 : ℝ) * A.val 1 0 :=
      Matrix.det_fin_two _
    _ = ((Matrix.det A.val : ℤ) : ℝ) := by
      rw [Matrix.det_fin_two]
      push_cast
      rfl

theorem fillingLinearTorus_fixed (A : GL (Fin 2) ℤ) :
    linearTorusDiffeomorph A torusBase = torusBase := by
  change Circle.matrixMap A.val (1, 1) = (1, 1)
  simp [Circle.matrixMap]

theorem fillingLinearTorus_derivative_det (A : GL (Fin 2) ℤ) :
    LinearMap.det (mfderiv torusModel torusModel (linearTorusDiffeomorph A)
      torusBase).toLinearMap = ((Matrix.det A.val : ℤ) : ℝ) := by
  have hinv := (isLocalDiffeomorph_torusCover 0).isInvertible_mfderiv (by simp)
  change ∃ e : (ℝ × ℝ) ≃L[ℝ]
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)),
    (e : (ℝ × ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) torusModel torusCover 0 :
        (ℝ × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) at hinv
  obtain ⟨e, he⟩ := hinv
  have hf : (linearTorusDiffeomorph A) ∘ torusCover =
      torusCover ∘ fillingLinearPlane A := by
    funext p
    exact linearTorusMap_torusCover A.val p
  have hder := mfderiv_comp (0 : ℝ × ℝ)
    ((linearTorusDiffeomorph A).mdifferentiable (by simp) _)
    (contMDiff_torusCover.mdifferentiable (by simp) 0)
  have hder' := mfderiv_comp (0 : ℝ × ℝ)
    (contMDiff_torusCover.mdifferentiable (by simp) _)
    (((fillingLinearPlane A).contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) 0)
  change mfderiv 𝓘(ℝ, ℝ × ℝ) torusModel (torusCover ∘ fillingLinearPlane A) 0 =
    (mfderiv 𝓘(ℝ, ℝ × ℝ) torusModel torusCover (fillingLinearPlane A 0)).comp
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fillingLinearPlane A) 0) at hder'
  rw [← hf, map_zero, torusCover_zero] at hder'
  rw [torusCover_zero] at hder
  have hK : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fillingLinearPlane A) 0 =
      fillingLinearPlane A := (fillingLinearPlane A).hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hK] at hder'
  have hconj : (mfderiv torusModel torusModel (linearTorusDiffeomorph A)
      torusBase).toLinearMap = e.toLinearEquiv.toLinearMap.comp
        ((fillingLinearPlane A).toLinearMap.comp e.symm.toLinearEquiv.toLinearMap) := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    change mfderiv torusModel torusModel (linearTorusDiffeomorph A) torusBase (e w) =
      e (fillingLinearPlane A (e.symm (e w)))
    rw [e.symm_apply_apply]
    have hew : e w = mfderiv 𝓘(ℝ, ℝ × ℝ) torusModel torusCover 0 w :=
      congrArg (fun L : (ℝ × ℝ) →L[ℝ] _ => L w) he
    have heK : e (fillingLinearPlane A w) =
        mfderiv 𝓘(ℝ, ℝ × ℝ) torusModel torusCover 0 (fillingLinearPlane A w) :=
      congrArg (fun L : (ℝ × ℝ) →L[ℝ] _ => L (fillingLinearPlane A w)) he
    rw [hew, heK]
    exact (congrArg (fun L => L w) hder).symm.trans (congrArg (fun L => L w) hder')
  rw [hconj]
  exact (LinearMap.det_conj (fillingLinearPlane A).toLinearMap e.toLinearEquiv).trans
    (fillingLinearPlane_det A)

theorem fillingLinearHalf_derivative_det (A : GL (Fin 2) ℤ) :
    LinearMap.det (mfderiv halfCollarModel halfCollarModel
      ((linearTorusDiffeomorph A).prodCongr
        (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞))
      (torusBase, halfZero)).toLinearMap = ((Matrix.det A.val : ℤ) : ℝ) := by
  have hd := mfderiv_prodMap (p := (torusBase, halfZero))
    ((linearTorusDiffeomorph A).mdifferentiable (by simp) torusBase)
    (mdifferentiableAt_id (I := 𝓡∂ 1) (x := halfZero))
  change mfderiv halfCollarModel halfCollarModel
    ((linearTorusDiffeomorph A).prodCongr
      (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)) (torusBase, halfZero) =
    (mfderiv torusModel torusModel (linearTorusDiffeomorph A) torusBase).prodMap
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) id halfZero) at hd
  rw [hd, mfderiv_id]
  change LinearMap.det (LinearMap.prodMap
    (mfderiv torusModel torusModel (linearTorusDiffeomorph A) torusBase).toLinearMap
    (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _)) = _
  exact (LinearMap.det_prodMap
    (mfderiv torusModel torusModel (linearTorusDiffeomorph A) torusBase).toLinearMap
    (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _)).trans
      (by rw [LinearMap.det_id, mul_one]; exact fillingLinearTorus_derivative_det A)

theorem fillingCollar_derivative_det {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (c : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) M ∞)
    (F : M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)
    (J : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      Torus × EuclideanHalfSpace 1)
    (p₀ : Torus × EuclideanHalfSpace 1) (hp : p₀ ∈ c.source) (hJ : J p₀ = p₀)
    (hEq : (F ∘ c) =ᶠ[𝓝 p₀] (c ∘ J)) :
    LinearMap.det (mfderiv (𝓡∂ 3) (𝓡∂ 3) F (c p₀)).toLinearMap =
      LinearMap.det (mfderiv halfCollarModel halfCollarModel J p₀).toLinearMap := by
  have hdiff : mfderiv halfCollarModel (𝓡∂ 3) (F ∘ c) p₀ =
      mfderiv halfCollarModel (𝓡∂ 3) (c ∘ J) p₀ := by
    have hd := hEq.mfderiv_eq (I := halfCollarModel) (I' := 𝓡∂ 3)
    ext v
    exact congrArg (fun L => L v) hd
  have hc : MDifferentiableAt halfCollarModel (𝓡∂ 3) c p₀ :=
    (c.contMDiffOn p₀ hp).contMDiffAt (c.open_source.mem_nhds hp) |>.mdifferentiableAt (by simp)
  have hcJ : MDifferentiableAt halfCollarModel (𝓡∂ 3) c (J p₀) := hJ.symm ▸ hc
  have hd := mfderiv_comp p₀ (F.mdifferentiable (by simp) (c p₀)) hc
  have hd' := mfderiv_comp p₀ hcJ (J.mdifferentiable (by simp) p₀)
  change mfderiv halfCollarModel (𝓡∂ 3) (c ∘ J) p₀ =
    (mfderiv halfCollarModel (𝓡∂ 3) c (J p₀)).comp
      (mfderiv halfCollarModel halfCollarModel J p₀) at hd'
  rw [hJ] at hd'
  have hinv := (c.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hp).isInvertible_mfderiv
    (by simp)
  change ∃ e : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
    EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
      (e : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =
      (mfderiv halfCollarModel (𝓡∂ 3) c p₀ :
        ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
          EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 3)) at hinv
  obtain ⟨e, he⟩ := hinv
  let K : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ((EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) :=
    mfderiv halfCollarModel halfCollarModel J p₀
  have hconj : (mfderiv (𝓡∂ 3) (𝓡∂ 3) F (c p₀)).toLinearMap =
      e.toLinearEquiv.toLinearMap.comp
        (K.toLinearMap.comp
          e.symm.toLinearEquiv.toLinearMap) := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    change mfderiv (𝓡∂ 3) (𝓡∂ 3) F (c p₀) (e w) =
      e (K (e.symm (e w)))
    rw [e.symm_apply_apply]
    have hew : e w = mfderiv halfCollarModel (𝓡∂ 3) c p₀ w :=
      congrArg (fun L : _ →L[ℝ] EuclideanSpace ℝ (Fin 3) => L w) he
    have heJ : e (K w) =
        mfderiv halfCollarModel (𝓡∂ 3) c p₀
          (K w) :=
      congrArg (fun L : _ →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
        L (K w)) he
    rw [hew, heJ]
    exact (congrArg (fun L => L w) hd).symm.trans
      ((congrArg (fun L => L w) hdiff).trans (congrArg (fun L => L w) hd'))
  rw [hconj]
  exact LinearMap.det_conj K.toLinearMap
    e.toLinearEquiv

theorem fillingLinearSolid_derivative_det (A : GL (Fin 2) ℤ)
    (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u})
    (δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
      F (solidTorusCollar p) = solidTorusCollar (linearTorusDiffeomorph A p.1, p.2)) :
    LinearMap.det (mfderiv (𝓡∂ 3) (𝓡∂ 3) F
      (solidTorusCollar (torusBase, halfZero))).toLinearMap =
        ((Matrix.det A.val : ℤ) : ℝ) := by
  let p₀ : Torus × EuclideanHalfSpace 1 := (torusBase, halfZero)
  let c := solidTorusCollar.{u}
  let J := (linearTorusDiffeomorph A).prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  have hp : p₀ ∈ c.source := zero_mem_halfCollarSource torusBase
  have hJ : J p₀ = p₀ := Prod.ext (fillingLinearTorus_fixed A) rfl
  have hcoord : Continuous fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0 :=
    ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).comp continuous_snd
  have hEq : (F ∘ c) =ᶠ[𝓝 p₀] (c ∘ J) := by
    filter_upwards [(c.open_source.inter (isOpen_lt hcoord continuous_const)).mem_nhds
      (show p₀ ∈ c.source ∩ {p | p.2.val 0 < δ} from ⟨hp, hδ⟩)] with p h
    exact hF p h.1 h.2
  exact (fillingCollar_derivative_det c F J p₀ hp hJ hEq).trans
    (fillingLinearHalf_derivative_det A)

theorem fillingLinearSolid_orientationSign (A : GL (Fin 2) ℤ)
    (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u})
    (δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
      F (solidTorusCollar p) = solidTorusCollar (linearTorusDiffeomorph A p.1, p.2)) :
    (Matrix.det A.val = 1 → F.preservesOrientation solidTorusCarrier.orientation
      solidTorusCarrier.orientation) ∧
    (Matrix.det A.val = -1 → F.preservesOrientation solidTorusCarrier.orientation
      solidTorusCarrier.orientation.opposite) := by
  let o : ManifoldOrientation (𝓡∂ 3) solidTorusSet.{u} 3 := solidTorusCarrier.orientation
  let x := solidTorusCollar.{u} (torusBase, halfZero)
  have hfix : F x = x := by
    have hh := hF (torusBase, halfZero) (zero_mem_halfCollarSource torusBase) hδ
    rw [fillingLinearTorus_fixed] at hh
    exact hh
  let L := (F.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hdet : LinearMap.det L.toLinearMap = ((Matrix.det A.val : ℤ) : ℝ) :=
    fillingLinearSolid_derivative_det A F δ hδ hF
  have hcard : Fintype.card (Fin 3) =
      Module.finrank ℝ (TangentSpace (𝓡∂ 3) x) := by
    change 3 = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp
  constructor
  · intro hA
    change F.preservesOrientation o o
    apply F.preservesOrientation_of_eq_at o o x
    have hm := (Orientation.map_eq_iff_det_pos (o.orientation x) L hcard).mpr
      (show 0 < LinearMap.det L.toLinearMap by rw [hdet, hA]; norm_num)
    rw [hfix]
    exact hm
  · intro hA
    change F.preservesOrientation o o.opposite
    apply F.preservesOrientation_of_eq_at o o.opposite x
    change Orientation.map (Fin 3) L (o.orientation x) = -o.orientation (F x)
    have hm := (Orientation.map_eq_neg_iff_det_neg (o.orientation x) L hcard).mpr
      (show LinearMap.det L.toLinearMap < 0 by rw [hdet, hA]; norm_num)
    rw [hfix]
    exact hm

theorem exists_linear_meridianPreserving_solidTorusDiffeomorph_with_orientationSign
    (A : GL (Fin 2) ℤ) (hA : A • meridianSlope = meridianSlope) :
    ∃ (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u}) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧
      (∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        F (solidTorusCollar p) = solidTorusCollar (linearTorusDiffeomorph A p.1, p.2)) ∧
      (Matrix.det A.val = 1 → F.preservesOrientation solidTorusCarrier.orientation
        solidTorusCarrier.orientation) ∧
      (Matrix.det A.val = -1 → F.preservesOrientation solidTorusCarrier.orientation
        solidTorusCarrier.orientation.opposite) := by
  obtain ⟨F, δ, hδ, hδ1, hF⟩ := exists_linear_meridianPreserving_solidTorusDiffeomorph A hA
  exact ⟨F, δ, hδ, hδ1, hF, fillingLinearSolid_orientationSign A F δ hδ hF⟩


end GC.Seifert
