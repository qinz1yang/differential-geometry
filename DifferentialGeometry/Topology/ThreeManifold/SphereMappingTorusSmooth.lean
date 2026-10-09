import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorus
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

namespace SphereMappingTorusIsotopy

abbrev flatten (D : SphereMappingTorusIsotopy) : SphereMappingTorusIsotopy where
  target := D.target
  isotopy t := D.isotopy (Real.smoothTransition (3 * t - 1))
  continuous_apply := D.continuous_apply.comp
    (continuous_fst.prodMk (Real.smoothTransition.continuous.comp (by fun_prop)))
  isotopy_zero := by
    rw [Real.smoothTransition.zero_of_nonpos (by norm_num)]
    exact D.isotopy_zero
  isotopy_one := by
    rw [Real.smoothTransition.one_of_one_le (by norm_num)]
    exact D.isotopy_one

theorem flatten_lower (D : SphereMappingTorusIsotopy) {t : ℝ} (ht : t ≤ 1 / 3) :
    D.flatten.isotopy t = Diffeomorph.refl (𝓡 2) SphereTwo ∞ := by
  change D.isotopy (Real.smoothTransition (3 * t - 1)) = _
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  exact D.isotopy_zero

theorem flatten_upper (D : SphereMappingTorusIsotopy) {t : ℝ} (ht : 2 / 3 ≤ t) :
    D.flatten.isotopy t = D.target := by
  change D.isotopy (Real.smoothTransition (3 * t - 1)) = _
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  exact D.isotopy_one

theorem contMDiff_flatten_apply (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1)) :
    ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.flatten.isotopy p.2 p.1) :=
  hD.comp (contMDiff_fst.prodMk
    (Real.smoothTransition.contDiff.contMDiff.comp
      (contMDiff_const.mul contMDiff_snd |>.sub contMDiff_const)))

theorem contMDiff_flatten_symm_apply (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.flatten.isotopy p.2).symm p.1) :=
  hD.comp (contMDiff_fst.prodMk
    (Real.smoothTransition.contDiff.contMDiff.comp
      (contMDiff_const.mul contMDiff_snd |>.sub contMDiff_const)))

end SphereMappingTorusIsotopy

def sphereMappingTorusSeamDomain : TopologicalSpace.Opens (SphereTwo × ℝ) :=
  ⟨univ ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4), isOpen_univ.prod isOpen_Ioo⟩

def sphereMappingTorusSeam
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (p : sphereMappingTorusSeamDomain) : SphereMappingTorus f :=
  if ht : 0 ≤ p.val.2 then
    Quotient.mk _ (p.val.1, ⟨p.val.2, ht, by linarith [p.property.2.2]⟩)
  else
    Quotient.mk _ (f.symm p.val.1,
      ⟨1 + p.val.2, by linarith [p.property.2.1], by linarith [not_le.mp ht]⟩)

theorem sphereMappingTorusHomeomorph_flatten_seam (D : SphereMappingTorusIsotopy)
    (p : sphereMappingTorusSeamDomain) :
    sphereMappingTorusHomeomorph D.flatten (sphereMappingTorusSeam D.target p) =
      (p.val.1, (p.val.2 : AddCircle (1 : ℝ))) := by
  unfold sphereMappingTorusSeam
  split_ifs with ht
  · change (D.flatten.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ))) = _
    rw [D.flatten_lower (by linarith [p.property.2.2])]
    rfl
  · change (D.flatten.isotopy (1 + p.val.2) (D.target.symm p.val.1),
      ((1 + p.val.2 : ℝ) : AddCircle (1 : ℝ))) = _
    rw [D.flatten_upper (by linarith [p.property.2.1]), D.target.apply_symm_apply]
    refine Prod.ext (by rfl) ?_
    simp only [AddCircle.coe_add, AddCircle.coe_period, zero_add]

private theorem isLocalDiffeomorph_sphere_prod_circle :
    IsLocalDiffeomorph IC IC ∞
      (fun p : SphereTwo × ℝ => (p.1, (p.2 : AddCircle (1 : ℝ)))) := by
  intro p
  obtain ⟨d, hp, hd⟩ := AddCircle.isLocalDiffeomorph_coe p.2
  let F : PartialDiffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × AddCircle (1 : ℝ)) ∞ :=
    { toPartialEquiv := (PartialEquiv.refl SphereTwo).prod d.toPartialEquiv
      open_source := isOpen_univ.prod d.open_source
      open_target := isOpen_univ.prod d.open_target
      contMDiffOn_toFun := contMDiff_fst.contMDiffOn.prodMk
        (d.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2))
      contMDiffOn_invFun := contMDiff_fst.contMDiffOn.prodMk
        (d.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2)) }
  refine ⟨F, ⟨mem_univ _, hp⟩, ?_⟩
  intro q hq
  exact Prod.ext rfl (hd hq.2)

@[instance_reducible]
def sphereMappingTorusChartedSpace (D : SphereMappingTorusIsotopy) :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (sphereMappingTorusHomeomorph D)

def sphereMappingTorusDiffeomorph (D : SphereMappingTorusIsotopy) :
    let _ := sphereMappingTorusChartedSpace D
    Diffeomorph IC IC (SphereMappingTorus D.target) (SphereTwo × AddCircle (1 : ℝ)) ∞ :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereMappingTorusHomeomorph D)

theorem sphereMappingTorusSeam_isLocalDiffeomorph (D : SphereMappingTorusIsotopy) :
    let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
      sphereMappingTorusChartedSpace D.flatten
    IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusSeam D.target) := by
  let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
      sphereMappingTorusChartedSpace D.flatten
  have hproj := DifferentialGeometry.isLocalDiffeomorph_restrict_open
    sphereMappingTorusSeamDomain
    (isLocalDiffeomorph_sphere_prod_circle.isLocalDiffeomorphOn sphereMappingTorusSeamDomain)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereMappingTorusDiffeomorph D.flatten).symm.isLocalDiffeomorph hproj
  have heq : (sphereMappingTorusDiffeomorph D.flatten).symm ∘
      (fun p : sphereMappingTorusSeamDomain => (p.val.1, (p.val.2 : AddCircle (1 : ℝ)))) =
        sphereMappingTorusSeam D.target := by
    funext p
    apply (sphereMappingTorusHomeomorph D.flatten).injective
    change sphereMappingTorusHomeomorph D.flatten
      ((sphereMappingTorusHomeomorph D.flatten).symm _) = _
    rw [Homeomorph.apply_symm_apply, sphereMappingTorusHomeomorph_flatten_seam]
  rw [heq] at h
  exact h


namespace SphereMappingTorusIsotopy

def track (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (D.isotopy p.2 p.1, p.2)
  invFun p := ((D.isotopy p.2).symm p.1, p.2)
  left_inv p := Prod.ext ((D.isotopy p.2).symm_apply_apply p.1) rfl
  right_inv p := Prod.ext ((D.isotopy p.2).apply_symm_apply p.1) rfl
  contMDiff_toFun := hD.prodMk contMDiff_snd
  contMDiff_invFun := hDi.prodMk contMDiff_snd

end SphereMappingTorusIsotopy

def sphereMappingTorusInteriorDomain : TopologicalSpace.Opens (SphereTwo × ℝ) :=
  ⟨univ ×ˢ Ioo (0 : ℝ) 1, isOpen_univ.prod isOpen_Ioo⟩

def sphereMappingTorusInterior
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (p : sphereMappingTorusInteriorDomain) : SphereMappingTorus f :=
  Quotient.mk _ (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

theorem sphereMappingTorusHomeomorph_interior (D : SphereMappingTorusIsotopy)
    (p : sphereMappingTorusInteriorDomain) :
    sphereMappingTorusHomeomorph D (sphereMappingTorusInterior D.target p) =
      (D.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ))) := rfl

theorem sphereMappingTorusInterior_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D
    IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusInterior D.target) := by
  let _ := sphereMappingTorusChartedSpace D
  have hfull := DifferentialGeometry.isLocalDiffeomorph_comp
    isLocalDiffeomorph_sphere_prod_circle (D.track hD hDi).isLocalDiffeomorph
  have hres := DifferentialGeometry.isLocalDiffeomorph_restrict_open
    sphereMappingTorusInteriorDomain (hfull.isLocalDiffeomorphOn sphereMappingTorusInteriorDomain)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereMappingTorusDiffeomorph D).symm.isLocalDiffeomorph hres
  have heq : (sphereMappingTorusDiffeomorph D).symm ∘
      (fun p : sphereMappingTorusInteriorDomain =>
        (D.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ)))) =
        sphereMappingTorusInterior D.target := by
    funext p
    apply (sphereMappingTorusHomeomorph D).injective
    change sphereMappingTorusHomeomorph D ((sphereMappingTorusHomeomorph D).symm _) = _
    rw [Homeomorph.apply_symm_apply, sphereMappingTorusHomeomorph_interior]
  change IsLocalDiffeomorph IC IC ∞ ((sphereMappingTorusDiffeomorph D).symm ∘
    (fun p : sphereMappingTorusInteriorDomain =>
      (D.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ))))) at h
  rw [heq] at h
  exact h

theorem sphereMappingTorus_interior_seam_cover
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :
    range (sphereMappingTorusInterior f) ∪ range (sphereMappingTorusSeam f) = univ := by
  apply eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    by_cases hz : p.2.val = 0
    · right
      refine ⟨⟨(p.1, 0), mem_univ _, by norm_num⟩, ?_⟩
      simp only [sphereMappingTorusSeam, le_refl, dite_true]
      congr 1
      exact Prod.ext rfl (Subtype.ext hz.symm)
    · by_cases ho : p.2.val = 1
      · right
        refine ⟨⟨(f p.1, 0), mem_univ _, by norm_num⟩, ?_⟩
        simp only [sphereMappingTorusSeam, le_refl, dite_true]
        exact Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨ho, rfl, rfl⟩))
      · left
        refine ⟨⟨(p.1, p.2.val), mem_univ _,
          lt_of_le_of_ne p.2.property.1 (Ne.symm hz), lt_of_le_of_ne p.2.property.2 ho⟩, ?_⟩
        rfl

theorem sphereMappingTorus_flatten_smooth_charts (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
      sphereMappingTorusChartedSpace D.flatten
    IsManifold IC ∞ (SphereMappingTorus D.target) ∧
      IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusInterior D.target) ∧
      IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusSeam D.target) := by
  let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
    sphereMappingTorusChartedSpace D.flatten
  refine ⟨?_, ?_, sphereMappingTorusSeam_isLocalDiffeomorph D⟩
  · exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (sphereMappingTorusHomeomorph D.flatten)
  · exact sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
      (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi)

end DifferentialGeometry.Topology
