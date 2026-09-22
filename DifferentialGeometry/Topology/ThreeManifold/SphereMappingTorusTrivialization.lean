import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusSmooth
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

def circleSphereOneDiffeomorph :
    Diffeomorph (𝓡 1) (𝓡 1) Circle (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∞ where
  toEquiv := circleSphereOneHomeomorph.toEquiv
  contMDiff_toFun := by
    let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by norm_num⟩
    apply ContMDiff.codRestrict_sphere
    exact Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp
      contMDiff_coe_sphere
  contMDiff_invFun := by
    let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by norm_num⟩
    apply ContMDiff.codRestrict_sphere
    exact Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp
      contMDiff_coe_sphere

def addCircleOneDiffeomorphSphereOne :
    Diffeomorph 𝓘(ℝ, ℝ) (𝓡 1) (AddCircle (1 : ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∞ :=
  AddCircle.diffeomorphCircle.trans circleSphereOneDiffeomorph

theorem addCircleOneDiffeomorphSphereOne_apply (t : AddCircle (1 : ℝ)) :
    addCircleOneDiffeomorphSphereOne t = addCircleOneHomeomorphSphereOne t := rfl

def sphereMappingTorusDiffeomorphSphereTwoTimesCircle (D : SphereMappingTorusIsotopy) :
    let _ := sphereMappingTorusChartedSpace D
    Diffeomorph IC ((𝓡 2).prod (𝓡 1)) (SphereMappingTorus D.target) SphereTwoTimesCircle ∞ := by
  let _ := sphereMappingTorusChartedSpace D
  let F := sphereMappingTorusDiffeomorph D
  let A := addCircleOneDiffeomorphSphereOne
  refine
    { toEquiv := (sphereMappingTorusHomeomorphSphereTwoTimesCircle D).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact F.contMDiff.fst.prodMk (A.contMDiff.comp F.contMDiff.snd)
  · have hpair : ContMDiff ((𝓡 2).prod (𝓡 1)) IC ∞
        (fun p : SphereTwoTimesCircle => (p.1, A.symm p.2)) :=
      contMDiff_fst.prodMk (A.symm.contMDiff.comp contMDiff_snd)
    exact F.symm.contMDiff.comp hpair

theorem sphereMappingTorusDiffeomorphSphereTwoTimesCircle_apply
    (D : SphereMappingTorusIsotopy) (p : SphereTwo × Icc (0 : ℝ) 1) :
    let _ := sphereMappingTorusChartedSpace D
    sphereMappingTorusDiffeomorphSphereTwoTimesCircle D (Quotient.mk _ p) =
      (D.isotopy p.2.val p.1, addCircleOneHomeomorphSphereOne (p.2.val : AddCircle (1 : ℝ))) := rfl

theorem exists_sphereMappingTorusIsotopy_of_degree_one
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (hf : Manifold.sphereDiffeomorphDegree f = 1) :
    ∃ D : SphereMappingTorusIsotopy, D.target = f ∧
      ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1) ∧
      ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1) ∧
      (∀ t : ℝ, t ≤ 1 / 3 → D.isotopy t = Diffeomorph.refl (𝓡 2) SphereTwo ∞) ∧
      ∀ t : ℝ, 2 / 3 ≤ t → D.isotopy t = f := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (Manifold.sphereDiffeomorphDegree_eq_one_iff_isotopy f).mp hf
  let A : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo := fun t => J (1 - t)
  have hA : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => A p.2 p.1) :=
    hJ.comp ((contMDiff_const.sub contMDiff_snd).prodMk contMDiff_fst)
  have hAi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (A p.2).symm p.1) :=
    hJi.comp ((contMDiff_const.sub contMDiff_snd).prodMk contMDiff_fst)
  let D : SphereMappingTorusIsotopy :=
    { target := f
      isotopy := A
      continuous_apply := hA.continuous
      isotopy_zero := by simpa only [A, sub_zero] using hJ1
      isotopy_one := by simpa only [A, sub_self] using hJ0 }
  exact ⟨D.flatten, rfl, D.contMDiff_flatten_apply hA, D.contMDiff_flatten_symm_apply hAi,
    fun _ ht => D.flatten_lower ht, fun _ ht => D.flatten_upper ht⟩

end DifferentialGeometry.Topology
