import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderSmoothRealization
import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusTrivialization
import DifferentialGeometry.Topology.Manifold.SphereCylinderReturnDegree

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.DoubleCylinder

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_mappingTorus_diffeomorph_of_opposite_slabs
    (J : SphereMappingTorusIsotopy)
    (hJ : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => J.isotopy p.2 p.1))
    (hJi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (J.isotopy p.2).symm p.1))
    (A P : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞)
    (η κ : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (hmonodromy : J.target = κ.symm.trans η)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source)
    (hP : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source)
    (hzero : ∀ z : SphereTwo, A (z,0) = P (κ z,1))
    (hone : ∀ z : SphereTwo, A (z,1) = P (η z,0))
    (hmeet : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P '' (univ ×ˢ ({0} : Set ℝ)) ∪ P '' (univ ×ˢ ({1} : Set ℝ)))
    (hcover : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1) = univ) :
    ∃ K : (SphereTwo × ℝ) ≃ₘ⟮IC,IC⟯ (SphereTwo × ℝ),
      K '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z : SphereTwo, K (z,0) = (η.symm z,1)) ∧
      (∀ z : SphereTwo, K (z,1) = (η.symm z,0)) ∧
      (∀ z : SphereTwo, (fun q => A (K q)) =ᶠ[𝓝 (z,0)] (fun q => P (q.1,-q.2))) ∧
      (∀ z : SphereTwo, (fun q => A (K q)) =ᶠ[𝓝 (z,1)] (fun q => P (J.target.symm q.1,2-q.2))) ∧
      let _ := sphereMappingTorusChartedSpace J.flatten
      ∃ D : M ≃ₘ⟮I,IC⟯ SphereMappingTorus J.target,
        (∀ p : Cylinder, D (A (K (p.1,p.2.val))) = bandToMappingTorus J.target p) ∧
        ∀ p : Cylinder, D (P (p.1,p.2.val)) = coreToMappingTorus J.target p := by
  let R : (SphereTwo × ℝ) ≃ₘ⟮IC,IC⟯ (SphereTwo × ℝ) :=
    (η.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)).trans
      (Diffeomorph.fiberwiseAffine (fun _ => (1:ℝ)) (fun _ => (-1:ℝ))
        contMDiff_const contMDiff_const (fun _ => by norm_num))
  have hR (q : SphereTwo × ℝ) : R q = (η.symm q.1,1-q.2) := by
    change (η.symm q.1,1 + -1*q.2) = _
    rw [neg_one_mul]
    rfl
  have hRb : R '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      rw [hR]
      exact ⟨mem_univ _,by constructor <;> linarith [hp.2.1,hp.2.2]⟩
    · intro hq
      refine ⟨(η q.1,1-q.2),⟨mem_univ _,by constructor <;> linarith [hq.2.1,hq.2.2]⟩,?_⟩
      rw [hR,η.symm_apply_apply,sub_sub_cancel]
  let a := R.toPartialDiffeomorph.trans A
  have ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source := by
    intro q hq
    refine ⟨mem_univ _,hA ?_⟩
    change R q ∈ univ ×ˢ Icc (0 : ℝ) 1
    rw [← hRb]
    exact mem_image_of_mem R hq
  have hai : a '' (univ ×ˢ Icc (0 : ℝ) 1) = A '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    calc
      _ = A '' (R '' (univ ×ˢ Icc (0 : ℝ) 1)) := by rw [image_image]; rfl
      _ = _ := by rw [hRb]
  have ha0 (z : SphereTwo) : a (z,0) = P (z,0) := by
    change A (R (z,0)) = _
    rw [hR,sub_zero,hone,η.apply_symm_apply]
  have ha1 (z : SphereTwo) : a (z,1) = P (J.target.symm z,1) := by
    change A (R (z,1)) = _
    rw [hR,sub_self,hzero,hmonodromy]
    rfl
  obtain ⟨G,hGb,hG0,hG1,hGlo,hGhi,hD⟩ := exists_mappingTorus_diffeomorph_of_double_slab J hJ hJi a P ha hP
    ha0 ha1 (by rw [hai]; exact hmeet) (by rw [hai]; exact hcover)
  let K := G.trans R
  refine ⟨K,?_,?_,?_,hGlo,hGhi,?_⟩
  · calc
      _ = R '' (G '' (univ ×ˢ Icc (0 : ℝ) 1)) := by rw [image_image]; rfl
      _ = _ := by rw [hGb,hRb]
  · intro z
    change R (G (z,0)) = _
    rw [hG0,hR,sub_zero]
  · intro z
    change R (G (z,1)) = _
    rw [hG1,hR,sub_self]
  · exact hD

theorem nonempty_diffeomorph_sphereTwoTimesCircle_of_opposite_slabs
    (A P : PartialDiffeomorph IC I (SphereTwo × ℝ) M ∞)
    (η κ : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (hdegree : Manifold.sphereDiffeomorphDegree (κ.symm.trans η) = 1)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source)
    (hP : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source)
    (hzero : ∀ z : SphereTwo, A (z,0) = P (κ z,1))
    (hone : ∀ z : SphereTwo, A (z,1) = P (η z,0))
    (hmeet : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P '' (univ ×ˢ ({0} : Set ℝ)) ∪ P '' (univ ×ˢ ({1} : Set ℝ)))
    (hcover : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1) = univ) :
    Nonempty (M ≃ₘ⟮I,(𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) := by
  obtain ⟨J,hJtarget,hJ,hJi,_,_⟩ := exists_sphereMappingTorusIsotopy_of_degree_one _ hdegree
  obtain ⟨_,_,_,_,_,_,hD⟩ := exists_mappingTorus_diffeomorph_of_opposite_slabs J hJ hJi
    A P η κ hJtarget hA hP hzero hone hmeet hcover
  let _ := sphereMappingTorusChartedSpace J.flatten
  obtain ⟨D,_,_⟩ := hD
  exact ⟨D.trans (sphereMappingTorusDiffeomorphSphereTwoTimesCircle J.flatten)⟩

theorem nonempty_diffeomorph_sphereTwoTimesCircle_of_oriented_opposite_slabs
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (o : Manifold.SmoothOrientation (𝓡 3) M)
    (A P : PartialDiffeomorph IC (𝓡 3) (SphereTwo × ℝ) M ∞)
    (η κ : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source)
    (hP : univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source)
    (hzero : ∀ z : SphereTwo, A (z,0) = P (κ z,1))
    (hone : ∀ z : SphereTwo, A (z,1) = P (η z,0))
    (hmeet : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      P '' (univ ×ˢ ({0} : Set ℝ)) ∪ P '' (univ ×ˢ ({1} : Set ℝ)))
    (hcover : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1) = univ) :
    Nonempty (M ≃ₘ⟮𝓡 3,(𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) := by
  let R : (SphereTwo × ℝ) ≃ₘ⟮IC,IC⟯ (SphereTwo × ℝ) :=
    (η.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)).trans
      (Diffeomorph.fiberwiseAffine (fun _ => (1:ℝ)) (fun _ => (-1:ℝ))
        contMDiff_const contMDiff_const (fun _ => by norm_num))
  have hR (q : SphereTwo × ℝ) : R q = (η.symm q.1,1-q.2) := by
    change (η.symm q.1,1 + -1*q.2) = _
    rw [neg_one_mul]
    rfl
  have hRb : R '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      rw [hR]
      exact ⟨mem_univ _,by constructor <;> linarith [hp.2.1,hp.2.2]⟩
    · intro hq
      refine ⟨(η q.1,1-q.2),⟨mem_univ _,by constructor <;> linarith [hq.2.1,hq.2.2]⟩,?_⟩
      rw [hR,η.symm_apply_apply,sub_sub_cancel]
  let a := R.toPartialDiffeomorph.trans A
  have ha : univ ×ˢ Icc (0 : ℝ) 1 ⊆ a.source := by
    intro q hq
    refine ⟨mem_univ _,hA ?_⟩
    change R q ∈ univ ×ˢ Icc (0 : ℝ) 1
    rw [← hRb]
    exact mem_image_of_mem R hq
  have hai : a '' (univ ×ˢ Icc (0 : ℝ) 1) = A '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    calc
      _ = A '' (R '' (univ ×ˢ Icc (0 : ℝ) 1)) := by rw [image_image]; rfl
      _ = _ := by rw [hRb]
  have ha0 (z : SphereTwo) : a (z,0) = P (z,0) := by
    change A (R (z,0)) = _
    rw [hR,sub_zero,hone,η.apply_symm_apply]
  have ha1 (z : SphereTwo) : a (z,1) = P ((κ.symm.trans η).symm z,1) := by
    change A (R (z,1)) = _
    rw [hR,sub_self,hzero]
    rfl
  have hd := Manifold.sphereDiffeomorphDegree_eq_one_of_closed_cylinder_return a P o ha hP
    (by rw [hai]; exact hmeet) (κ.symm.trans η) ha0 ha1
  exact nonempty_diffeomorph_sphereTwoTimesCircle_of_opposite_slabs
    A P η κ hd hA hP hzero hone hmeet hcover

end DifferentialGeometry.Topology.DoubleCylinder
