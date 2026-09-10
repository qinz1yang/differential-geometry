import DifferentialGeometry.Topology.SphereSeparation.GlobalNormalAdjugate
import DifferentialGeometry.Topology.SphereSeparation.NormalizeDerivative
import Mathlib.Geometry.Manifold.Algebra.Structures

open Function Set
open scoped ContDiff Manifold Topology Matrix.Norms.Elementwise

namespace Poincare.Topology.SphereSeparation

theorem mvfderiv_subtypeVal_punctured (y : puncturedEuclideanThree) :
    mvfderiv (modelWithCornersSelf ℝ EuclideanThree)
      ((↑) : puncturedEuclideanThree → EuclideanThree)
      y = ContinuousLinearMap.id ℝ EuclideanThree := by
  have hdiff : MDifferentiableAt
      (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree)
      ((↑) : puncturedEuclideanThree → EuclideanThree)
      y :=
    (contMDiff_subtype_val (n := ∞)).contMDiffAt.mdifferentiableAt (by simp)
  rw [hdiff.mvfderiv]
  simp only [writtenInExtChartAt, extChartAt,
    OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph,
    PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    modelWithCornersSelf_coe, range_id, fderivWithin_univ,
    chartAt_self_eq]
  change fderiv ℝ
      (Subtype.val ∘ ⇑(chartAt EuclideanThree
        y).symm)
      (y : EuclideanThree) = ContinuousLinearMap.id ℝ EuclideanThree
  have heq :
      (Subtype.val ∘ ⇑(chartAt EuclideanThree
        y).symm) =ᶠ[nhds (y : EuclideanThree)]
        id := by
    have hraw :=
      (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
        (H := EuclideanThree) puncturedEuclideanThree
        (x := y)).symm
    have hamb : chartAt EuclideanThree
        (y : EuclideanThree) =
        OpenPartialHomeomorph.refl EuclideanThree :=
      @chartAt_self_eq EuclideanThree _
        (y : EuclideanThree)
    rw [hamb] at hraw
    simpa [OpenPartialHomeomorph.refl_apply, Function.comp_def] using hraw
  rw [heq.fderiv_eq]
  exact fderiv_id

theorem mvfderiv_eq_fderiv_self (f : EuclideanThree → EuclideanThree)
    (x : EuclideanThree) :
    mvfderiv (modelWithCornersSelf ℝ EuclideanThree)
      f x = fderiv ℝ f x := by
  rw [mvfderiv, mfderiv_eq_fderiv]
  ext v
  rfl

theorem mfderiv_subtypeVal_punctured (y : puncturedEuclideanThree) :
    mfderiv (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree)
      ((↑) : puncturedEuclideanThree → EuclideanThree)
      y = ContinuousLinearMap.id ℝ EuclideanThree := by
  have h := mvfderiv_subtypeVal_punctured y
  rw [mvfderiv] at h
  ext v
  have hv := congrArg (fun L : EuclideanThree →L[ℝ] EuclideanThree ↦ L v) h
  exact hv

theorem mvfderiv_punctured_normalize (x : SphereTwo) :
    mvfderiv (modelWithCornersSelf ℝ EuclideanThree)
      (fun y : puncturedEuclideanThree ↦
        NormedSpace.normalize (y : EuclideanThree))
      (spherePointInPunctured x) =
        unitSphereTangentProjection (x : EuclideanThree) := by
  let y := spherePointInPunctured x
  have hdiff : MDifferentiableAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree)
      (fun z : puncturedEuclideanThree ↦
        NormedSpace.normalize (z : EuclideanThree)) y :=
    contMDiff_punctured_normalize.contMDiffAt.mdifferentiableAt (by simp)
  rw [hdiff.mvfderiv]
  simp only [writtenInExtChartAt, extChartAt,
    OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph,
    PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    modelWithCornersSelf_coe, range_id, fderivWithin_univ,
    chartAt_self_eq]
  change fderiv ℝ
      (NormedSpace.normalize ∘ Subtype.val ∘
        ⇑(chartAt EuclideanThree y).symm)
      (x : EuclideanThree) =
        unitSphereTangentProjection (x : EuclideanThree)
  have hchart :
      (Subtype.val ∘ ⇑(chartAt EuclideanThree y).symm) =ᶠ[
        nhds (x : EuclideanThree)] id := by
    have hraw :=
      (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
        (H := EuclideanThree) puncturedEuclideanThree (x := y)).symm
    have hamb : chartAt EuclideanThree (y : EuclideanThree) =
        OpenPartialHomeomorph.refl EuclideanThree :=
      @chartAt_self_eq EuclideanThree _ (y : EuclideanThree)
    rw [hamb] at hraw
    simpa [OpenPartialHomeomorph.refl_apply, Function.comp_def,
      y, spherePointInPunctured] using hraw
  have heq :
      (NormedSpace.normalize ∘ Subtype.val ∘
        ⇑(chartAt EuclideanThree y).symm) =ᶠ[
          nhds (x : EuclideanThree)] NormedSpace.normalize := by
    filter_upwards [hchart] with z hz
    exact congrArg NormedSpace.normalize hz
  rw [heq.fderiv_eq,
    fderiv_normalize_of_norm_eq_one (norm_eq_of_mem_sphere x)]

@[simp] theorem puncturedRadialProjection_spherePoint (x : SphereTwo) :
    puncturedRadialProjection (spherePointInPunctured x) = x := by
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (norm_eq_of_mem_sphere x)

theorem radialProjectionDerivative_inclusion_comp (x : SphereTwo) :
    (mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((↑) : SphereTwo → EuclideanThree) x).comp
        (mfderiv (modelWithCornersSelf ℝ EuclideanThree)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          puncturedRadialProjection (spherePointInPunctured x)) =
      unitSphereTangentProjection (x : EuclideanThree) := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  let y := spherePointInPunctured x
  have hcoe : MDifferentiableAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree)
      ((↑) : SphereTwo → EuclideanThree) (puncturedRadialProjection y) :=
    (contMDiff_coe_sphere (E := EuclideanThree) (n := 2) (m := ∞)).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hp : MDifferentiableAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      puncturedRadialProjection y :=
    contMDiff_puncturedRadialProjection.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y hcoe hp
  have hmvcomp :
      mvfderiv (modelWithCornersSelf ℝ EuclideanThree)
        (((↑) : SphereTwo → EuclideanThree) ∘ puncturedRadialProjection) y =
      (mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        ((↑) : SphereTwo → EuclideanThree) (puncturedRadialProjection y)).comp
          (mfderiv (modelWithCornersSelf ℝ EuclideanThree)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            puncturedRadialProjection y) := by
    rw [mvfderiv, hcomp]
    rfl
  rw [puncturedRadialProjection_spherePoint] at hmvcomp
  change _ = unitSphereTangentProjection (x : EuclideanThree)
  rw [← mvfderiv_punctured_normalize x]
  set_option backward.isDefEq.respectTransparency false in
    simpa [y, Function.comp_def, puncturedRadialProjection,
      spherePointInPunctured] using hmvcomp.symm

theorem radialProjectionDerivative_surjective (x : SphereTwo) :
    Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ EuclideanThree)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        puncturedRadialProjection (spherePointInPunctured x)) := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  let inc := mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    ((↑) : SphereTwo → EuclideanThree) x
  let dp := mfderiv (modelWithCornersSelf ℝ EuclideanThree)
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    puncturedRadialProjection (spherePointInPunctured x)
  intro v
  have hv : inc v ∈ (ℝ ∙ (x : EuclideanThree))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (E := EuclideanThree) (n := 2) x]
    exact ⟨v, rfl⟩
  rw [← range_unitSphereTangentProjection
    (x := (x : EuclideanThree)) (norm_eq_of_mem_sphere x)] at hv
  obtain ⟨z, hz⟩ := hv
  refine ⟨z, ?_⟩
  apply injective_mvfderiv_subtypeVal_sphere (E := EuclideanThree) (n := 2) x
  have hcomp := radialProjectionDerivative_inclusion_comp x
  have happly := congrArg
    (fun L : EuclideanThree →L[ℝ] EuclideanThree ↦ L z) hcomp
  change inc (dp z) = inc v
  set_option backward.isDefEq.respectTransparency false in
    have hfirst := happly
    change inc (dp z) =
      unitSphereTangentProjection (x : EuclideanThree) z at hfirst
    exact hfirst.trans hz

theorem radialProjectionDerivative_apply_self (x : SphereTwo) :
    mfderiv (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      puncturedRadialProjection (spherePointInPunctured x)
      (x : EuclideanThree) = 0 := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  apply injective_mvfderiv_subtypeVal_sphere (E := EuclideanThree) (n := 2) x
  have hcomp := radialProjectionDerivative_inclusion_comp x
  have happly := congrArg
    (fun L : EuclideanThree →L[ℝ] EuclideanThree ↦ L (x : EuclideanThree)) hcomp
  set_option backward.isDefEq.respectTransparency false in
    let inc := mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((↑) : SphereTwo → EuclideanThree) x
    let dp := mfderiv (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      puncturedRadialProjection (spherePointInPunctured x)
    change inc (dp (x : EuclideanThree)) = inc 0
    change inc (dp (x : EuclideanThree)) =
      unitSphereTangentProjection (x : EuclideanThree) x at happly
    have hproj := unitSphereTangentProjection_apply_self
      (x := (x : EuclideanThree)) (norm_eq_of_mem_sphere x)
    exact happly.trans (hproj.trans (map_zero inc).symm)

theorem radialExtensionDerivative_eq_comp
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    radialExtensionDerivative e x =
      (mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        e x).comp
        (mfderiv (modelWithCornersSelf ℝ EuclideanThree)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          puncturedRadialProjection (spherePointInPunctured x)) := by
  let y := spherePointInPunctured x
  have he' : MDifferentiableAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree)
      e (puncturedRadialProjection y) :=
    he.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hp : MDifferentiableAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      puncturedRadialProjection y :=
    contMDiff_puncturedRadialProjection.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y he' hp
  rw [puncturedRadialProjection_spherePoint] at hcomp
  rw [radialExtensionDerivative, puncturedRadialExtension]
  rw [mvfderiv, hcomp]
  rfl

theorem radialExtensionDerivative_apply_self
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    radialExtensionDerivative e x (x : EuclideanThree) = 0 := by
  have hcomp := radialExtensionDerivative_eq_comp he x
  have happly := congrArg
    (fun L : EuclideanThree →L[ℝ] EuclideanThree ↦ L (x : EuclideanThree)) hcomp
  have hzero := radialProjectionDerivative_apply_self x
  set_option backward.isDefEq.respectTransparency false in
    let de := mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) e x
    let dp := mfderiv (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      puncturedRadialProjection (spherePointInPunctured x)
    change radialExtensionDerivative e x x = de (dp (x : EuclideanThree)) at happly
    change dp (x : EuclideanThree) = (0 : TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x) at hzero
    exact happly.trans ((congrArg de hzero).trans (map_zero de))

theorem range_radialExtensionDerivative
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    LinearMap.range (radialExtensionDerivative e x).toLinearMap =
      embeddedSphereTangentPlane e x := by
  have hcomp := radialExtensionDerivative_eq_comp he x
  have hrange := congrArg
    (fun L : EuclideanThree →L[ℝ] EuclideanThree ↦
      LinearMap.range L.toLinearMap) hcomp
  rw [hrange]
  rw [embeddedSphereTangentPlane]
  set_option backward.isDefEq.respectTransparency false in
    let de := mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) e x
    let dp := mfderiv (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      puncturedRadialProjection (spherePointInPunctured x)
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨dp w, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := radialProjectionDerivative_surjective x v
      refine ⟨w, ?_⟩
      change de (dp w) = de v
      exact congrArg de hw

theorem finrank_range_radialExtensionDerivative
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    Module.finrank ℝ
      (LinearMap.range (radialExtensionDerivative e x).toLinearMap) = 2 := by
  rw [range_radialExtensionDerivative he x,
    finrank_embeddedSphereTangentPlane he]

theorem embeddedSphereAdjugateNormal_ne_zero_mem
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    embeddedSphereAdjugateNormal e x ≠ 0 ∧
      embeddedSphereAdjugateNormal e x ∈ embeddedSphereNormalLine e x :=
  embeddedSphereAdjugateNormal_spec e x
    (radialExtensionDerivative_apply_self he x)
    (finrank_range_radialExtensionDerivative he x)
    (range_radialExtensionDerivative he x)

noncomputable def puncturedLiftAt (x : SphereTwo) (z : EuclideanThree) :
    puncturedEuclideanThree :=
  if hz : z ≠ 0 then ⟨z, hz⟩ else spherePointInPunctured x

theorem contMDiffAt_puncturedLiftAt (x : SphereTwo) :
    ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (puncturedLiftAt x) (x : EuclideanThree) := by
  rw [← ContMDiffAt.subtypeVal_comp_iff puncturedEuclideanThree
    (puncturedLiftAt x) (x : EuclideanThree)]
  apply ContDiffAt.contMDiffAt
  apply (contDiffAt_id : ContDiffAt ℝ ∞ id
    (x : EuclideanThree)).congr_of_eventuallyEq
  filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton
    (ne_zero_of_mem_unit_sphere x)] with z hz
  change z ≠ 0 at hz
  simp [puncturedLiftAt, hz]

theorem contMDiffAt_radialProjection (x : SphereTwo) :
    ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      radialProjection (x : EuclideanThree) := by
  have hlocal : ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (puncturedRadialProjection ∘ puncturedLiftAt x)
      (x : EuclideanThree) :=
    contMDiff_puncturedRadialProjection.contMDiffAt.comp _
      (contMDiffAt_puncturedLiftAt x)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton
    (ne_zero_of_mem_unit_sphere x)] with z hz
  change z ≠ 0 at hz
  apply Subtype.ext
  simp [puncturedLiftAt, puncturedRadialProjection,
    radialProjection, hz]

noncomputable def totalRadialExtension
    (e : SphereTwo → EuclideanThree) (z : EuclideanThree) : EuclideanThree :=
  e (radialProjection z)

theorem contDiffAt_totalRadialExtension
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    ContDiffAt ℝ ∞ (totalRadialExtension e) (x : EuclideanThree) := by
  apply ContMDiffAt.contDiffAt
  exact he.contMDiff.contMDiffAt.comp _ (contMDiffAt_radialProjection x)

theorem radialExtensionDerivative_eq_fderiv_total
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    radialExtensionDerivative e x =
      fderiv ℝ (totalRadialExtension e) (x : EuclideanThree) := by
  let y := spherePointInPunctured x
  have hdiff : MDifferentiableAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree)
      (puncturedRadialExtension e) y :=
    (contMDiff_puncturedRadialExtension he).contMDiffAt.mdifferentiableAt
      (by simp)
  rw [radialExtensionDerivative]
  change mvfderiv (modelWithCornersSelf ℝ EuclideanThree)
    (puncturedRadialExtension e) y = _
  rw [hdiff.mvfderiv]
  simp only [writtenInExtChartAt, extChartAt,
    OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph,
    PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    modelWithCornersSelf_coe, range_id, fderivWithin_univ,
    chartAt_self_eq]
  change fderiv ℝ
      (puncturedRadialExtension e ∘
        ⇑(chartAt EuclideanThree y).symm)
      (x : EuclideanThree) =
        fderiv ℝ (totalRadialExtension e) (x : EuclideanThree)
  have hchart :
      (Subtype.val ∘ ⇑(chartAt EuclideanThree y).symm) =ᶠ[
        nhds (x : EuclideanThree)] id := by
    have hraw :=
      (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
        (H := EuclideanThree) puncturedEuclideanThree (x := y)).symm
    have hamb : chartAt EuclideanThree (y : EuclideanThree) =
        OpenPartialHomeomorph.refl EuclideanThree :=
      @chartAt_self_eq EuclideanThree _ (y : EuclideanThree)
    rw [hamb] at hraw
    simpa [OpenPartialHomeomorph.refl_apply, Function.comp_def,
      y, spherePointInPunctured] using hraw
  have heq :
      (puncturedRadialExtension e ∘
        ⇑(chartAt EuclideanThree y).symm) =ᶠ[
          nhds (x : EuclideanThree)] totalRadialExtension e := by
    filter_upwards [hchart] with z hz
    have hz' : (((chartAt EuclideanThree y).symm z :
        puncturedEuclideanThree) : EuclideanThree) = z := by
      simpa [Function.comp_def] using hz
    have hz0 : z ≠ 0 := by
      rw [← hz']
      exact (chartAt EuclideanThree y).symm z |>.property
    change e (puncturedRadialProjection
      ((chartAt EuclideanThree y).symm z)) = e (radialProjection z)
    congr 1
    apply Subtype.ext
    rw [coe_radialProjection_of_ne_zero z hz0]
    exact congrArg NormedSpace.normalize hz'
  exact heq.fderiv_eq

theorem contMDiff_radialExtensionDerivative
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ
        (EuclideanThree →L[ℝ] EuclideanThree)) ∞
      (radialExtensionDerivative e) := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  intro x
  have hfd : ContDiffAt ℝ ∞
      (fderiv ℝ (totalRadialExtension e)) (x : EuclideanThree) :=
    (contDiffAt_totalRadialExtension he x).fderiv_right (by simp)
  have hcoe : ContMDiffAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      ((↑) : SphereTwo → EuclideanThree) x :=
    (contMDiff_coe_sphere (E := EuclideanThree) (n := 2)
      (m := ∞)).contMDiffAt
  have hcomp : ContMDiffAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ
        (EuclideanThree →L[ℝ] EuclideanThree)) ∞
      (fderiv ℝ (totalRadialExtension e) ∘
        ((↑) : SphereTwo → EuclideanThree)) x :=
    hfd.contMDiffAt.comp x hcoe
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  exact radialExtensionDerivative_eq_fderiv_total he y

noncomputable def coordinateMatrixLinearMap :
    (EuclideanThree →L[ℝ] EuclideanThree) →ₗ[ℝ]
      Matrix (Fin 3) (Fin 3) ℝ where
  toFun A := LinearMap.toMatrix' (coordinateLinearMap A)
  map_add' A B := by
    ext i j
    simp [coordinateLinearMap]
  map_smul' c A := by
    ext i j
    simp [coordinateLinearMap]

noncomputable def coordinateMatrix :
    (EuclideanThree →L[ℝ] EuclideanThree) →L[ℝ]
      Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap coordinateMatrixLinearMap

theorem coordinateMatrix_apply
    (A : EuclideanThree →L[ℝ] EuclideanThree) :
    coordinateMatrix A = LinearMap.toMatrix' (coordinateLinearMap A) := rfl

theorem contMDiff_sphereCoordinates : ContMDiff
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    (modelWithCornersSelf ℝ R3) ∞
    (fun x : SphereTwo ↦ e3coord (x : EuclideanThree)) := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  exact e3coord.contDiff.contMDiff.comp
    (contMDiff_coe_sphere (E := EuclideanThree) (n := 2) (m := ∞))

theorem contMDiff_coordinateEmbeddedSphereAdjugateNormal
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ R3) ∞
      (fun x : SphereTwo ↦ matrixAdjugateNormal
        (coordinateMatrix (radialExtensionDerivative e x))
        (e3coord (x : EuclideanThree))) := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  have hentryAmbient : ∀ i j : Fin 3, ContDiff ℝ ∞
      (fun A : EuclideanThree →L[ℝ] EuclideanThree ↦
        coordinateMatrix A i j) := by
    intro i j
    exact (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 3 → ℝ) i).comp coordinateMatrix.contDiff)
  have hadjAmbient : ∀ i j : Fin 3, ContDiff ℝ ∞
      (fun A : EuclideanThree →L[ℝ] EuclideanThree ↦
        (coordinateMatrix A).adjugate i j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_three] using
        (hentryAmbient 1 1).mul (hentryAmbient 2 2) |>.sub
          ((hentryAmbient 1 2).mul (hentryAmbient 2 1))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentryAmbient 0 1).mul (hentryAmbient 2 2)).neg.add
          ((hentryAmbient 0 2).mul (hentryAmbient 2 1))
    · simpa [Matrix.adjugate_fin_three] using
        (hentryAmbient 0 1).mul (hentryAmbient 1 2) |>.sub
          ((hentryAmbient 0 2).mul (hentryAmbient 1 1))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentryAmbient 1 0).mul (hentryAmbient 2 2)).neg.add
          ((hentryAmbient 1 2).mul (hentryAmbient 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        (hentryAmbient 0 0).mul (hentryAmbient 2 2) |>.sub
          ((hentryAmbient 0 2).mul (hentryAmbient 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentryAmbient 0 0).mul (hentryAmbient 1 2)).neg.add
          ((hentryAmbient 0 2).mul (hentryAmbient 1 0))
    · simpa [Matrix.adjugate_fin_three] using
        (hentryAmbient 1 0).mul (hentryAmbient 2 1) |>.sub
          ((hentryAmbient 1 1).mul (hentryAmbient 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        ((hentryAmbient 0 0).mul (hentryAmbient 2 1)).neg.add
          ((hentryAmbient 0 1).mul (hentryAmbient 2 0))
    · simpa [Matrix.adjugate_fin_three] using
        (hentryAmbient 0 0).mul (hentryAmbient 1 1) |>.sub
          ((hentryAmbient 0 1).mul (hentryAmbient 1 0))
  have hadj : ∀ i j : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : SphereTwo ↦
        (coordinateMatrix (radialExtensionDerivative e x)).adjugate i j) := by
    intro i j
    exact (hadjAmbient i j).comp_contMDiff
      (contMDiff_radialExtensionDerivative he)
  have hx := contMDiff_sphereCoordinates
  rw [contMDiff_pi_space]
  intro i
  change ContMDiff
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    (modelWithCornersSelf ℝ ℝ) ∞
    (fun x : SphereTwo ↦
      ∑ j, (coordinateMatrix (radialExtensionDerivative e x)).adjugate j i *
        e3coord (x : EuclideanThree) j)
  exact ContMDiff.sum fun j _ ↦
    (hadj j i).mul ((contDiff_apply ℝ ℝ j).contMDiff.comp hx)

theorem contMDiff_embeddedSphereAdjugateNormal
    {e : SphereTwo → EuclideanThree}
    (he : Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (embeddedSphereAdjugateNormal e) := by
  let _ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by
    norm_num [EuclideanThree, Module.finrank_fin_fun]⟩
  have htransport : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞
      (fun x : SphereTwo ↦ e3coord.symm (matrixAdjugateNormal
        (coordinateMatrix (radialExtensionDerivative e x))
        (e3coord (x : EuclideanThree)))) := by
    exact e3coord.symm.contDiff.contMDiff.comp
      (contMDiff_coordinateEmbeddedSphereAdjugateNormal he)
  apply htransport.congr
  intro x
  rfl

end Poincare.Topology.SphereSeparation
