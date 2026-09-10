import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import DifferentialGeometry.Topology.SphereSeparation.LocalNormalForm

set_option autoImplicit false

open Function Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.SphereSeparation

variable {e : SphereTwo → EuclideanThree} {x : SphereTwo}

noncomputable def sphereImmersionLocalRetraction
    (h : Manifold.IsImmersionAtOfComplement ℝ
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    EuclideanThree → SphereTwo :=
  fun y ↦ h.domChart.symm ((h.equiv.symm (h.codChart y)).1)

private theorem immersion_normal_form_at_base
    (h : Manifold.IsImmersionAtOfComplement ℝ
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    h.codChart (e x) = h.equiv (h.domChart x, 0) := by
  have hxTarget : h.domChart x ∈ h.domChart.target :=
    h.domChart.map_source h.mem_domChart_source
  have hxNormal := writtenInCharts_sphereTwo h hxTarget
  simpa [Function.comp_apply,
    h.domChart.left_inv h.mem_domChart_source] using hxNormal


theorem contMDiffAt_sphereImmersionLocalRetraction
    (h : Manifold.IsImmersionAtOfComplement ℝ
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞
      (sphereImmersionLocalRetraction h) (e x) := by
  have hxTarget : h.domChart x ∈ h.domChart.target :=
    h.domChart.map_source h.mem_domChart_source
  have hcoord :
      (h.equiv.symm (h.codChart (e x))).1 = h.domChart x := by
    rw [immersion_normal_form_at_base h, h.equiv.symm_apply_apply]
  have hcod : ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ h.codChart (e x) :=
    contMDiffAt_of_mem_maximalAtlas
      h.codChart_mem_maximalAtlas h.mem_codChart_source
  have hlinear : ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun y : EuclideanThree ↦ (h.equiv.symm y).1) (h.codChart (e x)) := by
    exact ContDiffAt.contMDiffAt
      (ContDiff.contDiffAt (contDiff_fst.comp h.equiv.symm.contDiff))
  have hdom : ContMDiffAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞
      h.domChart.symm ((h.equiv.symm (h.codChart (e x))).1) := by
    rw [hcoord]
    exact contMDiffAt_symm_of_mem_maximalAtlas
      h.domChart_mem_maximalAtlas hxTarget
  exact hdom.comp (e x) (hlinear.comp (e x) hcod)


theorem sphereImmersionLocalRetraction_comp_eventuallyEq
    (h : Manifold.IsImmersionAtOfComplement ℝ
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    sphereImmersionLocalRetraction h ∘ e =ᶠ[nhds x] id := by
  filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
  have hyTarget : h.domChart y ∈ h.domChart.target :=
    h.domChart.map_source hy
  have hyNormal := writtenInCharts_sphereTwo h hyTarget
  change h.domChart.symm ((h.equiv.symm (h.codChart (e y))).1) = y
  have hyNormal' :
      h.codChart (e y) = h.equiv (h.domChart y, 0) := by
    simpa [Function.comp_apply, h.domChart.left_inv hy] using hyNormal
  rw [hyNormal', h.equiv.symm_apply_apply]
  exact h.domChart.left_inv hy

theorem injective_mfderiv_of_isImmersionAtOfComplement_real
    (h : Manifold.IsImmersionAtOfComplement ℝ
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    Function.Injective
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ EuclideanThree) e x) := by
  let r := sphereImmersionLocalRetraction h
  have hr : MDifferentiableAt
      (modelWithCornersSelf ℝ EuclideanThree)
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) r (e x) :=
    (contMDiffAt_sphereImmersionLocalRetraction h).mdifferentiableAt (by simp)
  have he : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) e x :=
    h.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (r ∘ e) x =
        (mfderiv (modelWithCornersSelf ℝ EuclideanThree)
          (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) r (e x)).comp
          (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ EuclideanThree) e x) :=
    mfderiv_comp x hr he
  have hid :
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (r ∘ e) x =
        ContinuousLinearMap.id ℝ
          (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) x) := by
    rw [(sphereImmersionLocalRetraction_comp_eventuallyEq h).mfderiv_eq]
    exact mfderiv_id
  have hleftInverse :
      (mfderiv (modelWithCornersSelf ℝ EuclideanThree)
          (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) r (e x)).comp
          (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ EuclideanThree) e x) =
        ContinuousLinearMap.id ℝ
          (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) x) :=
    hcomp.symm.trans hid
  intro v w hvw
  have hv := congrArg
    (fun L : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) x →L[ℝ]
        TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) x ↦ L v)
    hleftInverse
  have hw := congrArg
    (fun L : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) x →L[ℝ]
        TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) x ↦ L w)
    hleftInverse
  simp only [ContinuousLinearMap.id_apply] at hv hw
  exact hv.symm.trans ((congrArg _ hvw).trans hw)

theorem injective_mvfderiv_of_isImmersionAtOfComplement_real
    (h : Manifold.IsImmersionAtOfComplement ℝ
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    Function.Injective (mvfderiv
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) e x) :=
  (NormedSpace.fromTangentSpace (e x)).injective.comp
    (injective_mfderiv_of_isImmersionAtOfComplement_real h)


noncomputable def embeddedSphereTangentPlane
    (e : SphereTwo → EuclideanThree) (x : SphereTwo) :
    Submodule ℝ EuclideanThree :=
  LinearMap.range
    (mvfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) e x).toLinearMap

noncomputable def embeddedSphereNormalLine
    (e : SphereTwo → EuclideanThree) (x : SphereTwo) :
    Submodule ℝ EuclideanThree :=
  (embeddedSphereTangentPlane e x)ᗮ


theorem finrank_embeddedSphereTangentPlane
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    Module.finrank ℝ (embeddedSphereTangentPlane e x) = 2 := by
  rw [embeddedSphereTangentPlane,
    LinearMap.finrank_range_of_inj
      (injective_mvfderiv_of_isImmersionAtOfComplement_real
        (isImmersionAtOfComplement_real_of_isSmoothEmbedding he x))]
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
  norm_num [Module.finrank_fin_fun]

theorem finrank_embeddedSphereNormalLine
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    Module.finrank ℝ (embeddedSphereNormalLine e x) = 1 := by
  have hsum :=
    (embeddedSphereTangentPlane e x).finrank_add_finrank_orthogonal
  rw [finrank_embeddedSphereTangentPlane he] at hsum
  norm_num [EuclideanThree, Module.finrank_fin_fun] at hsum
  change Module.finrank ℝ ((embeddedSphereTangentPlane e x)ᗮ) = 1
  omega

theorem isCompl_embeddedSphereTangentPlane_normalLine
    (e : SphereTwo → EuclideanThree) (x : SphereTwo) :
    IsCompl (embeddedSphereTangentPlane e x) (embeddedSphereNormalLine e x) := by
  exact (embeddedSphereTangentPlane e x).isCompl_orthogonal

theorem mem_embeddedSphereNormalLine_iff
    (e : SphereTwo → EuclideanThree) (x : SphereTwo) (v : EuclideanThree) :
    v ∈ embeddedSphereNormalLine e x ↔
      ∀ w ∈ embeddedSphereTangentPlane e x, inner ℝ w v = 0 := by
  rw [embeddedSphereNormalLine, Submodule.mem_orthogonal]

theorem exists_nonzero_mem_embeddedSphereNormalLine
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    ∃ v : EuclideanThree, v ≠ 0 ∧ v ∈ embeddedSphereNormalLine e x := by
  have hne : embeddedSphereNormalLine e x ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank ℝ (embeddedSphereNormalLine e x) = 0 := by
      rw [hbot]
      simp
    rw [finrank_embeddedSphereNormalLine he] at hzero
    omega
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨v, hvne, hv⟩

theorem EmbeddedSphereNormalChart.contMDiffOn_normalCoordinate
    {e : SphereTwo → EuclideanThree} {x : SphereTwo}
    (c : EmbeddedSphereNormalChart e x) :
    ContMDiffOn (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ ℝ) ∞
      c.normalCoordinate c.neighborhood := by
  change ContMDiffOn (modelWithCornersSelf ℝ EuclideanThree)
    (modelWithCornersSelf ℝ ℝ) ∞
    (fun y ↦ (c.normalForm.equiv.symm (c.normalForm.codChart y)).2)
    c.neighborhood
  intro y hy
  have hcod : ContMDiffAt (modelWithCornersSelf ℝ EuclideanThree)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ c.normalForm.codChart y :=
    contMDiffAt_of_mem_maximalAtlas c.normalForm.codChart_mem_maximalAtlas
      (c.neighborhood_subset_codChart_source hy)
  have hlinear : ContDiff ℝ ∞ (fun z : EuclideanThree ↦
      (c.normalForm.equiv.symm z).2) :=
    contDiff_snd.comp c.normalForm.equiv.symm.contDiff
  exact (hlinear.contDiffAt.contMDiffAt.comp y hcod).contMDiffWithinAt

end DifferentialGeometry.Topology.SphereSeparation
