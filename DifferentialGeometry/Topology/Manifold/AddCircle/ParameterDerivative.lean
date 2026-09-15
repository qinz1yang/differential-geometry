import DifferentialGeometry.Topology.Manifold.AddCircle
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

section

noncomputable section
open scoped Manifold ContDiff Topology

namespace AddCircle

theorem isLocalDiffeomorph_coe :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    contMDiff_coe (fun t => (bijective_mfderiv_coe t).1) rfl

private theorem quotient_mfderiv_eq {x y : ℝ}
    (h : (x : AddCircle (1 : ℝ)) = y) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) y := by
  have heq : (fun t : ℝ => ((t + (y - x) : ℝ) : AddCircle (1 : ℝ))) =
      fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
    funext t
    simp only [coe_add, coe_sub, ← h, sub_self, add_zero]
  have hder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + (y - x)) x =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_id x |>.add_const (y - x)).fderiv
  have hh := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
    (f := fun t : ℝ => t + (y - x))
    (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) x
    (contMDiff_coe.mdifferentiableAt (by decide))
    ((contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun t : ℝ => t + (y - x))).contMDiff.mdifferentiableAt (by decide))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => ((t + (y - x) : ℝ) : AddCircle (1 : ℝ))) x = _ at hh
  rw [heq] at hh
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + (y - x))).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + (y - x)) x) := hh
  have hcomp' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + (y - x)) := by
    rw [hder] at hcomp
    apply ContinuousLinearMap.coeFn_injective
    funext z
    exact congrFun (congrArg DFunLike.coe hcomp) z
  rw [show x + (y - x) = y by ring] at hcomp'
  exact hcomp'

def parameterTangent (z : AddCircle (1 : ℝ)) : TangentSpace 𝓘(ℝ, ℝ) z :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ)))
    (Quotient.out z) (1 : ℝ)

theorem parameterTangent_coe (x : ℝ) :
    parameterTangent (x : AddCircle (1 : ℝ)) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) x (1 : ℝ) := by
  unfold parameterTangent
  rw [quotient_mfderiv_eq (Quotient.out_eq _)]
  rfl

theorem parameterTangent_ne_zero (z : AddCircle (1 : ℝ)) : parameterTangent z ≠ 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [parameterTangent_coe]
  exact fun hz => (one_ne_zero : (1 : ℝ) ≠ 0) ((bijective_mfderiv_coe x).1 (hz.trans (map_zero _).symm))


set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_parameterTangent :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun z : AddCircle (1 : ℝ) =>
        (⟨z, parameterTangent z⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro t
    rw [Bundle.contMDiffAt_section]
    convert (contMDiffAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (c := (1 : ℝ)) (x := t)) using 1
    funext s
    simp only [TangentBundle.trivializationAt_apply, mfld_simps]
    change (fderivWithin ℝ id Set.univ s) (1 : ℝ) = 1
    rw [fderivWithin_id uniqueDiffWithinAt_univ]
    rfl
  have ht := (contMDiff_coe.contMDiff_tangentMap (m := ∞) le_rfl).comp hs
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hx := isLocalDiffeomorph_coe x
  have hc := (ht _).comp _ hx.localInverse_contMDiffAt
  apply hc.congr_of_eventuallyEq
  have heq := hx.localInverse_eventuallyEq_right
  filter_upwards [heq] with y hy
  change (⟨y, parameterTangent y⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) =
    ⟨(hx.localInverse y : AddCircle (1 : ℝ)),
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) (hx.localInverse y) (1 : ℝ)⟩
  rw [← parameterTangent_coe]
  change (hx.localInverse y : AddCircle (1 : ℝ)) = y at hy
  rw [hy]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_comp_coe {f : AddCircle (1 : ℝ) → F} {x : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f (x : AddCircle (1 : ℝ))) :
    deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f (x : AddCircle (1 : ℝ))
        (parameterTangent (x : AddCircle (1 : ℝ))) := by
  rw [parameterTangent_coe]
  have hh := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, F))
    (f := fun t : ℝ => (t : AddCircle (1 : ℝ))) (g := f) x hf
    (contMDiff_coe.mdifferentiableAt (by decide))
  rw [mfderiv_eq_fderiv] at hh
  exact congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) hh


theorem contMDiffAt_mfderiv_parameterTangent {f : AddCircle (1 : ℝ) → F}
    {m n : ℕ∞ω} {z : AddCircle (1 : ℝ)}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n f z) (hmn : m + 1 ≤ n) (hm : m ≤ ∞) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) m
      (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y (parameterTangent y)) z := by
  let e := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) z
  have hdf := hf.mfderiv_const hmn
  have hX : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) m
      (fun y => (e ⟨y, parameterTangent y⟩).2) z :=
    (Bundle.contMDiffAt_section (n := m) z).mp
      ((contMDiff_parameterTangent.of_le hm).contMDiffAt)
  refine (hdf.clm_apply hX).congr_of_eventuallyEq ?_
  filter_upwards
    [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt ℝ
      (TangentSpace 𝓘(ℝ, ℝ)) z)] with y hy
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.id_def,
    TangentBundle.continuousLinearMapAt_model_space]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y (parameterTangent y) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y
      (e.symmL ℝ y ((e ⟨y, parameterTangent y⟩).2))
  congr 1
  rw [e.symmL_apply hy]
  exact (Bundle.Trivialization.symm_apply_apply_mk e hy (parameterTangent y)).symm

theorem mdifferentiableAt_mfderiv_parameterTangent {f : AddCircle (1 : ℝ) → F}
    {z : AddCircle (1 : ℝ)} (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f z) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
      (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f y (parameterTangent y)) z :=
  (contMDiffAt_mfderiv_parameterTangent (m := 1) hf (by norm_num) (by norm_num)).mdifferentiableAt
    (by decide)

theorem deriv_deriv_comp_coe_of_contMDiffAt {f : AddCircle (1 : ℝ) → F} {x : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f (x : AddCircle (1 : ℝ))) :
    deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
        (fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z))
        (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ))) := by
  have hevent : ∀ᶠ y in 𝓝 (x : AddCircle (1 : ℝ)),
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf
  have heq : deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ))) =ᶠ[𝓝 x]
      fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f (t : AddCircle (1 : ℝ))
        (parameterTangent (t : AddCircle (1 : ℝ))) := by
    filter_upwards [(contMDiff_coe.continuous.continuousAt).eventually hevent] with t ht
    exact deriv_comp_coe (ht.mdifferentiableAt (by decide))
  rw [heq.deriv_eq]
  exact deriv_comp_coe (mdifferentiableAt_mfderiv_parameterTangent hf)

theorem contMDiff_mfderiv_parameterTangent {f : AddCircle (1 : ℝ) → F}
    {m n : ℕ∞ω} (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n f) (hmn : m + 1 ≤ n) (hm : m ≤ ∞) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) m
      (fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z)) :=
  fun z => contMDiffAt_mfderiv_parameterTangent (hf z) hmn hm

theorem deriv_deriv_comp_coe {f : AddCircle (1 : ℝ) → F}
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 2 f) (x : ℝ) :
    deriv (deriv (fun t : ℝ => f (t : AddCircle (1 : ℝ)))) x =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
        (fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) f z (parameterTangent z))
        (x : AddCircle (1 : ℝ)) (parameterTangent (x : AddCircle (1 : ℝ))) :=
  deriv_deriv_comp_coe_of_contMDiffAt (hf _)

set_option backward.isDefEq.respectTransparency false in
theorem exists_smul_parameterTangent (z : AddCircle (1 : ℝ))
    (v : TangentSpace 𝓘(ℝ, ℝ) z) : ∃ a : ℝ, a • parameterTangent z = v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨a, ha⟩ := (bijective_mfderiv_coe x).2 v
  let aR : ℝ := a
  refine ⟨aR, ?_⟩
  rw [parameterTangent_coe, ← map_smul]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    (fun t : ℝ => (t : AddCircle (1 : ℝ))) x (aR * 1) = v
  simpa only [mul_one] using ha


section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_comp_coe {f : AddCircle (1 : ℝ) → M} {x : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f (x : AddCircle (1 : ℝ))) :
    mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => f (y : AddCircle (1 : ℝ))) x (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I f (x : AddCircle (1 : ℝ))
        (parameterTangent (x : AddCircle (1 : ℝ))) := by
  rw [parameterTangent_coe]
  exact congrArg (fun L => L (1 : ℝ)) (mfderiv_comp (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ)) (I'' := I) (f := fun y : ℝ => (y : AddCircle (1 : ℝ)))
    (g := f) x hf (contMDiff_coe.mdifferentiableAt (by simp)))


end

end AddCircle

end

end
