import DifferentialGeometry.Topology.Manifold.Interval.Tangent
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
open Set Function Bundle Manifold
open scoped ContDiff Topology
noncomputable section
namespace Poincare.Manifold.Interval

theorem contMDiff_tangentCoordinateIcc_symm
    {a b : ℝ} [Fact (a < b)] :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 1).tangent ∞
      (fun q : Icc a b × ℝ =>
        (⟨q.1, (tangentCoordinateIcc q.1).symm q.2⟩ : TangentBundle (𝓡∂ 1) (Icc a b))) := by
  have hinput : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun q : Icc a b × ℝ => (⟨q.1.val, q.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro q
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨(contMDiff_subtypeVal_Icc.comp contMDiff_fst) q, ?_⟩
    convert (contMDiff_snd (I := 𝓡∂ 1) (J := 𝓘(ℝ, ℝ)) (M := Icc a b) (N := ℝ) q) using 1
    simp only [mfld_simps]
  have hproj := (contMDiffOn_projIcc (x := a) (y := b) (n := ∞)).contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) (uniqueDiffOn_Icc (Fact.out : a < b)).uniqueMDiffOn
  have hh := hproj.comp_contMDiff hinput (fun q => q.1.property)
  apply hh.congr
  intro q
  rw [tangentCoordinateIcc_symm_apply]
  simp only [Function.comp_apply, tangentMapWithin]
  apply TotalSpace.ext
  · exact (projIcc_of_mem (Fact.out : a < b).le q.1.property).symm
  · change HEq (q.2 • (1 : TangentSpace (𝓡∂ 1) q.1))
      (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc a b (Fact.out : a < b).le) (Icc a b) q.1.val q.2)
    have hlin : mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1)
        (projIcc a b (Fact.out : a < b).le) (Icc a b) q.1.val q.2 =
        q.2 • (1 : TangentSpace (𝓡∂ 1) (projIcc a b (Fact.out : a < b).le q.1.val)) := by
      have hr : (q.2 : TangentSpace 𝓘(ℝ, ℝ) q.1.val) =
          q.2 • (1 : TangentSpace 𝓘(ℝ, ℝ) q.1.val) := by
        change q.2 = q.2 * 1
        exact (mul_one _).symm
      conv_lhs => rw [hr]
      rw [map_smul, mfderivWithin_projIcc_one q.1.property]
    rw [hlin, projIcc_of_mem (Fact.out : a < b).le q.1.property]

def tangentBundleIccDiffeomorph {a b : ℝ} [Fact (a < b)] :
    Diffeomorph (𝓡∂ 1).tangent ((𝓡∂ 1).prod 𝓘(ℝ, ℝ))
      (TangentBundle (𝓡∂ 1) (Icc a b)) (Icc a b × ℝ) ∞ where
  toFun p := (p.proj, tangentCoordinateIcc p.proj p.2)
  invFun q := ⟨q.1, (tangentCoordinateIcc q.1).symm q.2⟩
  left_inv p := by
    change (⟨p.proj, (tangentCoordinateIcc p.proj).symm (tangentCoordinateIcc p.proj p.2)⟩ :
      TangentBundle (𝓡∂ 1) (Icc a b)) = p
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv q := Prod.ext rfl ((tangentCoordinateIcc q.1).apply_symm_apply q.2)
  contMDiff_toFun := (contMDiff_proj (TangentSpace (𝓡∂ 1))).prodMk contMDiff_tangentCoordinateIcc
  contMDiff_invFun := contMDiff_tangentCoordinateIcc_symm


theorem tangentBundleIccDiffeomorph_apply {a b : ℝ} [Fact (a < b)]
    (p : TangentBundle (𝓡∂ 1) (Icc a b)) :
    tangentBundleIccDiffeomorph p = (p.proj, tangentCoordinateIcc p.proj p.2) := rfl


theorem tangentBundleIccDiffeomorph_symm_apply {a b : ℝ} [Fact (a < b)]
    (q : Icc a b × ℝ) :
    tangentBundleIccDiffeomorph.symm q =
      (⟨q.1, q.2 • (1 : TangentSpace (𝓡∂ 1) q.1)⟩ : TangentBundle (𝓡∂ 1) (Icc a b)) := by
  change (⟨q.1, (tangentCoordinateIcc q.1).symm q.2⟩ : TangentBundle (𝓡∂ 1) (Icc a b)) = _
  rw [tangentCoordinateIcc_symm_apply]

end Poincare.Manifold.Interval
