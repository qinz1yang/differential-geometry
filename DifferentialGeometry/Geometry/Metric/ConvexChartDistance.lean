import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap

section

set_option autoImplicit false
noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

set_option backward.isDefEq.respectTransparency false in
theorem riemannianEDist_le_mul_edist_of_convex
    {f : V → M} {U S : Set V} {C : ℝ≥0}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) I 1 f U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hC : ∀ p ∈ S, ∀ v : V,
      ‖mfderiv 𝓘(ℝ, V) I f p v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    riemannianEDist I (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η := η.contDiff.contMDiff
  have hηS : MapsTo η (Icc (0 : ℝ) 1) S := hS.mapsTo_lineMap hx hy
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (f ∘ η) (Icc 0 1) :=
    hf.comp hη.contMDiffOn (fun t ht => hSU (hηS ht))
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) I (f ∘ η) t 1‖ₑ ≤ (C : ℝ≥0∞) * ‖y - x‖ₑ := by
    intro t ht
    have hdf := ((hf _ (hSU (hηS ht))).contMDiffAt
      (hU.mem_nhds (hSU (hηS ht)))).mdifferentiableAt one_ne_zero
    have hder : HasDerivAt η (y - x) t := AffineMap.hasDerivAt_lineMap
    have hDη : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η t (1 : ℝ) = y - x := by
      rw [mfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := η) (x := t)).trans hder.deriv
    rw [mfderiv_comp t hdf hder.differentiableAt.mdifferentiableAt]
    change ‖mfderiv 𝓘(ℝ, V) I f (η t) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) η t) 1)‖ₑ ≤ _
    rw [hDη]
    exact hC _ (hηS ht) _
  have hlen : pathELength I (f ∘ η) 0 1 ≤ (C : ℝ≥0∞) * ‖y - x‖ₑ := by
    rw [pathELength_eq_lintegral_mfderiv_Icc]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (C : ℝ≥0∞) * ‖y - x‖ₑ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hspeed t ht
      _ = _ := by simp
  have hd : riemannianEDist I (f x) (f y) ≤ pathELength I (f ∘ η) 0 1 := by
    apply riemannianEDist_le_pathELength hγ _ _ zero_le_one
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_zero]
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_one]
  apply hd.trans
  simpa only [← edist_eq_enorm_sub y x, edist_comm y x] using hlen

end Manifold

end

end
