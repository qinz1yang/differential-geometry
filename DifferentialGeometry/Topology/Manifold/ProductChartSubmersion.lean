import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem contMDiff_and_surjective_mfderiv_snd_of_product_chart
    {E H W F H' M G H₀ N L H₁ P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H' M]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H₀]
    {K : ModelWithCorners ℝ G H₀} [TopologicalSpace N] [ChartedSpace H₀ N]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [TopologicalSpace H₁]
    {B : ModelWithCorners ℝ L H₁} [TopologicalSpace P] [ChartedSpace H₁ P]
    (O : TopologicalSpace.Opens (N × P)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮K.prod B, J⟯ V)
    (ι : W → M) (hι : ContMDiff I J ∞ ι)
    (hsurj : ∀ w, Function.Surjective (mfderiv I J ι w)) (hV : ∀ w, ι w ∈ V) :
    let q : W → P := fun w ↦ (Φ.symm ⟨ι w, hV w⟩ : N × P).2
    ContMDiff I B ∞ q ∧ ∀ w, Function.Surjective (mfderiv I B q w) := by
  let f : W → V := fun w ↦ ⟨ι w, hV w⟩
  have hf : ContMDiff I J ∞ f := (ContMDiff.subtypeVal_comp_iff V f).mp hι
  have hdf (w : W) : mfderiv I J f w = mfderiv I J ι w := by
    have h := mfderiv_comp w ((contMDiff_subtype_val (I := J) (n := ∞)).mdifferentiable (by decide) (f w))
      (hf.mdifferentiable (by decide) w)
    change mfderiv I J ι w = _ at h
    rw [mfderiv_subtype_val] at h
    ext z
    exact (DFunLike.congr_fun h z).symm
  let ψ : W → O := Φ.symm ∘ f
  have hψ : ContMDiff I (K.prod B) ∞ ψ := Φ.symm.contMDiff.comp hf
  have hψsurj (w : W) : Function.Surjective (mfderiv I (K.prod B) ψ w) := by
    change Function.Surjective (mfderiv I (K.prod B) (Φ.symm ∘ f) w)
    rw [mfderiv_comp w (Φ.symm.contMDiff.mdifferentiable (by decide) (f w))
      (hf.mdifferentiable (by decide) w), hdf]
    exact (Φ.symm.mfderivToContinuousLinearEquiv (by decide) (f w)).surjective.comp (hsurj w)
  let ψ' : W → N × P := fun w ↦ (ψ w : N × P)
  have hψ' : ContMDiff I (K.prod B) ∞ ψ' := contMDiff_subtype_val.comp hψ
  have hdψ' (w : W) : mfderiv I (K.prod B) ψ' w = mfderiv I (K.prod B) ψ w := by
    change mfderiv I (K.prod B) (Subtype.val ∘ ψ) w = _
    rw [mfderiv_comp w ((contMDiff_subtype_val (I := K.prod B) (n := ∞)).mdifferentiable (by decide) (ψ w))
      (hψ.mdifferentiable (by decide) w), mfderiv_subtype_val]
    change (ContinuousLinearMap.id ℝ (G × L)).comp (mfderiv I (K.prod B) ψ w : E →L[ℝ] G × L) = _
    exact ContinuousLinearMap.id_comp _
  refine ⟨contMDiff_snd.comp hψ', ?_⟩
  intro w y
  obtain ⟨z, hz⟩ := hψsurj w (0, y)
  refine ⟨z, ?_⟩
  change mfderiv I B (Prod.snd ∘ ψ') w z = y
  rw [mfderiv_comp w mdifferentiableAt_snd (hψ'.mdifferentiable (by decide) w), mfderiv_snd]
  change (mfderiv I (K.prod B) ψ' w z).2 = y
  rw [hdψ']
  change (mfderiv I (K.prod B) ψ w z : G × L).2 = y
  exact congrArg Prod.snd hz

end DifferentialGeometry.Topology.Manifold
