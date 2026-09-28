import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace G Y]

theorem mfderivWithin_curve_eq_mfderiv_comp_apply_one
    (f : X → Y) (η : ℝ → X) (α : ℝ → Y) {K : Set ℝ} {w : ℝ}
    (hη : MDifferentiableAt 𝓘(ℝ, ℝ) I η w)
    (hf : MDifferentiableAt I J f (η w))
    (hK : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K w) (hw : w ∈ K)
    (heq : EqOn (f ∘ η) α K) :
    mfderivWithin 𝓘(ℝ, ℝ) J α K w (1 : ℝ) = mfderiv I J f (η w) (mfderiv 𝓘(ℝ, ℝ) I η w (1 : ℝ)) := by
  have hcongr : mfderivWithin 𝓘(ℝ, ℝ) J (f ∘ η) K w =
      mfderivWithin 𝓘(ℝ, ℝ) J α K w := by
    rw [mfderivWithin_congr_of_mem heq hw]
    rfl
  rw [← hcongr]
  rw [mfderivWithin_eq_mfderiv hK (hf.comp w hη)]
  rw [mfderiv_comp w hf hη]
  rfl

theorem mfderivWithin_left_curve_eq_mfderiv_comp_apply_one
    (f : X → Y) (η : ℝ → X) (α : ℝ → Y) {c w : ℝ} (hcw : c < w)
    (hη : MDifferentiableAt 𝓘(ℝ, ℝ) I η w)
    (hf : MDifferentiableAt I J f (η w))
    (heq : EqOn (f ∘ η) α (Icc c w)) :
    mfderivWithin 𝓘(ℝ, ℝ) J α (Icc c w) w (1 : ℝ) = mfderiv I J f (η w) (mfderiv 𝓘(ℝ, ℝ) I η w (1 : ℝ)) := by
  exact mfderivWithin_curve_eq_mfderiv_comp_apply_one f η α hη hf
    ((uniqueDiffOn_Icc hcw).uniqueMDiffOn w ⟨hcw.le, le_rfl⟩) ⟨hcw.le, le_rfl⟩ heq

theorem mfderivWithin_right_curve_eq_mfderiv_comp_apply_one
    (f : X → Y) (η : ℝ → X) (α : ℝ → Y) {w d : ℝ} (hwd : w < d)
    (hη : MDifferentiableAt 𝓘(ℝ, ℝ) I η w)
    (hf : MDifferentiableAt I J f (η w))
    (heq : EqOn (f ∘ η) α (Icc w d)) :
    mfderivWithin 𝓘(ℝ, ℝ) J α (Icc w d) w (1 : ℝ) = mfderiv I J f (η w) (mfderiv 𝓘(ℝ, ℝ) I η w (1 : ℝ)) := by
  exact mfderivWithin_curve_eq_mfderiv_comp_apply_one f η α hη hf
    ((uniqueDiffOn_Icc hwd).uniqueMDiffOn w ⟨le_rfl, hwd.le⟩) ⟨le_rfl, hwd.le⟩ heq

end DifferentialGeometry.Geometry
