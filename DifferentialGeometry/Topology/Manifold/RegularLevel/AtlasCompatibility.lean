import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff
open DifferentialGeometry.Topology.Morse

noncomputable section

namespace DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a : ℝ}
  (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)

theorem contMDiff_levelAtlas_id :
    @ContMDiff ℝ _ (MorseModel m) _ _ (MorseModel m) _ 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (levelChartedSpace I hf hr)
      (MorseModel m) _ _ (MorseModel m) _ 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hr)
      ∞ (id : LevelSetSpace f a → LevelSetSpace f a) := by
  let _ := levelChartedSpace I hf hr
  let _ := levelIsManifold I hf hr
  exact contMDiff_levelSet_factor I f a hf hr
    (Subtype.val : LevelSetSpace f a → M)
    (contMDiff_level_inclusion I hf hr) (fun x => x.property)
    (hcs := manifoldLevelSetChartedSpace I f a hf hr) (hchart := fun _ => rfl)

theorem contMDiff_id_levelAtlas :
    @ContMDiff ℝ _ (MorseModel m) _ _ (MorseModel m) _ 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hr)
      (MorseModel m) _ _ (MorseModel m) _ 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (levelChartedSpace I hf hr)
      ∞ (id : LevelSetSpace f a → LevelSetSpace f a) := by
  let _ := manifoldLevelSetChartedSpace I f a hf hr
  exact contMDiff_level_factor I hf hr
    (contMDiff_levelSetInclusion I f a hf hr
      (hcs := manifoldLevelSetChartedSpace I f a hf hr) (hchart := fun _ => rfl))
    (fun x => x.property)

def levelAtlasDiffeomorph :
    @Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _ 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (levelChartedSpace I hf hr)
      (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hr) ∞ :=
  @Diffeomorph.mk ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
    (MorseModel m) _ (MorseModel m) _ 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m)
    (LevelSetSpace f a) _ (levelChartedSpace I hf hr)
    (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hr) ∞
    (Equiv.refl (LevelSetSpace f a))
    (contMDiff_levelAtlas_id I hf hr) (contMDiff_id_levelAtlas I hf hr)

@[simp]
theorem levelAtlasDiffeomorph_apply (x : LevelSetSpace f a) :
    levelAtlasDiffeomorph I hf hr x = x := rfl

@[simp]
theorem levelAtlasDiffeomorph_symm_apply (x : LevelSetSpace f a) :
    (@Diffeomorph.symm ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _ 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (levelChartedSpace I hf hr)
      (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hr) ∞
      (levelAtlasDiffeomorph I hf hr)) x = x := rfl

theorem levelAtlasDiffeomorph_apply_val (x : LevelSetSpace f a) :
    (levelAtlasDiffeomorph I hf hr x).val = x.val := rfl

theorem levelAtlasDiffeomorph_symm_apply_val (x : LevelSetSpace f a) :
    ((@Diffeomorph.symm ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _ 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ (levelChartedSpace I hf hr)
      (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hr) ∞
      (levelAtlasDiffeomorph I hf hr)) x).val = x.val := rfl

end DifferentialGeometry.Manifold.RegularLevel
