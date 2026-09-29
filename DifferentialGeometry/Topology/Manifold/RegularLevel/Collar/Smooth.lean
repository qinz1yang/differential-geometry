import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.ManifoldSmooth
import DifferentialGeometry.Topology.Manifold.RegularLevel.AtlasCompatibility
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel

set_option autoImplicit false

open Set Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology

noncomputable section

namespace DifferentialGeometry.Manifold.RegularLevel

theorem exists_smoothTwoSidedCollar_of_compact_regularLevel
    {m : ℕ} {f : MorseModel (m + 1) → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ)
    (hK : IsCompact {x | f x = a})
    (hr : ∀ x, f x = a → ¬ IsCriticalPointAt 𝓘(ℝ, MorseModel (m + 1)) f x) :
    let _ := manifoldLevelSetChartedSpace 𝓘(ℝ, MorseModel (m + 1)) f a hf.contMDiff hr
    ∃ c : SmoothTwoSidedCollar 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1))
      (Subtype.val : LevelSetSpace f a → MorseModel (m + 1)),
      ∀ p, f (c.toFun p) = a - p.2 := by
  let C := levelChartedSpace 𝓘(ℝ, MorseModel (m + 1)) hf.contMDiff hr
  let D := manifoldLevelSetChartedSpace
    𝓘(ℝ, MorseModel (m + 1)) f a hf.contMDiff hr
  let _ := D
  obtain ⟨c, hc⟩ := exists_smoothTwoSidedCollar_of_compact_regularLevel_manifold
    𝓘(ℝ, MorseModel (m + 1)) hf.contMDiff a hK hr
  let d : @Diffeomorph ℝ _ (MorseModel m) _ _ (MorseModel m) _ _
      (MorseModel m) _ (MorseModel m) _ 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m)
      (LevelSetSpace f a) _ C (LevelSetSpace f a) _ D ∞ :=
    levelAtlasDiffeomorph 𝓘(ℝ, MorseModel (m + 1)) hf.contMDiff hr
  have hd (x : LevelSetSpace f a) : d x = x := by
    rfl
  have hdi (x : LevelSetSpace f a) : d.symm x = x :=
    (d.toEquiv.symm_apply_eq).2 (hd x).symm
  let cD := @SmoothTwoSidedCollar.reparametrize
    (MorseModel m) _ _ (MorseModel m) _
    (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _
    𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1))
    (LevelSetSpace f a) _ C (MorseModel (m + 1)) _ inferInstance
    (Subtype.val : LevelSetSpace f a → MorseModel (m + 1)) c
    (MorseModel m) _ _ (MorseModel m) _ 𝓘(ℝ, MorseModel m)
    (LevelSetSpace f a) _ D d.symm
  let c' : SmoothTwoSidedCollar 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1))
      (Subtype.val : LevelSetSpace f a → MorseModel (m + 1)) :=
    { radius := cD.radius
      radius_pos := cD.radius_pos
      neighborhood := cD.neighborhood
      toDiffeomorph := cD.toDiffeomorph
      zero_eq := fun x => (cD.zero_eq x).trans (congrArg Subtype.val (hdi x)) }
  refine ⟨c', ?_⟩
  intro p
  exact hc (d.symm p.1, p.2)

end DifferentialGeometry.Manifold.RegularLevel
