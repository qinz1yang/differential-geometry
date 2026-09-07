import DifferentialGeometry.Topology.Morse.RegularSublevel
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

theorem mfderiv_manifoldLevelSetInclusion_injective (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : LevelSetSpace f a) :
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    Function.Injective (mfderiv 𝓘(ℝ, MorseModel m) I (fun y : LevelSetSpace f a => y.1) x) := by
  let hcs := manifoldLevelSetChartedSpace I f a hf hreg
  let := manifoldLevelSetIsManifold I f a hf hreg
  let b := sublevelPullbackBump I x.1
  have hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g := sublevelPullbackCutoff I f x.1 b
  let p := levelSetPullbackCutoffPoint I f a x b
  have hg : ContDiff ℝ ∞ g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
  have hr : fderiv ℝ g p.1 ≠ 0 := fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b
  let V := levelSetChartValue g a p hg hr
  let G : M → MorseModel m := V ∘ extChartAt I x.1
  have hV : ContDiff ℝ 1 V := (contDiff_levelSetChartValue g a p hg hr).of_le (by simp)
  have hG : MDifferentiableAt I 𝓘(ℝ, MorseModel m) G x.1 :=
    hV.contMDiff.contMDiffAt.mdifferentiableAt (by simp) |>.comp x.1
      (mdifferentiableAt_extChartAt (mem_chart_source H x.1))
  have hi := (contMDiff_levelSetInclusion I f a hf hreg).contMDiffAt
    (x := x) |>.mdifferentiableAt (by simp)
  have heq : (G ∘ (fun y : LevelSetSpace f a => y.1)) =ᶠ[nhds x]
      extChartAt 𝓘(ℝ, MorseModel m) x := by
    filter_upwards [(chartAt (MorseModel m) x).open_source.mem_nhds
      (mem_chart_source (MorseModel m) x)] with y hy
    change y ∈ (levelSetPullbackChart I f a x b hb ≫ₕ levelSetChart g a p hg hr).source at hy
    change V (extChartAt I x.1 y.1) =
      levelSetChart g a p hg hr (levelSetPullbackChart I f a x b hb y)
    rw [levelSetChart_apply_value', levelSetPullbackChart_apply_of_mem I f a x b hb hy.1]
  have hd : (mfderiv I 𝓘(ℝ, MorseModel m) G x.1).comp
      (mfderiv 𝓘(ℝ, MorseModel m) I (fun y : LevelSetSpace f a => y.1) x) =
      ContinuousLinearMap.id ℝ (MorseModel m) := by
    rw [← mfderiv_comp x hG hi, heq.mfderiv_eq, mfderiv_extChartAt_self]
    rfl
  intro u v huv
  have h := congrArg (mfderiv I 𝓘(ℝ, MorseModel m) G x.1) huv
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hd] at h
  exact h

end

end DifferentialGeometry.Topology.Morse
