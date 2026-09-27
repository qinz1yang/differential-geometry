import DifferentialGeometry.Geometry.Metric.Cylinder
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiff_vertical_inner
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner (x, t) (0, 1) (0, 1)) := by
  let s : M → M × ℝ := fun x => (x, t)
  have hs : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ s :=
    contMDiff_id.prodMk contMDiff_const
  have hV : ContMDiff I ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) ∞
      (fun x : M => (⟨s x, (0, 1)⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) :=
    DifferentialGeometry.Geometry.Metric.contMDiff_cylinderAxis.comp hs
  have htotal : ContMDiff I ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial (M × ℝ) ℝ) (s x)
        (g.inner (s x) (0, 1) (0, 1))) :=
    ContMDiff.clm_bundle_apply₂ (g.contMDiff.comp hs) hV hV
  intro x
  have hx := htotal x
  rw [contMDiffAt_totalSpace] at hx
  exact hx.2

theorem vertical_inner_pos
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (x : M) (t : ℝ) :
    0 < g.inner (x, t) (0, 1) (0, 1) := by
  apply g.pos
  intro hzero
  have h := congrArg Prod.snd hzero
  exact one_ne_zero h

theorem contMDiff_sqrt_vertical_inner
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Real.sqrt (g.inner (x, t) (0, 1) (0, 1))) := by
  intro x
  exact (Real.contDiffAt_sqrt (g.vertical_inner_pos x t).ne').contMDiffAt.comp x
    (g.contMDiff_vertical_inner t).contMDiffAt

theorem sqrt_vertical_inner_pos
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) (x : M) (t : ℝ) :
    0 < Real.sqrt (g.inner (x, t) (0, 1) (0, 1)) :=
  Real.sqrt_pos.mpr (g.vertical_inner_pos x t)

end DifferentialGeometry.SmoothRiemannianMetric
