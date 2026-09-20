import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section

open Filter Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M T G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem mdifferentiableAt_prod_of_differentiableAt_chart
    (f : T × M → G) (x : M) {v : E} (hv : v ∈ (extChartAt I x).target) (t : T)
    (hf : DifferentiableAt ℝ
      (fun z : E × T => f (z.2, (extChartAt I x).symm z.1)) (v, t)) :
    MDifferentiableAt ((𝓘(ℝ, T)).prod I) 𝓘(ℝ, G) f (t, (extChartAt I x).symm v) := by
  have hsource : (extChartAt I x).symm v ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hv
  have hchart := mdifferentiableAt_extChartAt (I := I) (by
    simpa only [extChartAt_source] using hsource)
  have hmap : MDifferentiableAt ((𝓘(ℝ, T)).prod I) 𝓘(ℝ, E × T)
      (fun z : T × M => ((extChartAt I x) z.2, z.1))
      (t, (extChartAt I x).symm v) :=
    (hchart.comp (t, (extChartAt I x).symm v)
      mdifferentiableAt_snd).prodMk_space mdifferentiableAt_fst
  have hcomp := hf.mdifferentiableAt.comp_of_eq
    (t, (extChartAt I x).symm v) hmap (by
      simp only [(extChartAt I x).right_inv hv])
  apply hcomp.congr_of_eventuallyEq
  have hnear : ∀ᶠ z : T × M in 𝓝 (t, (extChartAt I x).symm v),
      z.2 ∈ (extChartAt I x).source :=
    continuous_snd.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source (I := I) x).mem_nhds hsource)
  filter_upwards [hnear] with z hz
  simp only [Function.comp_apply, (extChartAt I x).left_inv hz]

end DifferentialGeometry.Topology.Manifold

variable {E₁ E₂ E₃ E₄ H₁ H₂ H₃ H₄ M₁ M₂ M₃ M₄ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
  [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace H₃] [TopologicalSpace H₄]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {I₃ : ModelWithCorners ℝ E₃ H₃} {I₄ : ModelWithCorners ℝ E₄ H₄}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  [TopologicalSpace M₄] [ChartedSpace H₄ M₄]

theorem IsLocalDiffeomorphAt.mdifferentiableAt_prodMap_of_comp
    {q : M₁ → M₂} {x : M₁} {n : WithTop ℕ∞}
    (hq : IsLocalDiffeomorphAt I₁ I₂ n q x) (hn : n ≠ 0)
    {f : M₄ × M₂ → M₃} (t : M₄)
    (hf : MDifferentiableAt (I₄.prod I₁) I₃ (fun z : M₄ × M₁ => f (z.1, q z.2))
      (t, x)) :
    MDifferentiableAt (I₄.prod I₂) I₃ f (t, q x) := by
  have hmap : MDifferentiableAt (I₄.prod I₂) (I₄.prod I₁)
      (fun z : M₄ × M₂ => (z.1, hq.localInverse z.2)) (t, q x) :=
    mdifferentiableAt_fst.prodMk
      ((hq.localInverse_mdifferentiableAt hn).comp (t, q x) mdifferentiableAt_snd)
  have hcomp := hf.comp_of_eq (t, q x) hmap (by
    simp only [hq.localInverse_left_inv hq.localInverse_mem_target])
  apply hcomp.congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : M₄ × M₂ → M₂)
      (𝓝 (t, q x)) (𝓝 (q x)) := continuous_snd.continuousAt
  have hnear : ∀ᶠ z : M₄ × M₂ in 𝓝 (t, q x),
      q (hq.localInverse z.2) = z.2 :=
    hsnd.eventually hq.localInverse_eventuallyEq_right
  filter_upwards [hnear] with z hz
  change f z = f (z.1, q (hq.localInverse z.2))
  rw [hz]
