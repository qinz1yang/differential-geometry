import DifferentialGeometry.Topology.Manifold.Boundary.SmoothMap
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Function Manifold Topology
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
  {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [TopologicalSpace X] [ChartedSpace G X]
  {J : ModelWithCorners ℝ F G} {ε : ℝ} [Fact ((0 : ℝ) < ε)]

theorem contMDiffAt_boundary_product_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M × Icc (0 : ℝ) ε} {x : X} :
    ContMDiffAt J (hI.boundaryI.prod (𝓡∂ 1)) k f x ↔
      ContMDiffAt J (I.prod 𝓘(ℝ, ℝ)) k
        (fun y => ((f y).1.val, (f y).2.val)) x := by
  constructor
  · intro h
    have hf := (DifferentialGeometry.Manifold.Boundary.contMDiffAt_boundary_iff hk).mp h.fst
    have ht := (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε) (n := k)).contMDiffAt.comp x h.snd
    exact hf.prodMk ht
  · intro h
    have hf := (DifferentialGeometry.Manifold.Boundary.contMDiffAt_boundary_iff hk).mpr h.fst
    have ht : ContMDiffAt J (𝓡∂ 1) k (fun y => (f y).2) x := by
      apply (ContMDiffAt.iff_comp_isImmersionAtOfComplement (f := fun y : X => (f y).2)
        (isImmersionOfComplement_subtypeVal_Icc (x := (0 : ℝ)) (y := ε) (n := k) (f x).2)).mpr
      exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr h.snd.continuousAt, h.snd⟩
    exact hf.prodMk ht


theorem contMDiff_boundary_product_iff {k : ℕ∞ω} (hk : k ≤ ∞)
    {f : X → BoundaryManifold I M × Icc (0 : ℝ) ε} :
    ContMDiff J (hI.boundaryI.prod (𝓡∂ 1)) k f ↔
      ContMDiff J (I.prod 𝓘(ℝ, ℝ)) k (fun y => ((f y).1.val, (f y).2.val)) := by
  exact forall_congr' fun _ => contMDiffAt_boundary_product_iff hk

end DifferentialGeometry.Manifold.BoundaryCollar
