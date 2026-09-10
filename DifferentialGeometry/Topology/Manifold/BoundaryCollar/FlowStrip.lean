import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowEmbedding
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.UniformFlow
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Function Filter Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.BoundaryCollar

theorem exists_smooth_embedded_boundary_strip
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ c : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε → M,
        Topology.IsClosedEmbedding c ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        ∀ p (t : Icc (0 : ℝ) ε), 0 < (t : ℝ) → (𝓡∂ (n + 1)).IsInteriorPoint (c (p, t)) := by
  obtain ⟨V, hV, _, U, hKU, ε, hε, F, hF, hzero, hcurve, hi, _⟩ :=
    exists_uniform_boundary_flow hK
  refine ⟨ε, hε, ?_⟩
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let c : B × Icc (0 : ℝ) ε → M := fun q => F ((q.1 : M), (q.2 : ℝ))
  have hc : ContMDiff ((HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)) I ∞ c := by
    exact hF.comp_contMDiff
      ((boundaryInclusion_contMDiff (I := I) (M := M)).prodMap
        (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)))
      (fun q => ⟨hKU q.1.2, q.2.2⟩)
  have hcinj : Injective c := boundary_flow_injective hV hKU hzero hcurve hi
  let : CompactSpace B := isCompact_iff_compactSpace.mp hK
  refine ⟨c, hc.continuous.isClosedEmbedding hcinj, hc, ?_, ?_⟩
  · intro p
    exact hzero p (hKU p.2)
  · intro p t ht
    exact hi p (hKU p.2) t ⟨ht, t.2.2⟩

end Poincare.Manifold.BoundaryCollar
