import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Smoothness

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section NormalCoordinateSmoothness

open Set Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M']
  [ConnectedSpace M'] [T3Space M']
variable [RiemannianBundle (fun x : M' => TangentSpace I x)]
variable [PseudoEMetricSpace M'] [IsRiemannianManifold I M'] [CompleteSpace M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
theorem normalChartCenterOfMass_contDiffOn
    [Module.Finite ℝ E]
    [IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M')
    (hEnorm : IsMetricNorm (I := I) (M := M') g)
    (p : M') {ι : Type} [Fintype ι] (join : M' → M' → ℝ → M') (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r)
    {V : Set ((ι → ℝ) × (ι → E))}
    (hchz : ∀ params₀ ∈ V, ∀ n : ℕ, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z)
      (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params₀.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))
          join p r (H params₀))))
    (hchξ : ∀ params₀ ∈ V, ∀ n : ℕ, ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ params₀ ∈ V, ∀ n : ℕ, ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M' × M' => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm
        (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params₀.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))
            join p r (H params₀))),
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∀ params₀ ∈ V, ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E)
        (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params₀.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))
            join p r (H params₀))))
    (hz₀' : ∀ params₀ ∈ V,
      normalChartCenterOfMassEquationStandard (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params₀.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))
            join p r (H params₀))) params₀ = 0)
    (hc_solves : ∀ params₀ ∈ V, ∀ᶠ params in nhds params₀,
      normalChartCenterOfMassEquationStandard (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
            join p r (H params))) params = 0)
    (hc_cont : ∀ params₀ ∈ V, Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E))
      (nhds params₀)
      (nhds (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params₀.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))
          join p r (H params₀))))) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E)) V := by
  rw [contDiffOn_infty]
  intro n params₀ hp
  have hcd := centerOfMass_contDiffAt (I := I) g hEnorm p
    (NormalCoordinates.normalChartAt (I := I) g p
      (centerOfMass (I := I) g params₀.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))
        join p r (H params₀)))
    params₀ (max 1 n) (le_max_left 1 n) join r H
    (hchz params₀ hp (max 1 n)) (hchξ params₀ hp (max 1 n)) (hsm params₀ hp (max 1 n))
    (hinv' params₀ hp) (hz₀' params₀ hp) (hc_solves params₀ hp) (hc_cont params₀ hp)
  exact (hcd.of_le (by exact_mod_cast le_max_right 1 n)).contDiffWithinAt

end NormalCoordinateSmoothness

end CheegerGromovCompactness
end DifferentialGeometry
