import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def expMap {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) : M :=
  (g.geodesicFlow p 1).proj

def expDomain {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    Set (TangentBundle I M) :=
  (fun p => (p, 1)) ⁻¹' g.geodesicFlowDomain

omit [I.Boundaryless] in
@[simp]
theorem zero_mem_expDomain {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) :
    (⟨x, 0⟩ : TangentBundle I M) ∈ g.expDomain :=
  g.mem_geodesicFlowDomain_zeroSection x 1

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

@[simp]
theorem expMap_zero (hr : 1 ≤ r) (x : M) :
    g.expMap (⟨x, 0⟩ : TangentBundle I M) = x := by
  exact congrArg TotalSpace.proj (g.geodesicFlow_zeroSection hr x 1)

theorem isOpen_expDomain (hr : 1 ≤ r) : IsOpen g.expDomain :=
  (g.isOpen_geodesicFlowDomain hr).preimage (continuous_id.prodMk continuous_const)

theorem contMDiffOn_expMap (hr : 1 ≤ r) :
    ContMDiffOn I.tangent I r g.expMap g.expDomain := by
  have htime : ContMDiff I.tangent (I.tangent.prod 𝓘(ℝ, ℝ)) r
      (fun p : TangentBundle I M => (p, (1 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  have hflow := (g.contMDiffOn_geodesicFlow hr).comp htime.contMDiffOn
    (s := g.expDomain) (fun _ hp => hp)
  have hproj : ContMDiff I.tangent I r (TotalSpace.proj : TangentBundle I M → M) :=
    Bundle.contMDiff_proj (TangentSpace I)
  exact hproj.comp_contMDiffOn hflow


end Bundle.ContMDiffRiemannianMetric

end
