import DifferentialGeometry.Geometry.Metric.MinimizingLog
import DifferentialGeometry.Topology.Compactness.DiagonalNeighborhood



noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



theorem exists_smooth_minimizingDiagLog_neighborhood (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ U : Set (M × M), IsOpen U ∧ (∀ p : M, (p, p) ∈ U) ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (minimizingDiagLog g hg) U := by
  have hlocal (p : M) : ∃ V : Set (M × M), IsOpen V ∧ (p, p) ∈ V ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (minimizingDiagLog g hg) V := by
    let B := standardDiagonalInverseBranch (I := I) g hg p
    have hB0 : B.hom (TotalSpace.mk' E p 0) = (p, p) := by
      refine (B.hom_eq B.zero_mem).trans ?_
      change (p, expMapIntrinsic (I := I) g hg p 0) = (p, p)
      rw [expMapIntrinsic_zero]
    have hpB : (p, p) ∈ B.hom.target := hB0 ▸ B.hom.map_source B.zero_mem
    obtain ⟨V, hV, hVopen, hpV⟩ := mem_nhds_iff.mp
      (inter_mem (B.hom.open_target.mem_nhds hpB)
        (minimizingDiagLog_eventually_eq_branch g hg p))
    refine ⟨V, hVopen, hpV, ?_⟩
    apply (B.inv_contMDiffOn.mono (fun y hy => (hV hy).1)).congr
    intro y hy
    exact (hV hy).2
  choose V hV hpV hsV using hlocal
  refine ⟨⋃ p, V p, isOpen_iUnion hV, fun p => mem_iUnion.mpr ⟨p, hpV p⟩, ?_⟩
  intro y hy
  obtain ⟨p, hyp⟩ := mem_iUnion.mp hy
  exact ((hsV p y hyp).contMDiffAt ((hV p).mem_nhds hyp)).contMDiffWithinAt



theorem exists_uniform_smooth_minimizingDiagLog (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ (ρ : ℝ≥0) (U : Set (M × M)), 0 < ρ ∧ IsOpen U ∧
      (∀ x y, Manifold.riemannianEDist I x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U) ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (minimizingDiagLog g hg) U := by
  obtain ⟨U, hU, hdiag, hs⟩ := exists_smooth_minimizingDiagLog_neighborhood g hg
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ : ℝ≥0, 0 < ρ ∧
      ∀ x y, Manifold.riemannianEDist I x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U := by
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    exact DifferentialGeometry.Analysis.exists_uniform_diagonal_radius hU hdiag
  exact ⟨ρ, U, hρ, hU, hρU, hs⟩

end DifferentialGeometry.Geometry
