import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_riemannianBallOf_subset_of_mem_nhds
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set M} (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ riemannianBallOf g p r ⊆ U := by
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have : RegularSpace M := inferInstance
  obtain ⟨c, hc, hsub⟩ := setOfPred_riemannianEDist_lt_subset_nhds (I := I) hU
  refine ⟨(c : ℝ), NNReal.coe_pos.mpr hc, ?_⟩
  intro y hy
  apply hsub
  change riemannianEDistOf (I := I) g p y < ENNReal.ofReal (c : ℝ) at hy
  rw [ENNReal.ofReal_coe_nnreal] at hy
  exact hy

end DifferentialGeometry
