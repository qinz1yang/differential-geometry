import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction
import DifferentialGeometry.Analysis.Calculus.Retraction.Approximation
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import Mathlib.Geometry.Manifold.SmoothApprox










noncomputable section

open Set Filter Function Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_riemannian_approximation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : V → M} (hu : Continuous u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : V → M, ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ v ∧
      ∀ x, riemannianEDistOf g (v x) (u x) < ENNReal.ofReal ε := by
  let : Nonempty M := ⟨u 0⟩
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    exists_compact_embedding_and_retraction (E := E) (M := M)
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨δ, hδ, hδr⟩ := DifferentialGeometry.Analysis.exists_uniform_retraction_radius
    he.continuous hU heU hr.continuousOn hleft (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨w, hw, hwu, _⟩ := (he.continuous.comp hu).exists_contDiff_approx (⊤ : ℕ∞)
    continuous_const (fun _ => hδ)
  have hwU (x : V) : w x ∈ U := (hδr (u x) (w x) (hwu x)).1
  refine ⟨r ∘ w, ?_, ?_⟩
  · intro x
    exact ((hr (w x) (hwU x)).contMDiffAt (hU.mem_nhds (hwU x))).comp x
      hw.contMDiff.contMDiffAt
  · intro x
    exact (hδr (u x) (w x) (hwu x)).2



theorem exists_smooth_disk_approximation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℂ → M, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ v ∧
      ∀ z : closedDisk, riemannianEDistOf g (v z) (u z) < ENNReal.ofReal ε := by
  obtain ⟨v, hv, hvu⟩ := exists_smooth_riemannian_approximation g
    (u.continuous.comp diskRetraction_lipschitz.continuous) hε
  refine ⟨v, hv, fun z => ?_⟩
  simpa only [Function.comp_apply, diskRetraction_coe] using hvu (z : ℂ)

end DifferentialGeometry.Geometry
