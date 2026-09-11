import DifferentialGeometry.Analysis.Sobolev.Chart.Regularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated
import DifferentialGeometry.Geometry.Comparison.Busemann.Line.HigherSobolev
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry.Geometry.Riemannian

open Analysis.Laplacian.MetricExtension
open Analysis.Sobolev
open Analysis.Sobolev.IntrinsicLp
open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.exists_busemann_chartPushedRaw_contDiffOn_ball
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Chart.chartPushedRaw (I := I) (M := M) α
          (busemann (I := I) γ))
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I α α)) ρ) := by
  classical
  let c : EuclN := toEuclidean (E := E) (extChartAt I α α)
  let u : EuclN → ℝ :=
    Chart.chartPushedRaw (I := I) (M := M) α (busemann (I := I) γ)
  obtain ⟨r, hr, hu⟩ :=
    hγ.exists_busemann_chartPushedRaw_memWkp_on_ball
      (I := I) hEnorm hd hRic α
  have hu_r : ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 u (Metric.ball c r) := by
    simpa only [u, c] using hu
  have hc_target :
      c ∈ Chart.chartTargetEuclid (I := I) (M := M) α := by
    refine ⟨extChartAt I α α,
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α), ?_⟩
    rfl
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp
    ((Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hc_target)
  let ρ : ℝ := min r ε / 2
  have hmin : 0 < min r ε := lt_min hr hε
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact half_pos hmin
  have hρ_le_r : ρ ≤ r := by
    dsimp only [ρ]
    calc
      min r ε / 2 ≤ min r ε := by linarith
      _ ≤ r := min_le_left _ _
  have hρ_le_ε : ρ ≤ ε := by
    dsimp only [ρ]
    calc
      min r ε / 2 ≤ min r ε := by linarith
      _ ≤ ε := min_le_right _ _
  have hball_r : Metric.ball c ρ ⊆ Metric.ball c r :=
    Metric.ball_subset_ball hρ_le_r
  have hball_target :
      Metric.ball c ρ ⊆ Chart.chartTargetEuclid (I := I) (M := M) α :=
    (Metric.ball_subset_ball hρ_le_ε).trans hε_sub
  have hu_small : ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 u (Metric.ball c ρ) := by
    intro k
    exact Analysis.Sobolev.Euclidean.MemWkp.mono_set
      (by norm_num) Metric.isOpen_ball hball_r (hu_r k)
  have hpos_cont : Continuous (busemann (I := I) γ) :=
    continuous_busemann (I := I) hγ.positive_ray
  have hcomp_cont : ContinuousOn
      (fun y : EuclN ↦ busemann (I := I) γ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (Chart.chartTargetEuclid (I := I) (M := M) α) :=
    hpos_cont.comp_continuousOn'
      (Chart.continuousOn_symm_toEuclideanSymm (I := I) (M := M) α)
  have hu_cont : ContinuousOn u (Metric.ball c ρ) := by
    refine (hcomp_cont.mono hball_target).congr ?_
    intro y hy
    exact Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (busemann (I := I) γ) (hball_target hy)
  refine ⟨ρ, hρ, ?_⟩
  exact Analysis.Sobolev.EuclideanIteratedEmbedding.contDiffOn_of_continuousOn_of_forall_memWkp_two
    Metric.isOpen_ball hu_cont hu_small

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.busemann_contMDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (busemann (I := I) γ) := by
  intro α
  obtain ⟨ρ, hρ, hraw⟩ :=
    hγ.exists_busemann_chartPushedRaw_contDiffOn_ball
      (I := I) hEnorm hd hRic α
  exact Chart.contMDiffAt_of_contDiffAt_chartPushedRaw (I := I) α
    (hraw.contDiffAt (Metric.ball_mem_nhds
      (toEuclidean (E := E) (extChartAt I α α)) hρ))

end DifferentialGeometry.Geometry.Riemannian
