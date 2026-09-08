import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder
import DifferentialGeometry.Geometry.Comparison.Busemann.Line.WeakSolution
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry.Geometry.Riemannian

open Analysis.Laplacian.MetricExtension
open Analysis.Sobolev
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
theorem IsMinimizingLine.exists_busemann_chartPushedRaw_memWkp_on_ball
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2
        (Chart.chartPushedRaw (I := I) (M := M) α
          (busemann (I := I) γ))
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I α α)) ρ) := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let c : EuclN := toEuclidean (E := E) (extChartAt I α α)
  let u : EuclN → ℝ :=
    Chart.chartPushedRaw (I := I) (M := M) α (busemann (I := I) γ)
  obtain ⟨r, hr, A, s, hs, hA, hsol⟩ :=
    hγ.exists_busemann_chartPushedRaw_isSolution_on_ball_with_metric_coefficient
      (I := I) hEnorm hd hRic α
  have hc_target :
      c ∈ Chart.chartTargetEuclid (I := I) (M := M) α := by
    refine ⟨extChartAt I α α,
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α), ?_⟩
    rfl
  let O : Set EuclN := Metric.ball c r ∩
    Chart.chartTargetEuclid (I := I) (M := M) α
  have hO_open : IsOpen O :=
    Metric.isOpen_ball.inter
      (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
  have hcO : c ∈ O := ⟨Metric.mem_ball_self hr, hc_target⟩
  have hsingleton_O : ({c} : Set EuclN) ⊆ O := by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hcO
  obtain ⟨δ, hδ, hδ_sub⟩ :=
    (isCompact_singleton : IsCompact ({c} : Set EuclN)).exists_cthickening_subset_open
      hO_open hsingleton_O
  let K : Set EuclN := Metric.cthickening δ ({c} : Set EuclN)
  have hK_eq : K = Metric.closedBall c δ := by
    dsimp only [K]
    exact Metric.cthickening_singleton c hδ.le
  have hK_compact : IsCompact K := by
    rw [hK_eq]
    exact isCompact_closedBall c δ
  have hK_ball : K ⊆ Metric.ball c r := fun x hx ↦ (hδ_sub hx).1
  have hK_target :
      K ⊆ Chart.chartTargetEuclid (I := I) (M := M) α :=
    fun x hx ↦ (hδ_sub hx).2
  obtain ⟨_, _, _, _, _, B, hB, _⟩ :=
    exists_smooth_metric_extension (I := I) g α hK_compact hK_target
  have hδ_half : 0 < δ / 2 := half_pos hδ
  have hδ_fourth : 0 < δ / 4 := by positivity
  have houter_K : Metric.closedBall c (δ / 2) ⊆ K := by
    intro x hx
    rw [hK_eq]
    exact Metric.closedBall_subset_closedBall (by linarith) hx
  have houter_original :
      Metric.closedBall c (δ / 2) ⊆ Metric.ball c r :=
    houter_K.trans hK_ball
  have hinner_compact : IsCompact (closure (Metric.ball c (δ / 4))) :=
    (isCompact_closedBall c (δ / 4)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hinner_outer :
      closure (Metric.ball c (δ / 4)) ⊆ Metric.ball c (δ / 2) :=
    Metric.closure_ball_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by linarith))
  let Ahalf : DeGiorgi.EllipticCoeff (Module.finrank ℝ E)
      (Metric.ball c (δ / 2)) :=
    A.1.restrict (Metric.ball_subset_closedBall.trans houter_original)
  have hsol_half : DeGiorgi.IsSolution Ahalf u := by
    dsimp only [Ahalf]
    exact hsol.restrict_ball (d := Module.finrank ℝ E)
      Metric.isOpen_ball hδ_half houter_original
  have hcoeff : ∀ x ∈ Metric.ball c (δ / 2),
      ∀ i j : Fin (Module.finrank ℝ E),
        Ahalf.a x i j = s * B.a x i j := by
    intro x hx i j
    have hxK : x ∈ K :=
      houter_K (Metric.ball_subset_closedBall hx)
    change A.1.a x i j = s * B.a x i j
    rw [hA x (hK_ball hxK) i j, hB x hxK i j]
  have hall : ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 u (Metric.ball c (δ / 4)) := fun k =>
    hsol_half.memWkp k Metric.isOpen_ball Metric.isOpen_ball hinner_compact hinner_outer
      B hs.ne' hcoeff
  refine ⟨δ / 4, hδ_fourth, ?_⟩
  simpa only [u, c] using hall

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.exists_busemann_chartPushedRaw_memWkp_two_on_ball
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (Chart.chartPushedRaw (I := I) (M := M) α
          (busemann (I := I) γ))
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I α α)) ρ) := by
  obtain ⟨ρ, hρ, hreg⟩ :=
    hγ.exists_busemann_chartPushedRaw_memWkp_on_ball (I := I) hEnorm hd hRic α
  exact ⟨ρ, hρ, hreg 2⟩

end DifferentialGeometry.Geometry.Riemannian
