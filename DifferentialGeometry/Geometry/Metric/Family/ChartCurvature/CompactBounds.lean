import DifferentialGeometry.Analysis.Calculus.TimeJet.EndpointJets
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Topology.Manifold.FiniteChartBalls

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_chartGram_jet_bound_on_compact
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J)
    {ι : Type*} [Finite ι] (α : ι → M) (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKt : ∀ i, K i ⊆ interior (extChartAt I (α i)).target)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b i j t, t ∈ J → ∀ x ∈ K b,
      ‖iteratedFDeriv ℝ k (chartGramOnE (g t) (α b) i j) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact
    (G := fun (b : ι × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) t x =>
      chartGramOnE (g t) (α b.1) b.2.1 b.2.2 x)
    (V := fun b => interior (extChartAt I (α b.1)).target) (K := fun b => K b.1)
    hJ (fun _ => isOpen_interior) hJc (fun b => hK b.1) (fun b => hKt b.1)
    (fun b => chartGramOnE_contDiffOn hg hJreg (α b.1) b.2.1 b.2.2) k
  exact ⟨C, hC, fun b i j t ht x hx => hbound (b, i, j) t ht x hx⟩

theorem exists_chartChristoffel_jet_bound_on_compact
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J)
    {ι : Type*} [Finite ι] (α : ι → M) (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKt : ∀ i, K i ⊆ interior (extChartAt I (α i)).target)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b i j l t, t ∈ J → ∀ x ∈ K b,
      ‖iteratedFDeriv ℝ k (chartChristoffel (g t) (α b) i j l) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact
    (G := fun (b : ι × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)) t x =>
      chartChristoffel (g t) (α b.1) b.2.1 b.2.2.1 b.2.2.2 x)
    (V := fun b => interior (extChartAt I (α b.1)).target) (K := fun b => K b.1)
    hJ (fun _ => isOpen_interior) hJc (fun b => hK b.1) (fun b => hKt b.1)
    (fun b => chartChristoffelOnE_contDiffOn hg hJreg hJ (α b.1) b.2.1 b.2.2.1 b.2.2.2) k
  exact ⟨C, hC, fun b i j l t ht x hx => hbound (b, i, j, l) t ht x hx⟩

theorem exists_finite_extChartAt_jet_bounds [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Finset M, ∃ K : M → Set E,
      (∀ p ∈ S, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      (∀ q, ∃ p ∈ S, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
        (∀ p ∈ S, ∀ i j t, t ∈ J → ∀ x ∈ K p,
          ‖iteratedFDeriv ℝ k (chartGramOnE (g t) p i j) x‖ ≤ C) ∧
        (∀ p ∈ S, ∀ i j l t, t ∈ J → ∀ x ∈ K p,
          ‖iteratedFDeriv ℝ k (chartChristoffel (g t) p i j l) x‖ ≤ C) := by
  obtain ⟨ρ, hρ, S, K, hK, hcover⟩ :=
    DifferentialGeometry.Topology.exists_finite_extChartAt_cover_with_margin (I := I) (M := M)
  have hKt (p : S) : K p ⊆ interior (extChartAt I (p : M)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p : M)).interior_eq]
    exact (hK p p.property).2
  refine ⟨ρ, hρ, S, K, hK, hcover, fun k => ?_⟩
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_chartGram_jet_bound_on_compact hg hJreg hJ hJc
    (fun p : S => (p : M)) (fun p => K p) (fun p => (hK p p.property).1) hKt k
  obtain ⟨C₂, _, hb₂⟩ := exists_chartChristoffel_jet_bound_on_compact hg hJreg hJ hJc
    (fun p : S => (p : M)) (fun p => K p) (fun p => (hK p p.property).1) hKt k
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_, ?_⟩
  · exact fun p hp i j t ht x hx => (hb₁ ⟨p, hp⟩ i j t ht x hx).trans (le_max_left _ _)
  · exact fun p hp i j l t ht x hx => (hb₂ ⟨p, hp⟩ i j l t ht x hx).trans (le_max_right _ _)

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
