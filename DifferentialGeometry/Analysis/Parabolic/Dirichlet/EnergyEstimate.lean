import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakUniqueness

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

theorem exists_uniform_weak_evolution_norm_sq_le_initial
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T),
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u →
        ‖u‖ ^ 2 ≤ C * ‖f₀‖ ^ 2 := by
  by_cases hpos : 0 < T
  · obtain ⟨C, hC, hsolution⟩ := exists_uniform_dirichlet_integrated_weak_solution_norm_sq_le
      hG hpos hreg X hXcont a hacont Bx Bv hX htrace ha
    refine ⟨C, hC, ?_⟩
    intro f₀ u hu
    obtain ⟨v, hv, hvnorm⟩ := hsolution f₀
    have huv : u = v :=
      hu.unique hXcont hacont (hv.isWeakEvolutionSolution hpos hXcont hacont)
    exact huv.symm ▸ hvnorm
  · refine ⟨0, le_rfl, ?_⟩
    intro f₀ u hu
    have hunorm : ‖u‖ = 0 := by
      simp only [Lp.norm_def, timeMeasure_eq_zero_of_nonpos (le_of_not_gt hpos),
        eLpNorm_measure_zero, ENNReal.toReal_zero]
    simp only [hunorm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      le_refl]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
