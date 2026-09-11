import DifferentialGeometry.Analysis.Parabolic.Dirichlet.EnergyEstimate

set_option autoImplicit false

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

variable {q : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M}
variable {D : RealTimeInterval}
variable {G : MetricConnectionFamilyOn (I := (modelWithCornersEuclideanHalfSpace n)) (M := M) D}
variable {hG : MetricFamilySmoothOn (I := (modelWithCornersEuclideanHalfSpace n)) (M := M) D G.metric}
variable {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
variable {X : ℝ → Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n); EuclideanSpace ℝ (Fin n),
    (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯}
variable {a : ℝ → ℝ} {Bx Bv : ℝ}
variable {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
    (G.metric t).inner x (X t x) (X t x) ≤ Bx}
variable {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
    |traceTimeDerivMetric (I := (modelWithCornersEuclideanHalfSpace n)) G.metric t x| ≤ Bv}

theorem exists_uniform_weak_evolution_dist_le_initial
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (modelWithCornersEuclideanHalfSpace n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ g₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := (modelWithCornersEuclideanHalfSpace n)) (M := M) q))
      (u v : timeL2 (H1ComplDirichlet q) T),
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u →
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace g₀ v →
        dist u v ≤ C * dist f₀ g₀ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_weak_evolution_norm_sq_le_initial
    hG hT hreg X hXcont a hacont Bx Bv hX htrace ha
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro f₀ g₀ u v hu hv
  have hsq := hbound (f₀ - g₀) (u - v) (hu.sub hv)
  have hsqrt : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  rw [dist_eq_norm, dist_eq_norm]
  have hright : 0 ≤ Real.sqrt C * ‖f₀ - g₀‖ :=
    mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _)
  have heq : (Real.sqrt C * ‖f₀ - g₀‖) ^ 2 = C * ‖f₀ - g₀‖ ^ 2 := by
    rw [mul_pow, hsqrt]
  nlinarith [norm_nonneg (u - v)]

theorem IsWeakEvolutionSolution.tendsto_of_initial
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (modelWithCornersEuclideanHalfSpace n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := (modelWithCornersEuclideanHalfSpace n)) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp ℝ 2 (riemannianVolumeMeasure (I := (modelWithCornersEuclideanHalfSpace n)) (M := M) q)}
    {v : ι → timeL2 (H1ComplDirichlet q) T}
    (hv : ∀ i, IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace (f i) (v i))
    (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto v l (𝓝 u) := by
  obtain ⟨C, _, hbound⟩ := exists_uniform_weak_evolution_dist_le_initial
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont ha
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlim : Tendsto (fun i => C * dist (f i) f₀) l (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_iff_dist_tendsto_zero.mp hf).const_mul C
  exact squeeze_zero (fun i => dist_nonneg)
    (fun i => hbound (f i) f₀ (v i) u (hv i) hu) hlim

theorem exists_weak_evolution_smooth_initial_approximation
    (hpos : 0 < T)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (modelWithCornersEuclideanHalfSpace n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := (modelWithCornersEuclideanHalfSpace n)) (M := M) q)) :
    ∃ u : timeL2 (H1ComplDirichlet q) T,
      IsWeakEvolutionSolution hG hpos.le hreg X a Bx Bv hX htrace f₀ u ∧
      ∃ v : ℕ → timeL2 (H1ComplDirichlet q) T,
        (∀ m, IsWeakEvolutionSolution hG hpos.le hreg X a Bx Bv hX htrace
          (smoothToLpDirichlet q (smoothDirichletBasisApproximation q m f₀)) (v m)) ∧
        Tendsto v atTop (𝓝 u) := by
  obtain ⟨u, hu⟩ := exists_dirichlet_weak_evolution_solution
    hG hpos hreg X hXcont a hacont Bx Bv hX htrace ha f₀
  have happrox (m : ℕ) := exists_dirichlet_weak_evolution_solution
    hG hpos hreg X hXcont a hacont Bx Bv hX htrace ha
      (smoothToLpDirichlet q (smoothDirichletBasisApproximation q m f₀))
  choose v hv using happrox
  refine ⟨u, hu, v, hv, ?_⟩
  exact hu.tendsto_of_initial hXcont hacont ha hv
    (tendsto_smoothToLpDirichlet_smoothDirichletBasisApproximation q f₀)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
