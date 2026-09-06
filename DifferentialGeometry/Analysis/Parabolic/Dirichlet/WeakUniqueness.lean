import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeightedEnergy

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem IsWeakEvolutionSolution.eq_zero
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) (hf₀ : f₀ = 0) : u = 0 := by
  obtain ⟨_, _, U, _, hUae, _, hbound⟩ :=
    hu.exists_continuous_l2_representative_with_energy_bound hXcont hacont
  have hUzero : ∀ t ∈ Icc (0 : ℝ) T, U t = 0 := by
    intro t ht
    have hnorm :
        ‖smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t)) (U t)‖ ^ 2 ≤ 0 := by
      have hb := hbound t ht
      rw [hf₀, map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hb
      exact hb
    have hzero : smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t)) (U t) = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        (smoothMulLp q (riemannianVolumeDensitySmoothMap q (G.metric t)) (U t))]
    apply smoothMulLp_injective q (riemannianVolumeDensitySmoothMap q (G.metric t))
      (Filter.Eventually.of_forall fun x => ne_of_gt (riemannianVolumeDensity_pos q (G.metric t) x))
    simpa only [map_zero] using hzero
  apply Lp.ext
  filter_upwards [hUae, ae_restrict_mem measurableSet_Icc,
    Lp.coeFn_zero (E := H1ComplDirichlet q) (p := 2) (μ := timeMeasure T)] with t hUt ht hz
  rw [hz]
  change u t = 0
  apply H1ComplDirichletToLp_injective q
  rw [map_zero, ← hUt, hUzero t ht]

theorem IsWeakEvolutionSolution.unique
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)}
    {u v : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u)
    (hv : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ v) : u = v := by
  exact sub_eq_zero.mp ((hu.sub hv).eq_zero hXcont hacont (sub_self f₀))

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
