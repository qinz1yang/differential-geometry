import DifferentialGeometry.Analysis.Integration.Measure.Family.LocalVariation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MovingMassTrace
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal RealInnerProductSpace Topology

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

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

omit [T2Space M] in
private theorem exists_weak_evolution_coefficient_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hreg : K ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M)) (K ×ˢ (Set.univ : Set M))) :
    ∃ Bx Bv : ℝ,
      (∀ t ∈ K, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx) ∧
      (∀ t ∈ K, ∀ x : M,
        |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv) := by
  have hquad : ContinuousOn
      (fun p : ℝ × M => (G.metric p.1).inner p.2 (X p.1 p.2) (X p.1 p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hmetric := (hG.metricCLMSmoothAt (t := p.1) (x := p.2)
      (D.regular_isOpen.mem_nhds (hreg hp.1))).continuousAt.continuousWithinAt
        (s := K ×ˢ (Set.univ : Set M))
    have hpair : ContinuousWithinAt
        (fun r : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) r.2
          ((G.metric r.1).inner r.2 (X r.1 r.2) (X r.1 r.2)))
        (K ×ˢ (Set.univ : Set M)) p :=
      hmetric.clm_bundle_apply₂ (F₁ := EuclideanSpace ℝ (Fin n))
        (F₂ := EuclideanSpace ℝ (Fin n)) (hXcont p hp) (hXcont p hp)
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hpair
    exact hpair.2
  have htrace : ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I_half n) G.metric p.1 p.2)
      (K ×ˢ (Set.univ : Set M)) := by
    apply (continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      D.regular_isOpen ?_).mono (Set.prod_mono hreg Set.Subset.rfl)
    intro α i j
    exact hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) α i j
  obtain ⟨Bx, hBx⟩ := ((hK.prod isCompact_univ).image_of_continuousOn hquad).bddAbove
  obtain ⟨Bv, hBv⟩ := ((hK.prod isCompact_univ).image_of_continuousOn htrace.abs).bddAbove
  refine ⟨Bx, Bv, ?_, ?_⟩
  · intro t ht x
    exact hBx ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩
  · intro t ht x
    exact hBv ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩

theorem exists_continuous_dirichlet_weak_evolution_solution
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    ∃ u : timeL2 (H1ComplDirichlet q) T,
      ∃ U : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q),
        ContinuousOn U (Icc (0 : ℝ) T) ∧
        (U =ᵐ[timeMeasure T] fun t => H1ComplDirichletToLp q (u t)) ∧
        U 0 = f₀ ∧
        ∃ Bx Bv : ℝ,
          ∃ hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
            (G.metric t).inner x (X t x) (X t x) ≤ Bx,
          ∃ htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
            |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv,
          IsWeakEvolutionSolution hG hT.le hreg X a Bx Bv hX htrace f₀ u := by
  obtain ⟨Bx, Bv, hXIcc, htraceIcc⟩ :=
    exists_weak_evolution_coefficient_bounds hG isCompact_Icc hreg X hXcont
  have hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx :=
    fun t ht x => hXIcc t ⟨ht.1, ht.2.le⟩ x
  have htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv :=
    fun t ht x => htraceIcc t ⟨ht.1, ht.2.le⟩ x
  obtain ⟨u, hu⟩ := exists_dirichlet_weak_evolution_solution
    hG hT hreg X hXcont a hacont Bx Bv hX htrace ha f₀
  obtain ⟨U, hUcont, hUae, hUzero⟩ := hu.exists_continuous_l2_representative hXcont hacont
  exact ⟨u, U, hUcont, hUae, hUzero, Bx, Bv, hX, htrace, hu⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
