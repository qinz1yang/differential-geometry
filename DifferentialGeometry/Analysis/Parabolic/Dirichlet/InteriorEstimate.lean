import DifferentialGeometry.Analysis.Parabolic.Dirichlet.EnergyEstimate
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.QuantitativeRegularity

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

theorem exists_uniform_local_weak_second_derivative_norm_le_initial
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T), IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u → ∀ i k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      ∀ H : Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)),
        (∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁), DeGiorgi.HasWeakPartialDeriv k
          (fun z => H (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
        ‖H‖ ≤ C * ‖f₀‖ := by
  classical
  obtain ⟨E, hE, henergy⟩ := exists_uniform_weak_evolution_norm_sq_le_initial
    hG hT hreg X hXcont a hacont Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace ha
  obtain ⟨K, L, hK, hL, hsecond⟩ := exists_uniform_local_weak_second_derivative_norm_bound_of_cutoff
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
    hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer ht₀ ht₁ hΩ₀ hηone
  let A := ∑ i, ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Real.sqrt (K * E) + L * A * Real.sqrt E, by positivity, ?_⟩
  intro f₀ u hu i k H hH
  have hbound := hsecond f₀ u hu i k H hH
  have hunorm := henergy f₀ u hu
  have huintegral : (∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) ≤ E * ‖f₀‖ ^ 2 := by
    simpa only [TimeSobolev.norm_sq_eq_integral, timeMeasure] using hunorm
  have hAnorm : ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖ ≤ A :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hfirst : Real.sqrt (K * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) ≤
      Real.sqrt (K * E) * ‖f₀‖ := by
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left huintegral hK)
    have heq : Real.sqrt (K * (E * ‖f₀‖ ^ 2)) = Real.sqrt (K * E) * ‖f₀‖ := by
      rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hK hE), Real.sqrt_sq (norm_nonneg _)]
    exact hs.trans_eq heq
  have hsecondnorm : ‖u‖ ≤ Real.sqrt E * ‖f₀‖ := by
    have hs := Real.sqrt_le_sqrt hunorm
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hE, Real.sqrt_sq (norm_nonneg _)] at hs
  calc
    ‖H‖ ≤ Real.sqrt (K * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) +
        L * ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖ * ‖u‖ := hbound
    _ ≤ Real.sqrt (K * E) * ‖f₀‖ + L * A * (Real.sqrt E * ‖f₀‖) := by
      apply add_le_add hfirst
      exact mul_le_mul (mul_le_mul_of_nonneg_left hAnorm hL) hsecondnorm
        (norm_nonneg _) (mul_nonneg hL hA)
    _ = _ := by ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
