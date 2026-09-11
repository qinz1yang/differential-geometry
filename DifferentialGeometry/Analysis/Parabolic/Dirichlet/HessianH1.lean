import DifferentialGeometry.Analysis.Parabolic.Dirichlet.ThirdWeakDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.exists_lp_h1_hessian_chartPullback_mul
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
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ ≤ t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ₀ := (timeMeasure T).restrict (Icc t₀ t₁)
    ∀ H₀ : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H₀ i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        (∀ i j k, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv k
          (fun z => K i j k (t, z)) (fun z => H₀ i j (t, z)) Ω₀) ∧
        ∃ v : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp (H1ComplDirichlet q) 2 μ₀,
        (∀ i j, ∀ᵐ t ∂μ₀,
          (H1ComplDirichletToLp q (v i j t) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I_hs) (M := M) q]
            chartPullback I_hs α (fun z => η z * H₀ i j (t, z))) ∧
        ∀ i j k, ∀ᵐ t ∂μ₀,
          (dirichletLocalWeakPartialLp q α hΩ₀
            (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
            (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (v i j t) : EuStd → ℝ) =ᵐ[
              volume.restrict Ω₀]
            fun z => η z * K i j k (t, z) +
              fderiv ℝ η z (EuclideanSpace.single k 1) * H₀ i j (t, z) := by
  intro μ₀ H₀ hH₀
  classical
  obtain ⟨K, hK⟩ := hu.exists_local_third_weak_derivative hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω H₀ hH₀
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hηc : HasCompactSupport η :=
    hΩ₀c.of_isClosed_subset (isClosed_tsupport η) (hηs.trans subset_closure)
  choose v hv using fun i j =>
    exists_lp_h1ComplDirichlet_chartPullback_mul_of_joint_weak_partials
      q α hΩ₀ hΩ₀c hΩ₀s hη hηc hηs (H₀ i j) (K i j) (hK i j)
  refine ⟨K, hK, v, hv, ?_⟩
  intro i j k
  filter_upwards [hv i j, hK i j k, (Lp.memLp (H₀ i j)).prodMk_left (by norm_num),
    (Lp.memLp (K i j k)).prodMk_left (by norm_num)] with t hvt hkt hHt hKt
  exact dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul
    q α hΩ₀ hΩ₀c hΩ₀s (v i j t) hvt hHt hKt k hkt hη hηc

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
