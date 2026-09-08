import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakGradientSourceBound
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakTimeDerivativeBound
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.QuantitativeRegularity

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem exists_uniform_lp_weak_gradient_equation_source_bound_of_cutoff
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
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T),
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u →
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U : ℝ × EuStd → ℝ := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ := fun i =>
      dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    let DA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DDA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => DA k i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
    let DC := fun k i (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DC₀ := fun k (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let Dρ := fun k (p : ℝ × EuStd) => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let DDρ := fun k (p : ℝ × EuStd) => fderiv ℝ (Dρ k) p (1, 0)
    let Q := fun i => Real.sqrt (K * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) +
      L * ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖ * ‖u‖
    let KR :=
      (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * Q i) +
      (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * DA j i j p) ∞ ν * lpNorm (V i) 2 ν) +
      (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * lpNorm (V i) 2 ν) +
      lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * lpNorm U 2 ν
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, (F k =ᵐ[ν] fun p =>
        (∑ i, ∑ j,
          (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
              (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
            C i p * H i k p)) +
          (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
          C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p)) ∧
      (∀ i k, ‖H i k‖ ≤ Q i) ∧
      ‖R‖ ≤ KR ∧
      (∀ k, ‖F k‖ ≤
        (∑ i, ∑ j, lpNorm (DA k i j) ∞ ν * Q i) +
        (∑ i, ∑ j, lpNorm (DDA k i j) ∞ ν * lpNorm (V i) 2 ν) +
        (∑ i, lpNorm (C i) ∞ ν * Q i) +
        (∑ i, lpNorm (DC k i) ∞ ν * lpNorm (V i) 2 ν) +
        lpNorm C₀ ∞ ν * lpNorm (V k) 2 ν + lpNorm (DC₀ k) ∞ ν * lpNorm U 2 ν +
        lpNorm (Dρ k) ∞ ν * KR + lpNorm (DDρ k) ∞ ν * lpNorm U 2 ν) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν := by
  obtain ⟨K, L, hK, hL, hquant⟩ :=
    exists_uniform_local_weak_second_derivative_norm_bound_of_cutoff
      (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace) hXcont hacont α hΩ hΩc hΩs
      hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer
      ht₀ ht₁ hΩ₀ hηone
  refine ⟨K, L, hK, hL, ?_⟩
  intro f₀ u hu μ ν ρ A U V B τ C C₀ DA DDA DC DC₀ Dρ DDρ
  have hΩ₀Ω : closure Ω₀ ⊆ Ω := by
    have hs : Ω₀ ⊆ tsupport η := by
      intro z hz
      apply subset_tsupport η
      change η z ≠ 0
      rw [hηone z hz]
      norm_num
    exact (closure_minimal hs (isClosed_tsupport η)).trans
      (hηs.trans (subset_closure.trans ((Metric.self_subset_cthickening (δ := r) _).trans
        (hroom.trans (subset_closure.trans hΩ'Ω)))))
  intro Q KR
  obtain ⟨R, H, F, hR, hH, hHsym, hFormula, hsource, hF⟩ :=
    hu.exists_lp_weak_gradient_equation_source_norm_le hXcont hacont α hΩ hΩc hΩs
      hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hHnorm (i k) : ‖H i k‖ ≤ Q i := hquant f₀ u hu i k (H i k) (hH i k)
  have hRnorm := hu.norm_weak_time_derivative_le hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω H hH R hR
  have hRnorm' : ‖R‖ ≤ KR := by
    apply hRnorm.trans
    dsimp only [KR]
    gcongr
    · exact lpNorm_nonneg
    · exact hHnorm _ _
  refine ⟨R, H, F, hR, hH, hHsym, hFormula, hHnorm, hRnorm', ?_, hF⟩
  intro k
  apply (hsource k).trans
  gcongr
  · exact lpNorm_nonneg
  · exact hHnorm _ _
  · exact lpNorm_nonneg
  · exact hHnorm _ _
  · exact lpNorm_nonneg

theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation_source_bound_of_cutoff
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
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
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
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    let DA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DDA := fun k i j (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => DA k i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
    let DC := fun k i (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DC₀ := fun k (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let Dρ := fun k (p : ℝ × EuStd) => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let DDρ := fun k (p : ℝ × EuStd) => fderiv ℝ (Dρ k) p (1, 0)
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧
    let Q := fun i => Real.sqrt (K * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) +
      L * ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖ * ‖u‖
    let KR :=
      (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * Q i) +
      (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * DA j i j p) ∞ ν * lpNorm (V i) 2 ν) +
      (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * lpNorm (V i) 2 ν) +
      lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * lpNorm U 2 ν
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, (F k =ᵐ[ν] fun p =>
        (∑ i, ∑ j,
          (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
              (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
            C i p * H i k p)) +
          (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
          C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p)) ∧
      (∀ i k, ‖H i k‖ ≤ Q i) ∧
      ‖R‖ ≤ KR ∧
      (∀ k, ‖F k‖ ≤
        (∑ i, ∑ j, lpNorm (DA k i j) ∞ ν * Q i) +
        (∑ i, ∑ j, lpNorm (DDA k i j) ∞ ν * lpNorm (V i) 2 ν) +
        (∑ i, lpNorm (C i) ∞ ν * Q i) +
        (∑ i, lpNorm (DC k i) ∞ ν * lpNorm (V i) 2 ν) +
        lpNorm C₀ ∞ ν * lpNorm (V k) 2 ν + lpNorm (DC₀ k) ∞ ν * lpNorm U 2 ν +
        lpNorm (Dρ k) ∞ ν * KR + lpNorm (DDρ k) ∞ ν * lpNorm U 2 ν) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν := by
  intro μ ν ρ A U V B τ C C₀ DA DDA DC DC₀ Dρ DDρ
  obtain ⟨K, L, hK, hL, hbound⟩ := exists_uniform_lp_weak_gradient_equation_source_bound_of_cutoff
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
    hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer ht₀ ht₁ hΩ₀ hηone
  exact ⟨K, L, hK, hL, hbound f₀ u hu⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
