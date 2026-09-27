import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorEstimate
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakTimeDerivativeBound
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeDerivativeUniqueness

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

private theorem lpNorm_coe_le_norm_of_measure_le
    {P : Type*} [MeasurableSpace P] {μ ν : Measure P}
    (hν : ν ≤ μ) (f : Lp ℝ 2 μ) : lpNorm f 2 ν ≤ ‖f‖ := by
  rw [← toReal_eLpNorm ((Lp.memLp f).mono_measure hν).aestronglyMeasurable, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _ hν)

private theorem exists_uniform_lp_weak_time_deriv_norm_le_initial_of_cutoff
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
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T),
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u →
      let ν := ((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)
      let U : ℝ × EuStd → ℝ := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
      ∃ R : Lp ℝ 2 ν,
        (∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ ψ p (1, 0) ∂ν) = -∫ p, R p * ψ p ∂ν) ∧
        ‖R‖ ≤ C * ‖f₀‖ := by
  classical
  obtain ⟨E, hE, henergy⟩ := exists_uniform_weak_evolution_norm_sq_le_initial
    hG hT hreg X hXcont a hacont Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace ha
  obtain ⟨Hc, hHc, hhessian⟩ := exists_uniform_local_weak_second_derivative_norm_le_initial
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont ha α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
    hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer ht₀ ht₁ hΩ₀ hηone
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  let ν := μ.prod (volume.restrict Ω₀)
  let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
  let A := fun i j (p : ℝ × EuStd) =>
    MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
  let B := fun i (p : ℝ × EuStd) =>
    DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
      ((toEuclidean (E := EuN)).symm p.2)
  let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
  let C := fun i (p : ℝ × EuStd) => ρ p * B i p
  let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
  let DA := fun i j (p : ℝ × EuStd) =>
    fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
  let UL := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T)
  let VL := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i
  let Q := fun i => ‖VL i‖ * Real.sqrt E
  let P := ‖UL‖ * Real.sqrt E
  let K :=
    (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * Hc) +
    (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * DA i j p) ∞ ν * Q i) +
    (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * Q i) +
    lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * P
  have hK : 0 ≤ K :=
    add_nonneg
      (add_nonneg
        (add_nonneg
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg lpNorm_nonneg hHc)
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg lpNorm_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))))
        (Finset.sum_nonneg fun _ _ =>
          mul_nonneg lpNorm_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))))
      (mul_nonneg lpNorm_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
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
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self
      (Measure.restrict_mono (subset_closure.trans hΩ₀Ω) le_rfl)
  refine ⟨K, hK, ?_⟩
  intro f₀ u hu
  dsimp only
  obtain ⟨R, hR⟩ := hu.exists_lp_weak_time_deriv hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  choose H hH using hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hHnorm (i j) : ‖H i j‖ ≤ Hc * ‖f₀‖ := hhessian f₀ u hu i j (H i j) (hH i j)
  have huenergy : ‖u‖ ≤ Real.sqrt E * ‖f₀‖ := by
    have hs := Real.sqrt_le_sqrt (henergy f₀ u hu)
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hE, Real.sqrt_sq (norm_nonneg _)] at hs
  have hUnorm : lpNorm (UL u) 2 ν ≤ P * ‖f₀‖ := by
    calc
      lpNorm (UL u) 2 ν ≤ ‖UL u‖ := lpNorm_coe_le_norm_of_measure_le hmeasure _
      _ ≤ ‖UL‖ * ‖u‖ := UL.le_opNorm u
      _ ≤ ‖UL‖ * (Real.sqrt E * ‖f₀‖) := mul_le_mul_of_nonneg_left huenergy (norm_nonneg _)
      _ = P * ‖f₀‖ := (mul_assoc _ _ _).symm
  have hVnorm (i) : lpNorm (VL i u) 2 ν ≤ Q i * ‖f₀‖ := by
    calc
      lpNorm (VL i u) 2 ν ≤ ‖VL i u‖ := lpNorm_coe_le_norm_of_measure_le hmeasure _
      _ ≤ ‖VL i‖ * ‖u‖ := (VL i).le_opNorm u
      _ ≤ ‖VL i‖ * (Real.sqrt E * ‖f₀‖) := mul_le_mul_of_nonneg_left huenergy (norm_nonneg _)
      _ = Q i * ‖f₀‖ := (mul_assoc _ _ _).symm
  have hRnorm := hu.norm_weak_time_derivative_le hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω H hH R hR
  refine ⟨R, hR, hRnorm.trans ?_⟩
  change
    (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * ‖H i j‖) +
    (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * DA i j p) ∞ ν * lpNorm (VL i u) 2 ν) +
    (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * lpNorm (VL i u) 2 ν) +
    lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * lpNorm (UL u) 2 ν ≤ _
  calc
    _ ≤ (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * (Hc * ‖f₀‖)) +
        (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * DA i j p) ∞ ν * (Q i * ‖f₀‖)) +
        (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * (Q i * ‖f₀‖)) +
        lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * (P * ‖f₀‖) := by
      gcongr
      · exact lpNorm_nonneg
      · exact hHnorm _ _
      · exact lpNorm_nonneg
      · exact hVnorm _
      · exact lpNorm_nonneg
      · exact hVnorm _
      · exact lpNorm_nonneg
    _ = K * ‖f₀‖ := by
      simp only [K, add_mul, ← mul_assoc, Finset.sum_mul]

theorem exists_uniform_lp_weak_time_deriv_norm_le_initial
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
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T),
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u →
      let ν := ((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)
      let U : ℝ × EuStd → ℝ := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
      ∃ R : Lp ℝ 2 ν,
        (∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ ψ p (1, 0) ∂ν) = -∫ p, R p * ψ p ∂ν) ∧
        ‖R‖ ≤ C * ‖f₀‖ := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨Ω', hΩ', hKΩ', hΩ'Ω, hΩ'c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ hΩ₀Ω
  obtain ⟨Ω'', hΩ'', hKΩ'', hΩ''Ω', hΩ''c⟩ :=
    exists_open_between_and_isCompact_closure hΩ₀c hΩ' hKΩ'
  obtain ⟨r, hr, hroom⟩ := hΩ''c.exists_cthickening_subset_open hΩ' hΩ''Ω'
  obtain ⟨ε, η, hε, _, hη, hηc, hηrange, hηone, hηs⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hΩ₀c hΩ'' hKΩ''
  have hηb : ∀ z, |η z| ≤ 1 := by
    intro z
    have hz := hηrange (mem_range_self z)
    exact (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩)
  let U := toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuclideanSpace ℝ (Fin n))).isOpenMap _ isOpen_interior
  obtain ⟨φ, _, hφ⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one
      q α hU (Subset.rfl : U ⊆ U) hΩc hΩs
  obtain ⟨lam, hlam, hcoer⟩ :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound
      hG isCompact_Icc hreg α hΩc (hΩs.trans (image_mono interior_subset))
  have hcoer' : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j := by
    intro t ht y hy ξ
    have hb := hcoer t ht y (subset_closure hy) (WithLp.toLp 2 ξ)
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
      PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Real.inner_apply] at hb
    convert hb using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact exists_uniform_lp_weak_time_deriv_norm_le_initial_of_cutoff
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont ha α hΩ hΩc hΩs hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
    hη hηc hηs hr hroom φ (fun z hz => hφ z (subset_closure hz)) hXsmooth hηb hlam hcoer' ht₀ ht₁ hΩ₀
    (fun z hz => hηone z (Metric.self_subset_cthickening _ (subset_closure hz)))

theorem exists_uniform_local_weak_time_derivative_norm_le_initial
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
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (u : timeL2 (H1ComplDirichlet q) T),
      IsWeakEvolutionSolution hG hT hreg X a Bx Bv
        (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u →
      let ν := ((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)
      let U : ℝ × EuStd → ℝ := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
      ∀ R : Lp ℝ 2 ν,
        (∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ ψ p (1, 0) ∂ν) = -∫ p, R p * ψ p ∂ν) →
        ‖R‖ ≤ C * ‖f₀‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lp_weak_time_deriv_norm_le_initial
    (hG := hG) (hT := hT) (hreg := hreg) (hX := hX) (htrace := htrace)
    hXcont hacont ha α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨C, hC, ?_⟩
  intro f₀ u hu
  dsimp only
  intro R hR
  obtain ⟨R', hR', hRnorm⟩ := hbound f₀ u hu
  have heq : R = R' := lp_eq_of_weak_time_deriv_integral hΩ₀ (by norm_num) hR hR'
  exact heq.symm ▸ hRnorm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
