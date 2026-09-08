import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationProduct

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private theorem fderiv_spatial_slice_apply
    {d : ℕ} {φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (t : ℝ) (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => φ (t, y)) x v = fderiv ℝ φ (t, x) (0, v) := by
  have h := (hφ (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  exact congrArg (fun L => L v) h.fderiv

private theorem weak_form_integrand_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ρ U dtφ φ τ a : ℝ) (DU B : ι → ℝ) (A : ι → κ → ℝ) (dφ : κ → ℝ) :
    ρ * (U * dtφ) +
      (ρ * ((1 / 2 : ℝ) * τ * (U * φ)) -
        (∑ i, DU i * ((∑ j, A i j * dφ j) * ρ - B i * ρ * φ)) -
        ρ * U * (a * φ)) =
    ρ * U * dtφ + ((∑ i, ρ * B i * DU i) + ρ * ((1 / 2 : ℝ) * τ - a) * U) * φ -
      ∑ i, ∑ j, ρ * A i j * DU i * dφ j := by
  have hq : (∑ i, DU i * (∑ j, A i j * dφ j) * ρ) =
      ∑ i, ∑ j, ρ * A i j * DU i * dφ j := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hb : (∑ i, DU i * (B i * ρ * φ)) = (∑ i, ρ * B i * DU i) * φ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hq' : (∑ i, DU i * ((∑ j, A i j * dφ j) * ρ)) =
      ∑ i, ∑ j, ρ * A i j * DU i * dφ j := by
    simpa only [mul_assoc] using hq
  rw [hq', hb]
  ring

private theorem integral_eq_neg_integral_of_divergence
    {P ι κ : Type*} [MeasurableSpace P] [Fintype ι] [Fintype κ]
    {μ : Measure P} {f ℓ r g φ : P → ℝ} {Q : ι → κ → P → ℝ}
    (hf : Integrable f μ) (hr : Integrable (fun p => r p * φ p) μ)
    (hg : Integrable (fun p => g p * φ p) μ)
    (hQ : ∀ i j, Integrable (Q i j) μ)
    (hrg : r =ᵐ[μ] fun p => g p + ℓ p)
    (hweak : (∫ p, f p + ℓ p * φ p - ∑ i, ∑ j, Q i j p ∂μ) = 0)
    (hdiv : (∫ p, g p * φ p ∂μ) = -∑ i, ∑ j, ∫ p, Q i j p ∂μ) :
    (∫ p, f p ∂μ) = -(∫ p, r p * φ p ∂μ) := by
  have hsum (i) : Integrable (fun p => ∑ j, Q i j p) μ :=
    integrable_finsetSum Finset.univ fun j _ => hQ i j
  have hall : Integrable (fun p => ∑ i, ∑ j, Q i j p) μ :=
    integrable_finsetSum Finset.univ fun i _ => hsum i
  have hℓ : (fun p => ℓ p * φ p) =ᵐ[μ] fun p => r p * φ p - g p * φ p := by
    filter_upwards [hrg] with p hp
    rw [hp]
    ring
  have hℓint : Integrable (fun p => ℓ p * φ p) μ := (hr.sub hg).congr hℓ.symm
  have hadd : Integrable (fun p => f p + ℓ p * φ p) μ := hf.add hℓint
  rw [integral_sub hadd hall, integral_add hf hℓint,
    integral_congr_ae hℓ, integral_sub hr hg,
    integral_finsetSum Finset.univ (fun i _ => hsum i)] at hweak
  have hs : (∑ i, ∫ p, ∑ j, Q i j p ∂μ) = ∑ i, ∑ j, ∫ p, Q i j p ∂μ := by
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j _ => hQ i j)
  rw [hs] at hweak
  linarith

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private theorem IsWeakEvolutionSolution.exists_lp_localEvolutionSource
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
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)
    let ρ := fun (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      chartDensityOnE (I := I_hs) (G.metric p.1) α ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm p.2)
    let A := fun i j (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let B := fun i (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      chartCoeffOnE (I := I_hs) α (X p.1) i ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm p.2)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ F R : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (R =ᵐ[μ.prod (volume.restrict Ω₀)] fun p => F p +
        (∑ i, ρ p * B i p * V i p) + ρ p *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p) ∧
      ∀ (φ : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, F p * φ p ∂μ.prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω₀) := by
  intro μ x ρ A B U V
  obtain ⟨F, hF⟩ := hu.exists_lp_divergence_localWeakPartial hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤
      (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hρ : MemLp ρ ∞ ((timeMeasure T).prod (volume.restrict Ω)) := by
    have h := MetricExtension.densityOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact h
  have hB (i) : MemLp (B i) ∞ ((timeMeasure T).prod (volume.restrict Ω)) := by
    have h := MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top X isCompact_Icc
      measurableSet_Icc α (hXcont.mono (Set.prod_mono Subset.rfl (subset_univ _)))
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) i (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact h
  have hτ : MemLp (fun p => traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2))
      ∞ ((timeMeasure T).prod (volume.restrict Ω)) := by
    have h := MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top hG isCompact_Icc
      hreg α hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact h
  have ha : MemLp (fun p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) => a p.1)
      ∞ ((timeMeasure T).prod (volume.restrict Ω)) := by
    have hc := hacont.comp continuousOn_fst (fun _ hp => hp.1 : MapsTo Prod.fst
      (Icc (0 : ℝ) T ×ˢ closure Ω) (Icc (0 : ℝ) T))
    have h := hc.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
      (measurableSet_Icc.prod hΩ.measurableSet) (Set.prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h
  have hflux (i) : MemLp (fun p => ρ p * B i p * V i p) 2
      ((timeMeasure T).prod (volume.restrict Ω)) :=
    (Lp.memLp (V i)).mul (hB i |>.mul (r := ∞) hρ)
  have hpot : MemLp (fun p => ρ p *
      ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p) 2
      ((timeMeasure T).prod (volume.restrict Ω)) :=
    (Lp.memLp U).mul (((hτ.const_mul (1 / 2 : ℝ)).sub ha).mul (r := ∞) hρ)
  have hR := (Lp.memLp F).add
    ((memLp_finsetSum Finset.univ (fun i _ => hflux i)).mono_measure hmeasure) |>.add
      (hpot.mono_measure hmeasure)
  exact ⟨F, hR.toLp _, hR.coeFn_toLp, hF⟩


theorem IsWeakEvolutionSolution.exists_lp_weak_time_deriv_density
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
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ρ := fun (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      chartDensityOnE (I := I_hs) (G.metric p.1) α ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm p.2)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∃ R : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
  intro μ ρ U
  let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)
  let A := fun i j (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
  let B := fun i (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      chartCoeffOnE (I := I_hs) α (X p.1) i ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm p.2)
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  obtain ⟨F, R, hR, hF⟩ := hu.exists_lp_localEvolutionSource hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨R, ?_⟩
  intro φ hφ hφc hφs
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  let ν := μ.prod (volume.restrict Ω₀)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hρ : MemLp ρ ∞ ν := by
    have h := MetricExtension.densityOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have hA (i j) : MemLp (A i j) ∞ ν := by
    have h := MetricExtension.weightedInvGramOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) i j (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hφLp : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hφc ν
  have hdLp (v) : MemLp (fun p => fderiv ℝ φ p v) ∞ ν :=
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hφc.fderiv_apply ℝ v) ν
  have htime : Integrable (fun p => ρ p * U p * fderiv ℝ φ p (1, 0)) ν :=
    (((hdLp (1, 0)).mul (r := 2) (hU.mul (r := 2) hρ))).integrable (by norm_num)
  have hRφ : Integrable (fun p => R p * φ p) ν :=
    (hφLp.mul (r := 2) (Lp.memLp R)).integrable (by norm_num)
  have hFφ : Integrable (fun p => F p * φ p) ν :=
    (hφLp.mul (r := 2) (Lp.memLp F)).integrable (by norm_num)
  have hQ (i j) : Integrable (fun p => A i j p * V i p *
      fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
    ((hdLp (0, EuclideanSpace.single j 1)).mul (r := 2) ((hV i).mul (r := 2) (hA i j))).integrable
      (by norm_num)
  have hdiv := hF φ hφ hφc (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  let ℓ := fun p => (∑ i, ρ p * B i p * V i p) + ρ p *
    ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p
  have hRae : R =ᵐ[ν] fun p => F p + ℓ p := by
    filter_upwards [hR] with p hp
    exact hp.trans (add_assoc _ _ _)
  have hw := hu.integral_spacetime_test_interior hXcont hacont α hΩ hΩc hΩs hφ hφc
    hΩ₀.measurableSet hsub ht₀ ht₁ hφs
  have hweak : (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) + ℓ p * φ p -
      ∑ i, ∑ j, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) = 0 := by
    convert hw using 1
    apply integral_congr_ae
    filter_upwards [] with p
    dsimp only [ℓ, ρ, A, B, U, V, x]
    rw [weak_form_integrand_eq]
    simp only [fderiv_spatial_slice_apply (hφ.differentiable (by norm_num))]
    rfl
  exact integral_eq_neg_integral_of_divergence htime hRφ hFφ hQ hRae hweak hdiv

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
