import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeDerivativeUniqueness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Integration.Lp.Multiplication
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

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

private theorem ae_local_divergence_source
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    {t₀ t₁ : ℝ} {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∀ (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ (Fdiv : Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, Fdiv p * φ p ∂ν) = -∑ i, ∑ j,
          ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      Fdiv =ᵐ[ν] fun p => ∑ i, ∑ j,
        (A i j p * H i j p + fderiv ℝ (fun z => A i j (p.1, z)) p.2
          (EuclideanSpace.single j 1) * V i p) := by
  intro μ ν A V H hH Fdiv hFdiv
  classical
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  let W := fun i => (hV i).toLp (V i)
  have hW (i) : W i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hWweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => W i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hW i), hc] with t ht hwt hct
    have he : (fun x => W i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hΩ₀target := hΩ₀s.trans (image_mono interior_subset)
  have hA (i j) : MemLp (A i j) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c hΩ₀target i j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c hΩ₀s i j j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hAsmooth (i j) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω₀ := by
    apply Filter.Eventually.of_forall
    intro t
    exact (MetricExtension.weightedInvGramOnEuclid_contDiffOn (G.metric t) α i j).mono
      (hsub.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have he := Sobolev.Euclidean.ae_eq_divergence_of_weak_partials
    isOpen_univ (Filter.Eventually.of_forall (fun _ => mem_univ _)) (by norm_num)
    hΩ₀ W H hA hDA hAsmooth hWweak (F := Fdiv) (by
      intro φ hφ hφc hφs
      rw [hFdiv φ hφ hφc hφs]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [hW i] with p hp
      rw [hp])
  filter_upwards [he, ae_all_iff.mpr hW] with p hp hwp
  rw [hp]
  simp only [hwp]

theorem IsWeakEvolutionSolution.weak_time_derivative_eq_source
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
    ∀ (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ (R : Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      R =ᵐ[ν] fun p =>
        (ρ p)⁻¹ * ((∑ i, ∑ j, (A i j p * H i j p +
          fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, C i p * V i p) + (C₀ p - fderiv ℝ ρ p (1, 0)) * U p) := by
  intro μ ν ρ A U V B τ C C₀ H hH R hR
  classical
  obtain ⟨Fdiv, S, hS, hFdiv⟩ := hu.exists_lp_local_evolution_source hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hFformula := ae_local_divergence_source (hG := hG) (hreg := hreg)
    α hΩ hΩc hΩs hΩ₀ hΩ₀Ω H hH Fdiv hFdiv
  have hSweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, S p * φ p ∂ν := by
    intro φ hφ hφc hφs
    let L := fun p => (∑ i, C i p * V i p) + C₀ p * U p
    have hSint : Integrable (fun p => S p * φ p) ν :=
      ((Lp.memLp S).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hFint : Integrable (fun p => Fdiv p * φ p) ν :=
      ((Lp.memLp Fdiv).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hL : (fun p => L p * φ p) =ᵐ[ν] fun p => S p * φ p - Fdiv p * φ p := by
      filter_upwards [hS] with p hp
      rw [hp]
      dsimp only [L, C, C₀, B, τ, ρ, U, V]
      simp only [MetricExtension.densityOnEuclid, DifferentialGeometry.Integral.DivergenceTheorem.chartDensityOnE]
      ring
    have hLint : (∫ p, L p * φ p ∂ν) = (∫ p, S p * φ p ∂ν) - ∫ p, Fdiv p * φ p ∂ν := by
      rw [integral_congr_ae hL, integral_sub hSint hFint]
    have hbase := hu.integral_spacetime_test_divergence hXcont hacont α hΩ hΩc hΩs hφ hφc
      hΩ₀.measurableSet hsub ht₀ ht₁ hφs
    change (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
      (∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
        ∫ p, L p * φ p ∂ν at hbase
    have hdiv := hFdiv φ hφ hφc (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
    linarith
  let chartTarget := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hV : IsOpen chartTarget := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩV : closure Ω ⊆ chartTarget := hΩs
  have hreg₀ : Ioo t₀ t₁ ⊆ D.regular := fun t ht =>
    hreg ⟨le_trans ht₀.le ht.1.le, le_trans ht.2.le ht₁.le⟩
  have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ chartTarget) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ chartTarget) : ρ p ≠ 0 :=
    ne_of_gt (MetricExtension.densityOnEuclid_pos (G.metric p.1) α
      ((image_mono interior_subset) hp))
  let v : ℝ × EuStd := (1, 0)
  let domain := Ioo t₀ t₁ ×ˢ Ω₀
  have hρinv : MemLp (fun p => (ρ p)⁻¹) ∞ ν := by
    have hc := hρsmooth.continuousOn.inv₀ (fun p hp => hρne p hp.2)
    have h := (hc.mono (Set.prod_mono hreg hΩV)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have hDρ : MemLp (fun p => fderiv ℝ ρ p v) ∞ ν := by
    have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ ρ p v) (D.regular ×ˢ chartTarget) :=
      (hρsmooth.fderiv_of_isOpen (D.regular_isOpen.prod hV) (by simp)).clm_apply contDiffOn_const
    have h := (hc.continuousOn.mono (Set.prod_mono hreg hΩV)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  let Rnew := fun p => (ρ p)⁻¹ * S p - ((ρ p)⁻¹ * fderiv ℝ ρ p v) * U p
  have hRnew : MemLp Rnew 2 ν :=
    ((Lp.memLp S).mul hρinv).sub (hU.mul (hDρ.mul (r := ∞) hρinv))
  have hRnewweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, hRnew.toLp Rnew p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have heq := Sobolev.integral_fderiv_eq_neg_of_weighted_identity
      (μ := ν) (S := domain) (isOpen_Ioo.prod hΩ₀) v (hU.locallyIntegrable (by norm_num))
      ((Lp.memLp S).locallyIntegrable (by norm_num))
      (hρsmooth.mono (prod_mono hreg₀ (hsub.trans (subset_closure.trans hΩV))))
      (fun p hp => hρne p (hsub.trans (subset_closure.trans hΩV) hp.2))
      hSweak hφ hφc hφs
    refine heq.trans (congrArg Neg.neg ?_)
    apply integral_congr_ae
    filter_upwards [hRnew.coeFn_toLp] with p hp
    exact congrArg (fun r => r * φ p) hp.symm
  have heq : R = hRnew.toLp Rnew := lp_eq_of_weak_time_deriv_integral hΩ₀ (by norm_num) hR hRnewweak
  rw [heq]
  filter_upwards [hRnew.coeFn_toLp, hS, hFformula] with p hp hSp hFp
  rw [hp]
  dsimp only [Rnew]
  rw [hSp, hFp]
  dsimp only [C, C₀, B, τ, ρ, v, U, V, A]
  simp only [MetricExtension.densityOnEuclid, DifferentialGeometry.Integral.DivergenceTheorem.chartDensityOnE]
  ring

private theorem norm_sum_mul_fields_le_lpNorm
    {P ι : Type*} [MeasurableSpace P] [Fintype ι] {μ : Measure P}
    (a : ι → P → ℝ) (ha : ∀ i, MemLp (a i) ∞ μ)
    (V : ι → P → ℝ) (hV : ∀ i, MemLp (V i) 2 μ)
    (F : Lp ℝ 2 μ) (hF : F =ᵐ[μ] fun p => ∑ i, a i p * V i p) :
    ‖F‖ ≤ ∑ i, lpNorm (a i) ∞ μ * lpNorm (V i) 2 μ := by
  have he : F =ᵐ[μ] fun p => ∑ i, a i p * (hV i).toLp (V i) p := by
    filter_upwards [hF, ae_all_iff.mpr (fun i => (hV i).coeFn_toLp)] with p hp hVp
    simpa only [hVp] using hp
  have hb := norm_varying_coefficient_sum_le a ha (fun i => lpNorm (a i) ∞ μ)
    (fun i => ae_le_lpNorm_exponent_top (ha i)) (fun i => (hV i).toLp (V i)) F he
  simpa only [Lp.norm_toLp, toReal_eLpNorm (hV _).aestronglyMeasurable] using hb

private theorem norm_weak_time_source_le
    {P ι : Type*} [MeasurableSpace P] [Fintype ι] {μ : Measure P}
    (a d : ι → ι → P → ℝ)
    (ha : ∀ i j, MemLp (a i j) ∞ μ) (hd : ∀ i j, MemLp (d i j) ∞ μ)
    (c : ι → P → ℝ) (hc : ∀ i, MemLp (c i) ∞ μ)
    (b : P → ℝ) (hb : MemLp b ∞ μ)
    (H : ι → ι → P → ℝ) (hH : ∀ i j, MemLp (H i j) 2 μ)
    (V : ι → P → ℝ) (hV : ∀ i, MemLp (V i) 2 μ)
    (U : P → ℝ) (hU : MemLp U 2 μ) (R : Lp ℝ 2 μ)
    (hR : R =ᵐ[μ] fun p =>
      (∑ i, ∑ j, a i j p * H i j p) +
      (∑ i, ∑ j, d i j p * V i p) +
      (∑ i, c i p * V i p) + b p * U p) :
    ‖R‖ ≤
      (∑ i, ∑ j, lpNorm (a i j) ∞ μ * lpNorm (H i j) 2 μ) +
      (∑ i, ∑ j, lpNorm (d i j) ∞ μ * lpNorm (V i) 2 μ) +
      (∑ i, lpNorm (c i) ∞ μ * lpNorm (V i) 2 μ) +
      lpNorm b ∞ μ * lpNorm U 2 μ := by
  let J := (ι × ι) ⊕ ((ι × ι) ⊕ (ι ⊕ Unit))
  let aa : J → P → ℝ := Sum.elim (fun ij => a ij.1 ij.2)
    (Sum.elim (fun ij => d ij.1 ij.2) (Sum.elim c (fun _ => b)))
  let VV : J → P → ℝ := Sum.elim (fun ij => H ij.1 ij.2)
    (Sum.elim (fun ij => V ij.1) (Sum.elim V (fun _ => U)))
  have haa : ∀ s, MemLp (aa s) ∞ μ := by
    rintro (⟨i, j⟩ | (⟨i, j⟩ | (i | u)))
    · exact ha i j
    · exact hd i j
    · exact hc i
    · exact hb
  have hVV : ∀ s, MemLp (VV s) 2 μ := by
    rintro (⟨i, j⟩ | (⟨i, j⟩ | (i | u)))
    · exact hH i j
    · exact hV i
    · exact hV i
    · exact hU
  have hR' : R =ᵐ[μ] fun p => ∑ s, aa s p * VV s p := by
    filter_upwards [hR] with p hp
    simpa [J, aa, VV, Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc] using hp
  have hn := norm_sum_mul_fields_le_lpNorm aa haa VV hVV R hR'
  simpa [J, aa, VV, Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc] using hn

theorem IsWeakEvolutionSolution.norm_weak_time_derivative_le
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
    ∀ (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ (R : Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      ‖R‖ ≤
        (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ * A i j p) ∞ ν * ‖H i j‖) +
        (∑ i, ∑ j, lpNorm (fun p => (ρ p)⁻¹ *
          fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)) ∞ ν * lpNorm (V i) 2 ν) +
        (∑ i, lpNorm (fun p => (ρ p)⁻¹ * C i p) ∞ ν * lpNorm (V i) 2 ν) +
        lpNorm (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ∞ ν * lpNorm U 2 ν := by
  intro μ ν ρ A U V B τ C C₀ H hH R hR
  classical
  have hformula := hu.weak_time_derivative_eq_source hXcont hacont α hΩ hΩc hΩs hXsmooth
    ht₀ ht₁ hΩ₀ hΩ₀Ω H hH R hR
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hΩ₀target := hΩ₀s.trans (image_mono interior_subset)
  have hA (i j) : MemLp (A i j) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c hΩ₀target i j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c hΩ₀s i j j (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hρ : MemLp ρ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hB (i) : MemLp (B i) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top X isCompact_Icc
      measurableSet_Icc α (hXcont.mono (prod_mono Subset.rfl (subset_univ _)))
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) i (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hτ : MemLp τ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have ha : MemLp (fun p : ℝ × EuStd => a p.1) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hc := hacont.comp continuousOn_fst (fun _ hp => hp.1 : MapsTo Prod.fst
      (Icc (0 : ℝ) T ×ˢ closure Ω₀) (Icc (0 : ℝ) T))
    have hb := hc.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩ₀c)
      (measurableSet_Icc.prod hΩ₀.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hC (i) : MemLp (C i) ∞ (μ.prod (volume.restrict Ω₀)) := (hB i).mul hρ
  have hC₀ : MemLp C₀ ∞ (μ.prod (volume.restrict Ω₀)) := ((hτ.const_mul (1 / 2 : ℝ)).sub ha).mul hρ
  let chartTarget := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hTarget : IsOpen chartTarget := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩV : closure Ω ⊆ chartTarget := hΩs
  have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ chartTarget) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ chartTarget) : ρ p ≠ 0 :=
    ne_of_gt (MetricExtension.densityOnEuclid_pos (G.metric p.1) α
      ((image_mono interior_subset) hp))
  let v : ℝ × EuStd := (1, 0)
  have hρinv : MemLp (fun p => (ρ p)⁻¹) ∞ ν := by
    have hc := hρsmooth.continuousOn.inv₀ (fun p hp => hρne p hp.2)
    have h := (hc.mono (Set.prod_mono hreg hΩV)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have hDρ : MemLp (fun p => fderiv ℝ ρ p v) ∞ ν := by
    have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ ρ p v) (D.regular ×ˢ chartTarget) :=
      (hρsmooth.fderiv_of_isOpen (D.regular_isOpen.prod hTarget) (by simp)).clm_apply contDiffOn_const
    have h := (hc.continuousOn.mono (Set.prod_mono hreg hΩV)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have he : R =ᵐ[ν] fun p =>
      (∑ i, ∑ j, ((ρ p)⁻¹ * A i j p) * H i j p) +
      (∑ i, ∑ j, ((ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1, z)) p.2
        (EuclideanSpace.single j 1)) * V i p) +
      (∑ i, ((ρ p)⁻¹ * C i p) * V i p) +
      ((ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) * U p := by
    filter_upwards [hformula] with p hp
    rw [hp]
    simp only [ρ, A, U, V, C, C₀, B, τ, Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_assoc]
  have hn := norm_weak_time_source_le
    (fun i j p => (ρ p)⁻¹ * A i j p)
    (fun i j p => (ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1))
    (fun i j => (hA i j).mul hρinv) (fun i j => (hDA i j).mul hρinv)
    (fun i p => (ρ p)⁻¹ * C i p) (fun i => (hC i).mul hρinv)
    (fun p => (ρ p)⁻¹ * (C₀ p - fderiv ℝ ρ p (1, 0))) ((hC₀.sub hDρ).mul hρinv)
    (fun i j p => H i j p) (fun i j => Lp.memLp (H i j))
    (fun i p => V i p) hV U hU R he
  have hHnorm (i j) : lpNorm (fun p => H i j p) 2 ν = ‖H i j‖ := by
    rw [← toReal_eLpNorm (Lp.memLp (H i j)).aestronglyMeasurable, Lp.norm_def]
  simpa only [hHnorm] using hn

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
