import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeProduct
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
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
  let ν := μ.prod (volume.restrict Ω₀)
  let L := fun p => (∑ i, ρ p * B i p * V i p) + ρ p *
    ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p
  have hRφ : Integrable (fun p => R p * φ p) ν :=
    ((Lp.memLp R).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  have hFφ : Integrable (fun p => F p * φ p) ν :=
    ((Lp.memLp F).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  have hL : (fun p => L p * φ p) =ᵐ[ν] fun p => R p * φ p - F p * φ p := by
    filter_upwards [hR] with p hp
    rw [hp]
    dsimp only [L]
    ring
  have hLint : (∫ p, L p * φ p ∂ν) =
      (∫ p, R p * φ p ∂ν) - ∫ p, F p * φ p ∂ν := by
    rw [integral_congr_ae hL, integral_sub hRφ hFφ]
  have hbase := hu.integral_spacetime_test_divergence hXcont hacont α hΩ hΩc hΩs hφ hφc
    hΩ₀.measurableSet (subset_closure.trans hΩ₀Ω) ht₀ ht₁ hφs
  change (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
    (∑ i, ∑ j, ∫ p, A i j p * V i p *
      fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, L p * φ p ∂ν at hbase
  have hdiv := hF φ hφ hφc (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  linarith


local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.exists_lp_weak_time_deriv
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
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∃ R : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuStd → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
  intro μ U
  let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
  let v : ℝ × EuStd := (1, 0)
  let S := Ioo t₀ t₁ ×ˢ Ω₀
  let ν := μ.prod (volume.restrict Ω₀)
  obtain ⟨R, hR⟩ := hu.exists_lp_weak_time_deriv_density hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  let V := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hV : IsOpen V := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩV : closure Ω ⊆ V := hΩs
  have hΩ₀V : closure Ω₀ ⊆ V := hΩ₀Ω.trans (subset_closure.trans hΩV)
  have hreg₀ : Ioo t₀ t₁ ⊆ D.regular := fun t ht =>
    hreg ⟨le_trans ht₀.le ht.1.le, le_trans ht.2.le ht₁.le⟩
  have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ V) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ V) : ρ p ≠ 0 :=
    ne_of_gt (MetricExtension.densityOnEuclid_pos (G.metric p.1) α
      ((image_mono interior_subset) hp))
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hρinv : MemLp (fun p => (ρ p)⁻¹) ∞ ν := by
    have hc := hρsmooth.continuousOn.inv₀ (fun p hp => hρne p hp.2)
    have h := (hc.mono (Set.prod_mono hreg hΩV)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have hDρ : MemLp (fun p => fderiv ℝ ρ p v) ∞ ν := by
    have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ ρ p v) (D.regular ×ˢ V) :=
      (hρsmooth.fderiv_of_isOpen (D.regular_isOpen.prod hV) (by simp)).clm_apply contDiffOn_const
    have h := (hc.continuousOn.mono (Set.prod_mono hreg hΩV)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  let F := fun p => (ρ p)⁻¹ * R p - ((ρ p)⁻¹ * fderiv ℝ ρ p v) * U p
  have hF : MemLp F 2 ν :=
    ((Lp.memLp R).mul hρinv).sub (hU.mul (hDρ.mul (r := ∞) hρinv))
  refine ⟨hF.toLp F, ?_⟩
  intro φ hφ hφc hφs
  have heq := DifferentialGeometry.Analysis.Sobolev.integral_fderiv_eq_neg_of_weighted_identity
    (μ := ν) (S := S) (isOpen_Ioo.prod hΩ₀) v (hU.locallyIntegrable (by norm_num))
    ((Lp.memLp R).locallyIntegrable (by norm_num))
    (hρsmooth.mono (Set.prod_mono hreg₀ (hsub.trans (subset_closure.trans hΩV))))
    (fun p hp => hρne p (hsub.trans (subset_closure.trans hΩV) hp.2))
    (fun ψ hψ hψc hψs => hR ψ hψ hψc hψs) hφ hφc hφs
  refine heq.trans (congrArg Neg.neg ?_)
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with p hp
  exact congrArg (fun r => r * φ p) hp.symm


private theorem exists_lp_chartInverse_eq_uncurry
    (q : SmoothRiemannianMetric I_hs M) (α : M)
    {Ω Ω₀ : Set EuStd} (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target)
    (hΩ₀ : MeasurableSet Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) {μ κ : Measure ℝ} (hμle : μ ≤ κ)
    (u : Lp (H1ComplDirichlet q) 2 κ) :
    ∃ P : Lp (Lp ℝ 2 (volume.restrict Ω₀)) 2 μ,
      (∀ᵐ t ∂μ, (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z =>
        H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) ∧
      (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P : ℝ × EuStd → ℝ)
        =ᵐ[μ.prod (volume.restrict Ω₀)]
          dirichletLocalSpacetimeLp q α hΩ hΩc hΩs κ u := by
  let uμ : Lp (H1ComplDirichlet q) 2 μ := ((Lp.memLp u).mono_measure hμle).toLp u
  let A := (chartRestrictionLp q α hΩ₀ hΩ₀c hΩ₀s 2).comp
    (H1ComplDirichletToLp q)
  let P := A.compLpL 2 μ uμ
  let U := dirichletLocalSpacetimeLp q α hΩ hΩc hΩs κ u
  have hP : ∀ᵐ t ∂μ, (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z =>
      H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [A.coeFn_compLpL uμ, MemLp.coeFn_toLp ((Lp.memLp u).mono_measure hμle)]
      with t ht htμ
    rw [show P t = A (uμ t) from ht, htμ]
    exact chartRestrictionLp_coeFn q α hΩ₀ hΩ₀c hΩ₀s 2
      (H1ComplDirichletToLp q (u t))
  have hU : ∀ᵐ t ∂μ, (fun z => U (t, z)) =ᵐ[volume.restrict Ω₀] fun z =>
      H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [(dirichletLocalSpacetimeLp_coeFn q α hΩ hΩc
      hΩs κ u).filter_mono (ae_mono hμle)] with t ht
    exact ht.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  refine ⟨P, hP, ?_⟩
  apply (Measure.ae_prod_iff_ae_ae
    ((Lp.stronglyMeasurable _).measurableSet_eq_fun (Lp.stronglyMeasurable U))).mpr
  filter_upwards [Lp.uncurry_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P,
    hP, hU] with t ht₁ ht₂ ht₃
  exact ht₁.trans (ht₂.trans ht₃.symm)

theorem IsWeakEvolutionSolution.exists_timeH1_chartInverse
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
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ < t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ w : timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (t₁ - t₀),
      ∀ᵐ s ∂timeMeasure (t₁ - t₀),
        (w.toFun s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z =>
          H1ComplDirichletToLp q (u (t₀ + s))
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  let μ := volume.restrict (Icc t₀ t₁)
  have hI : Icc t₀ t₁ ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht₀.le.trans ht.1, ht.2.trans ht₁.le⟩
  have hμ : (timeMeasure T).restrict (Icc t₀ t₁) = μ :=
    Measure.restrict_restrict_of_subset hI
  have hμle : μ ≤ timeMeasure T := by
    rw [← hμ]
    exact Measure.restrict_le_self
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset)))
  obtain ⟨P, hP, hUP⟩ := exists_lp_chartInverse_eq_uncurry q α
    hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset))
    hΩ₀.measurableSet hΩ₀c hΩ₀s hsub hμle u
  have hsource := hu.exists_lp_weak_time_deriv hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  dsimp only at hsource
  rw [hμ] at hsource
  obtain ⟨R, hR⟩ := hsource
  have hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
        fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
      -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
    intro φ hφ hφc hφs
    refine (integral_congr_ae ?_).trans (hR φ hφ hφc hφs)
    filter_upwards [hUP] with p hp
    exact congrArg (fun v => v * fderiv ℝ φ p (1, 0)) hp
  obtain ⟨w, hw, _⟩ := exists_timeH1_of_spacetime_weak_deriv_on ht₀₁ hΩ₀ P R hweak
  have hshift : MeasurePreserving (fun s : ℝ => t₀ + s) (timeMeasure (t₁ - t₀)) μ := by
    have h := (measurePreserving_add_right volume t₀).restrict_image_emb
      (Homeomorph.addRight t₀).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (t₁ - t₀))
    simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm t₀] using h
  refine ⟨w, ?_⟩
  filter_upwards [hw, hshift.quasiMeasurePreserving.ae hP] with s hs hsP
  rw [← hs]
  exact hsP

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
