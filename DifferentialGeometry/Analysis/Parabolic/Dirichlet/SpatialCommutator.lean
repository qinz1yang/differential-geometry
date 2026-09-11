import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationProduct
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientDerivativeBounds

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

theorem IsWeakEvolutionSolution.exists_lp_divergence_coefficient_fderiv_localWeakPartial
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
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let A := fun i j (p : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))) =>
      fderiv ℝ (MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j)
        p.2 (EuclideanSpace.single k 1)
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ F : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, F p * φ p ∂μ.prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω₀) := by
  intro μ A V
  classical
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤
      (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 (μ.prod (volume.restrict Ω₀)) :=
    (Lp.memLp (V i)).mono_measure hmeasure
  let W := fun i => (hV i).toLp (V i)
  have hW (i) : W i =ᵐ[μ.prod (volume.restrict Ω₀)] V i := (hV i).coeFn_toLp
  choose DV hDV using hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hA (i j) : MemLp (A i j) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c hΩ₀s i j k (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c hΩ₀s i j (EuclideanSpace.single k 1)
        (EuclideanSpace.single j 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hAsmooth (i j) : ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω₀ := by
    apply Filter.Eventually.of_forall
    intro t
    have hc := (MetricExtension.weightedInvGramOnEuclid_contDiffOn (G.metric t) α i j).mono
      (hsub.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
    exact (hc.fderiv_of_isOpen hΩ₀ (by simp)).clm_apply contDiffOn_const
  have hweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => DV i j (t, x)) (fun x => W i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hDV i j, Measure.ae_ae_of_ae_prod (hW i), hc] with t ht hwt hct
    have he : (fun x => W i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      hΩ₀ j he.symm ht
  obtain ⟨F, _, hF⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
      (by norm_num) hΩ₀ W DV hA hDA hAsmooth hweak
  refine ⟨F, ?_⟩
  intro φ hφ hφc hφs
  rw [hF φ hφ hφc hφs]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hW i] with p hp
  rw [hp]

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.exists_lp_spatial_commutator
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
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ρ := fun (p : ℝ × EuStd) =>
      MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i ((toEuclidean (E := EuN)).symm p.2)
    let Dρ := fun p : ℝ × EuStd =>
      fderiv ℝ (fun z => ρ (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let DB := fun i (p : ℝ × EuStd) =>
      fderiv ℝ (fun z => ρ (p.1, z) * B i (p.1, z)) p.2 (EuclideanSpace.single k 1)
    let A := fun i j (p : ℝ × EuStd) =>
      fderiv ℝ (MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j)
        p.2 (EuclideanSpace.single k 1)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ R Fdiv F : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ (φ : ℝ × EuStd → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀))) ∧
      (∀ (φ : ℝ × EuStd → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, Fdiv p * φ p ∂μ.prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂μ.prod (volume.restrict Ω₀)) ∧
      F =ᵐ[μ.prod (volume.restrict Ω₀)] fun p =>
        Fdiv p + (∑ i, DB i p * V i p) - a p.1 * Dρ p * U p - Dρ p * R p := by
  intro μ ρ B Dρ DB A U V
  obtain ⟨R, hR⟩ := hu.exists_lp_weak_time_deriv hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  obtain ⟨Fdiv, hFdiv⟩ := hu.exists_lp_divergence_coefficient_fderiv_localWeakPartial hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω k
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤
      (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 (μ.prod (volume.restrict Ω₀)) := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 (μ.prod (volume.restrict Ω₀)) :=
    (Lp.memLp (V i)).mono_measure hmeasure
  have hDρ : MemLp Dρ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_family_fderiv_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c hΩ₀s (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDB (i) : MemLp (DB i) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_mul_chartCoeffOnE_family_fderiv_memLp_top
      hG isCompact_Icc hreg α X hXsmooth hΩ₀.measurableSet hΩ₀c hΩ₀s i
      (EuclideanSpace.single k 1) (volume.prod volume)
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
  let F : ℝ × EuStd → ℝ := fun p =>
    Fdiv p + (∑ i, DB i p * V i p) - a p.1 * Dρ p * U p - Dρ p * R p
  have hF : MemLp F 2 (μ.prod (volume.restrict Ω₀)) :=
    (((Lp.memLp Fdiv).add (memLp_finsetSum Finset.univ fun i _ => (hV i).mul (hDB i))).sub
      (hU.mul (hDρ.mul (r := ∞) ha))).sub ((Lp.memLp R).mul hDρ)
  exact ⟨R, Fdiv, hF.toLp F, hR, hFdiv, hF.coeFn_toLp⟩

theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_commutator
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
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let L := fun p => (∑ i, ρ p * B i p * V i p) +
      ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric p.1 (x p.2) - a p.1) * U p
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, (A i j p * H k i p +
            fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
          (∫ p, L p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν) +
          ∫ p, (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0) * U p) * φ p ∂ν := by
  intro μ ν x ρ A B U V L
  obtain ⟨R, hR⟩ := hu.exists_lp_weak_time_deriv hXcont hacont α hΩ hΩc hΩs
    hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  obtain ⟨H, hH, hHsym⟩ := hu.exists_lp_symmetric_weak_second_deriv hXcont hacont α
    hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨R, H, hR, hH, hHsym, ?_⟩
  intro k φ hφ hφc hφs
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : LocallyIntegrable U ν := ((Lp.memLp U).mono_measure hmeasure).locallyIntegrable (by norm_num)
  have hV (i) : LocallyIntegrable (V i) ν :=
    ((Lp.memLp (V i)).mono_measure hmeasure).locallyIntegrable (by norm_num)
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => V i (t,z))
      (fun z => U (t,z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hsecond (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H k i (t,z))
      (fun z => V i (t,z)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i k, hc] with t ht hct
    have he : (fun z => V i (t, z)) =ᵐ[volume.restrict Ω₀]
        (fun z => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z) := by
      exact ae_restrict_of_ae_restrict_of_subset hsub hct
    rw [← hHsym i k]
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ k he.symm ht
  have hspace : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, V k p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      hU (hV k) k (hfirst k) ψ hψ hψc
      (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hflux (ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) :
      ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, H k ij.1 p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hV ij.1) ((Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num)) k (hsecond ij.1)
      ψ hψ hψc (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hJ : Ioo t₀ t₁ ⊆ D.regular := by
    intro t ht
    exact hreg ⟨ht₀.le.trans ht.1.le, ht.2.le.trans ht₁.le⟩
  have hΩs' := hsub.trans (subset_closure.trans hΩs)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (Ioo t₀ t₁ ×ˢ Ω₀) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG hJ α).mono
      (Set.prod_mono Subset.rfl (hΩs'.trans (image_mono interior_subset)))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (Ioo t₀ t₁ ×ˢ Ω₀) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG hJ α hΩs' i j
  have hbase : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, ρ p * U p * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN), ∫ p,
          A ij.1 ij.2 p * V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single ij.2 1) ∂ν) -
          ∫ p, L p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hb := hu.integral_spacetime_test_divergence hXcont hacont α hΩ hΩc hΩs hψ hψc
      hΩ₀.measurableSet hsub ht₀ ht₁ hψs
    simpa only [Fintype.sum_prod_type] using hb
  have hcomm := Sobolev.integral_weak_deriv_weighted_divergence Finset.univ
    (isOpen_Ioo.prod hΩ₀) (0, EuclideanSpace.single k 1) (1, 0)
    (fun ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN) =>
      (0, EuclideanSpace.single ij.2 1)) hU (hV k)
    ((Lp.memLp R).locallyIntegrable (by norm_num))
    (fun ij _ => hV ij.1) (fun ij _ => (Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num))
    hρ (fun ij _ => hA ij.1 ij.2) hspace hR (fun ij _ => hflux ij) hbase hφ hφc hφs
  simpa only [Fintype.sum_prod_type] using hcomm


end DifferentialGeometry.Analysis.Parabolic.Dirichlet
