import DifferentialGeometry.Analysis.Parabolic.Dirichlet.TimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.PotentialCoefficientBounds

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

private theorem exists_lp_product_source
    {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (k : Fin d)
    {c u v : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : MemLp c ∞ (μ.prod (volume.restrict Ω)))
    (hDc : MemLp (fun p => fderiv ℝ (fun x => c (p.1, x)) p.2
      (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hs : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => c (t, x)) Ω)
    (hu : MemLp u 2 (μ.prod (volume.restrict Ω)))
    (hv : MemLp v 2 (μ.prod (volume.restrict Ω)))
    (hw : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun x => v (t, x)) (fun x => u (t, x)) Ω) :
    ∃ F : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      ∀ (φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω →
        (∫ p, c p * u p * fderiv ℝ φ p (0, EuclideanSpace.single k 1)
          ∂μ.prod (volume.restrict Ω)) =
          -(∫ p, F p * φ p ∂μ.prod (volume.restrict Ω)) := by
  let U := hu.toLp u
  let V := hv.toLp v
  have hU : U =ᵐ[μ.prod (volume.restrict Ω)] u := hu.coeFn_toLp
  have hV : V =ᵐ[μ.prod (volume.restrict Ω)] v := hv.coeFn_toLp
  have hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V (t, x)) (fun x => U (t, x)) Ω := by
    filter_upwards [hw, Measure.ae_ae_of_ae_prod hU, Measure.ae_ae_of_ae_prod hV]
      with t ht hut hvt
    intro φ hφ hφc hφs
    calc
      _ = ∫ x in Ω, u (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
        apply integral_congr_ae
        filter_upwards [hut] with x hx
        rw [hx]
      _ = -(∫ x in Ω, v (t, x) * φ x) := ht φ hφ hφc hφs
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hvt] with x hx
        rw [hx]
  obtain ⟨F, _, hF⟩ := DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_product_weakPartial
    (by norm_num) hΩ k U V hc hDc hs hweak
  refine ⟨F, ?_⟩
  intro φ hφ hφc hφs
  have heq := DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
    ((hc.fun_mul (r := 2) (Lp.memLp U)).locallyIntegrable (by norm_num))
    ((Lp.memLp F).locallyIntegrable (by norm_num)) k hF φ hφ hφc hφs
  refine (integral_congr_ae ?_).trans heq
  filter_upwards [hU] with p hp
  simp only [hp]

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

theorem IsWeakEvolutionSolution.exists_lp_weakPartial_localLowerSource
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
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let L := fun p => (∑ i, (ρ p * B i p) * V i p) +
      (ρ p * ((1 / 2 : ℝ) * τ p - a p.1)) * U p
    ∃ F : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, L p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, F p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
  intro μ ρ B τ U V L
  classical
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
  choose DV hDV using hu.exists_ae_hasWeakPartialDeriv_localWeakPartial_on hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hVweak (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DV i k (t, x)) (fun x => V i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hDV i k, hc] with t ht hct
    have he : (fun x => V i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      ae_restrict_of_ae_restrict_of_subset hsub hct
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      hΩ₀ k he.symm ht
  have hUweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V k (t, x)) (fun x => U (t, x)) Ω₀ := by
    have ht := ae_restrict_of_ae (s := Icc t₀ t₁)
      (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [ht] with t ht
    exact ht.restrict hΩ₀ hsub
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
  let C := fun i (p : ℝ × EuStd) => ρ p * B i p
  let C₀ := fun p : ℝ × EuStd => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
  have hC (i) : MemLp (C i) ∞ (μ.prod (volume.restrict Ω₀)) := hρ.fun_mul (r := ∞) (hB i)
  have hC₀ : MemLp C₀ ∞ (μ.prod (volume.restrict Ω₀)) := hρ.fun_mul (r := ∞) ((hτ.const_mul (1 / 2 : ℝ)).sub ha)
  have hDC (i) : MemLp (fun p => fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_mul_chartCoeffOnE_family_fderiv_memLp_top hG isCompact_Icc
      hreg α X hXsmooth hΩ₀.measurableSet hΩ₀c hΩ₀s i (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDC₀ : MemLp (fun p => fderiv ℝ (fun x => C₀ (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.potentialCoefficient_family_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c hΩ₀s hacont (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) T :=
    ae_restrict_of_ae (s := Icc t₀ t₁) (ae_restrict_mem measurableSet_Icc)
  have hρs : ContDiffOn ℝ ∞ ρ (D.regular ×ˢ Ω₀) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset))))
  have hCs (i) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => C i (t, x)) Ω₀ := by
    have hBs := (MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α hXsmooth i).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset))))
    filter_upwards [hmem] with t ht
    exact (hρs.mul hBs).comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hreg ht, hy⟩)
  have hC₀s : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => C₀ (t, x)) Ω₀ := by
    have hτs := MetricExtension.traceTimeDerivMetric_comp_chartInverse_contDiffOn hG Subset.rfl α
      (subset_closure.trans hΩ₀s)
    filter_upwards [hmem] with t ht
    have hr := hρs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hreg ht, hy⟩)
    have hτt := hτs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hreg ht, hy⟩)
    exact hr.mul (((contDiffOn_const (c := (1 / 2 : ℝ))).mul hτt).sub (contDiffOn_const (c := a t)))
  choose F hF using fun i => exists_lp_product_source hΩ₀ k (hC i) (hDC i) (hCs i) (hV i)
    (Lp.memLp (DV i k)) (hVweak i)
  obtain ⟨F₀, hF₀⟩ := exists_lp_product_source hΩ₀ k hC₀ hDC₀ hC₀s hU (hV k) hUweak
  let f := fun p : ℝ × EuStd => (∑ i, F i p) + F₀ p
  have hf : MemLp f 2 (μ.prod (volume.restrict Ω₀)) :=
    (memLp_finsetSum Finset.univ fun i _ => Lp.memLp (F i)).add (Lp.memLp F₀)
  refine ⟨hf.toLp f, ?_⟩
  intro φ hφ hφc hφs
  let dφ := fun p : ℝ × EuStd => fderiv ℝ φ p (0, EuclideanSpace.single k 1)
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply (𝕜 := ℝ) (0, EuclideanSpace.single k 1)
  have hI (i) : Integrable (fun p => C i p * V i p * dφ p) (μ.prod (volume.restrict Ω₀)) :=
    (((hC i).fun_mul (r := 2) (hV i)).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hdφ hdφc
  have hI₀ : Integrable (fun p => C₀ p * U p * dφ p) (μ.prod (volume.restrict Ω₀)) :=
    ((hC₀.fun_mul (r := 2) hU).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hdφ hdφc
  have hFI (i) : Integrable (fun p => F i p * φ p) (μ.prod (volume.restrict Ω₀)) :=
    ((Lp.memLp (F i)).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hFI₀ : Integrable (fun p => F₀ p * φ p) (μ.prod (volume.restrict Ω₀)) :=
    ((Lp.memLp F₀).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  calc
    _ = (∑ i, ∫ p, C i p * V i p * dφ p ∂μ.prod (volume.restrict Ω₀)) +
        ∫ p, C₀ p * U p * dφ p ∂μ.prod (volume.restrict Ω₀) := by
      change (∫ p, ((∑ i, C i p * V i p) + C₀ p * U p) * dφ p ∂μ.prod (volume.restrict Ω₀)) = _
      simp_rw [add_mul, Finset.sum_mul]
      rw [integral_add (integrable_finsetSum _ (fun i _ => hI i)) hI₀,
        integral_finsetSum _ (fun i _ => hI i)]
    _ = -(∫ p, f p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
      dsimp only [dφ]
      simp_rw [hF _ φ hφ hφc hφs, hF₀ φ hφ hφc hφs]
      simp only [f, add_mul, Finset.sum_mul]
      rw [integral_add (integrable_finsetSum _ (fun i _ => hFI i)) hFI₀,
        integral_finsetSum _ (fun i _ => hFI i)]
      simp only [Finset.sum_neg_distrib, neg_add_rev]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with p hp
      rw [hp]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
