import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatGradientSourceRegularity
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_lp_weak_hessian_equation_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a ≤ b)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z)) :
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω) →
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω₀) →
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ S : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i j, H i j = H j i) ∧
      (∀ i j k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun z => K i j k (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
      (∀ k i l, K k i l = K k l i) ∧
      ∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k l p * φ p ∂ν := by
  intro F Df hDf μ ν ρ A DDf hDDf
  classical
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨R, H, Q, hR, hH, hHsym, _, hQ, DQ, hDQ, _, _⟩ :=
    exists_lp_weak_gradient_equation_with_source_spatial_derivative_of_heat_timeH1
      hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
      hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf DDf hDDf
  obtain ⟨K, hK⟩ := exists_local_third_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf H hH
  obtain ⟨DR, hDR, _, _⟩ := exists_spatial_weak_derivative_time_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf R hR
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => V i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hsecond (k i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => H k i (t, z)) (fun z => V k (t, z)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [hH k i, hc] with t ht hct
    exact hasWeakPartialDeriv_congr_ae hΩ₀ i
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub hct)) ht
  have hspace (i) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, V i p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hU.locallyIntegrable (by norm_num)) ((hV i).locallyIntegrable (by norm_num)) i
      (hfirst i) φ hφ hφc (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have htime (k) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, V k p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DR k p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have hc := Sobolev.integral_weak_deriv_fderiv_comm
      (0, EuclideanSpace.single k 1) (1, 0) (hspace k) hR hφ hφc hφs
    exact hc.trans (integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp R).locallyIntegrable (by norm_num))
      ((Lp.memLp (DR k)).locallyIntegrable (by norm_num)) k (hDR k) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl)))
  have hKsym (k i l) : K k i l = K k l i := by
    apply Lp.ext
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (K k i l)).measurable
        (Lp.stronglyMeasurable (K k l i)).measurable)).mpr
    filter_upwards [hH k i, hH k l, hK k i l, hK k l i,
      (Lp.memLp (K k i l)).prodMk_left (by norm_num),
      (Lp.memLp (K k l i)).prodMk_left (by norm_num)] with t hi hl hil hli hilLp hliLp
    exact Sobolev.ae_eq_of_weak_second_deriv_comm hΩ₀ (ae_restrict_mem hΩ₀.measurableSet)
      (EuclideanSpace.single i 1) (EuclideanSpace.single l 1) hi hl hil hli
      (hilLp.locallyIntegrable (by norm_num)) (hliLp.locallyIntegrable (by norm_num))
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hAall (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ Ω) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α
      (subset_closure.trans hΩs) i j
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : MemLp f ∞ ν := by
    have hb := (hc.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hPO : Ioo a b ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω :=
    prod_mono (fun t ht => hreg ⟨ha.le.trans ht.1.le, ht.2.le.trans hb.le⟩) hsub
  have hHint (k i) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, V k p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, H k i p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((hV k).locallyIntegrable (by norm_num))
      ((Lp.memLp (H k i)).locallyIntegrable (by norm_num)) i (hsecond k i) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hKint (k i j) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, H k i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
        -∫ p, K k i j p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp (H k i)).locallyIntegrable (by norm_num))
      ((Lp.memLp (K k i j)).locallyIntegrable (by norm_num)) j (hK k i j) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hDQint (k l) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, Q k p * fderiv ℝ φ p (0, EuclideanSpace.single l 1) ∂ν) =
        -∫ p, DQ k l p * φ p ∂ν := by
    intro φ hφ hφc hφs
    exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp (Q k)).locallyIntegrable (by norm_num))
      ((Lp.memLp (DQ k l)).locallyIntegrable (by norm_num)) l (hDQ k l) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hd {B : ℝ × EuStd → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (D.regular ×ˢ Ω))
      (v : ℝ × EuStd) : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ B p v) (D.regular ×ˢ Ω) :=
    (hB.fderiv_of_isOpen (m := ∞) (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
  have hbase (k) : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
          ∫ p, A ij.1 ij.2 p * H k ij.1 p *
            fderiv ℝ φ p (0, EuclideanSpace.single ij.2 1) ∂ν) - ∫ p, Q k p * φ p ∂ν := by
    simpa only [Fintype.sum_prod_type] using hQ k
  have hex (k l) := Sobolev.exists_lp_weak_deriv_weighted_divergence Finset.univ
    (isOpen_Ioo.prod hΩ₀) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (0, EuclideanSpace.single l 1) (1, 0)
    (fun ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN) =>
      (0, EuclideanSpace.single ij.2 1))
    (hV k) ((Lp.memLp (H k l)).locallyIntegrable (by norm_num)) (Lp.memLp (DR k)) (Lp.memLp (DQ k l))
    (fun ij _ => Lp.memLp (H k ij.1))
    (fun ij _ => (Lp.memLp (K k ij.1 l)).locallyIntegrable (by norm_num))
    (fun ij _ => Lp.memLp (K k ij.1 ij.2))
    (hρall.mono hPO) (fun ij _ => (hAall ij.1 ij.2).mono hPO)
    (fun ij _ => hlift _ (hd (hAall ij.1 ij.2) _).continuousOn)
    (fun ij _ => hlift _ (hd (hd (hAall ij.1 ij.2) _) _).continuousOn)
    (hlift _ (hd hρall _).continuousOn) (hlift _ (hd (hd hρall _) _).continuousOn)
    (hHint k l) (htime k) (fun ij _ => hKint k ij.1 l) (fun ij _ => hKint k ij.1 ij.2)
    (hDQint k l) (hbase k)
  choose S hSformula hS using hex
  refine ⟨H, K, S, hH, hHsym, hK, hKsym, ?_⟩
  intro k l φ hφ hφc hφs
  simpa only [Fintype.sum_prod_type, hKsym k _ l] using hS k l φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
