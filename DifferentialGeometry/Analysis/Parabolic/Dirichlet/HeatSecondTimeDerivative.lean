import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatTimeDerivativeHessian
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeFiniteSum
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

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

theorem exists_second_weak_time_derivative_of_heat_timeH1
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
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ i j, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω) →
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∀ Ft : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, F p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, Ft p * φ p ∂ν) →
    ∀ R : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      ∃ Rt : Lp ℝ 2 ν,
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
          (∫ p, R p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, Rt p * φ p ∂ν := by
  intro F Df hDf DDf hDDf μ ν U Ft hFt R hR
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨H, hH, _⟩ := exists_local_second_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀c hΩ₀Ω ha hb u f w hwmass hwderiv
  obtain ⟨DR, DDR, hDR, hDDR, _, _⟩ :=
    exists_second_spatial_weak_derivative_time_derivative_of_heat_timeH1
      hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
      hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf DDf hDDf R hR
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hformula := weak_time_derivative_eq_source_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hsub ha hb u f w hwmass hwderiv H hH R hR
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hF : MemLp F 2 ν := (Lp.memLp F).mono_measure hmeasure
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  let V₀ := fun i => (hV i).toLp (V i)
  let F₀ := hF.toLp F
  have hV₀ (i) : V₀ i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hF₀ : F₀ =ᵐ[ν] F := hF.coeFn_toLp
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => V i (t, x)) (fun x => U (t, x)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc a b)
      (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
        hΩ hΩc hΩs (timeMeasure T) i u)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hsecond (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => V i (t, x)) Ω₀ := by
    have hVi := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i j, hVi] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j
      (Filter.EventuallyEq.symm
        (he.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))) ht
  have hVtime (i) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω₀) :
      (∫ p, V i p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DR i p * φ p ∂ν :=
    integral_fderiv_prod_left_eq_neg_of_weak_partials (1 : ℝ) i
      (hU.locallyIntegrable (by norm_num)) ((hV i).locallyIntegrable (by norm_num))
      ((Lp.memLp R).locallyIntegrable (by norm_num))
      ((Lp.memLp (DR i)).locallyIntegrable (by norm_num))
      (hfirst i) (hDR i) hR hφ hφc hφs
  have hHtime (i j) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω₀) :
      (∫ p, H i j p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DDR i j p * φ p ∂ν :=
    integral_fderiv_prod_left_eq_neg_of_weak_partials (1 : ℝ) j
      ((hV i).locallyIntegrable (by norm_num))
      ((Lp.memLp (H i j)).locallyIntegrable (by norm_num))
      ((Lp.memLp (DR i)).locallyIntegrable (by norm_num))
      ((Lp.memLp (DDR i j)).locallyIntegrable (by norm_num))
      (hsecond i j) (hDDR i j) (hVtime i) hφ hφc hφs
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩ₀W : closure Ω₀ ⊆ W := hΩ₀Ω.trans (subset_closure.trans hΩs)
  let ρ := fun (p : ℝ × EuStd) => densityOnEuclid (g p.1) α p.2
  let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (g p.1) α i j p.2
  let P := fun i j p => (ρ p)⁻¹ * A i j p
  let Q := fun i (p : ℝ × EuStd) =>
    ∑ j, (ρ p)⁻¹ * fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)
  have hρ : ContDiffOn ℝ ∞ (fun p => (ρ p)⁻¹) (D.regular ×ˢ W) :=
    ((densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))).inv
        (fun p hp => (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp.2)).ne')
  have hP (i j) : ContDiffOn ℝ ∞ (P i j) (D.regular ×ˢ W) :=
    hρ.mul (weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j)
  have hQ (i) : ContDiffOn ℝ ∞ (Q i) (D.regular ×ˢ W) := by
    apply ContDiffOn.sum
    intro j _
    exact hρ.mul ((weightedInvGramOnEuclid_family_fderiv_contDiffOn
      (G := G) hG Subset.rfl α hW Subset.rfl i j).clm_apply contDiffOn_const)
  have hbound (c : ℝ × EuStd → ℝ) (hc : ContDiffOn ℝ ∞ c (D.regular ×ˢ W)) :
      MemLp c ∞ ν := by
    have hc' := DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn
      D.regular_isOpen isCompact_Icc hreg hW hΩ₀.measurableSet hΩ₀c hΩ₀W
      (A := fun t z => c (t, z)) (hc.of_le (by simp)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hc'
    exact hc'.1.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  let ι := (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) ⊕ Unit)
  let Y : ι → Lp ℝ 2 ν := Sum.elim (fun ij => H ij.1 ij.2) (Sum.elim V₀ (fun _ => F₀))
  let DY : ι → Lp ℝ 2 ν :=
    Sum.elim (fun ij => DDR ij.1 ij.2) (Sum.elim DR (fun _ => Ft))
  let B : ι → ℝ × EuStd → ℝ :=
    Sum.elim (fun ij => P ij.1 ij.2) (Sum.elim Q (fun _ _ => 1))
  have hBreg (i) : ContDiffOn ℝ ∞ (B i) (D.regular ×ˢ W) := by
    rcases i with ⟨i, j⟩ | (i | i)
    · exact hP i j
    · exact hQ i
    · exact contDiffOn_const
  have hDBreg (i) : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (B i) p (1, 0))
      (D.regular ×ˢ W) :=
    ((hBreg i).fderiv_of_isOpen (m := ∞) (D.regular_isOpen.prod hW) (by simp)).clm_apply
      contDiffOn_const
  have hBs (i) : ContDiffOn ℝ ∞ (B i) (Ioo a b ×ˢ Ω₀) :=
    (hBreg i).mono (prod_mono (fun t ht => hreg ⟨ha.le.trans ht.1.le, ht.2.le.trans hb.le⟩)
      (subset_closure.trans hΩ₀W))
  have hY (i) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω₀) :
      (∫ p, Y i p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, DY i p * φ p ∂ν := by
    rcases i with ⟨i, j⟩ | (i | i)
    · exact hHtime i j φ hφ hφc hφs
    · refine (integral_congr_ae ?_).trans (hVtime i φ hφ hφc hφs)
      filter_upwards [hV₀ i] with p hp
      exact congrArg (fun z => z * fderiv ℝ φ p (1, 0)) hp
    · refine (integral_congr_ae ?_).trans (hFt φ hφ hφc hφs)
      filter_upwards [hF₀] with p hp
      exact congrArg (fun z => z * fderiv ℝ φ p (1, 0)) hp
  have hRsum : R =ᵐ[ν] fun p => ∑ i, B i p * Y i p := by
    filter_upwards [hformula, hF₀, ae_all_iff.mpr hV₀] with p hp hf hv
    change R p = ∑ i : (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
      (Fin (Module.finrank ℝ EuN) ⊕ Unit), B i p * Y i p
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    change R p = (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
        P ij.1 ij.2 p * H ij.1 ij.2 p) + ((∑ i, Q i p * V₀ i p) + ∑ _ : Unit, 1 * F₀ p)
    simp only [Fintype.sum_prod_type, one_mul, Fintype.sum_unique]
    rw [hf]
    simp_rw [hv]
    rw [hp]
    change (ρ p)⁻¹ * (∑ i, ∑ j, (A i j p * H i j p +
      fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1) * V i p)) + F p = _
    simp only [P, Q, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add, mul_assoc, add_assoc]
  obtain ⟨Rt, _, hRt⟩ := DifferentialGeometry.Analysis.Sobolev.exists_lp_weak_deriv_of_ae_eq_finite_sum
    Finset.univ (isOpen_Ioo.prod hΩ₀) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (1, 0) R Y DY B
    (fun i _ => hbound _ (hBreg i)) (fun i _ => hbound _ (hDBreg i)) (fun i _ => hBs i)
    (fun i _ => hY i) hRsum
  exact ⟨Rt, hRt⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
