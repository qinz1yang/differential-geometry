import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatInteriorRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatWeakEquationChart
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeProduct
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeUniqueness
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
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

private theorem exists_local_lp_density_time_deriv_of_heat_divergence
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
    (hΩ₀ : IsOpen Ω₀) (hsub : Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let τ := fun p : ℝ × EuStd => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2)
    ∀ B : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω₀)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂μ.prod (volume.restrict Ω₀)) →
    ∃ R : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (R =ᵐ[μ.prod (volume.restrict Ω₀)] fun p => B p + ρ p * (τ p * U p + F p)) ∧
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
  intro μ ρ U A V x F τ B hB
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let ν := μ.prod (volume.restrict Ω₀)
  let L := fun p => ρ p * (τ p * U p + F p)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hρ : MemLp ρ ∞ ν := by
    have h := densityOnEuclid_family_memLp_top (G := G) hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  have hτ : MemLp τ ∞ ν := by
    have h := traceTimeDerivMetric_comp_chartInverse_memLp_top (G := G) hG isCompact_Icc hreg α
      hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at h
    exact (h.mono_measure hmeasure).const_mul (1 / 2 : ℝ)
  have hL : MemLp L 2 ν :=
    hρ.fun_mul (r := 2)
      ((hτ.fun_mul (r := 2) ((Lp.memLp U).mono_measure hmeasure)).add
        ((Lp.memLp F).mono_measure hmeasure))
  let R := fun p => B p + L p
  have hR : MemLp R 2 ν := (Lp.memLp B).add hL
  refine ⟨hR.toLp R, hR.coeFn_toLp, ?_⟩
  intro φ hφ hφc hφs
  have hφouter : tsupport φ ⊆ Ioo (0 : ℝ) T ×ˢ Ω :=
    hφs.trans (prod_mono (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩) hsub)
  have hbase := integral_spacetime_test_divergence_restrict_of_heat_timeH1 q g hG hT hreg hCg hequiv
    Cv hCv0 hCvtop hvol u f w hwmass hwderiv α hΩ hΩc hΩs hΩ₀.measurableSet hsub
    hφ hφc hφouter (hφs.trans (prod_mono Ioo_subset_Icc_self Subset.rfl))
  change (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
    (∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
      ∂ν) -
      ∫ p, L p * φ p ∂ν at hbase
  have hdiv := hB φ hφ hφc (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hBφ : Integrable (fun p => B p * φ p) ν :=
    ((Lp.memLp B).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  have hLφ : Integrable (fun p => L p * φ p) ν :=
    (hL.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  have hRint : (∫ p, (hR.toLp R) p * φ p ∂ν) =
      (∫ p, B p * φ p ∂ν) + ∫ p, L p * φ p ∂ν := by
    calc
      _ = ∫ p, B p * φ p + L p * φ p ∂ν := by
        apply integral_congr_ae
        filter_upwards [hR.coeFn_toLp] with p hp
        rw [hp]
        exact add_mul _ _ _
      _ = _ := integral_add hBφ hLφ
  rw [hRint]
  linarith

theorem exists_local_lp_weak_time_deriv_density_of_heat_timeH1
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
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∃ R : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
  intro μ ρ U
  obtain ⟨B, hB⟩ := exists_local_lp_divergence_of_heat_timeH1 hG hT hreg q hCg hequiv
    Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  obtain ⟨R, _, hR⟩ := exists_local_lp_density_time_deriv_of_heat_divergence hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ (subset_closure.trans hΩ₀Ω)
    ha hb u f w hwmass hwderiv B hB
  exact ⟨R, hR⟩

theorem exists_local_lp_weak_time_deriv_of_heat_timeH1
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
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    ∃ R : Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
          -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
  intro μ U
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let ρ := fun (p : ℝ × EuStd) => densityOnEuclid (I := I_hs) (g p.1) α p.2
  let v : ℝ × EuStd := (1, 0)
  let S := Ioo a b ×ˢ Ω₀
  let ν := μ.prod (volume.restrict Ω₀)
  obtain ⟨R, hR⟩ := exists_local_lp_weak_time_deriv_density_of_heat_timeH1 hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  let V := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hV : IsOpen V := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩV : closure Ω ⊆ V := hΩs
  have hreg₀ : Ioo a b ⊆ D.regular := fun t ht =>
    hreg ⟨le_trans ha.le ht.1.le, le_trans ht.2.le hb.le⟩
  have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ V) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ V) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (g p.1) α
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
  obtain ⟨R₀, _, hR₀⟩ := DifferentialGeometry.Analysis.Sobolev.exists_lp_weak_deriv_of_weighted_identity
    (μ := ν) (S := S) (isOpen_Ioo.prod hΩ₀) (by norm_num : (1 : ℝ≥0∞) ≤ 2) v hU (Lp.memLp R)
    (hρsmooth.mono (Set.prod_mono hreg₀ (hsub.trans (subset_closure.trans hΩV))))
    (fun p hp => hρne p (hsub.trans (subset_closure.trans hΩV) hp.2))
    hρinv (hρinv.fun_mul (r := ∞) hDρ) hR
  exact ⟨R₀, hR₀⟩

theorem weak_time_derivative_eq_source_of_heat_timeH1
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
    (hΩ₀ : IsOpen Ω₀) (hsub : Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T)
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
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ R : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) →
      R =ᵐ[ν] fun p => (ρ p)⁻¹ * (∑ i, ∑ j, (A i j p * H i j p +
        fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1) * V i p)) + F p := by
  intro μ ν ρ A U V F H hH R hR
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨B, hBval, hB⟩ := exists_lp_divergence_localWeakPartial_of_hasWeakPartialDeriv
    hG isCompact_Icc hreg (ae_restrict_mem measurableSet_Icc) q u α hΩ hΩc hΩs
    hΩ₀ hsub (Icc a b) H hH
  obtain ⟨S, hSval, hS⟩ := exists_local_lp_density_time_deriv_of_heat_divergence hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hsub ha hb u f w hwmass hwderiv B hB
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hreg₀ : Ioo a b ⊆ D.regular := fun t ht =>
    hreg ⟨ha.le.trans ht.1.le, ht.2.le.trans hb.le⟩
  have hρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ W) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ W) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp))
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hρinv : MemLp (fun p => (ρ p)⁻¹) ∞ ν := by
    have hc := hρsmooth.continuousOn.inv₀ (fun p hp => hρne p hp.2)
    have h := (hc.mono (prod_mono hreg hΩs)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure hmeasure
  let Q := fun p => (ρ p)⁻¹ * B p + F p
  have hQ : MemLp Q 2 ν :=
    (hρinv.fun_mul (r := 2) (Lp.memLp B)).add ((Lp.memLp F).mono_measure hmeasure)
  have hQval : (fun p => (ρ p)⁻¹ * S p - ((ρ p)⁻¹ * fderiv ℝ ρ p (1, 0)) * U p)
      =ᵐ[ν] Q := by
    filter_upwards [hSval, ae_mem_interior_time_prod hΩ₀.measurableSet] with p hp hpmem
    have hz : p.2 ∈ W := hΩs (subset_closure (hsub hpmem.2))
    have hd : fderiv ℝ ρ p (1, 0) = (1 / 2 : ℝ) *
        traceTimeDerivMetric (I := I_hs) g p.1
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) * ρ p :=
      densityOnEuclid_family_fderiv_time_eq (G := G) hG (hreg₀ hpmem.1) α hz
    calc
      _ = (ρ p)⁻¹ * (B p + ρ p * ((1 / 2 : ℝ) *
          traceTimeDerivMetric (I := I_hs) g p.1
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) * U p + F p)) -
          ((ρ p)⁻¹ * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) * ρ p)) * U p :=
        congrArg₂ (fun s d => (ρ p)⁻¹ * s - ((ρ p)⁻¹ * d) * U p) hp hd
      _ = Q p := by
        dsimp only [Q]
        field_simp [hρne p hz]
        ring
  have hQweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, hQ.toLp Q p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have he := Sobolev.integral_fderiv_eq_neg_of_weighted_identity
      (μ := ν) (S := Ioo a b ×ˢ Ω₀) (isOpen_Ioo.prod hΩ₀) (1, 0)
      (hU.locallyIntegrable (by norm_num)) ((Lp.memLp S).locallyIntegrable (by norm_num))
      (hρsmooth.mono (prod_mono hreg₀ (hsub.trans (subset_closure.trans hΩs))))
      (fun p hp => hρne p (hΩs (subset_closure (hsub hp.2)))) hS hφ hφc hφs
    refine he.trans (congrArg Neg.neg ?_)
    apply integral_congr_ae
    filter_upwards [hQval, hQ.coeFn_toLp] with p hp hqp
    rw [hp, hqp]
  have he : R = hQ.toLp Q := lp_eq_of_weak_time_deriv_integral hΩ₀ (by norm_num) hR hQweak
  rw [he]
  filter_upwards [hQ.coeFn_toLp, hBval] with p hp hbp
  rw [hp]
  dsimp only [Q]
  rw [hbp]
  rfl

theorem exists_timeH1_chartInverse_of_heat_timeH1
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
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a < b)
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
    ∃ v : timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (b - a),
      ∀ᵐ s ∂timeMeasure (b - a),
        (v.toFun s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z =>
          H1ComplDirichletToLp q (u (a + s))
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  let μ := volume.restrict (Icc a b)
  have hI : Icc a b ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hμ : (timeMeasure T).restrict (Icc a b) = μ :=
    Measure.restrict_restrict_of_subset hI
  have hμle : μ ≤ timeMeasure T := by
    rw [← hμ]
    exact Measure.restrict_le_self
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω₀)) := Lp.SecondCountableTopology
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  have hmeasure : μ.prod (volume.restrict Ω₀) ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono hμle (Measure.restrict_mono hsub le_rfl)
  have hUmem : MemLp U 2 (μ.prod (volume.restrict Ω₀)) := (Lp.memLp U).mono_measure hmeasure
  let P := Lp.curry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hUmem.toLp U)
  have hUP : (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P : ℝ × EuStd → ℝ)
      =ᵐ[μ.prod (volume.restrict Ω₀)] U := by
    rw [show Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P = hUmem.toLp U from
      Lp.uncurry_curry (𝕜 := ℝ) (by norm_num) _]
    exact hUmem.coeFn_toLp
  have hP : ∀ᵐ t ∂μ, (P t : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z =>
      H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [Lp.curry_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hUmem.toLp U),
      Measure.ae_ae_of_ae_prod hUmem.coeFn_toLp,
      (dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u).filter_mono (ae_mono hμle)]
      with t ht hc hu
    exact Filter.EventuallyEq.trans ht (Filter.EventuallyEq.trans hc
      (hu.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))))
  have hsource := exists_local_lp_weak_time_deriv_of_heat_timeH1 hG hT hreg q hCg hequiv
    Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  dsimp only at hsource
  rw [hμ] at hsource
  obtain ⟨R, hR⟩ := hsource
  have hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) p *
        fderiv ℝ φ p (1, 0) ∂μ.prod (volume.restrict Ω₀)) =
      -(∫ p, R p * φ p ∂μ.prod (volume.restrict Ω₀)) := by
    intro φ hφ hφc hφs
    refine (integral_congr_ae ?_).trans (hR φ hφ hφc hφs)
    filter_upwards [hUP] with p hp
    exact congrArg (fun v => v * fderiv ℝ φ p (1, 0)) hp
  obtain ⟨w, hw, _⟩ := exists_timeH1_of_spacetime_weak_deriv_on hab hΩ₀ P R hweak
  have hshift : MeasurePreserving (fun s : ℝ => a + s) (timeMeasure (b - a)) μ := by
    have h := (measurePreserving_add_right volume a).restrict_image_emb
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
    simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm a] using h
  refine ⟨w, ?_⟩
  filter_upwards [hw, hshift.quasiMeasurePreserving.ae hP] with s hs hsP
  rw [← hs]
  exact hsP

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
