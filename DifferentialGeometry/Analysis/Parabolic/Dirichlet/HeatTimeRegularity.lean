import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatInteriorRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatWeakEquationChart
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeProduct

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
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let ν := μ.prod (volume.restrict Ω₀)
  let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
  let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
  let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
  let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (((chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
  let τ := fun p : ℝ × EuStd => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2)
  let L := fun p => ρ p * (τ p * U p + F p)
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
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
    ((((Lp.memLp U).mono_measure hmeasure).mul' (r := 2) hτ).add
      ((Lp.memLp F).mono_measure hmeasure)).mul' (r := 2) hρ
  obtain ⟨B, hB⟩ := exists_local_lp_divergence_of_heat_timeH1 hG hT hreg q hCg hequiv
    Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  let R := fun p => B p + L p
  have hR : MemLp R 2 ν := (Lp.memLp B).add hL
  refine ⟨hR.toLp R, ?_⟩
  intro φ hφ hφc hφs
  have hφouter : tsupport φ ⊆ Ioo (0 : ℝ) T ×ˢ Ω :=
    hφs.trans (prod_mono (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩) hsub)
  have hbase := integral_spacetime_test_divergence_of_heat_timeH1 q g hG hT hreg hCg hequiv
    Cv hCv0 hCvtop hvol u f w hwmass hwderiv α hΩ hΩc hΩs hφ hφc hφouter
  have hres (v : ℝ × EuStd) (C : ℝ × EuStd → ℝ) :
      (∫ p, C p * fderiv ℝ φ p v ∂(timeMeasure T).prod (volume.restrict Ω)) =
        ∫ p, C p * fderiv ℝ φ p v ∂ν := by
    apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p v) (fun hs =>
      hp ⟨⟨(hφs (tsupport_fderiv_apply_subset ℝ v hs)).1.1.le,
        (hφs (tsupport_fderiv_apply_subset ℝ v hs)).1.2.le⟩,
          (hφs (tsupport_fderiv_apply_subset ℝ v hs)).2⟩), mul_zero]
  have hresφ : (∫ p, L p * φ p ∂(timeMeasure T).prod (volume.restrict Ω)) =
      ∫ p, L p * φ p ∂ν := by
    apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hs =>
      hp ⟨⟨(hφs hs).1.1.le, (hφs hs).1.2.le⟩, (hφs hs).2⟩), mul_zero]
  change (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂(timeMeasure T).prod (volume.restrict Ω)) =
    (∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
      ∂(timeMeasure T).prod (volume.restrict Ω)) -
      ∫ p, L p * φ p ∂(timeMeasure T).prod (volume.restrict Ω) at hbase
  simp_rw [hres, hresφ] at hbase
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
