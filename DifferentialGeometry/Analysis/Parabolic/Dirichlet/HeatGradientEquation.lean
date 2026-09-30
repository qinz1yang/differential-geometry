import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Parabolic.WeakEquationDensity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

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

theorem exists_lp_weak_gradient_commutator_of_heat_timeH1
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
    let ν := μ.prod (volume.restrict Ω₀)
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let L := fun p => ρ p * ((1 / 2 : ℝ) *
      traceTimeDerivMetric (I := I_hs) g p.1 (x p.2) * U p + F p)
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, (A i j p * H k i p +
            fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
          (∫ p, L p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν) +
          ∫ p, (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0) * U p) * φ p ∂ν := by
  intro μ ν x ρ A U V F L
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨H, hH, _⟩ := exists_local_second_weak_derivative_of_heat_timeH1 hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀Ω ha hb u f w hwmass hwderiv
  obtain ⟨R, hR⟩ := exists_local_lp_weak_time_deriv_of_heat_timeH1 hG hT hreg q
    hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  have hHsym (i k) : H i k = H k i := by
    apply Lp.ext
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (H i k)).measurable
        (Lp.stronglyMeasurable (H k i)).measurable)).mpr
    filter_upwards [hH i k, hH k i, (Lp.memLp (H i k)).prodMk_left (by norm_num),
      (Lp.memLp (H k i)).prodMk_left (by norm_num)] with t hik hki hikLp hkiLp
    have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
    have hi := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t))
    have hk := DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t))
    exact Sobolev.ae_eq_of_weak_second_deriv_comm hΩ₀
      (ae_restrict_mem hΩ₀.measurableSet) (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)
      hi hk hik hki (hikLp.locallyIntegrable (by norm_num)) (hkiLp.locallyIntegrable (by norm_num))
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
    have hc := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i k, hc] with t ht hct
    have he : (fun z => V i (t, z)) =ᵐ[volume.restrict Ω₀]
        (fun z => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z) := by
      exact ae_restrict_of_ae_restrict_of_subset hsub hct
    rw [← hHsym i k]
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ k he.symm ht
  have hspace : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, U p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, V k p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      hU (hV k) k (hfirst k) ψ hψ hψc
      (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hflux (ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) :
      ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, H k ij.1 p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hV ij.1) ((Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num)) k (hsecond ij.1)
      ψ hψ hψc (hψs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hJ : Ioo a b ⊆ D.regular := by
    intro t ht
    exact hreg ⟨ha.le.trans ht.1.le, ht.2.le.trans hb.le⟩
  have hΩs' := hsub.trans (subset_closure.trans hΩs)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (Ioo a b ×ˢ Ω₀) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG hJ α).mono
      (Set.prod_mono Subset.rfl (hΩs'.trans (image_mono interior_subset)))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (Ioo a b ×ˢ Ω₀) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG hJ α hΩs' i j
  have hbase : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, ρ p * U p * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN), ∫ p,
          A ij.1 ij.2 p * V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single ij.2 1) ∂ν) -
          ∫ p, L p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hb := integral_spacetime_test_divergence_restrict_of_heat_timeH1 q g hG hT hreg hCg hequiv
      Cv hCv0 hCvtop hvol u f w hwmass hwderiv α hΩ hΩc hΩs hΩ₀.measurableSet hsub
      hψ hψc (hψs.trans (prod_mono (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩) hsub))
      (hψs.trans (prod_mono Ioo_subset_Icc_self Subset.rfl))
    simpa only [Fintype.sum_prod_type] using hb
  have hcomm := Sobolev.integral_weak_deriv_weighted_divergence Finset.univ
    (isOpen_Ioo.prod hΩ₀) (0, EuclideanSpace.single k 1) (1, 0)
    (fun ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN) =>
      (0, EuclideanSpace.single ij.2 1)) hU (hV k)
    ((Lp.memLp R).locallyIntegrable (by norm_num))
    (fun ij _ => hV ij.1) (fun ij _ => (Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num))
    hρ (fun ij _ => hA ij.1 ij.2) hspace hR (fun ij _ => hflux ij) hbase hφ hφc hφs
  simpa only [Fintype.sum_prod_type] using hcomm

theorem exists_lp_weak_gradient_equation_of_heat_timeH1
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
    let ν := μ.prod (volume.restrict Ω₀)
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let c := fun p => ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2))
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω₀) →
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ Q : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, Q k =ᵐ[ν] fun p =>
        (c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
          (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)) +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (A i j) z (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * V i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, Q k p * φ p ∂ν := by
  intro μ ν x ρ A U V F c Df hDf
  let L := fun p => ρ p * ((1 / 2 : ℝ) *
    traceTimeDerivMetric (I := I_hs) g p.1 (x p.2) * U p + F p)
  classical
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  obtain ⟨R, H, hR, hH, hHsym, _⟩ := exists_lp_weak_gradient_commutator_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb
    u f w hwmass hwderiv
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hF : MemLp F 2 ν := (Lp.memLp F).mono_measure hmeasure
  let O := D.regular ×ˢ Ω
  let S := Ioo a b ×ˢ Ω₀
  have hO : IsOpen O := D.regular_isOpen.prod hΩ
  have hS : IsOpen S := isOpen_Ioo.prod hΩ₀
  have hJ : Ioo a b ⊆ D.regular := fun t ht => hreg ⟨ha.le.trans ht.1.le, ht.2.le.trans hb.le⟩
  have hSO : S ⊆ O := prod_mono hJ hsub
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ O :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) O :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α
      (subset_closure.trans hΩs) i j
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) c O := by
    exact hρ.mul (contDiffOn_const.mul (traceTimeDerivMetric_comp_chartInverse_contDiffOn
      (G := G) hG Subset.rfl α (subset_closure.trans hΩs)))
  have hdiff {C : ℝ × EuStd → ℝ} (hC : ContDiffOn ℝ (⊤ : ℕ∞) C O) (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ C p v) O :=
    (hC.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hlift {C : ℝ × EuStd → ℝ} (hC : ContDiffOn ℝ (⊤ : ℕ∞) C O) : MemLp C ∞ ν := by
    have hb := (hC.continuousOn.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hfirst (i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => V i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [(hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α
      hΩ hΩc hΩs (timeMeasure T) i u).filter_mono (ae_mono Measure.restrict_le_self)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hsecond (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => V i (t, z)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc a b)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i j, hc] with t ht hct
    have he : (fun z => V i (t, z)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      ae_restrict_of_ae_restrict_of_subset hsub hct
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  have hspace (i) : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S → (∫ p, U p * fderiv ℝ ψ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, V i p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hU.locallyIntegrable (by norm_num)) ((hV i).locallyIntegrable (by norm_num)) i
      (hfirst i) ψ hψ hψc (hψs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hflux (i j) : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S → (∫ p, V i p * fderiv ℝ ψ p (0, EuclideanSpace.single j 1) ∂ν) =
        -∫ p, H i j p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((hV i).locallyIntegrable (by norm_num)) ((Lp.memLp (H i j)).locallyIntegrable (by norm_num)) j
      (hsecond i j) ψ hψ hψc (hψs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hforcing (i) : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S → (∫ p, F p * fderiv ℝ ψ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, Df i p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    exact Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hF.locallyIntegrable (by norm_num)) ((Lp.memLp (Df i)).locallyIntegrable (by norm_num)) i
      (hDf i) ψ hψ hψc (hψs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hbase : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S → (∫ p, ρ p * U p * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN), ∫ p,
          A ij.1 ij.2 p * V ij.1 p * fderiv ℝ ψ p (0, EuclideanSpace.single ij.2 1) ∂ν) -
          ∫ p, L p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hb := integral_spacetime_test_divergence_restrict_of_heat_timeH1 q g hG hT hreg hCg hequiv
      Cv hCv0 hCvtop hvol u f w hwmass hwderiv α hΩ hΩc hΩs hΩ₀.measurableSet hsub
      hψ hψc (hψs.trans (prod_mono (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩) hsub))
      (hψs.trans (prod_mono Ioo_subset_Icc_self Subset.rfl))
    simpa only [Fintype.sum_prod_type] using hb
  let DL := fun k p => c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
    (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)
  have hDL (k) : MemLp (DL k) 2 ν :=
    (((hlift hc).fun_mul (r := 2) (hV k)).add
      ((hlift (hdiff hc _)).fun_mul (r := 2) hU)).add
        (((hlift hρ).fun_mul (r := 2) (Lp.memLp (Df k))).add
          ((hlift (hdiff hρ _)).fun_mul (r := 2) hF))
  have hLweak (k) : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S → (∫ p, L p * fderiv ℝ ψ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, DL k p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    let v : ℝ × EuStd := (0, EuclideanSpace.single k 1)
    have hleft := Sobolev.integral_weak_product_deriv hS v
      (hU.locallyIntegrable (by norm_num)) ((hV k).locallyIntegrable (by norm_num))
      (hc.mono hSO) (hspace k) hψ hψc hψs
    have hright := Sobolev.integral_weak_product_deriv hS v
      (hF.locallyIntegrable (by norm_num)) ((Lp.memLp (Df k)).locallyIntegrable (by norm_num))
      (hρ.mono hSO) (hforcing k) hψ hψc hψs
    have hint (Y : ℝ × EuStd → ℝ) (hY : MemLp Y 2 ν) : Integrable (fun p => Y p * ψ p) ν :=
      (hY.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hψ.continuous hψc
    have hintd (Y : ℝ × EuStd → ℝ) (hY : MemLp Y 2 ν) :
        Integrable (fun p => Y p * fderiv ℝ ψ p v) ν :=
      (hY.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const) (hψc.fderiv_apply ℝ v)
    have hLsplit : (∫ p, L p * fderiv ℝ ψ p v ∂ν) =
        (∫ p, c p * U p * fderiv ℝ ψ p v ∂ν) +
          ∫ p, ρ p * F p * fderiv ℝ ψ p v ∂ν := by
      rw [← integral_add (hintd _ ((hlift hc).fun_mul (r := 2) hU))
        (hintd _ ((hlift hρ).fun_mul (r := 2) hF))]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by dsimp only [L, c]; ring
    have hDLsplit : (∫ p, DL k p * ψ p ∂ν) =
        (∫ p, (c p * V k p + fderiv ℝ c p v * U p) * ψ p ∂ν) +
          ∫ p, (ρ p * Df k p + fderiv ℝ ρ p v * F p) * ψ p ∂ν := by
      calc
        _ = ∫ p, (c p * V k p + fderiv ℝ c p v * U p) * ψ p +
            (ρ p * Df k p + fderiv ℝ ρ p v * F p) * ψ p ∂ν := by
          apply integral_congr_ae
          exact Eventually.of_forall fun p => add_mul _ _ _
        _ = _ := integral_add
          (hint _ (((hlift hc).fun_mul (r := 2) (hV k)).add
            ((hlift (hdiff hc v)).fun_mul (r := 2) hU)))
          (hint _ (((hlift hρ).fun_mul (r := 2) (Lp.memLp (Df k))).add
            ((hlift (hdiff hρ v)).fun_mul (r := 2) hF)))
    rw [hLsplit, hDLsplit]
    linarith
  have hex (k : Fin (Module.finrank ℝ EuN)) :=
    Sobolev.exists_lp_weak_deriv_weighted_divergence Finset.univ hS (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (0, EuclideanSpace.single k 1) (1, 0)
      (fun ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN) =>
        (0, EuclideanSpace.single ij.2 1)) hU ((hV k).locallyIntegrable (by norm_num))
      (Lp.memLp R) (hDL k) (fun ij _ => hV ij.1)
      (fun ij _ => (Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num))
      (fun ij _ => Lp.memLp (H ij.1 ij.2)) (hρ.mono hSO) (fun ij _ => (hA ij.1 ij.2).mono hSO)
      (fun ij _ => hlift (hdiff (hA ij.1 ij.2) _))
      (fun ij _ => hlift (hdiff (hdiff (hA ij.1 ij.2) _) _))
      (hlift (hdiff hρ _)) (hlift (hdiff (hdiff hρ _) _)) (hspace k) hR
      (fun ij _ => by simpa only [hHsym] using hflux ij.1 k)
      (fun ij _ => hflux ij.1 ij.2) (hLweak k) hbase
  choose Q hQval hQweak using hex
  refine ⟨R, H, Q, hR, hH, hHsym, ?_, ?_⟩
  · intro k
    simpa only [Fintype.sum_prod_type] using hQval k
  · intro k φ hφ hφc hφs
    simpa only [Fintype.sum_prod_type] using hQweak k φ hφ hφc hφs


theorem exists_lp_weak_gradient_equation_fixed_density_of_heat_timeH1
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
    let ν := μ.prod (volume.restrict Ω₀)
    let x := fun z : EuStd => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let σ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    let c := fun p => ρ p * ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) g p.1 (x p.2))
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω₀) →
    ∃ R : Lp ℝ 2 ν,
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ Q : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, Q k =ᵐ[ν] fun p =>
        (c p * V k p + fderiv ℝ c p (0, EuclideanSpace.single k 1) * U p +
          (ρ p * Df k p + fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * F p)) +
        (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun z => fderiv ℝ (A i j) z (0, EuclideanSpace.single k 1)) p
            (0, EuclideanSpace.single j 1) * V i p)) -
        (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
          fderiv ℝ (fun z => fderiv ℝ ρ z (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, Q k p * φ p ∂ν) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, σ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * Q k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * V k p)) * φ p ∂ν := by
  intro μ ν x ρ σ r A U V F c Df hDf
  obtain ⟨R, H, Q, hR, hH, hHsym, hQval, hQ⟩ :=
    exists_lp_weak_gradient_equation_of_heat_timeH1 hG hT hreg q hCg hequiv Cv hCv0 hCvtop
      hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv Df hDf
  refine ⟨R, H, Q, hR, hH, hHsym, hQval, hQ, ?_⟩
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (k) : MemLp (V k) 2 ν := (Lp.memLp (V k)).mono_measure hmeasure
  have hσmem : MemLp σ ∞ ν := by
    have hs : MemLp (densityOnEuclid (I := I_hs) q α) ∞ (volume.restrict Ω₀) :=
      ((densityOnEuclid_contDiffOn q α).continuousOn.mono (hΩ₀Ω.trans hchart)).memLp_top_of_subset_isCompact
        hΩ₀c hΩ₀.measurableSet subset_closure
    exact hs.comp_snd μ
  have hJ : Ioo a b ⊆ D.regular :=
    fun t ht => hreg ⟨ha.le.trans ht.1.le, ht.2.le.trans hb.le⟩
  intro k φ hφ hφc hφs
  exact integral_fixed_density_eq_of_weighted_identity hG q α isOpen_Ioo hJ hΩ₀
    (hsub.trans hchart) ((hσmem.fun_mul (r := 2) (hV k)).locallyIntegrable (by norm_num))
    ((Lp.memLp (Q k)).locallyIntegrable (by norm_num))
    (fun ψ => ∑ i, ∑ j, ∫ p, A i j p * H k i p *
      fderiv ℝ ψ p (0, EuclideanSpace.single j 1) ∂ν) (hQ k) hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
