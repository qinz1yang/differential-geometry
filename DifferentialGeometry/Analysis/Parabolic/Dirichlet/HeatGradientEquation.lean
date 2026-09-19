import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
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

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
