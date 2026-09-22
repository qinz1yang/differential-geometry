import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceRegularity
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

theorem exists_local_weak_gradient_equation_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U S : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, S p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      ∀ DS : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
          (fun z => DS k (t, z)) (fun z => S (t, z)) Ω) →
      ∃ R : Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
            Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        ∃ C : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
          (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, U p * fderiv ℝ φ p (1, 0) ∂μ₀.prod (volume.restrict Ω₀)) =
              -∫ p, R p * φ p ∂μ₀.prod (volume.restrict Ω₀)) ∧
          (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
            (fun z => H i j (t, z)) (fun z => K i (t, z)) Ω₀) ∧
          (∀ i j, H i j = H j i) ∧
          (∀ k, C k =ᵐ[μ₀.prod (volume.restrict Ω₀)] fun p => DS k p +
            (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
              fderiv ℝ (fun y => fderiv ℝ (A i j) y (0, EuclideanSpace.single k 1))
                p (0, EuclideanSpace.single j 1) * K i p)) -
            (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
              fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) ∧
          ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, ρ p * K k p * fderiv ℝ φ p (1, 0) ∂μ₀.prod (volume.restrict Ω₀)) =
              (∑ i, ∑ j, ∫ p, A i j p * H k i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
                ∂μ₀.prod (volume.restrict Ω₀)) -
                ∫ p, C k p * φ p ∂μ₀.prod (volume.restrict Ω₀) := by
  intro μ ν ρ A U S K hK hweak μ₀ DS hDS
  obtain ⟨H, hH, _, _⟩ := exists_local_second_weak_derivative_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb U S K hK hweak
  obtain ⟨R, hR⟩ := exists_local_weak_time_deriv_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb U S K hK hweak
  let ν₀ := μ₀.prod (volume.restrict Ω₀)
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hUm : MemLp U 2 ν₀ := (Lp.memLp U).mono_measure hmeasure
  have hKm (i) : MemLp (K i) 2 ν₀ := (Lp.memLp (K i)).mono_measure hmeasure
  have hDSm (i) : MemLp (DS i) 2 ν₀ := (Lp.memLp (DS i)).mono_measure hmeasure
  have hfirst (i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d) (hK i)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hforcing (i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
      (fun z => DS i (t, z)) (fun z => S (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d) (hDS i)] with t ht
    exact ht.restrict hΩ₀ hsub
  have hHsym (i j) : H i j = H j i := by
    apply Lp.ext
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (H i j)).measurable
        (Lp.stronglyMeasurable (H j i)).measurable)).mpr
    filter_upwards [hfirst i, hfirst j, hH i j, hH j i,
      (Lp.memLp (H i j)).prodMk_left (by norm_num),
      (Lp.memLp (H j i)).prodMk_left (by norm_num)] with t hi hj hij hji hmij hmji
    exact Sobolev.ae_eq_of_weak_second_deriv_comm hΩ₀
      (ae_restrict_mem hΩ₀.measurableSet) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      hi hj hij hji (hmij.locallyIntegrable (by norm_num)) (hmji.locallyIntegrable (by norm_num))
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  let O := D.regular ×ˢ W
  let V := Ioo c d ×ˢ Ω₀
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hO : IsOpen O := D.regular_isOpen.prod hW
  have hV : IsOpen V := isOpen_Ioo.prod hΩ₀
  have hΩW : closure Ω ⊆ W := hΩs
  have hVO : V ⊆ O :=
    prod_mono (fun t ht => hreg ⟨(hac.trans ht.1).le, (ht.2.trans hdb).le⟩)
      (hsub.trans (subset_closure.trans hΩW))
  have hbounded {C : ℝ × EuStd → ℝ} (hC : ContDiffOn ℝ (⊤ : ℕ∞) C O) :
      MemLp C ∞ ν₀ := by
    have hm := (hC.continuousOn.mono (prod_mono hreg hΩW)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm.mono_measure hmeasure
  have hdiff {C : ℝ × EuStd → ℝ} (hC : ContDiffOn ℝ (⊤ : ℕ∞) C O) (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ C p v) O :=
    (hC.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ O :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) O :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hspace (i) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ V) :
      (∫ p, U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν₀) =
        -∫ p, K i p * φ p ∂ν₀ :=
    integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv (hUm.locallyIntegrable (by norm_num))
      ((hKm i).locallyIntegrable (by norm_num)) i (hfirst i) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hflux (i j) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ V) :
      (∫ p, K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) =
        -∫ p, H i j p * φ p ∂ν₀ :=
    integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv ((hKm i).locallyIntegrable (by norm_num))
      ((Lp.memLp (H i j)).locallyIntegrable (by norm_num)) j (hH i j) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hsource (i) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ V) :
      (∫ p, S p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν₀) =
        -∫ p, DS i p * φ p ∂ν₀ :=
    integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (((Lp.memLp S).mono_measure hmeasure).locallyIntegrable (by norm_num))
      ((hDSm i).locallyIntegrable (by norm_num)) i (hforcing i) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hbase (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ V) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
          ∫ p, A ij.1 ij.2 p * K ij.1 p * fderiv ℝ φ p (0, EuclideanSpace.single ij.2 1) ∂ν₀) -
          ∫ p, S p * φ p ∂ν₀ := by
    have hw := hweak φ hφ hφc
      (hφs.trans (prod_mono (fun t ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩) hsub))
    have hφsupport : tsupport φ ⊆ Icc c d ×ˢ Ω₀ :=
      hφs.trans (prod_mono Ioo_subset_Icc_self Subset.rfl)
    have hres (v : ℝ × EuStd) (C : ℝ × EuStd → ℝ) :
        (∫ p, C p * fderiv ℝ φ p v ∂ν) = ∫ p, C p * fderiv ℝ φ p v ∂ν₀ := by
      apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p v)
        (fun hs => hp (hφsupport (tsupport_fderiv_apply_subset ℝ v hs))), mul_zero]
    have hresφ : (∫ p, S p * φ p ∂ν) = ∫ p, S p * φ p ∂ν₀ := by
      apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφsupport hs)), mul_zero]
    simp_rw [hres, hresφ] at hw
    simpa only [Fintype.sum_prod_type] using hw
  have hex (k : Fin (Module.finrank ℝ EuN)) :=
    Sobolev.exists_lp_weak_deriv_weighted_divergence
      (μ := ν₀) (p := 2) (Finset.univ : Finset (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)))
      hV (by norm_num) (0, EuclideanSpace.single k 1) (1, 0)
      (fun ij => (0, EuclideanSpace.single ij.2 1)) hUm ((hKm k).locallyIntegrable (by norm_num))
      (Lp.memLp R) (hDSm k) (fun ij _ => hKm ij.1)
      (fun ij _ => (Lp.memLp (H k ij.1)).locallyIntegrable (by norm_num))
      (fun ij _ => Lp.memLp (H ij.1 ij.2)) (hρ.mono hVO)
      (fun ij _ => (hA ij.1 ij.2).mono hVO)
      (fun ij _ => hbounded (hdiff (hA ij.1 ij.2) _))
      (fun ij _ => hbounded (hdiff (hdiff (hA ij.1 ij.2) _) _))
      (hbounded (hdiff hρ _)) (hbounded (hdiff (hdiff hρ _) _))
      (hspace k) hR
      (fun ij _ φ hφ hφc hφs => by rw [hHsym k ij.1]; exact hflux ij.1 k φ hφ hφc hφs)
      (fun ij _ => hflux ij.1 ij.2) (hsource k) hbase
  choose C hC hCweak using hex
  refine ⟨R, H, C, hR, hH, hHsym, ?_, ?_⟩
  · intro k
    simpa only [Fintype.sum_prod_type] using hC k
  · intro k φ hφ hφc hφs
    simpa only [Fintype.sum_prod_type] using hCweak k φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic
