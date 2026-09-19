import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceHigherRegularity
import DifferentialGeometry.Analysis.Parabolic.SecondOrderWeakRegularity

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

theorem exists_local_mixed_weak_partial_trees_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∀ F : ℕ → ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ k m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F k (m + 1) (Fin.cons i β) (t, z)) (fun z => F k m β (t, z)) Ω) →
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, F k 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν) =
          -∫ p, F (k + 1) 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∀ L N : ℕ, ∃ P : ℕ → ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
        (P 0 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] U) ∧
        (∀ k ≤ L, ∀ m < N, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω₀) ∧
        ∀ k < L, ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, P k 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, P (k + 1) 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀ := by
  intro μ ν ρ A U K F hK hF hFt hweak μ₀ ν₀
  obtain ⟨P, Q, hP, hPw, _, _⟩ :=
    exists_local_weak_partial_trees_of_all_orders_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K (F 0) hK (hF 0) hweak
  let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hKalign (i) : P 1 (Fin.cons i e) =ᵐ[ν₀] K i := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (P 1 (Fin.cons i e))).measurable
        (Lp.stronglyMeasurable (K i)).measurable)).mpr
    filter_upwards [hPw 0 e i, Measure.ae_ae_of_ae_prod hP,
      ae_restrict_of_ae (s := Icc c d) (hK i),
      (Lp.memLp (P 1 (Fin.cons i e))).prodMk_left (by norm_num),
      ((Lp.memLp (K i)).mono_measure hmeasure).prodMk_left (by norm_num)] with t ht hu hk hm hkLp
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (hasWeakPartialDeriv_congr_ae hΩ₀ i hu ht) (hk.restrict hΩ₀ hsub)
      (hm.locallyIntegrable (by norm_num)) (hkLp.locallyIntegrable (by norm_num))
  have hSm (k m β) := (Lp.memLp (F k m β)).mono_measure hmeasure
  let S := fun k m β => (hSm k m β).toLp (F k m β)
  have hS (k m β) : S k m β =ᵐ[ν₀] F k m β := (hSm k m β).coeFn_toLp
  have hSw (k m β i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
      (fun z => S k (m + 1) (Fin.cons i β) (t, z)) (fun z => S k m β (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d) (hF k m β i),
      Measure.ae_ae_of_ae_prod (hS k m β),
      Measure.ae_ae_of_ae_prod (hS k (m + 1) (Fin.cons i β))] with t ht hu hv
    exact (ht.restrict hΩ₀ hsub).congr_ae (Filter.EventuallyEq.symm hu) (Filter.EventuallyEq.symm hv)
  have hrestrict (φ : ℝ × EuStd → ℝ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀)
      (B : ℝ × EuStd → ℝ) : (∫ p, B p * φ p ∂ν) = ∫ p, B p * φ p ∂ν₀ := by
    apply integral_eq_integral_restrict_prod_of_support_subset hΩ₀.measurableSet hsub
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (f := φ)
      (fun hs => hp ((Set.prod_mono Ioo_subset_Icc_self Subset.rfl) (hφs hs))), mul_zero]
  have hrestrictD (φ : ℝ × EuStd → ℝ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀)
      (v : ℝ × EuStd) (B : ℝ × EuStd → ℝ) :
      (∫ p, B p * fderiv ℝ φ p v ∂ν) = ∫ p, B p * fderiv ℝ φ p v ∂ν₀ :=
    hrestrict _ ((tsupport_fderiv_apply_subset ℝ v).trans hφs) B
  have hregion : Ioo c d ×ˢ Ω₀ ⊆ Ioo a b ×ˢ Ω :=
    prod_mono (fun t ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩) hsub
  have hSt (k) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ interior (Icc c d) ×ˢ Ω₀) :
      (∫ p, S k 0 e p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, S (k + 1) 0 e p * φ p ∂ν₀ := by
    rw [interior_Icc] at hφs
    have h := hFt k φ hφ hφc (hφs.trans hregion)
    rw [hrestrictD φ hφs, hrestrict φ hφs] at h
    calc
      _ = ∫ p, F k 0 e p * fderiv ℝ φ p (1, 0) ∂ν₀ := by
        apply integral_congr_ae
        filter_upwards [hS k 0 e] with p hp
        rw [hp]
      _ = -∫ p, F (k + 1) 0 e p * φ p ∂ν₀ := h
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hS (k + 1) 0 e] with p hp
        rw [hp]
  have hweak₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ interior (Icc c d) ×ˢ Ω₀) :
      (∫ p, ρ p * P 0 e p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        (∑ i, ∑ j, ∫ p, A i j p * P 1 (Fin.cons i e) p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) - ∫ p, S 0 0 e p * φ p ∂ν₀ := by
    rw [interior_Icc] at hφs
    have h := hweak φ hφ hφc (hφs.trans hregion)
    simp_rw [hrestrictD φ hφs, hrestrict φ hφs] at h
    have hleft : (∫ p, ρ p * P 0 e p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        ∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀ := by
      apply integral_congr_ae
      filter_upwards [hP] with p hp
      rw [hp]
    rw [hleft, h]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [hKalign i] with p hp
      rw [hp]
    · apply integral_congr_ae
      filter_upwards [hS 0 0 e] with p hp
      rw [hp]
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ W) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hρne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ W) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp.2))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ W) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  intro L N
  obtain ⟨T, hT, hTw, hTt⟩ := exists_lp_mixed_weak_partial_trees_of_weighted_divergence
    (μ := μ) isCompact_Icc D.regular_isOpen ((Icc_subset_Icc hac.le hdb.le).trans hreg)
    hW hΩ₀ (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
    (hΩ₀Ω.trans (subset_closure.trans hΩs)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (1 : ℝ)
    P S hPw hSw hSt ρ A hρ hρne hA hweak₀ L N
  refine ⟨T, ?_, hTw, ?_⟩
  · rw [hT]
    exact hP
  · simpa only [interior_Icc] using hTt

theorem exists_local_mixed_weak_partial_trees_of_homogeneous_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) (hcd : c < d) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν)) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∀ L N : ℕ, ∃ P : ℕ → ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
        (P 0 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] U) ∧
        (∀ k ≤ L, ∀ m < N, ∀ β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => P k (m + 1) (Fin.cons i β) (t, z)) (fun z => P k m β (t, z)) Ω₀) ∧
        ∀ k < L, ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, P k 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, P (k + 1) 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀ := by
  intro μ ν ρ A U K hK hweak μ₀ ν₀
  let F : ℕ → ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν := fun _ _ _ => 0
  have hzero : (0 : Lp ℝ 2 ν) =ᵐ[ν] (fun _ => 0) := Lp.coeFn_zero ℝ 2 ν
  have hF (k m β i) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => F k (m + 1) (Fin.cons i β) (t, z)) (fun z => F k m β (t, z)) Ω := by
    filter_upwards [Measure.ae_ae_of_ae_prod hzero] with t ht
    have hz : DeGiorgi.HasWeakPartialDeriv i (fun _ => 0) (fun _ => 0) Ω := by
      intro φ hφ hφc hφs
      simp
    exact hz.congr_ae (Filter.EventuallyEq.symm ht) (Filter.EventuallyEq.symm ht)
  have hzeroIntegral (B : ℝ × EuStd → ℝ) : (∫ p, (0 : Lp ℝ 2 ν) p * B p ∂ν) = 0 := by
    trans ∫ p, (0 : ℝ) ∂ν
    · apply integral_congr_ae
      filter_upwards [hzero] with p hp
      rw [hp, zero_mul]
    · exact integral_zero _ _
  apply exists_local_mixed_weak_partial_trees_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF
  · intro k φ hφ hφc hφs
    change (∫ p, (0 : Lp ℝ 2 ν) p * fderiv ℝ φ p (1, 0) ∂ν) =
      -∫ p, (0 : Lp ℝ 2 ν) p * φ p ∂ν
    rw [hzeroIntegral, hzeroIntegral, neg_zero]
  · intro φ hφ hφc hφs
    change (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
      (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
        ∫ p, (0 : Lp ℝ 2 ν) p * φ p ∂ν
    rw [hzeroIntegral, sub_zero]
    exact hweak φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic
