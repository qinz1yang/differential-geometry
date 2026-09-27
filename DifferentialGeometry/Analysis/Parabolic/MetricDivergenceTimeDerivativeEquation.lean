import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceHigherRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

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

theorem exists_local_weak_time_derivative_equation_of_metric_divergence_equation
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
      ∀ F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ m < 1, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∀ Ft : Lp ℝ 2 ν₀,
        (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, F 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, Ft p * φ p ∂ν₀) →
        ∃ (R : Lp ℝ 2 ν₀) (DR : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν₀)
          (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν₀)
          (C : Lp ℝ 2 ν₀),
          (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, R p * φ p ∂ν₀) ∧
          (∀ i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
            (fun z => DR i (t, z)) (fun z => R (t, z)) Ω₀) ∧
          (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
            (fun z => H i j (t, z)) (fun z => K i (t, z)) Ω₀) ∧
          (C =ᵐ[ν₀] fun p => Ft p +
            (∑ i, ∑ j, (fderiv ℝ (A i j) p (1, 0) * H i j p +
              fderiv ℝ (fun y => fderiv ℝ (A i j) y (1, 0)) p
                (0, EuclideanSpace.single j 1) * K i p)) -
            (fderiv ℝ ρ p (1, 0) * R p +
              fderiv ℝ (fun y => fderiv ℝ ρ y (1, 0)) p (1, 0) * U p)) ∧
          ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, ρ p * R p * fderiv ℝ φ p (1, 0) ∂ν₀) =
              (∑ i, ∑ j, ∫ p, A i j p * DR i p *
                fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) -∫ p, C p * φ p ∂ν₀ := by
  intro μ ν ρ A U K F hK hF hweak μ₀ ν₀ Ft hFt
  obtain ⟨P, Q, hP, hPweak, hQweak, hQtime⟩ :=
    exists_local_weak_partial_trees_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd 1 U K F hK hF hweak
  let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
  let S := F 0 e
  let V := fun i => P 1 (Fin.cons i e)
  let H := fun i j => P 2 (Fin.cons j (Fin.cons i e))
  let R := Q 0 e
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : V i =ᵐ[ν₀] K i := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (V i)).measurable
        (Lp.stronglyMeasurable (K i)).measurable)).mpr
    filter_upwards [hPweak 0 (by omega) e i, Measure.ae_ae_of_ae_prod hP,
      ae_restrict_of_ae (s := Icc c d) (hK i),
      (Lp.memLp (V i)).prodMk_left (by norm_num),
      ((Lp.memLp (K i)).mono_measure hmeasure).prodMk_left (by norm_num)] with t ht hu hk hm hkLp
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (hasWeakPartialDeriv_congr_ae hΩ₀ i hu ht) (hk.restrict hΩ₀ hsub)
      (hm.locallyIntegrable (by norm_num)) (hkLp.locallyIntegrable (by norm_num))
  have hHV (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => V i (t, z)) Ω₀ :=
    hPweak 1 (by omega) (Fin.cons i e) j
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hΩW : closure Ω ⊆ W := hΩs
  have hbounded (C : ℝ × EuStd → ℝ) (hC : ContinuousOn C (D.regular ×ˢ W)) :
      MemLp C ∞ ν₀ := by
    have hm := (hC.mono (prod_mono hreg hΩW)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm.mono_measure hmeasure
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ W) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ W) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hregion : Ioo c d ×ˢ Ω₀ ⊆ D.regular ×ˢ W :=
    prod_mono (fun t ht => hreg ⟨(hac.trans ht.1).le, (ht.2.trans hdb).le⟩)
      (hsub.trans (subset_closure.trans hΩW))
  have hweak₀ (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        (∑ i, ∑ j, ∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) -
          ∫ p, S p * φ p ∂ν₀ := by
    have hbase := hweak φ hφ hφc
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
    dsimp only [S, e] at hresφ
    simp_rw [hres, hresφ] at hbase
    refine hbase.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hV i] with p hp
    rw [hp]
  have hroot (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, P 0 e p * fderiv ℝ φ p (1, 0) ∂ν₀) = -∫ p, Q 0 e p * φ p ∂ν₀ := by
    refine (integral_congr_ae ?_).trans (hQtime φ hφ hφc hφs)
    filter_upwards [hP] with p hp
    rw [hp]
  have htime := integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
    1 (1 : ℝ) (fun m β p => P m β p) (fun m β p => Q m β p)
    (fun m _ β => (Lp.memLp (P m β)).locallyIntegrable (by norm_num))
    (fun m _ β => (Lp.memLp (Q m β)).locallyIntegrable (by norm_num))
    (fun m hm β i => hPweak m (by omega) β i) hQweak hroot
  let DR := fun i => Q 1 (Fin.cons i e)
  have hdiff {B : ℝ × EuStd → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (D.regular ×ˢ W))
      (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ B p v) (D.regular ×ˢ W) :=
    (hB.fderiv_of_isOpen (D.regular_isOpen.prod hW) (by simp)).clm_apply contDiffOn_const
  have hdiv (i j) (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) =
        -∫ p, H i j p * φ p ∂ν₀ :=
    integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp (V i)).locallyIntegrable (by norm_num))
      ((Lp.memLp (H i j)).locallyIntegrable (by norm_num)) j (hHV i j) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
  have hbase (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
          ∫ p, A ij.1 ij.2 p * V ij.1 p * fderiv ℝ φ p (0, EuclideanSpace.single ij.2 1) ∂ν₀) -
          ∫ p, S p * φ p ∂ν₀ := by
    simpa only [Fintype.sum_prod_type] using hweak₀ φ hφ hφc hφs
  obtain ⟨C, hC, hCweak⟩ := Sobolev.exists_lp_weak_deriv_weighted_divergence
    (μ := ν₀) (p := 2)
    (Finset.univ : Finset (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)))
    (isOpen_Ioo.prod hΩ₀) (by norm_num) (1, 0) (1, 0)
    (fun ij => (0, EuclideanSpace.single ij.2 1))
    ((Lp.memLp U).mono_measure hmeasure) ((Lp.memLp R).locallyIntegrable (by norm_num))
    (Lp.memLp R) (Lp.memLp Ft) (fun ij _ => Lp.memLp (V ij.1))
    (fun ij _ => (Lp.memLp (DR ij.1)).locallyIntegrable (by norm_num))
    (fun ij _ => Lp.memLp (H ij.1 ij.2)) (hρ.mono hregion)
    (fun ij _ => (hA ij.1 ij.2).mono hregion)
    (fun ij _ => hbounded _ (hdiff (hA ij.1 ij.2) _).continuousOn)
    (fun ij _ => hbounded _ (hdiff (hdiff (hA ij.1 ij.2) _) _).continuousOn)
    (hbounded _ (hdiff hρ _).continuousOn) (hbounded _ (hdiff (hdiff hρ _) _).continuousOn)
    hQtime hQtime (fun ij _ => htime 1 le_rfl (Fin.cons ij.1 e))
    (fun ij _ => hdiv ij.1 ij.2) hFt hbase
  refine ⟨R, DR, H, C, hQtime, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hQweak 0 (by omega) e i
  · intro i j
    filter_upwards [hHV i j, Measure.ae_ae_of_ae_prod (hV i)] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j he ht
  · filter_upwards [hC, ae_all_iff.mpr hV] with p hp hv
    simpa only [Fintype.sum_prod_type, hv] using hp
  · intro φ hφ hφc hφs
    simpa only [Fintype.sum_prod_type] using hCweak φ hφ hφc hφs

theorem exists_local_weak_partial_trees_of_time_derivative_equation_of_metric_divergence_equation
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
      ∀ F : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => F (m + 1) (Fin.cons i β) (t, z)) (fun z => F m β (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, F 0 (fun i => Fin.elim0 i) p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      let ν₀ := μ₀.prod (volume.restrict Ω₀)
      ∀ Ft : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
        (∀ m β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
          (fun z => Ft (m + 1) (Fin.cons i β) (t, z)) (fun z => Ft m β (t, z)) Ω₀) →
        (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, F 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
            -∫ p, Ft 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀) →
        ∃ P Q C : ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → Lp ℝ 2 ν₀,
          (P 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] U) ∧
          (∀ m β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
            (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω₀) ∧
          (∀ m β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
            (fun z => Q (m + 1) (Fin.cons i β) (t, z)) (fun z => Q m β (t, z)) Ω₀) ∧
          (∀ m β i, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
            (fun z => C (m + 1) (Fin.cons i β) (t, z)) (fun z => C m β (t, z)) Ω₀) ∧
          (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν₀) =
              -∫ p, Q 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀) ∧
          (C 0 (fun i => Fin.elim0 i) =ᵐ[ν₀] fun p => Ft 0 (fun i => Fin.elim0 i) p +
            (∑ i, ∑ j, (fderiv ℝ (A i j) p (1, 0) *
              P 2 (Fin.cons j (Fin.cons i (fun l => Fin.elim0 l))) p +
              fderiv ℝ (fun y => fderiv ℝ (A i j) y (1, 0)) p
                (0, EuclideanSpace.single j 1) * P 1 (Fin.cons i (fun l => Fin.elim0 l)) p)) -
            (fderiv ℝ ρ p (1, 0) * Q 0 (fun i => Fin.elim0 i) p +
              fderiv ℝ (fun y => fderiv ℝ ρ y (1, 0)) p (1, 0) * P 0 (fun i => Fin.elim0 i) p)) ∧
          ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
            (∫ p, ρ p * Q 0 (fun i => Fin.elim0 i) p * fderiv ℝ φ p (1, 0) ∂ν₀) =
              (∑ i, ∑ j, ∫ p, A i j p * Q 1 (Fin.cons i (fun l => Fin.elim0 l)) p *
                fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν₀) -
                  ∫ p, C 0 (fun i => Fin.elim0 i) p * φ p ∂ν₀ := by
  intro μ ν ρ A U K F hK hF hweak μ₀ ν₀ Ft hFtweak hFt
  obtain ⟨P, Q, hP, hPweak, hQweak, hQtime⟩ :=
    exists_local_weak_partial_trees_of_all_orders_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK hF hweak
  let e : Fin 0 → Fin (Module.finrank ℝ EuN) := fun i => Fin.elim0 i
  obtain ⟨R, DR, H, C, hR, hDR, hH, hC, hCweak⟩ :=
    exists_local_weak_time_derivative_equation_of_metric_divergence_equation
      hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb hcd U K F hK
      (fun m _ β i => hF m β i) hweak (Ft 0 e) hFt
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hKalign (i) : P 1 (Fin.cons i e) =ᵐ[ν₀] K i := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (P 1 (Fin.cons i e))).measurable
        (Lp.stronglyMeasurable (K i)).measurable)).mpr
    filter_upwards [hPweak 0 e i, Measure.ae_ae_of_ae_prod hP,
      ae_restrict_of_ae (s := Icc c d) (hK i),
      (Lp.memLp (P 1 (Fin.cons i e))).prodMk_left (by norm_num),
      ((Lp.memLp (K i)).mono_measure hmeasure).prodMk_left (by norm_num)] with t ht hu hk hm hkLp
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (hasWeakPartialDeriv_congr_ae hΩ₀ i hu ht) (hk.restrict hΩ₀ hsub)
      (hm.locallyIntegrable (by norm_num)) (hkLp.locallyIntegrable (by norm_num))
  have hHalign (i j) : P 2 (Fin.cons j (Fin.cons i e)) = H i j := by
    apply Lp.ext_curry
    filter_upwards [hPweak 1 (Fin.cons i e) j,
      Measure.ae_ae_of_ae_prod (hKalign i), hH i j,
      (Lp.memLp (P 2 (Fin.cons j (Fin.cons i e)))).prodMk_left (by norm_num),
      (Lp.memLp (H i j)).prodMk_left (by norm_num)] with t ht hk hh hm hhm
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀
      (hasWeakPartialDeriv_congr_ae hΩ₀ j hk ht) hh
      (hm.locallyIntegrable (by norm_num)) (hhm.locallyIntegrable (by norm_num))
  have hmem : ∀ᵐ p ∂ν₀, p ∈ Ioo c d ×ˢ Ω₀ := by
    have htime : μ₀ = volume.restrict (Ioo c d) := by
      change (volume.restrict (Icc a b)).restrict (Icc c d) = volume.restrict (Ioo c d)
      rw [Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (Icc_subset_Icc hac.le hdb.le)]
      exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    change ∀ᵐ p ∂μ₀.prod (volume.restrict Ω₀), p ∈ Ioo c d ×ˢ Ω₀
    rw [htime]
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod hΩ₀.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (ae_restrict_mem hΩ₀.measurableSet).mono fun z hz => ⟨ht, hz⟩
  have hQalign : Q 0 e = R := Sobolev.lp_eq_of_weak_deriv_integral
    (isOpen_Ioo.prod hΩ₀) hmem (by norm_num) (1, 0) hQtime hR
  have hDRalign (i) : Q 1 (Fin.cons i e) = DR i := by
    apply Lp.ext_curry
    filter_upwards [hQweak 0 e i, hDR i,
      (Lp.memLp (Q 1 (Fin.cons i e))).prodMk_left (by norm_num),
      (Lp.memLp (DR i)).prodMk_left (by norm_num)] with t ht hd hm hdm
    rw [hQalign] at ht
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ₀ ht hd
      (hm.locallyIntegrable (by norm_num)) (hdm.locallyIntegrable (by norm_num))
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ W) :=
    (densityOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ W) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hdiff {B : ℝ × EuStd → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (D.regular ×ˢ W))
      (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ B p v) (D.regular ×ˢ W) :=
    (hB.fderiv_of_isOpen (D.regular_isOpen.prod hW) (by simp)).clm_apply contDiffOn_const
  let Idx := Unit ⊕ (Bool ⊕ ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN))))
  let B : Idx → ℝ × EuStd → ℝ :=
    Sum.elim (fun _ _ => 1)
      (Sum.elim (fun b p => if b then -fderiv ℝ ρ p (1, 0)
        else -fderiv ℝ (fun y => fderiv ℝ ρ y (1, 0)) p (1, 0))
        (Sum.elim (fun ij p => fderiv ℝ (A ij.1 ij.2) p (1, 0))
          (fun ij p => fderiv ℝ (fun y => fderiv ℝ (A ij.1 ij.2) y (1, 0)) p
            (0, EuclideanSpace.single ij.2 1))))
  let Y : Idx → ∀ m : ℕ, (Fin m → Fin (Module.finrank ℝ EuN)) → ℝ × EuStd → ℝ :=
    Sum.elim (fun _ m β p => Ft m β p)
      (Sum.elim (fun b m β p => if b then Q m β p else P m β p)
        (Sum.elim (fun ij m β p => P (m + 2) (Fin.snoc (Fin.snoc β ij.2) ij.1) p)
          (fun ij m β p => P (m + 1) (Fin.snoc β ij.1) p)))
  have hIc : Icc c d ⊆ D.regular := (Icc_subset_Icc hac.le hdb.le).trans hreg
  have hB (j : Idx) : ContDiffOn ℝ (⊤ : ℕ∞) (B j) (Icc c d ×ˢ W) := by
    rcases j with u | (b | (ij | ij))
    · exact contDiffOn_const
    · cases b
      · exact ((hdiff (hdiff hρ _) _).neg).mono (prod_mono hIc Subset.rfl)
      · exact ((hdiff hρ _).neg).mono (prod_mono hIc Subset.rfl)
    · exact (hdiff (hA ij.1 ij.2) _).mono (prod_mono hIc Subset.rfl)
    · exact (hdiff (hdiff (hA ij.1 ij.2) _) _).mono (prod_mono hIc Subset.rfl)
  have hY (j : Idx) (m β) : MemLp (Y j m β) 2 ν₀ := by
    rcases j with u | (b | (ij | ij))
    · exact Lp.memLp (Ft m β)
    · cases b
      · exact Lp.memLp (P m β)
      · exact Lp.memLp (Q m β)
    · exact Lp.memLp (P (m + 2) (Fin.snoc (Fin.snoc β ij.2) ij.1))
    · exact Lp.memLp (P (m + 1) (Fin.snoc β ij.1))
  have hYw (j : Idx) (m β i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
      (fun z => Y j (m + 1) (Fin.cons i β) (t, z)) (fun z => Y j m β (t, z)) Ω₀ := by
    rcases j with u | (b | (ij | ij))
    · exact hFtweak m β i
    · cases b
      · exact hPweak m β i
      · exact hQweak m β i
    · simpa only [Y, Sum.elim_inr, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hPweak (m + 2) (Fin.snoc (Fin.snoc β ij.2) ij.1) i
    · simpa only [Y, Sum.elim_inr, Fin.cons_snoc_eq_snoc_cons] using
        hPweak (m + 1) (Fin.snoc β ij.1) i
  have hformula : C =ᵐ[ν₀] fun p => Ft 0 e p +
      (∑ i, ∑ j, (fderiv ℝ (A i j) p (1, 0) * P 2 (Fin.cons j (Fin.cons i e)) p +
        fderiv ℝ (fun y => fderiv ℝ (A i j) y (1, 0)) p (0, EuclideanSpace.single j 1) *
          P 1 (Fin.cons i e) p)) -
      (fderiv ℝ ρ p (1, 0) * Q 0 e p +
        fderiv ℝ (fun y => fderiv ℝ ρ y (1, 0)) p (1, 0) * P 0 e p) := by
    filter_upwards [hC, hP, ae_all_iff.mpr hKalign] with p hc hu hk
    change P 0 e p = U p at hu
    rw [hc]
    simp only [hHalign, hQalign, hk, hu]
    rfl
  have hsum : C =ᵐ[ν₀] fun p => ∑ j : Idx, B j p * Y j 0 e p := by
    filter_upwards [hformula] with p hp
    have hsnoc (i : Fin (Module.finrank ℝ EuN)) :
        (Fin.snoc e i : Fin 1 → Fin (Module.finrank ℝ EuN)) = Fin.cons i e := by
      ext j; fin_cases j; rfl
    have hsnoc₂ (i j : Fin (Module.finrank ℝ EuN)) :
        (Fin.snoc (Fin.cons j e) i : Fin 2 → Fin (Module.finrank ℝ EuN)) =
          Fin.cons j (Fin.cons i e) := by ext l; fin_cases l <;> rfl
    rw [hp]
    simp only [Idx, B, Y, Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl,
      Sum.elim_inr, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, Fintype.sum_prod_type,
      hsnoc, hsnoc₂, one_mul]
    simp_rw [Finset.sum_add_distrib]
    ring
  have hfinite (N : ℕ) := exists_lp_weak_partial_tree_of_finite_sum_of_contDiffOn
    (μ := μ) isCompact_Icc hW hΩ₀
    (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
    (hΩ₀Ω.trans (subset_closure.trans hΩs)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) N C B hB Y
    (fun j m _ β => hY j m β) (fun j m _ β i => hYw j m β i) hsum
  obtain ⟨CF, hCF, hCFw⟩ := exists_lp_weak_partial_tree_of_finite_orders (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ₀ C (by
    intro N
    obtain ⟨T, hT, hTw⟩ := hfinite N
    exact ⟨T, by rw [hT], hTw⟩)
  refine ⟨P, Q, CF, hP, hPweak, hQweak, hCFw, hQtime, hCF.trans hformula, ?_⟩
  intro φ hφ hφc hφs
  have hEq := hCweak φ hφ hφc hφs
  rw [← hQalign] at hEq
  simp only [← hDRalign] at hEq
  refine hEq.trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [hCF] with p hp
  rw [hp]

end DifferentialGeometry.Analysis.Parabolic
