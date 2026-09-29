import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffMetricEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffTimeEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffScalarSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartFlux
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeightedDivergence

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_local_second_weak_derivative_of_metric_divergence_equation
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
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
          (fun z => H i j (t, z)) (fun z => K i (t, z)) Ω₀) ∧
        (∀ᵐ t ∂μ₀, MemWkp 2 2 (fun z => U (t, z)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm 2 2 (fun z => U (t, z)) Ω₀).toReal) 2 μ₀ := by
  intro μ ν ρ A U S K hK hweak μ₀
  let q := g a
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨δ, η, _, _, hη, _, _, hηone, hηs⟩ :=
    exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ hΩ₀Ω
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) (hηs.trans subset_closure)
  have hηone' : ∀ z ∈ Ω₀, η z = 1 := fun z hz =>
    hηone z (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hz))
  obtain ⟨v, hv⟩ := exists_lp_h1ComplDirichlet_chartPullback_mul_of_joint_weak_partials
    q α hΩ hΩc hΩs hη hηc hηs U K hK
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  let σ := fun p : ℝ × EuStd => densityOnEuclid q α p.2
  let r := fun p => ρ p / σ p
  let C := fun p => (r p)⁻¹ * S p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)
  let Q := fun j p => ∑ i, (η p.2 / r p) * A i j p * K i p
  let B := fun p => η p.2 * C p -
    ∑ i, ∑ j, A i j p * K i p * fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
  obtain ⟨hQ, hB, ⟨ℓ, hℓ⟩, htensor⟩ := exists_lp_dual_of_cutoff_metric_divergence_equation
    (μ₀ := volume) hG q α hW Subset.rfl hΩ hΩc hΩs hreg hη hηs
    (Lp.memLp U) (Lp.memLp S) (fun i => Lp.memLp (K i)) hweak
  obtain ⟨w, hw, hd⟩ := exists_timeH1_of_cutoff_tensor_identity α hΩ hΩc hΩs hη hηs
    hab μ rfl U v ℓ Q B hv hℓ htensor
  have hflux := ae_cutoff_flux_eq_density_ratio q g α hΩ hΩc hΩs U
    (fun j p => K j p) (Lp.memLp U) (fun j => Lp.memLp (K j))
    (fun t => v t) hv hK hη
  obtain ⟨β, f, _, hpair, _, hsource⟩ := exists_lp_scalar_source_of_cutoff_flux q hG
    isCompact_Icc hreg α hΩ hΩc hΩs (μ := μ) le_rfl U K v ℓ hη hηs hK Q B hQ hB hℓ hflux
  obtain ⟨H, hH, _⟩ := exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
    (G := G) hG hab.le hreg q α hΩ hΩc hΩs hac hdb rfl
    v f ℓ β w hw hd hpair hsource hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : μ₀.prod (volume.restrict Ω₀) ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hK₀ (i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d) (hK i)] with t ht
    exact ht.restrict hΩ₀ hsub
  have halign (i) : ∀ᵐ t ∂μ₀,
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) : EuStd → ℝ)
        =ᵐ[volume.restrict Ω₀] fun z => K i (t, z) := by
    apply ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul_eq_one q α
      hΩ hΩc hΩs hΩ₀ hsub (fun t => v t) (fun t z => U (t, z)) i
      (fun t z => K i (t, z)) hηone' (ae_restrict_of_ae hv) ?_ (hK₀ i)
    exact (((Lp.memLp (K i)).mono_measure hmeasure).prodMk_left (by norm_num)).mono
      (fun _ ht => ht.locallyIntegrable (by norm_num))
  have hH₀ (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => K i (t, z)) Ω₀ := by
    filter_upwards [hH i j, halign i] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j he ht
  have hKreg (i) := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
    ((Lp.memLp (K i)).mono_measure hmeasure) (fun j => Lp.memLp (H i j)) (hH₀ i)
  have hUreg := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
    ((Lp.memLp U).mono_measure hmeasure) (fun i => (hKreg i).1) (fun i => (hKreg i).2) hK₀
  exact ⟨H, hH₀, hUreg.1, hUreg.2⟩

theorem exists_local_weak_time_deriv_of_metric_divergence_equation
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
      ∃ R : Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂μ₀.prod (volume.restrict Ω₀)) =
            -∫ p, R p * φ p ∂μ₀.prod (volume.restrict Ω₀) := by
  intro μ ν ρ A U S K hK hweak μ₀
  obtain ⟨H, hH, _, _⟩ := exists_local_second_weak_derivative_of_metric_divergence_equation
    hG hab hreg α hΩ hΩc hΩs hΩ₀ hΩ₀Ω hac hdb U S K hK hweak
  let ν₀ := μ₀.prod (volume.restrict Ω₀)
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : ν₀ ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hKmem (i) : MemLp (K i) 2 ν₀ := (Lp.memLp (K i)).mono_measure hmeasure
  let V := fun i => (hKmem i).toLp (K i)
  have hV (i) : V i =ᵐ[ν₀] K i := (hKmem i).coeFn_toLp
  have hHV (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => V i (t, z)) Ω₀ := by
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hV i)] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j (Filter.EventuallyEq.symm he) ht
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
  have hρne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ W) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (g p.1) α ((image_mono interior_subset) hp.2))
  have hρinv := hbounded (fun p => (ρ p)⁻¹) (hρ.continuousOn.inv₀ hρne)
  have hDρsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ ρ p (1, 0))
      (D.regular ×ˢ W) :=
    (hρ.fderiv_of_isOpen (D.regular_isOpen.prod hW) (by simp)).clm_apply contDiffOn_const
  have hDρ := hbounded _ hDρsmooth.continuousOn
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ W) :=
    weightedInvGramOnEuclid_family_contDiffOn (G := G) hG Subset.rfl α Subset.rfl i j
  have hAb (i j) := hbounded (A i j) (hA i j).continuousOn
  have hDAb (i j) : MemLp
      (fun p => fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single j 1)) ∞ ν₀ :=
    hbounded _ (((weightedInvGramOnEuclid_family_fderiv_contDiffOn
      (G := G) hG Subset.rfl α hW Subset.rfl i j).clm_apply contDiffOn_const).continuousOn)
  have hAs (i j) : ∀ᵐ t ∂μ₀, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A i j (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d)
      (ae_restrict_mem (μ := volume) measurableSet_Icc)] with t ht
    exact (hA i j).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hreg ht, hΩW (subset_closure (hsub hz))⟩)
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
  obtain ⟨R, _, hR⟩ := exists_lp_weak_deriv_of_weighted_divergence
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_Ioo hΩ₀ (1 : ℝ)
    ((Lp.memLp U).mono_measure hmeasure) ((Lp.memLp S).mono_measure hmeasure)
    V H hAb hDAb hAs hHV (hρ.mono hregion) (fun p hp => hρne p (hregion hp))
    hρinv (hρinv.fun_mul (r := ∞) hDρ) hweak₀
  exact ⟨R, hR⟩

end DifferentialGeometry.Analysis.Parabolic
