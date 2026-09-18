import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityTimeRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Commutation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem exists_local_lp_weak_gradient_equation_of_weighted_weak_equation
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hweak : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, MetricExtension.densityOnEuclid (G.metric p.1) α p.2 * U p *
        fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, (∑ i, MetricExtension.weightedInvGramOnEuclid
            (G.metric p.1) α i j p.2 * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, F p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (DF : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hFspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => DF k (t, x)) (fun x => F (t, x)) Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ R : Lp ℝ 2 ν, ∃ S : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
        (∀ i k, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv k (fun x => H i k (t, x)) (fun x => K i (t, x)) Ω₀) ∧
        (∀ i k, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv i (fun x => H i k (t, x)) (fun x => K k (t, x)) Ω₀) ∧
        (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
        (R =ᵐ[ν] fun p => (ρ p)⁻¹ *
          ((∑ i, ∑ j, (A i j p * H i j p +
            fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K i p)) +
              F p - fderiv ℝ ρ p (1, 0) * U p)) ∧
        (∀ k, S k =ᵐ[ν] fun p => DF k p +
          (∑ i, ∑ j, (fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun q => fderiv ℝ (A i j) q (0, EuclideanSpace.single k 1)) p
              (0, EuclideanSpace.single j 1) * K i p)) -
          (fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p +
            fderiv ℝ (fun q => fderiv ℝ ρ q (0, EuclideanSpace.single k 1)) p (1, 0) * U p)) ∧
        ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, ρ p * K k p * fderiv ℝ φ p (1, 0) ∂ν) =
            (∑ j, ∫ p, (∑ i, A i j p * H i k p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
              ∫ p, S k p * φ p ∂ν := by
  intro ν ρ A
  classical
  let μ := volume.restrict (Icc c d)
  let νouter := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
  have hI : Icc c d ⊆ Icc a b := fun _ ht => ⟨hac.le.trans ht.1, ht.2.trans hdb.le⟩
  have hIoo : Ioo c d ⊆ Ioo a b := fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩
  have hreg₀ : Icc c d ⊆ D.regular := hI.trans hreg
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hμ : μ ≤ volume.restrict (Icc a b) := Measure.restrict_mono hI le_rfl
  have hν : ν ≤ νouter :=
    Measure.prod_mono hμ (Measure.restrict_mono hsub le_rfl)
  obtain ⟨H, R, hH, _, hRformula, hR⟩ :=
    exists_local_lp_time_weak_derivative_of_weighted_weak_equation
      hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak hac hdb hΩ₀ hΩ₀Ω
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hν
  have hF : MemLp F 2 ν := (Lp.memLp F).mono_measure hν
  have hK (i) : MemLp (K i) 2 ν := (Lp.memLp (K i)).mono_measure hν
  have hDF (i) : MemLp (DF i) 2 ν := (Lp.memLp (DF i)).mono_measure hν
  have hfirst (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω₀ := by
    filter_upwards [(hspatial k).filter_mono (ae_mono hμ)] with t ht
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht
  have hDFweak (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DF k (t, x)) (fun x => F (t, x)) Ω₀ := by
    filter_upwards [(hFspatial k).filter_mono (ae_mono hμ)] with t ht
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub ht
  have hHcomm (i k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => H i k (t, x)) (fun x => K k (t, x)) Ω₀ := by
    filter_upwards [hfirst k, hfirst i, hH i k] with t hk hi hik
    exact hk.comm hi hik
  let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ O) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α Subset.rfl i j
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hOt)
  have hd (f : ℝ × EuStd → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (D.regular ×ˢ O))
      (v : ℝ × EuStd) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ f p v) (D.regular ×ˢ O) :=
    (hf.fderiv_of_isOpen (D.regular_isOpen.prod hO) (by simp)).clm_apply contDiffOn_const
  have hlift (f : ℝ × EuStd → ℝ) (hf : ContinuousOn f (D.regular ×ˢ O)) : MemLp f ∞ ν := by
    have hm := (hf.mono (Set.prod_mono hreg₀ hΩ₀s)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm
  have hAmem (i j) : MemLp (A i j) ∞ ν := hlift _ (hA i j).continuousOn
  have hflux_sum (V : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ)
      (hV : ∀ i, MemLp (V i) 2 ν) (φ : ℝ × EuStd → ℝ)
      (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
      (∑ j, ∫ p, (∑ i, A i j p * V i p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
      ∑ i, ∑ j, ∫ p, A i j p * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [Finset.sum_mul]
    apply integral_finsetSum
    intro i _
    exact (((hV i).mul (r := 2) (hAmem i j)).locallyIntegrable
      (by norm_num)).integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1))
  have hrestrict (f ψ : ℝ × EuStd → ℝ) (hs : tsupport ψ ⊆ Icc c d ×ˢ Ω₀) :
      (∫ p, f p * ψ p ∂νouter) = ∫ p, f p * ψ p ∂ν := by
    dsimp only [νouter, ν, μ]
    rw [Measure.prod_restrict, Measure.prod_restrict]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Icc.prod hΩ.measurableSet) (Set.prod_mono hI hsub)
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp.2 (hs h)), mul_zero]
  have hweakInner (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ j, ∫ p, (∑ i, A i j p * K i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F p * φ p ∂ν := by
    have hs : tsupport φ ⊆ Icc c d ×ˢ Ω₀ :=
      hφs.trans (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
    have hd (v : ℝ × EuStd) : tsupport (fun p => fderiv ℝ φ p v) ⊆ Icc c d ×ˢ Ω₀ :=
      (tsupport_fderiv_apply_subset ℝ v).trans hs
    calc
      _ = ∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂νouter :=
        (hrestrict (fun p => ρ p * U p) (fun p => fderiv ℝ φ p (1, 0)) (hd (1, 0))).symm
      _ = _ := by
        rw [hweak φ hφ hφc (hφs.trans (Set.prod_mono hIoo hsub))]
        apply congrArg₂ (fun x y : ℝ => x - y) ?_ (hrestrict F φ hs)
        apply Finset.sum_congr rfl
        intro j _
        exact hrestrict (fun p => ∑ i, A i j p * K i p)
          (fun p => fderiv ℝ φ p (0, EuclideanSpace.single j 1)) (hd (0, EuclideanSpace.single j 1))
  have hbase (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN),
          ∫ p, A ij.1 ij.2 p * K ij.1 p *
            fderiv ℝ φ p (0, EuclideanSpace.single ij.2 1) ∂ν) -
          ∫ p, F p * φ p ∂ν := by
    rw [hweakInner φ hφ hφc hφs, hflux_sum (fun i => K i) hK φ hφ hφc]
    simp only [Fintype.sum_prod_type]
  have hdomain : Ioo c d ×ˢ Ω₀ ⊆ D.regular ×ˢ O :=
    Set.prod_mono (Ioo_subset_Icc_self.trans hreg₀) (subset_closure.trans hΩ₀s)
  have hliftWeak (V W : ℝ × EuStd → ℝ) (hV : MemLp V 2 ν) (hW : MemLp W 2 ν)
      (i : Fin (Module.finrank ℝ EuN))
      (hw : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun x => W (t, x)) (fun x => V (t, x)) Ω₀)
      (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo c d ×ˢ Ω₀) :
      (∫ p, V p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, W p * φ p ∂ν :=
    Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      (hV.locallyIntegrable (by norm_num)) (hW.locallyIntegrable (by norm_num)) i hw
      φ hφ hφc (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hex (k : Fin (Module.finrank ℝ EuN)) :=
    Sobolev.exists_lp_weak_deriv_weighted_divergence
      (μ := ν) (Ω := Ioo c d ×ˢ Ω₀)
      (U := U) (W := K k) (R := R) (ρ := ρ) (F := F) (DF := DF k)
      (V := fun ij : Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN) => K ij.1)
      (H := fun ij => H ij.1 k) (J := fun ij => H ij.1 ij.2)
      (A := fun ij => A ij.1 ij.2)
      Finset.univ (isOpen_Ioo.prod hΩ₀) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (0, EuclideanSpace.single k 1) (1, 0) (fun ij => (0, EuclideanSpace.single ij.2 1))
      hU ((hK k).locallyIntegrable (by norm_num)) (Lp.memLp R) (hDF k)
      (fun ij _ => hK ij.1)
      (fun ij _ => (Lp.memLp (H ij.1 k)).locallyIntegrable (by norm_num))
      (fun ij _ => Lp.memLp (H ij.1 ij.2)) (hρ.mono hdomain)
      (fun ij _ => (hA ij.1 ij.2).mono hdomain)
      (fun ij _ => hlift _ (hd _ (hA ij.1 ij.2) _).continuousOn)
      (fun ij _ => hlift _ (hd _ (hd _ (hA ij.1 ij.2) _) _).continuousOn)
      (hlift _ (hd _ hρ _).continuousOn)
      (hlift _ (hd _ (hd _ hρ _) _).continuousOn)
      (hliftWeak U (K k) hU (hK k) k (hfirst k)) hR
      (fun ij _ => hliftWeak (K ij.1) (H ij.1 k)
        (hK ij.1) (Lp.memLp (H ij.1 k)) k (hH ij.1 k))
      (fun ij _ => hliftWeak (K ij.1) (H ij.1 ij.2)
        (hK ij.1) (Lp.memLp (H ij.1 ij.2)) ij.2 (hH ij.1 ij.2))
      (hliftWeak F (DF k) hF (hDF k) k (hDFweak k)) hbase
  choose S hS hSeq using hex
  refine ⟨H, R, S, hH, hHcomm, hR, hRformula, ?_, ?_⟩
  · intro k
    simpa only [Fintype.sum_prod_type] using hS k
  · intro k φ hφ hφc hφs
    rw [hflux_sum (fun i => H i k) (fun i => Lp.memLp (H i k)) φ hφ hφc]
    simpa only [Fintype.sum_prod_type] using hSeq k φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
