import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem ae_hasWeakPartialDeriv_time_derivative_of_weighted_source
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (U F R : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (K T DF : Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (J : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
      Fin (Module.finrank ℝ EuN) →
      Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => K k (t, x)) (fun x => U (t, x)) Ω)
    (hsecond : ∀ i k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => H i k (t, x)) (fun x => K i (t, x)) Ω)
    (hthird : ∀ i j k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => J i j k (t, x)) (fun x => H i j (t, x)) Ω)
    (hFspatial : ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => DF k (t, x)) (fun x => F (t, x)) Ω)
    (htime : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, U p * fderiv ℝ φ p (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ p, R p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hKtime : ∀ k (φ : ℝ × EuStd → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, K k p * fderiv ℝ φ p (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ p, T k p * φ p ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hformula :
      let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
      let A := fun i j (p : ℝ × EuStd) =>
        MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
      R =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] fun p => (ρ p)⁻¹ *
        ((∑ i, ∑ j, (A i j p * H i j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K i p)) +
            F p - fderiv ℝ ρ p (1, 0) * U p)) :
    ∀ k, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv k
      (fun x => T k (t, x)) (fun x => R (t, x)) Ω := by
  classical
  let μ := volume.restrict (Icc a b)
  let ν := μ.prod (volume.restrict Ω)
  let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
  let A := fun i j (p : ℝ × EuStd) =>
    MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
  let DA := fun i j (p : ℝ × EuStd) =>
    fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1)
  let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ O) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α Subset.rfl i j
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hOt)
  have hρinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => (ρ p)⁻¹) (D.regular ×ˢ O) :=
    hρ.inv (fun p hp =>
      (MetricExtension.densityOnEuclid_pos (G.metric p.1) α (hOt hp.2)).ne')
  have hDA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (DA i j) (D.regular ×ˢ O) :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t x => A i j (t, x)) D.regular_isOpen.uniqueDiffOn hO
      (hA i j)).clm_apply contDiffOn_const
  have hρt : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => fderiv ℝ ρ p (1, 0)) (D.regular ×ˢ O) :=
    (hρ.fderiv_of_isOpen (D.regular_isOpen.prod hO) (by simp)).clm_apply contDiffOn_const
  have hlift (f : ℝ × EuStd → ℝ) (hf : ContinuousOn f (D.regular ×ˢ O)) : MemLp f ∞ ν := by
    have hm := (hf.mono (Set.prod_mono hreg hΩs)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm
  let ι := (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
    ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕ Bool)
  let Y : ι → Lp ℝ 2 ν :=
    Sum.elim (fun ij => H ij.1 ij.2) (Sum.elim (fun ij => K ij.1) (fun z => if z then F else U))
  let DY : ι → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν :=
    Sum.elim (fun ij k => J ij.1 ij.2 k)
      (Sum.elim (fun ij k => H ij.1 k) (fun z k => if z then DF k else K k))
  let B : ι → ℝ × EuStd → ℝ :=
    Sum.elim (fun ij p => (ρ p)⁻¹ * A ij.1 ij.2 p)
      (Sum.elim (fun ij p => (ρ p)⁻¹ * DA ij.1 ij.2 p)
        (fun z p => if z then (ρ p)⁻¹ else -((ρ p)⁻¹ * fderiv ℝ ρ p (1, 0))))
  have hBsmooth (i : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (B i) (D.regular ×ˢ O) := by
    rcases i with ⟨i, j⟩ | (⟨i, j⟩ | z)
    · exact hρinv.mul (hA i j)
    · exact hρinv.mul (hDA i j)
    · cases z
      · exact (hρinv.mul hρt).neg
      · exact hρinv
  have hB (i : ι) : MemLp (B i) ∞ ν := hlift _ (hBsmooth i).continuousOn
  have hDB (i : ι) (k : Fin (Module.finrank ℝ EuN)) :
      MemLp (fun p => fderiv ℝ (fun x => B i (p.1, x)) p.2
        (EuclideanSpace.single k 1)) ∞ ν :=
    hlift _ ((DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t x => B i (t, x)) D.regular_isOpen.uniqueDiffOn hO
      (hBsmooth i)).clm_apply contDiffOn_const).continuousOn
  have hBslice (i : ι) : ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => B i (t, x)) Ω := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hBsmooth i).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hreg ht, hΩs (subset_closure hx)⟩)
  have hY (i : ι) (k : Fin (Module.finrank ℝ EuN)) :
      ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => DY i k (t, x)) (fun x => Y i (t, x)) Ω := by
    rcases i with ⟨i, j⟩ | (⟨i, j⟩ | z)
    · exact hthird i j k
    · exact hsecond i k
    · cases z
      · exact hspatial k
      · exact hFspatial k
  have hRsum : R =ᵐ[ν] fun p => ∑ i, B i p * Y i p := by
    filter_upwards [hformula] with p hp
    change R p = (ρ p)⁻¹ *
      ((∑ i, ∑ j, (A i j p * H i j p + DA i j p * K i p)) +
        F p - fderiv ℝ ρ p (1, 0) * U p) at hp
    rw [hp]
    change _ = ∑ i : (Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕
      ((Fin (Module.finrank ℝ EuN) × Fin (Module.finrank ℝ EuN)) ⊕ Bool), B i p * Y i p
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [B, Y, Fintype.sum_prod_type, Fintype.sum_bool, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte]
    simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    ring
  obtain ⟨DR, hDR, _, _, _, _⟩ :=
    Sobolev.Euclidean.exists_lp_spatial_weak_partials_of_ae_eq_finite_sum
      hΩ R Y DY B hB hDB hBslice hY hRsum
  have hliftWeak (V W : Lp ℝ 2 ν) (i : Fin (Module.finrank ℝ EuN))
      (hw : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun x => W (t, x)) (fun x => V (t, x)) Ω)
      (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
      (∫ p, V p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂ν) =
        -∫ p, W p * φ p ∂ν :=
    Sobolev.Euclidean.integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp V).locallyIntegrable (by norm_num))
      ((Lp.memLp W).locallyIntegrable (by norm_num)) i hw
      φ hφ hφc (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
  have hmem : ∀ᵐ p ∂ν, p ∈ Ioo a b ×ˢ Ω := by
    have hμ : μ = volume.restrict (Ioo a b) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    change ∀ᵐ p ∂μ.prod (volume.restrict Ω), p ∈ Ioo a b ×ˢ Ω
    rw [hμ]
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod hΩ.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact ⟨ht, hx⟩
  intro k
  have hRwithT (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
      (∫ p, R p * fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν) =
        -∫ p, T k p * φ p ∂ν := by
    have he := Sobolev.integral_weak_deriv_fderiv_comm
      (0, EuclideanSpace.single k 1) (1, 0)
      (hliftWeak U (K k) k (hspatial k)) htime hφ hφc hφs
    exact he.symm.trans (hKtime k φ hφ hφc hφs)
  have heq : DR k = T k := Sobolev.lp_eq_of_weak_deriv_integral
    (isOpen_Ioo.prod hΩ) hmem (by norm_num) (0, EuclideanSpace.single k 1)
    (hliftWeak R (DR k) k (hDR k)) hRwithT
  simpa only [heq] using hDR k

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
