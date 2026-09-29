import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensityRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

theorem exists_local_lp_time_weak_derivative_of_weighted_weak_equation
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
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let ν := (volume.restrict (Icc c d)).prod (volume.restrict Ω₀)
    let ρ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ R : Lp ℝ 2 ν,
        (∀ i j, ∀ᵐ t ∂volume.restrict (Icc c d),
          DeGiorgi.HasWeakPartialDeriv j (fun x => H i j (t, x)) (fun x => K i (t, x)) Ω₀) ∧
        (∀ᵐ t ∂volume.restrict (Icc c d),
          Sobolev.Euclidean.MemWkp 2 2 (fun x => U (t, x)) Ω₀) ∧
        (R =ᵐ[ν] fun p => (ρ p)⁻¹ *
          ((∑ i, ∑ j, (A i j p * H i j p +
            fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K i p)) +
              F p - fderiv ℝ ρ p (1, 0) * U p)) ∧
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
          (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν := by
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
  have hν : ν ≤ νouter :=
    Measure.prod_mono (Measure.restrict_mono hI le_rfl) (Measure.restrict_mono hsub le_rfl)
  have hexH := exists_local_dirichlet_second_weak_derivative_of_weighted_weak_equation
    hG hab hreg α hΩ hΩc hΩs U F K hspatial hweak hac hdb hΩ₀ hΩ₀Ω
  rw [Measure.restrict_restrict_of_subset hI] at hexH
  obtain ⟨H, hH, hUtwo⟩ := hexH
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hν
  have hF : MemLp F 2 ν := (Lp.memLp F).mono_measure hν
  have hK (i) : MemLp (K i) 2 ν := (Lp.memLp (K i)).mono_measure hν
  let V := fun i => (hK i).toLp (K i)
  have hV (i) : V i =ᵐ[ν] K i := (hK i).coeFn_toLp
  have hHV (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => V i (t, x)) Ω₀ := by
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hV i)] with t ht hVt
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j (Filter.EventuallyEq.symm hVt) ht
  let O := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hO : IsOpen O := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hOt : O ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ O) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α Subset.rfl i j
  have hlift (f : ℝ × EuStd → ℝ) (hf : ContinuousOn f (D.regular ×ˢ O)) : MemLp f ∞ ν := by
    have hm := (hf.mono (Set.prod_mono hreg₀ hΩ₀s)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (Set.prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm
  have hAmem (i j) : MemLp (A i j) ∞ ν := hlift _ (hA i j).continuousOn
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1)) ∞ ν :=
    hlift _ ((spatialFDeriv_contDiffOn (G := fun t x => A i j (t, x))
      D.regular_isOpen.uniqueDiffOn hO (hA i j)).clm_apply contDiffOn_const).continuousOn
  have hAsmooth (i j) : ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hA i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hreg₀ ht, hΩ₀s (subset_closure hx)⟩)
  obtain ⟨Div, hDiv, hDivtest⟩ := Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ₀ V H hAmem hDA hAsmooth hHV
  have hDivK : Div =ᵐ[ν] fun p => ∑ i, ∑ j,
      (A i j p * H i j p +
        fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * K i p) := by
    filter_upwards [hDiv, ae_all_iff.mpr hV] with p hp hVp
    simpa only [hVp] using hp
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
  let Source := fun p => Div p + F p
  have hSource : MemLp Source 2 ν := (Lp.memLp Div).add hF
  have hweighted : ∀ φ : ℝ × EuStd → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo c d ×ˢ Ω₀ →
      (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, Source p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have hint (i j) : Integrable (fun p => A i j p * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
      (((hAmem i j).fun_mul (r := 2) (Lp.memLp (V i))).locallyIntegrable
        (by norm_num)).integrable_smul_right_of_hasCompactSupport
          ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1))
    have hflux : (∑ j, ∫ p, (∑ i, A i j p * K i p) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
        ∑ i, ∑ j, ∫ p, A i j p * V i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∫ p, ∑ i, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
          apply integral_congr_ae
          filter_upwards [ae_all_iff.mpr hV] with p hp
          simp only [hp, Finset.sum_mul]
        _ = _ := integral_finsetSum _ (fun i _ => hint i j)
    have hD := hDivtest φ hφ hφc (hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl))
    have he := hweakInner φ hφ hφc hφs
    rw [hflux] at he
    have hDi : Integrable (fun p => Div p * φ p) ν :=
      ((Lp.memLp Div).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hFi : Integrable (fun p => F p * φ p) ν :=
      (hF.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    dsimp only [Source]
    simp_rw [add_mul]
    rw [integral_add hDi hFi]
    linarith only [hD, he]
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ O) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hOt)
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ O) : ρ p ≠ 0 :=
    (MetricExtension.densityOnEuclid_pos (G.metric p.1) α (hOt hp)).ne'
  have hρinv : MemLp (fun p => (ρ p)⁻¹) ∞ ν :=
    hlift _ (hρ.inv (fun p hp => hρne p hp.2)).continuousOn
  have hρt : MemLp (fun p => fderiv ℝ ρ p (1, 0)) ∞ ν :=
    hlift _ (((hρ.fderiv_of_isOpen (D.regular_isOpen.prod hO)
      (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const).continuousOn)
  let T := fun p => (ρ p)⁻¹ * Source p - ((ρ p)⁻¹ * fderiv ℝ ρ p (1, 0)) * U p
  have hT : MemLp T 2 ν :=
    (hρinv.fun_mul (r := 2) hSource).sub
      ((hρinv.fun_mul (r := ∞) hρt).fun_mul (r := 2) hU)
  refine ⟨H, hT.toLp T, hH, hUtwo, ?_, ?_⟩
  · filter_upwards [hT.coeFn_toLp, hDivK] with p hp hDp
    rw [hp]
    dsimp only [T, Source]
    rw [hDp]
    ring
  · intro φ hφ hφc hφs
    have hdomain : Ioo c d ×ˢ Ω₀ ⊆ D.regular ×ˢ O :=
      Set.prod_mono (Ioo_subset_Icc_self.trans hreg₀) (subset_closure.trans hΩ₀s)
    have he := Sobolev.integral_fderiv_eq_neg_of_weighted_identity
      (μ := ν) (isOpen_Ioo.prod hΩ₀) (1, 0)
      (hU.locallyIntegrable (by norm_num)) (hSource.locallyIntegrable (by norm_num))
      (hρ.mono hdomain) (fun p hp => hρne p (hdomain hp).2)
      hweighted hφ hφc hφs
    apply he.trans
    apply congrArg Neg.neg
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with p hp
    exact congrArg (fun y => y * φ p) hp.symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
