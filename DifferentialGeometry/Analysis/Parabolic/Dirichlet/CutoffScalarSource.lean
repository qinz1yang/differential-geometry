import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

section Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_lp_scalar_source_of_weak_gradient
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω)
    (B V : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    {A : Fin d → Fin d → ℝ × E → ℝ}
    (hA : ∀ i j, MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i j, MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i j, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω)
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => V (t, x)) Ω) :
    ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (A i j p * H j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
        (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
          (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, (∑ i, A i j p * V p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  obtain ⟨D, hD, hDtest⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ (fun _ => V) (fun _ => H)
      hA hDA hAsmooth (fun _ => hweak)
  refine ⟨B - D, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub B D, hD] with p hp hDp
    simpa only [Pi.sub_apply, hDp] using hp
  · intro φ hφ hφc hφs
    have hBint : Integrable (fun p => B p * φ p) (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp B).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hDint : Integrable (fun p => D p * φ p) (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp D).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have heq : (∫ p, (B - D) p * φ p ∂μ.prod (volume.restrict Ω)) =
        (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) -
          ∫ p, D p * φ p ∂μ.prod (volume.restrict Ω) := by
      rw [← integral_sub hBint hDint]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub B D] with p hp
      simp only [hp, Pi.sub_apply, sub_mul]
    rw [heq, hDtest φ hφ hφc hφs, sub_neg_eq_add]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [Finset.sum_mul]
    symm
    apply integral_finsetSum
    intro i _
    have hflux : MemLp (fun p => A i j p * V p) 2 (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp V).mul (hA i j)
    exact (hflux.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1))

end Euclidean

open Manifold
open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

omit [T2Space M] [CompactSpace M] in
private theorem exists_lp_scalar_source_of_cutoff_gradient
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (hμ : μ ≤ volume.restrict J)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (B V : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => V (t, x)) Ω) :
    let A := fun i j (p : ℝ × EuStd) =>
      (MetricExtension.densityOnEuclid q α p.2 *
        MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
    ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (A i j p * H j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
        (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
          (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, (∑ i, A i j p * V p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  intro A
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hUt : U ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ U) := by
    have hden : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2)
        (D.regular ×ˢ U) :=
      (MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => hUt hp.2)
    have hηd : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      (hη.contDiff_fderiv_apply (by simp)).comp (contDiff_snd.prodMk contDiff_const)
    exact (hden.mul (MetricExtension.invGramOnEuclid_family_contDiffOn
      hG Subset.rfl α (show U ⊆ U from Subset.rfl) i j)).mul hηd.contDiffOn
  have hAmem (i j) : MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have h := ((hA i j).continuousOn.mono (prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)) := by
    have hc := (spatialFDeriv_contDiffOn (G := fun t x => A i j (t, x))
      D.regular_isOpen.uniqueDiffOn hU (hA i j)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single j 1))
    have h := (hc.continuousOn.mono (prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hAsmooth (i j) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω := by
    filter_upwards [(ae_restrict_mem hJc.measurableSet).filter_mono (ae_mono hμ)] with t ht
    exact (hA i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hJ ht, hΩs (subset_closure hx)⟩)
  exact exists_lp_scalar_source_of_weak_gradient hΩ B V H
    hAmem hDA hAsmooth hweak

theorem exists_lp_scalar_source_of_cutoff_pairing
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} (hμ : μ ≤ volume.restrict J)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : tsupport η ⊆ Ω)
    {B V : ℝ × EuStd → ℝ}
    (hB : MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hV : MemLp V 2 (μ.prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => hV.toLp V (t, x)) Ω)
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ :
      let E := fun j p => ∑ i,
        (MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
            fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
      ∀ (τ : Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * β t z ∂μ) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
            ∂μ.prod (volume.restrict Ω)) +
          ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    ∃ f : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      let P := fun i j (p : ℝ × EuStd) =>
        (MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
            fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (P i j p * H j p +
          fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ z : Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, β t (z t) ∂μ) =
          ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  let : IsLocallyFiniteMeasure μ := Measure.isLocallyFiniteMeasure_of_le hμ
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport η) (hηs.trans subset_closure)
  let ν := μ.prod (volume.restrict Ω)
  let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2
  let E := fun j p => ∑ i,
    (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
      fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
  let W : Lp ℝ 2 ν := hV.toLp V
  have hW : W =ᵐ[ν] V := hV.coeFn_toLp
  let BW : Lp ℝ 2 ν := hB.toLp B
  have hBWeq : BW =ᵐ[ν] B := hB.coeFn_toLp
  obtain ⟨f, hf, hftest⟩ := exists_lp_scalar_source_of_cutoff_gradient q hG hJc hJ
    α hΩ hΩc hΩs (μ := μ) hμ hη BW W H hweak
  refine ⟨f, ?_⟩
  classical
  intro P
  have hfeq : f =ᵐ[ν] fun p => B p - ∑ i, ∑ j,
      (P i j p * H j p +
        fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p) := by
    filter_upwards [hf, hW, hBWeq] with p hp hWp hBp
    simpa only [hWp, hBp] using hp
  have htest (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω) :
      (∫ p, f p * φ p ∂ν) = (∫ p, B p * φ p ∂ν) +
        ∑ j, ∫ p, E j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
    rw [hftest φ hφ hφc hφs]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · apply integral_congr_ae
      filter_upwards [hBWeq] with p hp
      rw [hp]
    · apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [hW] with p hp
      rw [hp]
  have hPs (t : ℝ) (i j) : tsupport (fun x => P i j (t, x)) ⊆ tsupport η :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
  have hPzero (p : ℝ × EuStd) (hp : p.2 ∉ tsupport η) (i j) : P i j p = 0 := by
    exact image_eq_zero_of_notMem_tsupport (f := fun x => P i j (p.1, x))
      (fun hx => hp (hPs p.1 i j hx))
  have hDPzero (p : ℝ × EuStd) (hp : p.2 ∉ tsupport η) (i j) :
      fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun hx => hp (hPs p.1 i j hx))]
    rfl
  have hS : ∀ᵐ p ∂ν, p.2 ∉ tsupport η → f p - B p = 0 := by
    filter_upwards [hfeq] with p hp hout
    simp only [hp, hPzero p hout, hDPzero p hout, zero_mul, add_zero,
      Finset.sum_const_zero, sub_zero, sub_self]
  have hE : ∀ j, ∀ᵐ p ∂ν, p.2 ∉ tsupport η → E j p = 0 := by
    intro j
    exact Filter.Eventually.of_forall fun p hp => by
      change (∑ i, P i j p * V p) = 0
      simp only [hPzero p hp, zero_mul, Finset.sum_const_zero]
  refine ⟨hfeq, ?_⟩
  exact integral_chart_source_dual_eq_of_compact_flux_pairing α hΩ hΩc hΩs
    hηc.isCompact hηs f hB hS hE htest β hβ

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
