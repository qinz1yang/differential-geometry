import DifferentialGeometry.Analysis.Integration.Lp.SmoothPairing
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual
import DifferentialGeometry.Analysis.Sobolev.Euclidean.CompactSource

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology


open Bundle Manifold
open scoped ContDiff Manifold NNReal
namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure

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

theorem integral_chart_tensor_test_of_smooth
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (μ : Measure ℝ) {W B : ℝ × EuStd → ℝ}
    {Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ)
    (hraw :
      let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
      (∫ p, deriv τ p.1 * W p * ψ p.2 ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) -
        ∫ p, τ p.1 * B p * ψ p.2 ∂μ.prod (volume.restrict Ω)) :
    (∫ p, deriv τ p.1 * W p *
      H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
        ∂μ.prod (volume.restrict Ω)) =
      (∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
        (smoothToH1ComplDirichlet q v) p.2 ∂μ.prod (volume.restrict Ω)) -
      ∫ p, τ p.1 * B p * H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
        ∂μ.prod (volume.restrict Ω) := by
  let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let R := fun z => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let ν := μ.prod (volume.restrict Ω)
  have hR : R =ᵐ[volume.restrict Ω] ψ := by
    rw [show R = (fun z => smoothToLpDirichlet q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) by
      funext z; simp only [R, H1ComplDirichletToLp_smoothToH1ComplDirichlet]]
    have h := ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) v.memLp_two.coeFn_toLp
    change (fun z => v.memLp_two.toLp v.toFun ((extChartAt I_hs α).symm
      ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω] ψ
    exact h
  have hRp : (fun p : ℝ × EuStd => R p.2) =ᵐ[ν] fun p => ψ p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume.restrict Ω)).ae hR
  have hleft : (∫ p, deriv τ p.1 * W p * R p.2 ∂ν) =
      ∫ p, deriv τ p.1 * W p * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hRp] with p hp
    exact congrArg (fun r : ℝ => deriv τ p.1 * W p * r) hp
  have hright : (∫ p, τ p.1 * B p * R p.2 ∂ν) =
      ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hRp] with p hp
    exact congrArg (fun r : ℝ => τ p.1 * B p * r) hp
  have hflux : (∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (smoothToH1ComplDirichlet q v) p.2 ∂ν) =
      ∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν := by
    apply Finset.sum_congr rfl
    intro j _
    have hD := dirichletLocalWeakPartialLp_smoothToH1ComplDirichlet_coeFn q α hΩ hΩc hΩs j v
    have hDp := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume.restrict Ω)).ae hD
    apply integral_congr_ae
    filter_upwards [hDp] with p hp
    exact congrArg (fun r : ℝ => τ p.1 * Q j p * r) hp
  exact hleft.trans (hraw.trans (congrArg₂ (fun a b : ℝ => a - b) hflux hright).symm)

theorem integral_chart_source_dual_of_smooth_tensor_test
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (htest : ∀ (τ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ →
      ∀ v : SmoothScalarDirichlet q,
        (∫ t, τ t * β t (smoothToH1ComplDirichlet q v) ∂μ) =
          ∫ p, τ p.1 * f p * v.toFun ((extChartAt I_hs α).symm
            ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) :
    ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) =
        ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  obtain ⟨ℓ, hℓ, _, hℓvar⟩ := exists_lp_chart_source_dual_integral α hΩ hΩc hΩs f
  have heq : β = ℓ := by
    apply MeasureTheory.Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange
      (smoothToH1ComplDirichlet q) (denseRange_smoothToH1ComplDirichlet q) (by norm_num)
    intro τ hτ hτc v
    have hτmem : MemLp τ 2 μ := hτ.continuous.memLp_of_hasCompactSupport hτc
    have hτae := hτmem.coeFn_toLp
    have hR : (fun x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) =ᵐ[volume.restrict Ω]
          fun x => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)) := by
      simp only [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
      exact ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) v.memLp_two.coeFn_toLp
    have hpair := hℓ (hτmem.toLp τ) (smoothToH1ComplDirichlet q v)
    have hleft : (∫ t, hτmem.toLp τ t * ℓ t (smoothToH1ComplDirichlet q v) ∂μ) =
        ∫ t, τ t * ℓ t (smoothToH1ComplDirichlet q v) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hτae] with t ht
      rw [ht]
    have hright : (∫ p, hτmem.toLp τ p.1 * f p *
        H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v) ((extChartAt I_hs α).symm
          ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) =
        ∫ p, τ p.1 * f p * v.toFun ((extChartAt I_hs α).symm
          ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ)
        (ν := volume.restrict Ω)).ae hτae,
        (Measure.quasiMeasurePreserving_snd (μ := μ)
          (ν := volume.restrict Ω)).ae hR] with p hτp hRp
      rw [hτp, hRp]
    rw [hleft, hright] at hpair
    exact (htest τ hτ hτc v).trans hpair.symm
  exact heq ▸ hℓvar


omit [T2Space M] [CompactSpace M] in
private theorem smoothScalarDirichlet_chartInverse_bounds
    {q : SmoothRiemannianMetric I_hs M}
    (α : M) {Ω : Set EuStd} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : SmoothScalarDirichlet q) :
    let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω ∧ MemLp ψ 2 (volume.restrict Ω) := by
  intro ψ
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) ψ U := by
    apply (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn α v.smooth).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  have hbound : MemLp ψ ∞ (volume.restrict Ω) :=
    (hP.continuousOn.mono hΩs).memLp_top_of_subset_isCompact hΩc hΩ subset_closure
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa using (measure_mono (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  exact ⟨hP.mono (subset_closure.trans hΩs), hbound.mono_exponent (by simp)⟩

theorem integral_chart_source_dual_eq_of_compact_flux
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω K : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    {B : ℝ × EuStd → ℝ} {P : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (hB : MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hS : ∀ᵐ p ∂μ.prod (volume.restrict Ω), p.2 ∉ K → f p - B p = 0)
    (hP : ∀ j, ∀ᵐ p ∂μ.prod (volume.restrict Ω), p.2 ∉ K → P j p = 0)
    (htest : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
      (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
        (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
          ∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂μ.prod (volume.restrict Ω))
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ : ∀ (τ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ →
      ∀ v : SmoothScalarDirichlet q,
        let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (∫ t, τ t * β t (smoothToH1ComplDirichlet q v) ∂μ) =
          (∫ p, τ p.1 * B p * ψ p.2 ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, τ p.1 * P j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
              ∂μ.prod (volume.restrict Ω)) :
    ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) =
        ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  apply integral_chart_source_dual_of_smooth_tensor_test α hΩ hΩc hΩs f β
  intro τ hτ hτc v
  let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  obtain ⟨hψ, hψmem⟩ := smoothScalarDirichlet_chartInverse_bounds α hΩ.measurableSet hΩc hΩs v
  have hτmem : MemLp τ 2 μ := hτ.continuous.memLp_of_hasCompactSupport hτc
  have hint (F : ℝ × EuStd → ℝ) (hF : MemLp F 2 (μ.prod (volume.restrict Ω))) :
      Integrable (fun p => τ p.1 * F p * ψ p.2) (μ.prod (volume.restrict Ω)) := by
    apply (hF.integrable_mul_tensor (hτmem.toLp τ) (hψmem.toLp ψ)).congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := volume.restrict Ω)).ae hτmem.coeFn_toLp,
      (Measure.quasiMeasurePreserving_snd (μ := μ)
        (ν := volume.restrict Ω)).ae hψmem.coeFn_toLp] with p hτp hψp
    rw [hτp, hψp]
  have h := DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_source_tensor_eq_of_compact_flux_support
    hΩ hK hKΩ ((Lp.memLp f).locallyIntegrable (by norm_num))
      (hB.locallyIntegrable (by norm_num)) hS hP htest hψ hτ hτc
      (hint f (Lp.memLp f)) (hint B hB)
  exact (hβ τ hτ hτc v).trans h.symm


theorem integral_chart_source_dual_eq_of_compact_flux_pairing
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω K : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    {B : ℝ × EuStd → ℝ} {P : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (hB : MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hS : ∀ᵐ p ∂μ.prod (volume.restrict Ω), p.2 ∉ K → f p - B p = 0)
    (hP : ∀ j, ∀ᵐ p ∂μ.prod (volume.restrict Ω), p.2 ∉ K → P j p = 0)
    (htest : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ω →
      (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
        (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
          ∑ j, ∫ p, P j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
            ∂μ.prod (volume.restrict Ω))
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ : ∀ (τ : Lp ℝ 2 μ) (v : H1ComplDirichlet q),
      (∫ t, τ t * β t v ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q v ((extChartAt I_hs α).symm
          ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) +
          ∑ j, ∫ p, τ p.1 * P j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2
            ∂μ.prod (volume.restrict Ω)) :
    ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) =
        ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  apply integral_chart_source_dual_eq_of_compact_flux α hΩ hΩc hΩs hK hKΩ f hB hS hP htest β
  intro τ hτ hτc v
  let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  have hτmem : MemLp τ 2 μ := hτ.continuous.memLp_of_hasCompactSupport hτc
  have hτp := (Measure.quasiMeasurePreserving_fst (μ := μ)
    (ν := volume.restrict Ω)).ae hτmem.coeFn_toLp
  have hR : (fun x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) =ᵐ[volume.restrict Ω] ψ := by
    simp only [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) v.memLp_two.coeFn_toLp
  have h := hβ (hτmem.toLp τ) (smoothToH1ComplDirichlet q v)
  have hl : (∫ t, hτmem.toLp τ t * β t (smoothToH1ComplDirichlet q v) ∂μ) =
      ∫ t, τ t * β t (smoothToH1ComplDirichlet q v) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hτmem.coeFn_toLp] with t ht
    rw [ht]
  have hb : (∫ p, hτmem.toLp τ p.1 * B p * H1ComplDirichletToLp q
      (smoothToH1ComplDirichlet q v) ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) =
      ∫ p, τ p.1 * B p * ψ p.2 ∂μ.prod (volume.restrict Ω) := by
    apply integral_congr_ae
    filter_upwards [hτp, (Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := volume.restrict Ω)).ae hR] with p hτp hRp
    rw [hτp, hRp]
  have hflux : (∑ j, ∫ p, hτmem.toLp τ p.1 * P j p *
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (smoothToH1ComplDirichlet q v) p.2
        ∂μ.prod (volume.restrict Ω)) =
      ∑ j, ∫ p, τ p.1 * P j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
        ∂μ.prod (volume.restrict Ω) := by
    apply Finset.sum_congr rfl
    intro j _
    have hD := dirichletLocalWeakPartialLp_smoothToH1ComplDirichlet_coeFn q α hΩ hΩc hΩs j v
    apply integral_congr_ae
    filter_upwards [hτp, (Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := volume.restrict Ω)).ae hD] with p hτp hDp
    rw [hτp, hDp]
  rw [hl, hb, hflux] at h
  exact h

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
