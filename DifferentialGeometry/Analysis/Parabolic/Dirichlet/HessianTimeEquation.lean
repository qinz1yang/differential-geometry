import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HessianTimeDual
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HessianSourceDual
import DifferentialGeometry.Analysis.Parabolic.WeakEquationTensor
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartMassPairing

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
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

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem cutoff_lp_dual_deriv
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    {T t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T) (ht₀₁ : t₀ < t₁)
    (H : Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω)))
    (v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc t₀ t₁)))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀))
    (ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 ((timeMeasure T).restrict (Icc t₀ t₁)))
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hv : ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁),
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * H (t, z)))
    (hw : ∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (t₀ + s))) (H1ComplDirichletToLp q z))
    (hℓ : ∀ (τ : Lp ℝ 2 ((timeMeasure T).restrict (Icc t₀ t₁))) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂(timeMeasure T).restrict (Icc t₀ t₁)) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω))
    (htensor : ∀ (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo t₀ t₁ →
      let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
      (∫ p, deriv τ p.1 * (η p.2 * (MetricExtension.densityOnEuclid q α p.2 * H p)) * ψ p.2
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)
          ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω)) -
          ∫ p, τ p.1 * B p * ψ p.2
            ∂((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω)) :
    w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s) := by
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  let σ := fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2
  let mass : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (H1ComplDirichletToLp q) (H1ComplDirichletToLp q)
  have hμ : μ = volume.restrict (Icc t₀ t₁) :=
    Measure.restrict_restrict_of_subset (fun t ht => ⟨ht₀.trans ht.1, ht.2.trans ht₁⟩)
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) (hηs.trans subset_closure)
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω)) := Lp.SecondCountableTopology
  obtain ⟨P, hP, _⟩ := Lp.exists_curry (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) H
  have hvP : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * P t z) := by
    filter_upwards [hv, hP] with t hvt hPt
    apply hvt.trans
    apply chartPullback_ae_eq_of_ae_eq q α
    have hall := (ae_restrict_iff' hΩ.measurableSet).mp hPt
    filter_upwards [hall] with x hx
    by_cases hxs : x ∈ tsupport η
    · exact congrArg (η x * ·) (hx (hηs hxs)).symm
    · simp only [image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  refine timeH1.deriv_ae_eq_of_tensor_mass_dual (ν := volume.restrict Ω)
    (X := H1ComplDirichlet q) (S := SmoothScalarDirichlet q) ht₀₁ μ hμ
    (smoothToH1ComplDirichlet q) (denseRange_smoothToH1ComplDirichlet q)
    mass v w ℓ hw
    (W := fun x => η x.2 * (σ x * H x)) (B := B) (Q := Q)
    (R := fun z x => H1ComplDirichletToLp q (smoothToH1ComplDirichlet q z)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)))
    (D := fun z j => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (smoothToH1ComplDirichlet q z)) ?_ ?_ ?_
  · intro τ z
    have h := integral_mass_inner_eq_integral_chart_prod q α hΩ hΩc hΩs hη hηc hηs
      τ v P H (hP.mono fun _ ht => ht.symm) (smoothToH1ComplDirichlet q z) hvP
    apply h.trans
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [σ]
    ring
  · intro τ z
    exact hℓ τ (smoothToH1ComplDirichlet q z)
  · intro z τ hτ hτc hτs
    exact integral_chart_tensor_test_of_smooth q α hΩ hΩc hΩs μ z τ (htensor z τ hτ hτc hτs)

omit [T2Space M] [CompactSpace M] in
private theorem integral_chart_cutoff_tensor_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (G.metric p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (G.metric p.1) α i j p.2
    ∀ (V : Lp ℝ 2 ν) (K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν) (C : ℝ × EuStd → ℝ),
      let P := fun j p => ∑ i, A i j p * K i p
      let Q := fun j p => ∑ i, (η p.2 / r p) * A i j p * K i p
      let B := fun p => η p.2 * C p - ∑ i, ∑ j, A i j p * K i p *
        fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      MemLp C 2 ν → (∀ j, MemLp (P j) 2 ν) → (∀ j, MemLp (Q j) 2 ν) →
      (∀ j, MemLp (fun p => fderiv ℝ (fun z : ℝ × EuStd => η z.2 / r z) p
        (0, EuclideanSpace.single j 1)) ∞ ν) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, σ p * V p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
              ∫ p, C p * φ p ∂ν) →
      ∀ (z : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo t₀ t₁ →
        let ψ := fun x => z.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
        (∫ p, deriv τ p.1 * (η p.2 * (σ p * V p)) * ψ p.2 ∂ν) =
          (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
            ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
  intro μ ν ρ σ r A V K C P Q B hC hP hQ hdηr hfixed
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hηc : HasCompactSupport η :=
    hΩ₀c.of_isClosed_subset (isClosed_tsupport _) (hηs.trans subset_closure)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl hchart)
  have hσall : ContDiffOn ℝ (⊤ : ℕ∞) σ (D.regular ×ˢ Ω) :=
    (MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
      (fun p hp => hchart hp.2)
  have hσne (p : ℝ × EuStd) (hp : p.2 ∈ Ω) : σ p ≠ 0 :=
    (MetricExtension.densityOnEuclid_pos q α (hchart hp)).ne'
  have hρne (p : ℝ × EuStd) (hp : p.2 ∈ Ω) : ρ p ≠ 0 :=
    (MetricExtension.densityOnEuclid_pos (G.metric p.1) α (hchart hp)).ne'
  have hrall : ContDiffOn ℝ (⊤ : ℕ∞) r (D.regular ×ˢ Ω) :=
    hρall.div hσall (fun p hp => hσne p hp.2)
  have hrne (p : ℝ × EuStd) (hp : p ∈ D.regular ×ˢ Ω) : r p ≠ 0 :=
    div_ne_zero (hρne p hp.2) (hσne p hp.2)
  have hAmem (i j) : MemLp (A i j) ∞ ν := by
    have hc := MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α
      (subset_closure.trans hΩs) i j
    have hb := (hc.continuousOn.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hSsub : Ioo t₀ t₁ ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg ⟨ht₀.trans hp.1.1.le, hp.1.2.le.trans ht₁⟩, hsub hp.2⟩
  have hr := hrall.mono hSsub
  intro z τ hτ hτc hτs ψ
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hψU : ContDiffOn ℝ (⊤ : ℕ∞) ψ U := by
    apply (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn α z.smooth).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro y ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hx
  have hψ := hψU.mono (subset_closure.trans hΩ₀s)
  have hψmem : MemLp ψ ∞ (volume.restrict Ω₀) :=
    (hψU.continuousOn.mono hΩ₀s).memLp_top_of_subset_isCompact
      hΩ₀c hΩ₀.measurableSet subset_closure
  have hdψmem (j) : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j 1)) ∞
      (volume.restrict Ω₀) :=
    ((((hψU.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (g := fun _ => EuclideanSpace.single j 1) contDiffOn_const).continuousOn).mono hΩ₀s).memLp_top_of_subset_isCompact hΩ₀c hΩ₀.measurableSet subset_closure
  have hτmem : MemLp τ ∞ μ := hτ.continuous.memLp_top_of_hasCompactSupport hτc μ
  have hηmem : MemLp η ∞ (volume.restrict Ω₀) :=
    hη.continuous.memLp_top_of_hasCompactSupport hηc _
  have hQeq (j) (p : ℝ × EuStd) : (η p.2 / r p) * P j p = Q j p := by
    simp only [P, Q, Finset.mul_sum, mul_assoc]
  have hBeq (p : ℝ × EuStd) : (η p.2 * C p - ∑ j, P j p * fderiv ℝ
      (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) = B p := by
    simp only [P, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmain (j) : Integrable (fun p => τ p.1 * ((η p.2 / r p) * P j p) *
      fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) ν := by
    simp_rw [hQeq]
    convert (((hQ j).mul (r := 2) (hτmem.comp_fst (volume.restrict Ω₀))).mul
      (r := 2) ((hdψmem j).comp_snd μ)).integrable (by norm_num) using 1
    ext p
    simp only [Pi.mul_apply]
    ring
  have herr (j) : Integrable (fun p => τ p.1 * (P j p * fderiv ℝ
      (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) * ψ p.2) ν := by
    convert ((((hdηr j).mul (r := 2) (hP j)).mul (r := 2)
      (hτmem.comp_fst (volume.restrict Ω₀))).mul (r := 2)
      (hψmem.comp_snd μ)).integrable (by norm_num) using 1
    ext p
    simp only [Pi.mul_apply]
    ring
  have hsource : Integrable (fun p => τ p.1 * (η p.2 * C p) * ψ p.2) ν := by
    convert ((((hC).mul (r := 2) (hηmem.comp_snd μ)).mul (r := 2)
      (hτmem.comp_fst (volume.restrict Ω₀))).mul (r := 2)
      (hψmem.comp_snd μ)).integrable (by norm_num) using 1
    ext p
    simp only [Pi.mul_apply]
    ring
  have hmem : ∀ᵐ p ∂ν, p.1 ∈ Icc t₀ t₁ ∧ p.2 ∈ Ω₀ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ₀.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    filter_upwards [ae_restrict_mem hΩ₀.measurableSet] with x hx
    exact ⟨ht, hx⟩
  have hgood : ∀ᵐ p ∂ν, DifferentiableAt ℝ ψ p.2 ∧ DifferentiableAt ℝ r p ∧ r p ≠ 0 := by
    filter_upwards [hmem] with p hp
    have hpS : p ∈ D.regular ×ˢ Ω :=
      ⟨hreg ⟨ht₀.trans hp.1.1, hp.1.2.trans ht₁⟩, hsub hp.2⟩
    exact ⟨(hψ.contDiffAt (hΩ₀.mem_nhds hp.2)).differentiableAt (by simp),
      (hrall.contDiffAt ((D.regular_isOpen.prod hΩ).mem_nhds hpS)).differentiableAt (by simp),
      hrne p hpS⟩
  have hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, (σ p * V p) * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, C p * φ p ∂ν := by
    intro φ hφ hφc hφs
    have hφrs : tsupport (fun z => φ z / r z) ⊆ Ioo t₀ t₁ ×ˢ Ω₀ := by
      simpa only [div_eq_mul_inv] using
        (tsupport_mul_subset_left (f := φ) (g := fun z => (r z)⁻¹)).trans hφs
    have hφr : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z / r z) :=
      (hφ.contDiffOn.div hr (fun p hp => hrne p (hSsub hp))).contDiff_of_tsupport_subset
        (isOpen_Ioo.prod hΩ₀) hφrs
    have hφrc : HasCompactSupport (fun z => φ z / r z) := by
      exact hφc.isCompact.of_isClosed_subset (isClosed_tsupport _) (by
        simpa only [div_eq_mul_inv] using
          (tsupport_mul_subset_left (f := φ) (g := fun z => (r z)⁻¹)))
    have hdφ (j) : MemLp (fun p => fderiv ℝ (fun z => φ z / r z) p
        (0, EuclideanSpace.single j 1)) ∞ ν :=
      ((hφr.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hφrc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
    have hin (i j) : Integrable (fun p => A i j p * K i p *
        fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1)) ν :=
      ((hdφ j).mul (r := 2) ((Lp.memLp (K i)).mul (r := 2)
        (hAmem i j))).integrable (by norm_num)
    have heach (j) : (∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p
        (0, EuclideanSpace.single j 1) ∂ν) =
        ∑ i, ∫ p, A i j p * K i p *
          fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν := by
      simp only [P, Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => hin i j)
    simp_rw [heach]
    rw [Finset.sum_comm]
    exact hfixed φ hφ hφc hφs
  have he := integral_fixed_density_tensor_test (fun j => EuclideanSpace.single j 1)
    hΩ₀ hη hηc hηs hψ hgood hweak hτ hτc hτs hmain herr hsource
  simpa only [hQeq, hBeq] using he

theorem IsWeakEvolutionSolution.exists_timeH1_cutoff_hessian_dual_deriv
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T) (ht₀₁ : t₀ < t₁)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ K : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ S : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i j, H i j = H j i) ∧
      (∀ i j l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
        (fun z => K i j l (t, z)) (fun z => H i j (t, z)) Ω₀) ∧
      (∀ k i l, K k i l = K k l i) ∧
      (∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, S k l p * φ p ∂ν) ∧
      (∀ k l (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, σ p * H k l p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K k l i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * S k l p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * H k l p)) * φ p ∂ν) ∧
      let C := fun k l p => (r p)⁻¹ * S k l p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * H k l p)
      let Q := fun k l j p => ∑ i, (η p.2 / r p) * A i j p * K k l i p
      let B := fun k l p => η p.2 * C k l p -
        ∑ i, ∑ j, A i j p * K k l i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      (∀ k l j, MemLp (Q k l j) 2 ν) ∧ (∀ k l, MemLp (B k l) 2 ν) ∧
      ∃ v : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp (H1ComplDirichlet q) 2 μ,
        (∀ k l, ∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v k l t) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I_hs) (M := M) q]
            chartPullback I_hs α (fun z => η z * H k l (t, z))) ∧
        ∀ k l, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
          ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (t₁ - t₀),
            (∀ τ : Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
              (∫ t, τ t * ℓ t z ∂μ) =
                (∫ p, τ p.1 * B k l p * H1ComplDirichletToLp q z
                  ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
                ∑ j, ∫ p, τ p.1 * Q k l j p *
                  dirichletLocalWeakPartialLp q α hΩ₀
                    (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                    (hΩ₀Ω.trans (subset_closure.trans hΩs)) j z p.2 ∂ν) ∧
            (∀ᵐ s ∂timeMeasure (t₁ - t₀), ∀ z : H1ComplDirichlet q,
              w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v k l (t₀ + s)))
                (H1ComplDirichletToLp q z)) ∧
            w.deriv =ᵐ[timeMeasure (t₁ - t₀)] (fun s => ℓ (t₀ + s)) ∧
            ∀ ζ : timeH1 (H1ComplDirichlet q) (t₁ - t₀),
              ζ.toFun 0 = 0 → ζ.toFun (t₁ - t₀) = 0 →
              (∫ s, inner ℝ (H1ComplDirichletToLp q (v k l (t₀ + s)))
                (H1ComplDirichletToLp q (ζ.deriv s)) ∂timeMeasure (t₁ - t₀)) +
                (∫ s, ℓ (t₀ + s) (ζ.toFun s) ∂timeMeasure (t₁ - t₀)) = 0 := by
  intro μ ν ρ σ r A
  classical
  obtain ⟨H, K, S, hH, hHsym, hK, hKsym, hS, hfixed, hsource⟩ :=
    hu.exists_lp_cutoff_hessian_source_dual hXcont hacont α hΩ hΩc hΩs hXsmooth
      ht₀ ht₁ ht₀₁.le hΩ₀ hΩ₀Ω hη
  refine ⟨H, K, S, hH, hHsym, hK, hKsym, hS, hfixed, ?_⟩
  intro C Q B
  obtain ⟨hC, hP, hQ, hB, hdηr, hdual⟩ := hsource
  obtain ⟨v, hv, hmass⟩ := hu.exists_timeH1_cutoff_hessian_mass_dual hXcont hacont
    α hΩ hΩc hΩs hXsmooth ht₀ ht₁ ht₀₁ hΩ₀ hΩ₀Ω hη hηs H hH
  refine ⟨hQ, hB, v, hv, ?_⟩
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  intro k l
  obtain ⟨ℓ, hℓ⟩ := hdual k l
  obtain ⟨w, hw⟩ := hmass k l
  have hd : w.deriv =ᵐ[timeMeasure (t₁ - t₀)] fun s => ℓ (t₀ + s) :=
    cutoff_lp_dual_deriv α hΩ₀ hΩ₀c hΩ₀s hη hηs ht₀.le ht₁.le ht₀₁
      (H k l) (v k l) w ℓ (Q k l) (B k l) (hv k l) hw hℓ
      (integral_chart_cutoff_tensor_test hG hreg α hΩ hΩc hΩs ht₀.le ht₁.le hΩ₀ hΩ₀Ω
        hη hηs (H k l) (K k l) (C k l) (hC k l) (hP k l) (hQ k l) hdηr (hfixed k l))
  refine ⟨ℓ, w, hℓ, hw, hd, ?_⟩
  intro ζ hζ0 hζ1
  exact integral_timeH1_test_of_mass_dual ht₀₁.le
    ((innerSL ℝ).bilinearComp (H1ComplDirichletToLp q) (H1ComplDirichletToLp q))
    (fun t => v k l t) w (fun t => ℓ t) hw hd ζ hζ0 hζ1

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
