import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientSourceDual
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import DifferentialGeometry.Analysis.Parabolic.WeakEquationTensor

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

private theorem integrable_tensor_mul_lp
    {Z E : Type*} [MeasurableSpace Z] [MeasurableSpace E]
    {μ : Measure Z} {ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {τ : Z → ℝ} {ψ : E → ℝ} {c F : Z × E → ℝ}
    (hτ : MemLp τ ∞ μ) (hψ : MemLp ψ ∞ ν)
    (hc : MemLp c ∞ (μ.prod ν)) (hF : MemLp F 2 (μ.prod ν)) :
    Integrable (fun p => τ p.1 * (c p * F p) * ψ p.2) (μ.prod ν) := by
  have hτp := hτ.comp_fst ν
  have hψp := hψ.comp_snd μ
  have hm : MemLp (fun p => τ p.1 * (c p * F p) * ψ p.2) 2 (μ.prod ν) := by
    exact hψp.mul (r := 2) ((hF.mul (r := 2) hc).mul (r := 2) hτp)
  exact hm.integrable (by norm_num)

private theorem integrable_fixed_density_tensor_terms
    {d : ℕ} {μ : Measure ℝ} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {τ : ℝ → ℝ} {η ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {r C : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {P : Fin d → ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hτ : MemLp τ ∞ μ) (hψ : MemLp ψ ∞ ν)
    (hdψ : ∀ j, MemLp (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) ∞ ν)
    (hη : MemLp η ∞ ν)
    (hηr : MemLp (fun p => η p.2 / r p) ∞ (μ.prod ν))
    (hdηr : ∀ j, MemLp (fun p => fderiv ℝ (fun z => η z.2 / r z) p
      (0, EuclideanSpace.single j 1)) ∞ (μ.prod ν))
    (hC : MemLp C 2 (μ.prod ν)) (hP : ∀ j, MemLp (P j) 2 (μ.prod ν)) :
    (∀ j, Integrable (fun p => τ p.1 * ((η p.2 / r p) * P j p) *
      fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) (μ.prod ν)) ∧
    (∀ j, Integrable (fun p => τ p.1 * (P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) * ψ p.2) (μ.prod ν)) ∧
    Integrable (fun p => τ p.1 * (η p.2 * C p) * ψ p.2) (μ.prod ν) := by
  refine ⟨fun j => integrable_tensor_mul_lp hτ (hdψ j) hηr (hP j), ?_,
    integrable_tensor_mul_lp hτ hψ (hη.comp_snd μ) hC⟩
  intro j
  simpa only [mul_comm (P j _) (fderiv ℝ (fun z => η z.2 / r z) _
    (0, EuclideanSpace.single j 1))] using
    integrable_tensor_mul_lp hτ hψ (hdηr j) (hP j)

open Bundle Manifold
open scoped ContDiff Manifold NNReal

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

omit [T2Space M] [CompactSpace M] in
private theorem smoothScalarDirichlet_chartInverse_bounds
    {q : SmoothRiemannianMetric I_hs M}
    (α : M) {Ω : Set EuStd} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : SmoothScalarDirichlet q) :
    let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω ∧ MemLp ψ ∞ (volume.restrict Ω) ∧
      ∀ j : Fin (Module.finrank ℝ EuN),
        MemLp (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) ∞ (volume.restrict Ω) := by
  intro ψ
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) ψ U := by
    apply (scalarOnE_contDiffOn α v.smooth).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  refine ⟨hP.mono (subset_closure.trans hΩs),
    (hP.continuousOn.mono hΩs).memLp_top_of_subset_isCompact hΩc hΩ subset_closure, ?_⟩
  intro j
  have hc := (((hP.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (g := fun _ => EuclideanSpace.single j 1) contDiffOn_const).continuousOn).mono hΩs
  exact hc.memLp_top_of_subset_isCompact hΩc hΩ subset_closure

theorem IsWeakEvolutionSolution.exists_lp_cutoff_gradient_tensor_identity
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
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω₀) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν) ∧
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, σ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * V k p)) * φ p ∂ν) ∧
      let C := fun k p => (r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * V k p)
      let Q := fun k j p => ∑ i, (η p.2 / r p) * A i j p * H k i p
      let B := fun k p => η p.2 * C k p -
        ∑ i, ∑ j, A i j p * H k i p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
      (∀ k j, MemLp (Q k j) 2 ν) ∧ (∀ k, MemLp (B k) 2 ν) ∧
      (∀ k, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∀ τ : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t v ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j v p.2 ∂ν) ∧
      ∀ k (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) τ → HasCompactSupport τ → tsupport τ ⊆ Ioo t₀ t₁ →
        let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (∫ p, deriv τ p.1 * (η p.2 * (σ p * V k p)) * ψ p.2 ∂ν) =
          (∑ j, ∫ p, τ p.1 * Q k j p *
            fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
          ∫ p, τ p.1 * B k p * ψ p.2 ∂ν := by
  intro μ ν ρ σ r A U V
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hF, hfixed, hsource⟩ :=
    hu.exists_lp_cutoff_gradient_source_dual hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω hη
  refine ⟨R, H, F, hR, hH, hHsym, hF, hfixed, ?_⟩
  intro C Q B
  obtain ⟨hQ, hB, hdual⟩ := hsource
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (k) : MemLp (V k) 2 ν := (Lp.memLp (V k)).mono_measure hmeasure
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
  have hAall (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ Ω) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α
      (subset_closure.trans hΩs) i j
  have hηall : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × EuStd => η p.2) (D.regular ×ˢ Ω) :=
    (hη.comp contDiff_snd).contDiffOn
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : MemLp f ∞ ν := by
    have hb := (hc.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hrinv : MemLp (fun p => (r p)⁻¹) ∞ ν := hlift _ (hrall.inv hrne).continuousOn
  have hrt : MemLp (fun p => fderiv ℝ r p (1, 0)) ∞ ν :=
    hlift _ ((hrall.fderiv_of_isOpen (m := (⊤ : ℕ∞)) (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hσmem : MemLp σ ∞ ν := hlift _ hσall.continuousOn
  have hηmem : MemLp (fun p : ℝ × EuStd => η p.2) ∞ ν := hlift _ hηall.continuousOn
  have hAmem (i j) : MemLp (A i j) ∞ ν := hlift _ (hAall i j).continuousOn
  have hC (k) : MemLp (C k) 2 ν :=
    ((Lp.memLp (F k)).mul (r := 2) hrinv).sub (((hV k).mul (r := 2) hσmem).mul (r := 2) (hrt.mul (r := ∞) hrinv))
  have hdηr (j) : MemLp (fun p => fderiv ℝ (fun z : ℝ × EuStd => η z.2 / r z) p
      (0, EuclideanSpace.single j 1)) ∞ ν :=
    hlift _ (((hηall.div hrall hrne).fderiv_of_isOpen (m := (⊤ : ℕ∞)) (D.regular_isOpen.prod hΩ)
      (by simp)).clm_apply contDiffOn_const).continuousOn
  refine ⟨hQ, hB, hdual, ?_⟩
  intro k v τ hτ hτc hτs ψ
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let P := fun j p => ∑ i, A i j p * H k i p
  have hP (j) : MemLp (P j) 2 ν := by
    apply memLp_finsetSum
    intro i _
    exact (Lp.memLp (H k i)).mul (r := 2) (hAmem i j)
  obtain ⟨hψ, hψmem, hdψmem⟩ :=
    smoothScalarDirichlet_chartInverse_bounds α hΩ₀.measurableSet hΩ₀c hΩ₀s v
  have hηr : MemLp (fun p => η p.2 / r p) ∞ ν := by
    convert hrinv.mul (r := ∞) hηmem using 1
    ext p
    simp only [div_eq_mul_inv, Pi.mul_apply]
  have hτmem : MemLp τ ∞ μ := hτ.continuous.memLp_top_of_hasCompactSupport hτc μ
  have hηsp : MemLp η ∞ (volume.restrict Ω₀) :=
    hη.continuous.memLp_top_of_hasCompactSupport hηc _
  obtain ⟨hmain, herr, hsource⟩ := integrable_fixed_density_tensor_terms
    hτmem hψmem hdψmem hηsp hηr hdηr (hC k) hP
  have hmem : ∀ᵐ p ∂ν, p.1 ∈ Icc t₀ t₁ ∧ p.2 ∈ Ω₀ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ₀.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    filter_upwards [ae_restrict_mem hΩ₀.measurableSet] with z hz
    exact ⟨ht, hz⟩
  have hgood : ∀ᵐ p ∂ν, DifferentiableAt ℝ ψ p.2 ∧ DifferentiableAt ℝ r p ∧ r p ≠ 0 := by
    filter_upwards [hmem] with p hp
    have hpS : p ∈ D.regular ×ˢ Ω :=
      ⟨hreg ⟨ht₀.le.trans hp.1.1, hp.1.2.trans ht₁.le⟩, hsub hp.2⟩
    exact ⟨(hψ.contDiffAt (hΩ₀.mem_nhds hp.2)).differentiableAt (by simp),
      (hrall.contDiffAt ((D.regular_isOpen.prod hΩ).mem_nhds hpS)).differentiableAt (by simp),
      hrne p hpS⟩
  have hSsub : Ioo t₀ t₁ ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg ⟨ht₀.le.trans hp.1.1.le, hp.1.2.le.trans ht₁.le⟩, hsub hp.2⟩
  have hr := hrall.mono hSsub
  have hw : ∀ ψ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
      (∫ p, (σ p * V k p) * fderiv ℝ ψ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => ψ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, C k p * ψ p ∂ν := by
    intro ψ hψ hψc hψs
    have hψrs : tsupport (fun z => ψ z / r z) ⊆ Ioo t₀ t₁ ×ˢ Ω₀ := by
      simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun z => (r z)⁻¹)).trans hψs
    have hψr : ContDiff ℝ (⊤ : ℕ∞) (fun z => ψ z / r z) :=
      (hψ.contDiffOn.div hr (fun p hp => hrne p (hSsub hp))).contDiff_of_tsupport_subset
        (isOpen_Ioo.prod hΩ₀) hψrs
    have hψrc : HasCompactSupport (fun z => ψ z / r z) := by
      exact hψc.isCompact.of_isClosed_subset (isClosed_tsupport _) (by
        simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun z => (r z)⁻¹)))
    have hdψ (j) : MemLp (fun p => fderiv ℝ (fun z => ψ z / r z) p (0, EuclideanSpace.single j 1)) ∞ ν :=
      ((hψr.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hψrc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
    have hin (i j) : Integrable (fun p => A i j p * H k i p *
        fderiv ℝ (fun z => ψ z / r z) p (0, EuclideanSpace.single j 1)) ν :=
      (((hdψ j).mul (r := 2) ((Lp.memLp (H k i)).mul (r := 2) (hAmem i j))).integrable (by norm_num))
    have heach (j) : (∫ p, P j p * fderiv ℝ (fun z => ψ z / r z) p
        (0, EuclideanSpace.single j 1) ∂ν) =
        ∑ i, ∫ p, A i j p * H k i p * fderiv ℝ (fun z => ψ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν := by
      simp only [P, Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => hin i j)
    simp_rw [heach]
    rw [Finset.sum_comm]
    exact hfixed k ψ hψ hψc hψs
  have he := integral_fixed_density_tensor_test (fun j => EuclideanSpace.single j 1)
    hΩ₀ hη hηc hηs hψ hgood hw hτ hτc hτs hmain herr hsource
  have hQeq (j) (p : ℝ × EuStd) : (η p.2 / r p) * P j p = Q k j p := by
    simp only [P, Q, Finset.mul_sum, mul_assoc]
  have hBeq (p : ℝ × EuStd) : (η p.2 * C k p - ∑ j, P j p * fderiv ℝ
      (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) = B k p := by
    simp only [P, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  simpa only [hQeq, hBeq] using he

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
