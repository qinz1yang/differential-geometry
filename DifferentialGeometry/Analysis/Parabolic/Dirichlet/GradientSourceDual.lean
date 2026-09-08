import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SpatialGradientEquation
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientH1

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private theorem exists_lp_chart_source_sub_divergence_dual
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} {B : ℝ × EuStd → ℝ} {Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (hB : MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hQ : ∀ j, MemLp (Q j) 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ, ∀ τ : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
      (∫ t, τ t * ℓ t v ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2
          ∂μ.prod (volume.restrict Ω) := by
  obtain ⟨Ls, hLs⟩ := exists_lp_chart_source_dual α hΩ hΩc hΩs (hB.toLp B)
  obtain ⟨Ld, hLd⟩ := exists_lp_chart_divergence_dual α hΩ hΩc hΩs
    (fun j => (hQ j).toLp (Q j))
  refine ⟨Ls - Ld, ?_⟩
  intro τ v
  have hints : Integrable (fun t => τ t * Ls t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Ls)
  have hintd : Integrable (fun t => τ t * Ld t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Ld)
  calc
    (∫ t, τ t * (Ls - Ld) t v ∂μ) =
        (∫ t, τ t * Ls t v ∂μ) - ∫ t, τ t * Ld t v ∂μ := by
      rw [← integral_sub hints hintd]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub Ls Ld] with t ht
      rw [ht]
      change τ t * (Ls t v - Ld t v) = _
      ring
    _ = _ := by
      rw [hLs, hLd]
      apply congrArg₂ (fun a b : ℝ => a - b)
      · apply integral_congr_ae
        filter_upwards [hB.coeFn_toLp] with p hp
        rw [hp]
      · apply Finset.sum_congr rfl
        intro j _
        apply integral_congr_ae
        filter_upwards [(hQ j).coeFn_toLp] with p hp
        rw [hp]


theorem IsWeakEvolutionSolution.exists_lp_cutoff_gradient_source_dual
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
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
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
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
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
      ∀ k, ∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
        ∀ τ : Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
          (∫ t, τ t * ℓ t v ∂μ) =
            (∫ p, τ p.1 * B k p * H1ComplDirichletToLp q v
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
            ∑ j, ∫ p, τ p.1 * Q k j p *
              dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) j v p.2 ∂ν := by
  intro μ ν ρ σ r A U V
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hF, hfixed⟩ :=
    hu.exists_lp_weak_gradient_equation_fixed_density hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨R, H, F, hR, hH, hHsym, hF, hfixed, ?_⟩
  intro C Q B
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
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
  have hQ (k j) : MemLp (Q k j) 2 ν := by
    apply memLp_finsetSum
    intro i _
    convert (Lp.memLp (H k i)).mul (r := 2) ((hAmem i j).mul (r := ∞) (hrinv.mul (r := ∞) hηmem)) using 1
    ext p
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hdηr (j) : MemLp (fun p => fderiv ℝ (fun z : ℝ × EuStd => η z.2 / r z) p
      (0, EuclideanSpace.single j 1)) ∞ ν :=
    hlift _ (((hηall.div hrall hrne).fderiv_of_isOpen (m := (⊤ : ℕ∞)) (D.regular_isOpen.prod hΩ)
      (by simp)).clm_apply contDiffOn_const).continuousOn
  have hB (k) : MemLp (B k) 2 ν := by
    apply ((hC k).mul hηmem).sub
    apply memLp_finsetSum
    intro i _
    apply memLp_finsetSum
    intro j _
    exact (hdηr j).mul (r := 2) ((Lp.memLp (H k i)).mul (r := 2) (hAmem i j))
  refine ⟨hQ, hB, ?_⟩
  intro k
  exact exists_lp_chart_source_sub_divergence_dual α hΩ₀ hΩ₀c hΩ₀s (hB k) (hQ k)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
