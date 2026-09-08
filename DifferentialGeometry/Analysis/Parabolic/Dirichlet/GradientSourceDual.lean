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

private theorem fderiv_spatial_cutoff_mul
    {d : ℕ} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    {φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : Differentiable ℝ η) (hφ : Differentiable ℝ φ)
    (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun z => η z.2 * φ z) p (1, 0) = η p.2 * fderiv ℝ φ p (1, 0) := by
  have h := (((hη p.2).hasFDerivAt).comp p hasFDerivAt_snd).mul ((hφ p).hasFDerivAt)
  change fderiv ℝ (η ∘ Prod.snd * φ) p (1, 0) = _
  rw [h.fderiv]
  simp

private theorem integral_cutoff_weak_equation
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {a b : ℝ}
    (hΩ : IsOpen Ω) {ν : Measure (ℝ × EuclideanSpace ℝ (Fin d))}
    {r W C : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {P : Fin d → ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hr : ContDiffOn ℝ (⊤ : ℕ∞) r (Ioo a b ×ˢ Ω))
    (hrne : ∀ p ∈ Ioo a b ×ˢ Ω, r p ≠ 0)
    (hC : LocallyIntegrable (fun p => η p.2 * C p) ν)
    (hQ : ∀ j, LocallyIntegrable (fun p => (η p.2 / r p) * P j p) ν)
    (hB : ∀ j, LocallyIntegrable (fun p => P j p * fderiv ℝ
      (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) ν)
    (hweak : ∀ (φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, W p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p
          (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, C p * φ p ∂ν)
    (φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
    (∫ p, η p.2 * W p * fderiv ℝ φ p (1, 0) ∂ν) =
      (∑ j, ∫ p, ((η p.2 / r p) * P j p) * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
      ∫ p, (η p.2 * C p - ∑ j, P j p * fderiv ℝ (fun z => η z.2 / r z) p
        (0, EuclideanSpace.single j 1)) * φ p ∂ν := by
  classical
  let f := fun z : ℝ × EuclideanSpace ℝ (Fin d) => η z.2 / r z
  have hfs : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo a b ×ˢ Ω) :=
    (hη.comp contDiff_snd).contDiffOn.div hr hrne
  have hd (p : ℝ × EuclideanSpace ℝ (Fin d)) (j) :
      fderiv ℝ (fun z => η z.2 * φ z / r z) p (0, EuclideanSpace.single j 1) =
        f p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) +
          fderiv ℝ f p (0, EuclideanSpace.single j 1) * φ p := by
    have heq : (fun z => η z.2 * φ z / r z) = fun z => f z * φ z := by
      funext z
      dsimp [f]
      ring
    rw [heq]
    by_cases hp : p ∈ tsupport φ
    · have hf := (hfs.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds (hφs hp))).differentiableAt (by simp)
      change fderiv ℝ (f * φ) p (0, EuclideanSpace.single j 1) = _
      rw [(hf.hasFDerivAt.mul ((hφ.differentiable (by simp)) p).hasFDerivAt).fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · have he := image_eq_zero_of_notMem_tsupport hp
      have heφ : fderiv ℝ φ p = 0 := fderiv_of_notMem_tsupport ℝ hp
      have hp' : p ∉ tsupport (fun z => f z * φ z) := fun h => hp (tsupport_mul_subset_right h)
      rw [fderiv_of_notMem_tsupport ℝ hp', he, heφ]
      simp
  have hmain (j) : Integrable (fun p => (f p * P j p) * fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
    (hQ j).integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1))
  have herr (j) : Integrable (fun p => (P j p * fderiv ℝ f p (0, EuclideanSpace.single j 1)) * φ p) ν :=
    (hB j).integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hc : Integrable (fun p => (η p.2 * C p) * φ p) ν :=
    hC.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have heach (j) : (∫ p, P j p * fderiv ℝ (fun z => η z.2 * φ z / r z) p
      (0, EuclideanSpace.single j 1) ∂ν) =
      (∫ p, (f p * P j p) * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
      ∫ p, (P j p * fderiv ℝ f p (0, EuclideanSpace.single j 1)) * φ p ∂ν := by
    rw [← integral_add (hmain j) (herr j)]
    apply integral_congr_ae
    filter_upwards with p
    rw [hd]
    ring
  have hw := hweak (fun z => η z.2 * φ z) ((hη.comp contDiff_snd).mul hφ)
    hφc.mul_left (tsupport_mul_subset_right.trans hφs)
  have hleft : (∫ p, W p * fderiv ℝ (fun z => η z.2 * φ z) p (1, 0) ∂ν) =
      ∫ p, η p.2 * W p * fderiv ℝ φ p (1, 0) ∂ν := by
    apply integral_congr_ae
    filter_upwards with p
    rw [fderiv_spatial_cutoff_mul (hη.differentiable (by simp)) (hφ.differentiable (by simp))]
    ring
  have hsource : (∫ p, C p * (η p.2 * φ p) ∂ν) = ∫ p, (η p.2 * C p) * φ p ∂ν := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hs : (∫ p, (η p.2 * C p - ∑ j, P j p * fderiv ℝ f p
      (0, EuclideanSpace.single j 1)) * φ p ∂ν) =
      (∫ p, (η p.2 * C p) * φ p ∂ν) - ∑ j, ∫ p, (P j p * fderiv ℝ f p
      (0, EuclideanSpace.single j 1)) * φ p ∂ν := by
    simp_rw [sub_mul, Finset.sum_mul]
    rw [integral_sub hc (integrable_finsetSum _ (fun j _ => herr j)), integral_finsetSum _ (fun j _ => herr j)]
  rw [hleft, hsource] at hw
  simp_rw [heach, Finset.sum_add_distrib] at hw
  rw [hs]
  linarith


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

theorem IsWeakEvolutionSolution.exists_lp_cutoff_gradient_weak_equation
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
      (∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, η p.2 * (σ p * V k p) * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ j, ∫ p, Q k j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, B k p * φ p ∂ν) ∧
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
  refine ⟨hQ, hB, ?_, ?_⟩
  · intro k φ hφ hφc hφs
    let : IsFiniteMeasure (volume.restrict Ω₀) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
    let P := fun j p => ∑ i, A i j p * H k i p
    have hP (j) : MemLp (P j) 2 ν := by
      apply memLp_finsetSum
      intro i _
      exact (Lp.memLp (H k i)).mul (r := 2) (hAmem i j)
    have hSsub : Ioo t₀ t₁ ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω := by
      intro p hp
      exact ⟨hreg ⟨ht₀.le.trans hp.1.1.le, hp.1.2.le.trans ht₁.le⟩, hsub hp.2⟩
    have hr := hrall.mono hSsub
    have hpQ (j) : LocallyIntegrable (fun p => η p.2 / r p * P j p) ν := by
      have hm : MemLp (fun p => η p.2 / r p * P j p) 2 ν := by
        convert (hP j).mul (r := 2) (hrinv.mul (r := ∞) hηmem) using 1
        ext p
        simp [div_eq_mul_inv]
      exact (hm.integrable (by norm_num)).locallyIntegrable
    have hpB (j) : LocallyIntegrable (fun p => P j p * fderiv ℝ
        (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) ν :=
      (((hdηr j).mul (r := 2) (hP j)).integrable (by norm_num)).locallyIntegrable
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
    have he := integral_cutoff_weak_equation hΩ₀ hη hr (fun p hp => hrne p (hSsub hp))
      ((((hC k).mul (r := 2) hηmem).integrable (by norm_num)).locallyIntegrable) hpQ hpB hw
      φ hφ hφc hφs
    have hQeq (j) (p : ℝ × EuStd) : (η p.2 / r p) * P j p = Q k j p := by
      simp only [P, Q, Finset.mul_sum, mul_assoc]
    have hBeq (p : ℝ × EuStd) : (η p.2 * C k p - ∑ j, P j p * fderiv ℝ
        (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) = B k p := by
      simp only [P, B, Finset.sum_mul]
      rw [Finset.sum_comm]
    simpa only [hQeq, hBeq] using he
  · exact hdual

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
