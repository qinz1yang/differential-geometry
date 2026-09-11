import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MixedWeakDerivative
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SpatialLowerSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SpatialCommutator
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationProduct
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorRegularity

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

section

variable {𝕜 Z E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem fderiv_prod_right {f : Z × E → F} {p : Z × E}
    (hf : DifferentiableAt 𝕜 f p) :
    fderiv 𝕜 (fun x => f (p.1, x)) p.2 =
      (fderiv 𝕜 f p).comp (ContinuousLinearMap.inr 𝕜 Z E) := by
  exact (hf.hasFDerivAt.comp p.2
    ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv

private theorem fderiv_prod_right_apply {f : Z × E → F} {p : Z × E}
    (hf : DifferentiableAt 𝕜 f p) (v : E) :
    fderiv 𝕜 (fun x => f (p.1, x)) p.2 v = fderiv 𝕜 f p (0, v) := by
  rw [fderiv_prod_right hf]
  rfl

end

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation
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
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
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
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν := by
  intro μ ν ρ A U V
  classical
  obtain ⟨R, H, hR, hH, hHsym, hcomm⟩ :=
    hu.exists_lp_weak_gradient_commutator hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  have hρall : ContDiffOn ℝ (⊤ : ℕ∞) ρ (D.regular ×ˢ Ω) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (Set.prod_mono Subset.rfl (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hAall (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ Ω) :=
    MetricExtension.weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α
      (subset_closure.trans hΩs) i j
  have hlift (f : ℝ × EuStd → ℝ) (hc : ContinuousOn f (D.regular ×ˢ Ω)) : MemLp f ∞ ν := by
    have hb := (hc.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hAmem (i j) : MemLp (A i j) ∞ ν := hlift _ (hAall i j).continuousOn
  have hmem : ∀ᵐ p ∂ν, p ∈ Icc (0 : ℝ) T ×ˢ Ω₀ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ₀.measurableSet)).mpr
    filter_upwards [ae_restrict_of_ae (s := Icc t₀ t₁)
      (ae_restrict_mem measurableSet_Icc : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) T)] with t ht
    exact (ae_restrict_mem hΩ₀.measurableSet).mono fun z hz => ⟨ht, hz⟩
  have hex (k : Fin (Module.finrank ℝ EuN)) : ∃ F : Lp ℝ 2 ν,
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F p * φ p ∂ν := by
    obtain ⟨Fdiv, hFdiv⟩ := hu.exists_lp_divergence_coefficient_fderiv_localWeakPartial
      hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω k
    obtain ⟨Flower, hFlower⟩ := hu.exists_lp_weakPartial_localLowerSource
      hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω k
    let Dρ := fun p => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let DDρ := fun p => fderiv ℝ Dρ p (1, 0)
    have hDρc : ContDiffOn ℝ (⊤ : ℕ∞) Dρ (D.regular ×ˢ Ω) :=
      (hρall.fderiv_of_isOpen (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
    have hDDρc : ContDiffOn ℝ (⊤ : ℕ∞) DDρ (D.regular ×ˢ Ω) :=
      (hDρc.fderiv_of_isOpen (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
    have hDρ := hlift _ hDρc.continuousOn
    have hDDρ := hlift _ hDDρc.continuousOn
    let C := fun p => Dρ p * R p + DDρ p * U p
    have hC : MemLp C 2 ν := ((Lp.memLp R).mul hDρ).add (hU.mul hDDρ)
    let f := fun p => Fdiv p + Flower p - C p
    have hf : MemLp f 2 ν := ((Lp.memLp Fdiv).add (Lp.memLp Flower)).sub hC
    refine ⟨hf.toLp f, ?_⟩
    intro φ hφ hφc hφs
    have hφu := hφs.trans (Set.prod_mono (subset_univ _) Subset.rfl)
    have hb := hcomm k φ hφ hφc hφs
    have hlower := hFlower φ hφ hφc hφu
    have hdiv := hFdiv φ hφ hφc hφu
    have hdiv' : (∑ i, ∑ j, ∫ p, fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) = -(∫ p, Fdiv p * φ p ∂ν) := by
      rw [hdiv, neg_neg]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [hmem] with p hp
      have hpa : p ∈ D.regular ×ˢ Ω := ⟨hreg hp.1, hsub hp.2⟩
      have hdiff : DifferentiableAt ℝ (A i j) p :=
        ((hAall i j).contDiffAt ((D.regular_isOpen.prod hΩ).mem_nhds hpa)).differentiableAt (by simp)
      rw [← fderiv_prod_right_apply hdiff]
    have hDAmem (i j) : MemLp (fun p => fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1)) ∞ ν :=
      hlift _ (((hAall i j).fderiv_of_isOpen (m := (⊤ : ℕ∞)) (D.regular_isOpen.prod hΩ)
        (by simp)).clm_apply contDiffOn_const).continuousOn
    have hdmem (j) : MemLp (fun p => fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ∞ ν :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1)) ν
    have hmainI (i j) : Integrable (fun p => A i j p * H k i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
      ((hdmem j).mul (r := 2) ((Lp.memLp (H k i)).mul (r := 2) (hAmem i j))).integrable (by norm_num)
    have herrorI (i j) : Integrable (fun p => fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν :=
      ((hdmem j).mul (r := 2) ((hV i).mul (r := 2) (hDAmem i j))).integrable (by norm_num)
    have hsplit (i j) : (∫ p, (A i j p * H k i p +
        fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
        (∫ p, A i j p * H k i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
        ∫ p, fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
      simp_rw [add_mul]
      exact integral_add (hmainI i j) (herrorI i j)
    have hsum' : (∑ i, ∑ j, ∫ p, (A i j p * H k i p +
        fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p) *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) =
        (∑ i, ∑ j, ∫ p, A i j p * H k i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
        (∑ i, ∑ j, ∫ p, fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p *
          fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) := by
      calc
        _ = ∑ i, ∑ j, ((∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) +
            ∫ p, fderiv ℝ (A i j) p (0, EuclideanSpace.single k 1) * V i p *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hsplit i j
        _ = _ := by
          simp_rw [Finset.sum_add_distrib]
    have hφLp : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hφc ν
    have hint (g : ℝ × EuStd → ℝ) (hg : MemLp g 2 ν) : Integrable (fun p => g p * φ p) ν :=
      (hφLp.mul (r := 2) hg).integrable (by norm_num)
    have hFeq : (∫ p, (hf.toLp f) p * φ p ∂ν) =
        (∫ p, Fdiv p * φ p ∂ν) + (∫ p, Flower p * φ p ∂ν) - ∫ p, C p * φ p ∂ν := by
      have hc : (∫ p, (hf.toLp f) p * φ p ∂ν) = ∫ p, f p * φ p ∂ν := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with p hp
        rw [hp]
      rw [hc]
      have hsumint : Integrable (fun p => Fdiv p * φ p + Flower p * φ p) ν :=
        (hint _ (Lp.memLp Fdiv)).add (hint _ (Lp.memLp Flower))
      have hsubint : Integrable (fun p => Fdiv p * φ p + Flower p * φ p - C p * φ p) ν :=
        hsumint.sub (hint _ hC)
      simp only [f, sub_mul, add_mul]
      rw [integral_sub hsumint (hint _ hC), integral_add (hint _ (Lp.memLp Fdiv)) (hint _ (Lp.memLp Flower))]
    change (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) = _
    linarith [hb, hsum', hdiv', hlower, hFeq]
  choose F hF using hex
  exact ⟨R, H, F, hR, hH, hHsym, hF⟩

theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation_fixed_density
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
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
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
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, σ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1) ∂ν) -
          ∫ p, ((r p)⁻¹ * F k p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) *
            (σ p * V k p)) * φ p ∂ν := by
  intro μ ν ρ σ r A U V
  classical
  obtain ⟨R, H, F, hR, hH, hHsym, hF⟩ :=
    hu.exists_lp_weak_gradient_equation hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω
  refine ⟨R, H, F, hR, hH, hHsym, hF, ?_⟩
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hchart : Ω ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    subset_closure.trans (hΩs.trans (image_mono interior_subset))
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  let : IsFiniteMeasure (volume.restrict Ω₀) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩ₀c.measure_lt_top
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
  have hσmem : MemLp σ ∞ ν := by
    have hb := (hσall.continuousOn.mono (prod_mono hreg hΩ₀Ω)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩ₀c) (measurableSet_Icc.prod hΩ₀.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hSsub : Ioo t₀ t₁ ×ˢ Ω₀ ⊆ D.regular ×ˢ Ω := by
    intro p hp
    exact ⟨hreg ⟨ht₀.le.trans hp.1.1.le, hp.1.2.le.trans ht₁.le⟩, hsub hp.2⟩
  have hr : ContDiffOn ℝ (⊤ : ℕ∞) r (Ioo t₀ t₁ ×ˢ Ω₀) :=
    ((hρall.div hσall (fun p hp => hσne p hp.2)).mono hSsub)
  have hrne (p : ℝ × EuStd) (hp : p ∈ Ioo t₀ t₁ ×ˢ Ω₀) : r p ≠ 0 :=
    div_ne_zero (hρne p (hsub hp.2)) (hσne p (hsub hp.2))
  have hmem : ∀ᵐ p ∂ν, p.2 ∈ Ω₀ := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd hΩ₀.measurableSet)).mpr
    exact ae_of_all μ (fun _ => ae_restrict_mem hΩ₀.measurableSet)
  intro k φ hφ hφc hφs
  have hW : LocallyIntegrable (fun p => σ p * V k p) ν :=
    (((hV k).mul (r := 2) hσmem).integrable (by norm_num)).locallyIntegrable
  have hFlocal : LocallyIntegrable (F k) ν :=
    ((Lp.memLp (F k)).integrable (by norm_num)).locallyIntegrable
  let L : ((ℝ × EuStd) → ℝ) → ℝ := fun ψ =>
    ∑ i, ∑ j, ∫ p, A i j p * H k i p * fderiv ℝ ψ p (0, EuclideanSpace.single j 1) ∂ν
  apply DifferentialGeometry.Analysis.Sobolev.integral_fderiv_eq_of_weighted_identity
    (isOpen_Ioo.prod hΩ₀) (1, 0) hW hFlocal hr hrne L
  · intro ψ hψ hψc hψs
    have heq : (∫ p, r p * (σ p * V k p) * fderiv ℝ ψ p (1, 0) ∂ν) =
        ∫ p, ρ p * V k p * fderiv ℝ ψ p (1, 0) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hmem] with p hp
      dsimp only [r]
      field_simp [hσne p (hsub hp)]
    rw [heq]
    exact hF k ψ hψ hψc hψs
  · exact hφ
  · exact hφc
  · exact hφs

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
