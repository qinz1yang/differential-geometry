import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialLinearSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SourceFormula
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SpatialLowerSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SpatialCommutator

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

private theorem ae_lower_source_of_weak_derivatives
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    {t₀ t₁ : ℝ} {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let ρ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid (I := I_hs) (G.metric p.1) α p.2
    let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    ∀ (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ (k : Fin (Module.finrank ℝ EuN)) (Flower : Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, ((∑ i, C i p * V i p) + C₀ p * U p) *
          fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν) = -∫ p, Flower p * φ p ∂ν) →
      Flower =ᵐ[ν] fun p =>
        (∑ i, (C i p * H i k p +
          fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1) * V i p)) +
          (C₀ p * V k p +
            fderiv ℝ (fun x => C₀ (p.1, x)) p.2 (EuclideanSpace.single k 1) * U p) := by
  intro μ ν ρ U V B τ C C₀ H hH k Flower hFlower
  classical
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  let W := fun i => (hV i).toLp (V i)
  let U₀ := hU.toLp U
  have hW (i) : W i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hU₀ : U₀ =ᵐ[ν] U := hU.coeFn_toLp
  have hWweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => W i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hW i), hc] with t ht hwt hct
    have he : (fun x => W i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  have hU₀weak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => W k (t, x)) (fun x => U₀ (t, x)) Ω₀ := by
    have ht := ae_restrict_of_ae (s := Icc t₀ t₁)
      (hasWeakPartialDeriv_dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u)
    filter_upwards [ht, Measure.ae_ae_of_ae_prod hU₀,
      Measure.ae_ae_of_ae_prod (hW k)] with t ht hut hwt
    have hweak := ht.restrict hΩ₀ hsub
    intro φ hφ hφc hφs
    calc
      _ = ∫ x in Ω₀, U (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
        apply integral_congr_ae
        filter_upwards [hut] with x hx
        rw [hx]
      _ = -(∫ x in Ω₀, V k (t, x) * φ x) := hweak φ hφ hφc hφs
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hwt] with x hx
        rw [hx]
  have hΩ₀s := hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hρ : MemLp ρ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_family_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hB (i) : MemLp (B i) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top X isCompact_Icc
      measurableSet_Icc α (hXcont.mono (prod_mono Subset.rfl (subset_univ _)))
      hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) i (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hτ : MemLp τ ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c (hΩ₀s.trans (image_mono interior_subset)) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have ha : MemLp (fun p : ℝ × EuStd => a p.1) ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hc := hacont.comp continuousOn_fst (fun _ hp => hp.1 : MapsTo Prod.fst
      (Icc (0 : ℝ) T ×ˢ closure Ω₀) (Icc (0 : ℝ) T))
    have hb := hc.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩ₀c)
      (measurableSet_Icc.prod hΩ₀.measurableSet) (prod_mono Subset.rfl subset_closure)
      (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hC (i) : MemLp (C i) ∞ (μ.prod (volume.restrict Ω₀)) := (hB i).mul hρ
  have hC₀ : MemLp C₀ ∞ (μ.prod (volume.restrict Ω₀)) := ((hτ.const_mul (1 / 2 : ℝ)).sub ha).mul hρ
  have hDC (i) : MemLp (fun p => fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.densityOnEuclid_mul_chartCoeffOnE_family_fderiv_memLp_top hG isCompact_Icc
      hreg α X hXsmooth hΩ₀.measurableSet hΩ₀c hΩ₀s i (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDC₀ : MemLp (fun p => fderiv ℝ (fun x => C₀ (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω₀)) := by
    have hb := MetricExtension.potentialCoefficient_family_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c hΩ₀s hacont (EuclideanSpace.single k 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) T :=
    ae_restrict_of_ae (s := Icc t₀ t₁) (ae_restrict_mem measurableSet_Icc)
  have hρs : ContDiffOn ℝ ∞ ρ (D.regular ×ˢ Ω₀) :=
    (MetricExtension.densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset))))
  have hCs (i) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => C i (t, x)) Ω₀ := by
    have hBs := (MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α hXsmooth i).mono
      (prod_mono Subset.rfl (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset))))
    filter_upwards [hmem] with t ht
    exact (hρs.mul hBs).comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hreg ht, hy⟩)
  have hC₀s : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => C₀ (t, x)) Ω₀ := by
    have hτs := MetricExtension.traceTimeDerivMetric_comp_chartInverse_contDiffOn hG Subset.rfl α
      (subset_closure.trans hΩ₀s)
    filter_upwards [hmem] with t ht
    have hr := hρs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hreg ht, hy⟩)
    have hτt := hτs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hreg ht, hy⟩)
    exact hr.mul (((contDiffOn_const (c := (1 / 2 : ℝ))).mul hτt).sub (contDiffOn_const (c := a t)))
  have hFlowerFormula : Flower =ᵐ[ν] fun p =>
      (∑ i, (C i p * H i k p +
        fderiv ℝ (fun x => C i (p.1, x)) p.2 (EuclideanSpace.single k 1) * V i p)) +
        (C₀ p * V k p +
          fderiv ℝ (fun x => C₀ (p.1, x)) p.2 (EuclideanSpace.single k 1) * U p) := by
    have he := Sobolev.Euclidean.ae_eq_weak_partial_linear_source hΩ₀ (by norm_num) k
      U₀ W (fun i => H i k) hU₀weak (fun i => hWweak i k) C C₀
      hC hDC hCs hC₀ hDC₀ hC₀s (Flower := Flower) (by
        intro φ hφ hφc hφs
        calc
          _ = ∫ p, ((∑ i, C i p * V i p) + C₀ p * U p) *
              fderiv ℝ φ p (0, EuclideanSpace.single k 1) ∂ν := by
            apply integral_congr_ae
            filter_upwards [hU₀, ae_all_iff.mpr hW] with p hp hwp
            simp only [hp, hwp]
          _ = _ := hFlower φ hφ hφc hφs)
    filter_upwards [he, hU₀, ae_all_iff.mpr hW] with p hp hup hwp
    rw [hp]
    simp only [hup, hwp]
  exact hFlowerFormula

private theorem ae_divergence_source_of_weak_derivatives
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    {t₀ t₁ : ℝ} {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    let μ := (timeMeasure T).restrict (Icc t₀ t₁)
    let ν := μ.prod (volume.restrict Ω₀)
    let A := fun i j (p : ℝ × EuStd) =>
      MetricExtension.weightedInvGramOnEuclid (I := I_hs) (G.metric p.1) α i j p.2
    let V := fun i => dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) i u
    ∀ (H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H i j (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∀ (k : Fin (Module.finrank ℝ EuN)) (Fdiv : Lp ℝ 2 ν),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ univ ×ˢ Ω₀ →
        (∫ p, Fdiv p * φ p ∂ν) = -∑ i, ∑ j, ∫ p,
          fderiv ℝ (fun x => A i j (p.1,x)) p.2 (EuclideanSpace.single k 1) * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) →
      Fdiv =ᵐ[ν] fun p => ∑ i, ∑ j,
        (fderiv ℝ (fun z => A i j (p.1,z)) p.2 (EuclideanSpace.single k 1) * H i j p +
          fderiv ℝ (fun x => fderiv ℝ (fun z => A i j (p.1,z)) x
            (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p) := by
  intro μ ν A V H hH k Fdiv hFdiv
  classical
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hV (i) : MemLp (V i) 2 ν := (Lp.memLp (V i)).mono_measure hmeasure
  let W := fun i => (hV i).toLp (V i)
  have hW (i) : W i =ᵐ[ν] V i := (hV i).coeFn_toLp
  have hWweak (i j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (t, x)) (fun x => W i (t, x)) Ω₀ := by
    have hc := ae_restrict_of_ae (s := Icc t₀ t₁)
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) i u)
    filter_upwards [hH i j, Measure.ae_ae_of_ae_prod (hW i), hc] with t ht hwt hct
    have he : (fun x => W i (t, x)) =ᵐ[volume.restrict Ω₀]
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) :=
      Filter.EventuallyEq.trans hwt (ae_restrict_of_ae_restrict_of_subset hsub hct)
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae hΩ₀ j he.symm ht
  let DA := fun i j (p : ℝ × EuStd) =>
    fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1)
  have hDA (i j) : MemLp (DA i j) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_memLp_top hG isCompact_Icc hreg α
      hΩ₀.measurableSet hΩ₀c (hΩ₀Ω.trans (subset_closure.trans hΩs)) i j k (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDDA (i j) : MemLp
      (fun p => fderiv ℝ (fun x => DA i j (p.1, x)) p.2 (EuclideanSpace.single j 1)) ∞ ν := by
    have hb := MetricExtension.weightedInvGramOnEuclid_family_fderiv_fderiv_memLp_top hG isCompact_Icc
      hreg α hΩ₀.measurableSet hΩ₀c (hΩ₀Ω.trans (subset_closure.trans hΩs)) i j
      (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) (volume.prod volume)
    rw [← Measure.prod_restrict] at hb
    exact hb.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hDAsmooth (i j) : ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => DA i j (t, x)) Ω₀ := by
    apply Filter.Eventually.of_forall
    intro t
    have hc := (MetricExtension.weightedInvGramOnEuclid_contDiffOn (G.metric t) α i j).mono
      (hsub.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
    exact (hc.fderiv_of_isOpen hΩ₀ (by simp)).clm_apply contDiffOn_const
  have hFdivFormula : Fdiv =ᵐ[ν] fun p => ∑ i, ∑ j,
      (DA i j p * H i j p + fderiv ℝ (fun x => DA i j (p.1, x)) p.2
        (EuclideanSpace.single j 1) * V i p) := by
    have he := Sobolev.Euclidean.ae_eq_divergence_of_weak_partials
      isOpen_univ (Filter.Eventually.of_forall (fun _ => mem_univ _)) (by norm_num)
      hΩ₀ W H hDA hDDA hDAsmooth hWweak (F := Fdiv) (by
        intro φ hφ hφc hφs
        rw [hFdiv φ hφ hφc hφs]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply integral_congr_ae
        filter_upwards [hW i] with p hp
        rw [hp])
    filter_upwards [he, ae_all_iff.mpr hW] with p hp hwp
    rw [hp]
    simp only [hwp]
  exact hFdivFormula

theorem IsWeakEvolutionSolution.exists_lp_weak_gradient_equation_with_source_formula
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
    let B := fun i (p : ℝ × EuStd) =>
      DifferentialGeometry.Integral.DivergenceTheorem.chartCoeffOnE (I := I_hs) α (X p.1) i
        ((toEuclidean (E := EuN)).symm p.2)
    let τ := fun (p : ℝ × EuStd) => traceTimeDerivMetric (I := I_hs) G.metric p.1
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
    let C := fun i (p : ℝ × EuStd) => ρ p * B i p
    let C₀ := fun (p : ℝ × EuStd) => ρ p * ((1 / 2 : ℝ) * τ p - a p.1)
    ∃ R : Lp ℝ 2 ν, ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      ∃ F : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν) ∧
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t,z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) ∧
      (∀ i k, H i k = H k i) ∧
      (∀ k, (F k =ᵐ[ν] fun p =>
        (∑ i, ∑ j,
          (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
              (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
            C i p * H i k p)) +
          (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
          C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p)) ∧
      ∀ k (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F k p * φ p ∂ν := by
  intro μ ν ρ A U V B τ C C₀
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
      (F =ᵐ[ν] fun p =>
        (∑ i, ∑ j,
          (fderiv ℝ (fun z => A i j (p.1, z)) p.2 (EuclideanSpace.single k 1) * H i j p +
            fderiv ℝ (fun z => fderiv ℝ (fun y => A i j (p.1, y)) z
              (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single j 1) * V i p)) +
          (∑ i, (fderiv ℝ (fun z => C i (p.1, z)) p.2 (EuclideanSpace.single k 1) * V i p +
            C i p * H i k p)) +
          (fderiv ℝ (fun z => C₀ (p.1, z)) p.2 (EuclideanSpace.single k 1) -
            fderiv ℝ (fun y => fderiv ℝ ρ y (0, EuclideanSpace.single k 1)) p (1, 0)) * U p +
          C₀ p * V k p - fderiv ℝ ρ p (0, EuclideanSpace.single k 1) * R p) ∧
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo t₀ t₁ ×ˢ Ω₀ →
        (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * H k i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) - ∫ p, F p * φ p ∂ν := by
    obtain ⟨Fdiv, hFdiv⟩ := hu.exists_lp_divergence_coefficient_fderiv_localWeakPartial
      hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω k
    obtain ⟨Flower, hFlower⟩ := hu.exists_lp_weakPartial_localLowerSource
      hXcont hacont α hΩ hΩc hΩs hXsmooth ht₀ ht₁ hΩ₀ hΩ₀Ω k
    have hFdivFormula := ae_divergence_source_of_weak_derivatives (hG := hG) (hreg := hreg)
      α hΩ hΩc hΩs hΩ₀ hΩ₀Ω H hH k Fdiv hFdiv
    have hFlowerFormula := ae_lower_source_of_weak_derivatives (hG := hG) (hreg := hreg) hXcont hacont α hΩ hΩc hΩs
      hXsmooth hΩ₀ hΩ₀Ω H hH k Flower hFlower
    let Dρ := fun p => fderiv ℝ ρ p (0, EuclideanSpace.single k 1)
    let DDρ := fun p => fderiv ℝ Dρ p (1, 0)
    have hDρc : ContDiffOn ℝ (⊤ : ℕ∞) Dρ (D.regular ×ˢ Ω) :=
      (hρall.fderiv_of_isOpen (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
    have hDDρc : ContDiffOn ℝ (⊤ : ℕ∞) DDρ (D.regular ×ˢ Ω) :=
      (hDρc.fderiv_of_isOpen (D.regular_isOpen.prod hΩ) (by simp)).clm_apply contDiffOn_const
    have hDρ := hlift _ hDρc.continuousOn
    have hDDρ := hlift _ hDDρc.continuousOn
    let corr := fun p => Dρ p * R p + DDρ p * U p
    have hCorr : MemLp corr 2 ν := ((Lp.memLp R).mul hDρ).add (hU.mul hDDρ)
    let f := fun p => Fdiv p + Flower p - corr p
    have hf : MemLp f 2 ν := ((Lp.memLp Fdiv).add (Lp.memLp Flower)).sub hCorr
    refine ⟨hf.toLp f, ?_, ?_⟩
    · exact ae_source_formula_toLp k Fdiv Flower hf hFdivFormula hFlowerFormula
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
        (∫ p, Fdiv p * φ p ∂ν) + (∫ p, Flower p * φ p ∂ν) - ∫ p, corr p * φ p ∂ν := by
      have hc : (∫ p, (hf.toLp f) p * φ p ∂ν) = ∫ p, f p * φ p ∂ν := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with p hp
        rw [hp]
      rw [hc]
      have hsumint : Integrable (fun p => Fdiv p * φ p + Flower p * φ p) ν :=
        (hint _ (Lp.memLp Fdiv)).add (hint _ (Lp.memLp Flower))
      have hsubint : Integrable (fun p => Fdiv p * φ p + Flower p * φ p - corr p * φ p) ν :=
        hsumint.sub (hint _ hCorr)
      simp only [f, sub_mul, add_mul]
      rw [integral_sub hsumint (hint _ hCorr), integral_add (hint _ (Lp.memLp Fdiv)) (hint _ (Lp.memLp Flower))]
    change (∫ p, ρ p * V k p * fderiv ℝ φ p (1, 0) ∂ν) = _
    linarith [hb, hsum', hdiv', hlower, hFeq]
  choose F hFormula hF using hex
  exact ⟨R, H, F, hR, hH, hHsym, hFormula, hF⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
