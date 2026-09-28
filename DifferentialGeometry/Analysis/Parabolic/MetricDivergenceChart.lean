import DifferentialGeometry.Analysis.Parabolic.MetricDivergenceClosedBall

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Analysis.Parabolic
open Tensor.Coordinates Integral.Measure Geometry.Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private theorem weak_divergence_eq_comp_toEuclidean
    {J : Set ℝ} {Ω : Set E} {ρ U : ℝ × E → ℝ}
    {A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    (hweak : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ z, ρ z * U z * fderiv ℝ φ z (1, 0) ∂volume.prod (modelHaar (E := E))) =
        ∑ i, ∑ j, ∫ z, A z i j * lineDeriv ℝ U z (0, chartModelBasis E j) *
          fderiv ℝ φ z (0, chartModelBasis E i) ∂volume.prod (modelHaar (E := E))) :
    let ep := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := E))
    ∀ φ : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ ((toEuclidean (E := E)) '' Ω) →
      (∫ z, ρ (ep.symm z) * U (ep.symm z) * fderiv ℝ φ z (1, 0) ∂volume.prod volume) =
        ∑ i, ∑ j, ∫ z, A (ep.symm z) i j * lineDeriv ℝ (U ∘ ep.symm) z (0, EuclideanSpace.single j 1) *
          fderiv ℝ φ z (0, EuclideanSpace.single i 1) ∂volume.prod volume := by
  intro ep φ hφ hφc hφs
  let e := toEuclidean (E := E)
  have he : MeasurePreserving e (modelHaar (E := E)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  have hp : MeasurePreserving ep (volume.prod (modelHaar (E := E))) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod he
  let ψ := φ ∘ ep
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp ep.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph ep.toHomeomorph
  have hψs : tsupport ψ ⊆ J ×ˢ Ω := by
    intro z hz
    have h := hφs (tsupport_comp_subset_preimage φ ep.continuous hz)
    refine ⟨h.1, ?_⟩
    obtain ⟨y, hy, heq⟩ := h.2
    exact (e.injective heq) ▸ hy
  have hdir (z v : ℝ × E) : fderiv ℝ ψ z v = fderiv ℝ φ (ep z) (ep v) := by
    rw [ep.comp_right_fderiv]
    rfl
  have ht : ep (1, 0) = (1, 0) := by simp [ep]
  have hs (i : Fin (Module.finrank ℝ E)) : ep (0, chartModelBasis E i) = (0, EuclideanSpace.single i 1) := by
    simp only [ep, ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
      chartModelBasis_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hl (z : ℝ × E) (j : Fin (Module.finrank ℝ E)) :
      lineDeriv ℝ (U ∘ ep.symm) (ep z) (0, EuclideanSpace.single j 1) =
        lineDeriv ℝ U z (0, chartModelBasis E j) := by
    rw [← hs j]
    simp only [lineDeriv, Function.comp_apply, ← map_smul, ← map_add,
      ContinuousLinearEquiv.symm_apply_apply]
  have h := hweak ψ hψ hψc hψs
  calc
    _ = ∫ z, ρ z * U z * fderiv ℝ ψ z (1, 0) ∂volume.prod (modelHaar (E := E)) := by
      rw [← hp.integral_comp ep.toHomeomorph.measurableEmbedding]
      simp only [ContinuousLinearEquiv.symm_apply_apply, hdir, ht]
    _ = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hp.integral_comp ep.toHomeomorph.measurableEmbedding]
      simp only [ContinuousLinearEquiv.symm_apply_apply, hl, hdir, hs]

section
variable {n : ℕ} [NeZero n]
  {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open Geometry.Curvature Laplacian.MetricExtension
open scoped Matrix
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))
private local instance : MeasurableSpace EuN := borel EuN
private local instance : BorelSpace EuN := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem contDiffOn_of_chart_weak_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g) {a b : ℝ} (hreg : Ioo a b ⊆ D.regular)
    (α : M) {Ω₀ : Set EuN} (hΩ₀ : IsOpen Ω₀)
    (hΩ₀s : Ω₀ ⊆ interior (extChartAt I α).target) {U : ℝ × EuN → ℝ}
    (hU : LocallyLipschitzOn (Ioo a b ×ˢ Ω₀) U)
    (hweak : ∀ φ : ℝ × EuN → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ z, chartDensityOnE (g z.1) α z.2 * U z * fderiv ℝ φ z (1, 0)
        ∂volume.prod (modelHaar (E := EuN))) =
        ∑ i, ∑ j, ∫ z, (chartInvGramOnE (g z.1) α i j z.2 * chartDensityOnE (g z.1) α z.2) *
          lineDeriv ℝ U z (0, chartModelBasis EuN j) * fderiv ℝ φ z (0, chartModelBasis EuN i)
            ∂volume.prod (modelHaar (E := EuN))) :
    ContDiffOn ℝ (⊤ : ℕ∞) U (Ioo a b ×ˢ Ω₀) := by
  let e := toEuclidean (E := EuN)
  let ep := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e
  let Ω := e '' Ω₀
  have hΩ : IsOpen Ω := e.toHomeomorph.isOpenMap _ hΩ₀
  have hΩs : Ω ⊆ e '' interior (extChartAt I α).target := image_mono hΩ₀s
  have hmaps : MapsTo ep.symm (Ioo a b ×ˢ Ω) (Ioo a b ×ˢ Ω₀) := by
    rintro ⟨t, y⟩ ⟨ht, z, hz, rfl⟩
    exact ⟨ht, by simpa only [ep, ContinuousLinearEquiv.prodCongr_symm,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.symm_apply_apply] using hz⟩
  have hUl : LocallyLipschitzOn (Ioo a b ×ˢ Ω) (U ∘ ep.symm) :=
    hU.comp ep.symm.lipschitzWith.locallyLipschitz.locallyLipschitzOn hmaps
  have hw := weak_divergence_eq_comp_toEuclidean hweak
  have hsm := (contDiffOn_and_metric_divergence_eq_of_locallyLipschitzOn hG hreg α hΩ hΩs
    (U ∘ ep.symm) hUl (fun φ hφ hφc hφs => ?_)).1
  · have hc : ContDiffOn ℝ (⊤ : ℕ∞) ((U ∘ ep.symm) ∘ ep)
        (Ioo a b ×ˢ Ω₀) :=
      hsm.comp ep.contDiff.contDiffOn (fun z hz => ⟨hz.1, mem_image_of_mem e hz.2⟩)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hc
  · let ρ := fun p : ℝ × EuStd => densityOnEuclid (g p.1) α p.2
    let A := fun p : ℝ × EuStd => Matrix.of fun i j => weightedInvGramOnEuclid (g p.1) α i j p.2
    let V : ℝ × EuStd → ℝ := U ∘ ep.symm
    let ν : Measure (ℝ × EuStd) := (volume.restrict (Ioo a b)).prod (volume.restrict Ω)
    have htest (f : ℝ × EuStd → ℝ) (v : ℝ × EuStd) :
        (∫ z, f z * fderiv ℝ φ z v ∂ν) = ∫ z, f z * fderiv ℝ φ z v ∂volume.prod volume := by
      rw [show ν = (volume.prod volume).restrict (Ioo a b ×ˢ Ω) from Measure.prod_restrict _ _]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ φ z v)
        (fun h => hz (hφs (tsupport_fderiv_apply_subset ℝ v h))), mul_zero]
    have h := hw φ hφ hφc hφs
    have hAc (i j) : ContinuousOn (fun p => A p i j) (Ioo a b ×ˢ Ω) :=
      ((weightedInvGramOnEuclid_family_contDiffOn (G :=
        { metric := g, connection := fun t => Geometry.Connection.leviCivitaConnectionOfMetric (g t),
          metricCompatible := fun t => Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (g t) })
        hG Subset.rfl α Subset.rfl i j).mono (prod_mono hreg hΩs)).continuousOn
    have hdl (i) : LocallyIntegrableOn (fun z => lineDeriv ℝ V z (0, EuclideanSpace.single i 1))
        (Ioo a b ×ˢ Ω) (volume.prod volume) := by
      apply (locallyIntegrableOn_iff (isOpen_Ioo.prod hΩ).isLocallyClosed).mpr
      intro K hKs hK
      exact memLp_one_iff_integrable.mp (hUl.memLp_lineDeriv_of_isCompact
        (isOpen_Ioo.prod hΩ) hK hKs hK.measure_ne_top (0, EuclideanSpace.single i 1) 1)
    have hint (i j) : Integrable (fun p => A p i j * lineDeriv ℝ V p (0, EuclideanSpace.single i 1) *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1)) ν := by
      exact (((hdl i).continuousOn_mul (hAc i j) (isOpen_Ioo.prod hΩ).isLocallyClosed).integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hφs)).mono_measure
        (by rw [show ν = (volume.prod volume).restrict (Ioo a b ×ˢ Ω) from Measure.prod_restrict _ _];
            exact Measure.restrict_le_self)
    change (∫ p, ρ p * V p * fderiv ℝ φ p (1, 0) ∂ν) =
      ∑ j, ∫ p, ((A p).transpose *ᵥ (fun i => lineDeriv ℝ V p (0, EuclideanSpace.single i 1))) j *
        fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν
    rw [htest]
    have hρeq (z : ℝ × EuStd) : ρ z = chartDensityOnE (g z.1) α (e.symm z.2) := rfl
    simp only [hρeq]
    have h' : (∫ z, chartDensityOnE (g z.1) α (e.symm z.2) * V z * fderiv ℝ φ z (1, 0)
        ∂volume.prod volume) =
        ∑ i, ∑ j, ∫ z, (chartInvGramOnE (g z.1) α i j (e.symm z.2) *
          chartDensityOnE (g z.1) α (e.symm z.2)) *
          lineDeriv ℝ V z (0, EuclideanSpace.single j 1) *
          fderiv ℝ φ z (0, EuclideanSpace.single i 1) ∂volume.prod volume := by
      simpa only [V, ep, e, ContinuousLinearEquiv.prodCongr_symm,
        ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_symm,
        ContinuousLinearEquiv.refl_apply, Function.comp_def] using h
    rw [h']
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
    simp_rw [integral_finsetSum _ (fun i _ => hint i _)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [htest]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Ioo a b ×ˢ Ω
    · have hs := weightedInvGramOnEuclid_symm_of_mem (g z.1) α i j
        ((image_mono (hΩ₀s.trans interior_subset)) hz.2)
      change (chartInvGramOnE (g z.1) α i j (e.symm z.2) * chartDensityOnE (g z.1) α (e.symm z.2)) *
          lineDeriv ℝ V z (0, EuclideanSpace.single j 1) * fderiv ℝ φ z (0, EuclideanSpace.single i 1) = _
      have hAeq : A z j i = chartInvGramOnE (g z.1) α i j (e.symm z.2) *
          chartDensityOnE (g z.1) α (e.symm z.2) := by
        rw [show A z j i = weightedInvGramOnEuclid (g z.1) α j i z.2 from rfl, ← hs]
        exact mul_comm _ _
      rw [hAeq]
    · rw [image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ φ z (0, EuclideanSpace.single i 1))
        (fun ht => hz (hφs (tsupport_fderiv_apply_subset ℝ _ ht))), mul_zero, mul_zero]
end

end DifferentialGeometry.Analysis.Parabolic
