import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem chartInverse_prod_contMDiffOn (α : M) (J : Set ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ × EuclN) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × EuclN =>
        (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hfst : ContMDiffOn 𝓘(ℝ, ℝ × EuclN) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × EuclN → ℝ) (J ×ˢ chartTargetEuclid (I := I) α) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × EuclN) 𝓘(ℝ, EuclN) ∞
      (Prod.snd : ℝ × EuclN → EuclN) (J ×ˢ chartTargetEuclid (I := I) α) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
  exact hfst.prodMk ((contMDiffOn_chart_symm (I := I) α).comp hsnd (fun p hp => hp.2))

private theorem chartInverse_mem_baseSet (α : M) {z : EuclN}
    (hz : z ∈ chartTargetEuclid (I := I) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
  rw [trivializationAt_baseSet_eq_chartAt_source,
    ← extChartAt_source_eq_chartAt_source (I := I)]
  exact (extChartAt I α).map_target (toEuclidean_symm_mem_target hz)

theorem densityOnEuclid_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hd := chartDensityOnE_family_contDiffOn hG hJ α
  have hc := hd.comp (s := J ×ˢ chartTargetEuclid (I := I) α)
    (contDiff_fst.prodMk ((toEuclidean (E := E)).symm.contDiff.comp contDiff_snd)).contDiffOn
    (fun p hp => ⟨hp.1, toEuclidean_symm_mem_target hp.2⟩)
  exact hc

theorem invGramOnEuclid_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclN => invGramOnEuclid (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ Ω) := by
  have hA := hG.chartInvGramOnE_contDiffOn (I := I) hJ α i j
  have hcomp := hA.comp
    ((contDiff_fst.prodMk ((toEuclidean (E := E)).symm.contDiff.comp contDiff_snd)).contDiffOn)
    (s := J ×ˢ Ω) (by
      intro (p : ℝ × EuclN) hp
      refine ⟨hp.1, ?_⟩
      obtain ⟨z, hz, hzeq⟩ := hΩs hp.2
      change (toEuclidean (E := E)).symm p.2 ∈ interior (extChartAt I α).target
      rw [← hzeq, ContinuousLinearEquiv.symm_apply_apply]
      exact hz)
  exact hcomp

theorem invGramOnEuclid_family_fderiv_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (invGramOnEuclid (I := I) (G.metric p.1) α i j) p.2) (J ×ˢ Ω) := by
  have hA := invGramOnEuclid_family_contDiffOn hG Subset.rfl α hΩs i j
  exact (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => invGramOnEuclid (I := I) (G.metric t) α i j y)
    D.regular_isOpen.uniqueDiffOn hΩ hA).mono (prod_mono hJ Subset.rfl)

theorem weightedInvGramOnEuclid_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2) (J ×ˢ Ω) := by
  exact ((densityOnEuclid_family_contDiffOn hG hJ α).mono
    (prod_mono Subset.rfl (hΩs.trans (image_mono interior_subset)))).mul
      (invGramOnEuclid_family_contDiffOn hG hJ α hΩs i j)

theorem chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {J : Set ℝ} (α : M)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm p.2))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  have hcoord : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => (e (TotalSpace.mk' E p.2 (X p.1 p.2))).2)
      (J ×ˢ e.baseSet) :=
    ((e.contMDiffOn_iff (fun p hp => e.mem_source.mpr hp.2)).mp hX).2
  let L := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hc := L.contDiff.contMDiff.comp_contMDiffOn hcoord
  have hcomp := hc.comp (chartInverse_prod_contMDiffOn (I := I) α J)
    (fun p hp => ⟨hp.1, chartInverse_mem_baseSet α hp.2⟩)
  exact hcomp.contDiffOn

theorem chartCoeffOnE_comp_toEuclidean_symm_family_fderiv_contDiffOn
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (α : M)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    {Ω : Set EuclN} (hΩ : IsOpen Ω) (hΩs : Ω ⊆ chartTargetEuclid (I := I) α)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (fun y => chartCoeffOnE (I := I) α (X p.1) i
        ((toEuclidean (E := E)).symm y)) p.2) (J ×ˢ Ω) := by
  exact DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => chartCoeffOnE (I := I) α (X t) i ((toEuclidean (E := E)).symm y))
    hJ hΩ ((chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α hX i).mono
      (prod_mono Subset.rfl hΩs))

variable [T2Space M] [SigmaCompactSpace M]

theorem riemannianVolumeDensity_mul_chartInverse_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (q : SmoothRiemannianMetric I M)
    (α : M) (φ : C^∞⟮I, M; ℝ⟯) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      (riemannianVolumeDensitySmoothMap (G.metric p.1) q * φ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hnum : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => densityOnEuclid q α p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) :=
    (densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn (fun p hp => hp.2)
  have hden := densityOnEuclid_family_contDiffOn hG hJ α
  have hφ : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) :=
    ((φ.contMDiff.comp_contMDiffOn (contMDiffOn_chart_symm (I := I) α)).contDiffOn).comp
      contDiff_snd.contDiffOn (fun p hp => hp.2)
  have hc := (hnum.div hden (fun p hp => ne_of_gt
    (chartDensity_pos (G.metric p.1) α (by
      have hx := chartInverse_mem_baseSet α hp.2
      rwa [trivializationAt_baseSet_eq_chartAt_source] at hx)))).mul hφ
  refine hc.congr ?_
  intro p hp
  change riemannianVolumeDensity (G.metric p.1) q _ * φ _ = _
  rw [riemannianVolumeDensity_apply_of_mem_chart_source (G.metric p.1) q α (by
    have hx := chartInverse_mem_baseSet α hp.2
    rwa [trivializationAt_baseSet_eq_chartAt_source] at hx)]
  rfl

theorem weightedInvGramOnEuclid_mul_fderiv_volumeDensity_family_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (q : SmoothRiemannianMetric I M)
    (α : M) (φ : C^∞⟮I, M; ℝ⟯) {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    let P := fun t z => (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2 *
        fderiv ℝ (P p.1) p.2 (EuclideanSpace.single j 1)) (J ×ˢ Ω) := by
  intro P
  have hP : ContDiffOn ℝ ∞ (Function.uncurry P) (D.regular ×ˢ Ω) :=
    (riemannianVolumeDensity_mul_chartInverse_family_contDiffOn hG Subset.rfl q α φ).mono
      (prod_mono Subset.rfl (hΩs.trans (image_mono interior_subset)))
  have hPd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    D.regular_isOpen.uniqueDiffOn hΩ hP
  exact ((weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α hΩs i j).mul
    (hPd.clm_apply contDiffOn_const)).mono (prod_mono hJ Subset.rfl)

theorem weightedInvGramOnEuclid_mul_fderiv_volumeDensity_family_fderiv_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (q : SmoothRiemannianMetric I M)
    (α : M) (φ : C^∞⟮I, M; ℝ⟯) {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    let P := fun t z => (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    let R := fun t z => weightedInvGramOnEuclid (I := I) (G.metric t) α i j z *
      fderiv ℝ (P t) z (EuclideanSpace.single j 1)
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => fderiv ℝ (R p.1) p.2) (J ×ˢ Ω) := by
  intro P R
  have hR : ContDiffOn ℝ ∞ (Function.uncurry R) (D.regular ×ˢ Ω) :=
    weightedInvGramOnEuclid_mul_fderiv_volumeDensity_family_contDiffOn
      hG Subset.rfl q α φ hΩ hΩs i j
  exact (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    D.regular_isOpen.uniqueDiffOn hΩ hR).mono (prod_mono hJ Subset.rfl)


omit [T2Space M] [SigmaCompactSpace M] in
theorem weightedInvGramOnEuclid_family_fderiv_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j) p.2) (J ×ˢ Ω) := by
  exact (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => weightedInvGramOnEuclid (I := I) (G.metric t) α i j y)
    D.regular_isOpen.uniqueDiffOn hΩ
    (weightedInvGramOnEuclid_family_contDiffOn hG Subset.rfl α hΩs i j)).mono
      (prod_mono hJ Subset.rfl)


omit [T2Space M] [SigmaCompactSpace M] in
theorem hasDerivAt_densityOnEuclid
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (α : M) {z : EuclN}
    (hz : z ∈ chartTargetEuclid (I := I) α) :
    HasDerivAt (fun s => densityOnEuclid (I := I) (G.metric s) α z)
      ((1 / 2) * traceTimeDerivMetric (I := I) G.metric t
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
          densityOnEuclid (G.metric t) α z) t := by
  exact hasDerivAt_chartDensity_of_chartGram_contMDiffOn D.regular_isOpen
    (hG.chartGramMatrix_contDiffOn Subset.rfl) ht α (chartInverse_mem_baseSet α hz)

omit [T2Space M] [SigmaCompactSpace M] in
theorem densityOnEuclid_family_fderiv_time_eq
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular) (α : M) {z : EuclN}
    (hz : z ∈ toEuclidean (E := E) '' interior (extChartAt I α).target) :
    fderiv ℝ (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2)
      (t, z) (1, 0) =
      (1 / 2) * traceTimeDerivMetric (I := I) G.metric t
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
          densityOnEuclid (G.metric t) α z := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hc := (densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
    (prod_mono Subset.rfl (image_mono interior_subset))
  have hd := (hc.differentiableOn (by simp) (t, z) ⟨ht, hz⟩).differentiableAt
    ((D.regular_isOpen.prod hU).mem_nhds ⟨ht, hz⟩)
  have hs := hd.hasFDerivAt.comp t ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) z t))
  have hderiv := (hs.hasDerivAt).deriv
  have htderiv := (hasDerivAt_densityOnEuclid hG ht α ((image_mono interior_subset) hz)).deriv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] using hderiv.symm.trans htderiv

omit [T2Space M] [SigmaCompactSpace M] in
theorem traceTimeDerivMetric_comp_chartInverse_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN}
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN => traceTimeDerivMetric (I := I) G.metric p.1
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))) (J ×ˢ Ω) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  let ρ := fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hρ : ContDiffOn ℝ ∞ ρ (D.regular ×ˢ U) :=
    (densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hdρ : ContDiffOn ℝ ∞ (fun p => fderiv ℝ ρ p (1, 0)) (D.regular ×ˢ U) :=
    (hρ.fderiv_of_isOpen (D.regular_isOpen.prod hU) (by simp)).clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : EuclN))))
  have hρne (p : ℝ × EuclN) (hp : p ∈ D.regular ×ˢ U) : ρ p ≠ 0 :=
    ne_of_gt (densityOnEuclid_pos (G.metric p.1) α ((image_mono interior_subset) hp.2))
  have hnum : ContDiffOn ℝ ∞ (fun p => (2 : ℝ) * fderiv ℝ ρ p (1, 0)) (D.regular ×ˢ U) :=
    (contDiffOn_const (c := (2 : ℝ))).mul hdρ
  have hc := hnum.div hρ hρne
  apply (hc.mono (prod_mono hJ hΩs)).congr
  intro p hp
  change traceTimeDerivMetric (I := I) G.metric p.1 _ =
    (2 : ℝ) * fderiv ℝ ρ p (1, 0) / ρ p
  rw [densityOnEuclid_family_fderiv_time_eq hG (hJ hp.1) α (hΩs hp.2)]
  have hn := hρne p ⟨hJ hp.1, hΩs hp.2⟩
  dsimp only [ρ] at hn ⊢
  field_simp

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
