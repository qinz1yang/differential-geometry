import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn

noncomputable section

set_option autoImplicit false

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
private theorem chartInverse_prod_continuousOn {Z : Type*} [TopologicalSpace Z] (α : M) (J : Set Z) :
    ContinuousOn
      (fun p : Z × EuclN =>
        (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  apply continuous_fst.continuousOn.prodMk
  apply (continuousOn_extChartAt_symm (I := I) α).comp
    ((toEuclidean (E := E)).symm.continuous.comp continuous_snd).continuousOn
  intro p hp
  exact toEuclidean_symm_mem_target hp.2

private theorem chartInverse_prod_mapsTo_baseSet {Z : Type*} (α : M) (J : Set Z) :
    MapsTo
      (fun p : Z × EuclN =>
        (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  rw [trivializationAt_baseSet_eq_chartAt_source,
    ← extChartAt_source_eq_chartAt_source (I := I)]
  exact (extChartAt I α).map_target (toEuclidean_symm_mem_target hp.2)

theorem densityOnEuclid_family_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) :
    ContinuousOn (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hd : ContinuousOn (fun p : ℝ × M => chartDensity (I := I) (G.metric p.1) α p.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (chartDensity_family_contMDiffOn (I := I) G.metric α
      (hG.chartGramMatrix_contDiffOn (I := I) hJ α)).continuousOn
  have hc := hd.comp (chartInverse_prod_continuousOn (I := I) α J)
    (chartInverse_prod_mapsTo_baseSet (I := I) α J)
  exact hc

theorem gramOnEuclid_family_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × EuclN => gramOnEuclid (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hg := hG.chartGramMatrix_continuousOn (I := I) hJ α i j
  have hc := hg.comp (chartInverse_prod_continuousOn (I := I) α J)
    (chartInverse_prod_mapsTo_baseSet (I := I) α J)
  exact hc

theorem invGramOnEuclid_family_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × EuclN => invGramOnEuclid (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  let A := fun p : ℝ × EuclN =>
    chartGramMatrix (I := I) (G.metric p.1) α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))
  have hA : ContinuousOn A (J ×ˢ chartTargetEuclid (I := I) α) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact gramOnEuclid_family_continuousOn hG hJ α i j
  intro p hp
  have hdet : (A p).det ≠ 0 := ne_of_gt
    (chartGramMatrix_det_pos (G.metric p.1) α
      ((chartInverse_prod_mapsTo_baseSet (I := I) α J) hp).2)
  have hinv : ContinuousAt Ring.inverse (A p).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hc := (continuousAt_matrix_inv (A p) hinv).comp_continuousWithinAt (hA p hp)
  exact (continuous_apply j).continuousAt.comp_continuousWithinAt
    ((continuous_apply i).continuousAt.comp_continuousWithinAt hc)

theorem exists_uniform_inv_gram_quadratic_lower_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {K : Set EuclN} (hKc : IsCompact K) (hKs : K ⊆ chartTargetEuclid (I := I) α) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ y ∈ K, ∀ ξ : EuclN,
      c * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          invGramOnEuclid (I := I) (G.metric t) α i j y)) ξ⟫_ℝ := by
  obtain ⟨c, hc, hbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound (hJc.prod hKc)
    (fun p : ℝ × EuclN => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      invGramOnEuclid (I := I) (G.metric p.1) α i j p.2))
    (fun i j => (invGramOnEuclid_family_continuousOn hG hJ α i j).mono
      (prod_mono Subset.rfl hKs))
    (fun p hp => invGramOnEuclid_posDef (I := I) (G.metric p.1) α (hKs hp.2))
  refine ⟨c, hc, ?_⟩
  intro t ht y hy ξ
  change c * ‖ξ‖ ^ 2 ≤ (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ star ξ.ofLp
  rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
  exact hbound (t, y) ⟨ht, hy⟩ ξ

theorem exists_uniform_weighted_inv_gram_quadratic_lower_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {K : Set EuclN} (hKc : IsCompact K) (hKs : K ⊆ chartTargetEuclid (I := I) α) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ y ∈ K, ∀ ξ : EuclN,
      c * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) (G.metric t) α i j y)) ξ⟫_ℝ := by
  obtain ⟨c, hc, hbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound (hJc.prod hKc)
    (fun p : ℝ × EuclN => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2))
    (fun i j => ((densityOnEuclid_family_continuousOn hG hJ α).mul
      (invGramOnEuclid_family_continuousOn hG hJ α i j)).mono (prod_mono Subset.rfl hKs))
    (fun p hp => weightedInvGramOnEuclid_posDef (I := I) (G.metric p.1) α (hKs hp.2))
  refine ⟨c, hc, ?_⟩
  intro t ht y hy ξ
  change c * ‖ξ‖ ^ 2 ≤ (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ star ξ.ofLp
  rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
  exact hbound (t, y) ⟨ht, hy⟩ ξ

theorem _root_.DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_family_continuousOn
    {Z : Type*} [TopologicalSpace Z]
    (X : Z → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {J : Set Z} (α : M)
    (hX : ContinuousOn (fun p : Z × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : Z × M => chartCoeff (I := I) α (X p.1) i p.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  have hc : ContinuousOn (fun p : Z × M =>
      (e (TotalSpace.mk' E p.2 (X p.1 p.2))).2) (J ×ˢ e.baseSet) := by
    apply continuous_snd.comp_continuousOn
    apply e.continuousOn.comp hX
    intro p hp
    exact e.mem_source.mpr hp.2
  let L := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hcomp := L.continuous.comp_continuousOn hc
  refine hcomp.congr ?_
  intro p _
  change (chartModelBasis E).repr ((e (TotalSpace.mk' E p.2 (X p.1 p.2))).2) i =
    (chartModelBasis E).coord i ((e (TotalSpace.mk' E p.2 (X p.1 p.2))).2)
  rw [Module.Basis.coord_apply]

theorem chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn
    {Z : Type*} [TopologicalSpace Z]
    (X : Z → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {J : Set Z} (α : M)
    (hX : ContinuousOn (fun p : Z × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : Z × EuclN =>
      chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm p.2))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hc := chartCoeff_family_continuousOn (I := I) X α
    hX i
  have hcomp := hc.comp (chartInverse_prod_continuousOn (I := I) α J)
    (chartInverse_prod_mapsTo_baseSet (I := I) α J)
  exact hcomp

theorem traceTimeDerivMetric_comp_chartInverse_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) :
    ContinuousOn (fun p : ℝ × EuclN =>
      traceTimeDerivMetric (I := I) G.metric p.1
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  apply (continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
    D.regular_isOpen (fun β i j => hG.chartGramMatrix_contDiffOn (I := I) Subset.rfl β i j)).comp
    (chartInverse_prod_continuousOn (I := I) α J)
  intro p hp
  exact ⟨hJ hp.1, mem_univ _⟩

theorem densityOnEuclid_family_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (densityOnEuclid_family_continuousOn hG hJ α).mono
    (prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩm)
      (prod_mono Subset.rfl subset_closure)

theorem invGramOnEuclid_family_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (i j : Fin (Module.finrank ℝ E)) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => invGramOnEuclid (I := I) (G.metric p.1) α i j p.2) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (invGramOnEuclid_family_continuousOn hG hJ α i j).mono
    (prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩm)
      (prod_mono Subset.rfl subset_closure)

theorem weightedInvGramOnEuclid_family_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (i j : Fin (Module.finrank ℝ E)) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact MemLp.mul' (p := ∞) (q := ∞) (r := ∞)
    (invGramOnEuclid_family_memLp_top hG hJc hJ α hΩm hΩc hΩs i j μ)
    (densityOnEuclid_family_memLp_top hG hJc hJ α hΩm hΩc hΩs μ)

theorem chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (X : Z → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {J : Set Z} (hJc : IsCompact J) (hJm : MeasurableSet J) (α : M)
    (hX : ContinuousOn (fun p : Z × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α)
    (i : Fin (Module.finrank ℝ E)) (μ : Measure (Z × EuclN)) :
    MemLp (fun p : Z × EuclN =>
      chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm p.2)) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn X α hX i).mono
    (prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJm.prod hΩm)
      (prod_mono Subset.rfl subset_closure)

theorem traceTimeDerivMetric_comp_chartInverse_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN =>
      traceTimeDerivMetric (I := I) G.metric p.1
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (traceTimeDerivMetric_comp_chartInverse_continuousOn hG hJ α).mono
    (prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩm)
      (prod_mono Subset.rfl subset_closure)

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
