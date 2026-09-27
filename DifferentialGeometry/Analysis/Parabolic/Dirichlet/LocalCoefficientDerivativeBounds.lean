import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientBounds

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem densityOnEuclid_family_fderiv_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ chartTargetEuclid (I := I) α) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (densityOnEuclid (I := I) (G.metric p.1) α) p.2) (J ×ˢ Ω) := by
  exact (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => densityOnEuclid (I := I) (G.metric t) α y)
    D.regular_isOpen.uniqueDiffOn hΩ
    ((densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl hΩs))).mono (prod_mono hJ Subset.rfl)

theorem weightedInvGramOnEuclid_family_fderiv_fderiv_contDiffOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) (v : EuclN) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (fun y =>
        fderiv ℝ (weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j) y v) p.2)
      (J ×ˢ Ω) := by
  exact (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => fderiv ℝ (weightedInvGramOnEuclid (I := I) (G.metric t) α i j) y v)
    D.regular_isOpen.uniqueDiffOn hΩ
    ((weightedInvGramOnEuclid_family_fderiv_contDiffOn hG Subset.rfl α hΩ hΩs i j).clm_apply
      (contDiffOn_const (c := v)))).mono (prod_mono hJ Subset.rfl)

theorem weightedInvGramOnEuclid_family_fderiv_fderiv_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) (v w : EuclN) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN =>
      fderiv ℝ (fun y =>
        fderiv ℝ (weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j) y v) p.2 w)
      ∞ (μ.restrict (J ×ˢ Ω)) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hc := (weightedInvGramOnEuclid_family_fderiv_fderiv_contDiffOn hG hJ α hU Subset.rfl
    i j v).clm_apply (contDiffOn_const (c := w))
  exact (hc.continuousOn.mono (prod_mono Subset.rfl hΩs)).memLp_top_of_subset_isCompact
    (hJc.prod hΩc) (hJc.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

theorem densityOnEuclid_family_fderiv_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (v : EuclN) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN =>
      fderiv ℝ (densityOnEuclid (I := I) (G.metric p.1) α) p.2 v)
      ∞ (μ.restrict (J ×ˢ Ω)) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hc := (densityOnEuclid_family_fderiv_contDiffOn hG hJ α hU
    (image_mono interior_subset)).clm_apply (contDiffOn_const (c := v))
  exact (hc.continuousOn.mono (prod_mono Subset.rfl hΩs)).memLp_top_of_subset_isCompact
    (hJc.prod hΩc) (hJc.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

theorem densityOnEuclid_family_fderiv_fderiv_time_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (v : EuclN) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => fderiv ℝ
      (fun z : ℝ × EuclN => fderiv ℝ
        (densityOnEuclid (I := I) (G.metric z.1) α) z.2 v) p (1, 0))
      ∞ (μ.restrict (J ×ˢ Ω)) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hc := (densityOnEuclid_family_fderiv_contDiffOn hG Subset.rfl α hU
    (image_mono interior_subset)).clm_apply (contDiffOn_const (c := v))
  have hd := (hc.fderiv_of_isOpen (m := ∞) (D.regular_isOpen.prod hU) (by simp)).clm_apply
    (contDiffOn_const (c := ((1, 0) : ℝ × EuclN)))
  exact (hd.continuousOn.mono (prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
    (hJc.prod hΩc) (hJc.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

theorem densityOnEuclid_mul_chartCoeffOnE_family_fderiv_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    {Ω : Set EuclN} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) (v : EuclN) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => fderiv ℝ (fun y =>
      densityOnEuclid (I := I) (G.metric p.1) α y *
        chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm y)) p.2 v)
      ∞ (μ.restrict (J ×ˢ Ω)) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hc := (densityOnEuclid_family_contDiffOn hG Subset.rfl α).mul
    (chartCoeffOnE_comp_toEuclidean_symm_family_contDiffOn X α hX i)
  have hd := (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => densityOnEuclid (I := I) (G.metric t) α y *
      chartCoeffOnE (I := I) α (X t) i ((toEuclidean (E := E)).symm y))
    D.regular_isOpen.uniqueDiffOn hU
    (hc.mono (prod_mono Subset.rfl (image_mono interior_subset)))).clm_apply
      (contDiffOn_const (c := v))
  exact (hd.continuousOn.mono (prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
    (hJc.prod hΩc) (hJc.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
