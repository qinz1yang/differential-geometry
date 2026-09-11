import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientDerivativeBounds

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

theorem potentialCoefficient_family_fderiv_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    {a : ℝ → ℝ} (ha : ContinuousOn a J) (v : EuclN) (μ : Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => fderiv ℝ (fun y =>
      densityOnEuclid (I := I) (G.metric p.1) α y *
        ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I) G.metric p.1
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) - a p.1)) p.2 v)
      ∞ (μ.restrict (J ×ˢ Ω)) := by
  let U := toEuclidean (E := E) '' interior (extChartAt I α).target
  let ρ := fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2
  let τ := fun p : ℝ × EuclN => traceTimeDerivMetric (I := I) G.metric p.1
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))
  let Q := fun p : ℝ × EuclN => ρ p * ((1 / 2 : ℝ) * τ p)
  have hU : IsOpen U := (toEuclidean (E := E)).isOpenMap _ isOpen_interior
  have hρ : ContDiffOn ℝ ∞ ρ (D.regular ×ˢ U) :=
    (densityOnEuclid_family_contDiffOn hG Subset.rfl α).mono
      (prod_mono Subset.rfl (image_mono interior_subset))
  have hτ : ContDiffOn ℝ ∞ τ (D.regular ×ˢ U) :=
    traceTimeDerivMetric_comp_chartInverse_contDiffOn hG Subset.rfl α Subset.rfl
  have hQ : ContDiffOn ℝ ∞ Q (D.regular ×ˢ U) :=
    hρ.mul ((contDiffOn_const (c := (1 / 2 : ℝ))).mul hτ)
  have hDρ : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (fun y => ρ (p.1, y)) p.2 v) (D.regular ×ˢ U) :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => ρ (t, y)) D.regular_isOpen.uniqueDiffOn hU hρ).clm_apply
      (contDiffOn_const (c := v))
  have hDQ : ContDiffOn ℝ ∞ (fun p : ℝ × EuclN =>
      fderiv ℝ (fun y => Q (p.1, y)) p.2 v) (D.regular ×ˢ U) :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => Q (t, y)) D.regular_isOpen.uniqueDiffOn hU hQ).clm_apply
      (contDiffOn_const (c := v))
  have hc : ContinuousOn (fun p : ℝ × EuclN =>
      fderiv ℝ (fun y => Q (p.1, y)) p.2 v -
        a p.1 * fderiv ℝ (fun y => ρ (p.1, y)) p.2 v) (J ×ˢ closure Ω) :=
    (hDQ.continuousOn.mono (prod_mono hJ hΩs)).sub
      ((ha.comp continuousOn_fst (fun _ hp => hp.1)).mul
        (hDρ.continuousOn.mono (prod_mono hJ hΩs)))
  have heq (p : ℝ × EuclN) (hp : p ∈ J ×ˢ closure Ω) :
      fderiv ℝ (fun y => ρ (p.1, y) * ((1 / 2 : ℝ) * τ (p.1, y) - a p.1)) p.2 v =
        fderiv ℝ (fun y => Q (p.1, y)) p.2 v -
          a p.1 * fderiv ℝ (fun y => ρ (p.1, y)) p.2 v := by
    have hr : ContDiffOn ℝ ∞ (fun y => ρ (p.1, y)) U :=
      hρ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hJ hp.1, hy⟩)
    have hq : ContDiffOn ℝ ∞ (fun y => Q (p.1, y)) U :=
      hQ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hJ hp.1, hy⟩)
    have hr' := (hr.contDiffAt (hU.mem_nhds (hΩs hp.2))).differentiableAt (by simp)
    have hq' := (hq.contDiffAt (hU.mem_nhds (hΩs hp.2))).differentiableAt (by simp)
    have hf : (fun y => ρ (p.1, y) * ((1 / 2 : ℝ) * τ (p.1, y) - a p.1)) =
        (fun y => Q (p.1, y) - a p.1 * ρ (p.1, y)) := by
      funext y
      dsimp only [Q]
      ring
    rw [hf, fderiv_fun_sub hq' (hr'.const_mul _), fderiv_const_mul hr']
    rfl
  have hresult := (hc.congr (fun p hp => heq p hp)).memLp_top_of_subset_isCompact
    (hJc.prod hΩc) (hJc.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure) (μ := μ)
  simpa [ρ, τ] using hresult

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
