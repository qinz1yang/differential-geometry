import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual
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
    have hinner := (hF.fun_mul (r := 2) hc).fun_mul (r := 2) hτp
    have houter := hψp.fun_mul (r := 2) hinner
    simpa only [mul_assoc, mul_left_comm, mul_comm] using houter
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

theorem exists_lp_dual_of_fixed_density_cutoff_equation
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : Measure ℝ} {a b : ℝ} [IsFiniteMeasure (μ.restrict (Icc a b))]
    {O : Set (ℝ × EuStd)} (hO : IsOpen O) (hKO : Icc a b ×ˢ closure Ω ⊆ O)
    {r W C : ℝ × EuStd → ℝ} {P : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (hr : ContDiffOn ℝ (⊤ : ℕ∞) r O) (hrne : ∀ p ∈ O, r p ≠ 0)
    (hC : MemLp C 2 ((μ.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hP : ∀ j, MemLp (P j) 2 ((μ.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, W p * fderiv ℝ φ p (1, 0) ∂(μ.restrict (Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1)
          ∂(μ.restrict (Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, C p * φ p ∂(μ.restrict (Icc a b)).prod (volume.restrict Ω))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    let ν := (μ.restrict (Icc a b)).prod (volume.restrict Ω)
    let Q := fun j p => (η p.2 / r p) * P j p
    let B := fun p => η p.2 * C p - ∑ j, P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
    (∀ j, MemLp (Q j) 2 ν) ∧ MemLp B 2 ν ∧
    (∃ ℓ : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (μ.restrict (Icc a b)),
      ∀ τ : Lp ℝ 2 (μ.restrict (Icc a b)), ∀ v : H1ComplDirichlet q,
        (∫ t, τ t * ℓ t v ∂μ.restrict (Icc a b)) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q v
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2 ∂ν) ∧
    ∀ (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) τ →
      HasCompactSupport τ → tsupport τ ⊆ Ioo a b →
      let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
      (∫ p, deriv τ p.1 * (η p.2 * W p) * ψ p.2 ∂ν) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
        ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
  intro ν Q B
  classical
  let : IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  have hlift {f : ℝ × EuStd → ℝ} (hf : ContinuousOn f O) : MemLp f ∞ ν := by
    have hb := (hf.mono hKO).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (μ.restrict (Icc a b)).prod volume)
    rw [← Measure.prod_restrict, Measure.restrict_restrict_of_subset (Subset.rfl : Icc a b ⊆ Icc a b)] at hb
    exact hb
  have hηall : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × EuStd => η p.2) O :=
    (hη.comp contDiff_snd).contDiffOn
  have hηr : MemLp (fun p : ℝ × EuStd => η p.2 / r p) ∞ ν :=
    hlift (hηall.div hr hrne).continuousOn
  have hdηr (j) : MemLp (fun p => fderiv ℝ (fun z : ℝ × EuStd => η z.2 / r z) p
      (0, EuclideanSpace.single j 1)) ∞ ν :=
    hlift (((hηall.div hr hrne).fderiv_of_isOpen (m := (⊤ : ℕ∞)) hO (by simp)).clm_apply
      contDiffOn_const).continuousOn
  have hQ (j) : MemLp (Q j) 2 ν := by
    simpa only [Q] using hηr.fun_mul (r := 2) (hP j)
  have hB : MemLp B 2 ν := by
    apply (hlift hηall.continuousOn).fun_mul (r := 2) hC |>.sub
    apply memLp_finsetSum
    intro j _
    exact (hP j).fun_mul (r := 2) (hdηr j)
  refine ⟨hQ, hB, exists_lp_chart_source_sub_divergence_dual α hΩ hΩc hΩs hB hQ, ?_⟩
  intro v τ hτ hτc hτs ψ
  obtain ⟨hψ, hψmem, hdψmem⟩ :=
    smoothScalarDirichlet_chartInverse_bounds α hΩ.measurableSet hΩc hΩs v
  have hτmem : MemLp τ ∞ (μ.restrict (Icc a b)) :=
    hτ.continuous.memLp_top_of_hasCompactSupport hτc _
  have hηsp : MemLp η ∞ (volume.restrict Ω) :=
    hη.continuous.memLp_top_of_hasCompactSupport hηc _
  obtain ⟨hmain, herr, hsource⟩ := integrable_fixed_density_tensor_terms
    hτmem hψmem hdψmem hηsp hηr hdηr hC hP
  have hmem : ∀ᵐ p ∂ν, p ∈ Icc a b ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
    exact ⟨ht, hz⟩
  have hgood : ∀ᵐ p ∂ν, DifferentiableAt ℝ ψ p.2 ∧ DifferentiableAt ℝ r p ∧ r p ≠ 0 := by
    filter_upwards [hmem] with p hp
    have hpO := hKO ⟨hp.1, subset_closure hp.2⟩
    exact ⟨(hψ.contDiffAt (hΩ.mem_nhds hp.2)).differentiableAt (by simp),
      (hr.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp), hrne p hpO⟩
  exact integral_fixed_density_tensor_test (fun j => EuclideanSpace.single j 1)
    hΩ hη hηc hηs hψ hgood hweak hτ hτc hτs hmain herr hsource

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
