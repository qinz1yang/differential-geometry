import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLocalEllipticity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLocalScalarOperatorBounds


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private def chartRadiusSq (c x : M) : ℝ :=
  ‖toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)‖ ^ 2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem chartRadiusSq_smoothOn (c : M) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartRadiusSq (I := I) c) (chartAt H c).source := by
  have hq : ContDiff ℝ ∞ (fun z : E =>
      ‖toEuclidean (E := E) (z - extChartAt I c c)‖ ^ 2) :=
    ((toEuclidean (E := E)).contDiff.comp (contDiff_id.sub contDiff_const)).norm_sq ℝ
  exact hq.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (I := I) (x := c))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem radial_partial (z z₀ : E) (ρ : ℝ) (i : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) i (fun w => ρ ^ 2 - ‖toEuclidean (E := E) (w - z₀)‖ ^ 2) z =
      -2 * (toEuclidean (E := E) (z - z₀)) i := by
  have h := (((toEuclidean (E := E)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const z₀))).norm_sq
  have h' := h.const_sub (ρ ^ 2)
  simp only [Function.comp_def, id_eq] at h'
  unfold partialDeriv
  rw [h'.fderiv]
  simp only [neg_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    coe_innerSL_apply, chartModelBasis_apply,
    ContinuousLinearEquiv.apply_symm_apply, EuclideanSpace.inner_single_right,
    starRingEnd_apply, star_trivial, one_mul]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem radial_gradient_formula
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c x : M)
    (hx : x ∈ (chartAt H c).source) (ρ : ℝ)
    (hfeq : f =ᶠ[𝓝 x] fun y => ρ ^ 2 - chartRadiusSq (I := I) c y) :
    g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) =
      4 * ∑ i, ∑ j,
        chartInvGramOnE (I := I) g c i j (extChartAt I c x) *
          (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)) i *
          (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)) j := by
  have hxext : x ∈ (extChartAt I c).source := by simpa only [extChartAt_source] using hx
  have hz := (extChartAt I c).map_source hxext
  have hW := isOpen_extChartAt_target (I := I) c
  have hsymm : Tendsto (extChartAt I c).symm (𝓝 (extChartAt I c x)) (𝓝 x) := by
    simpa only [(extChartAt I c).left_inv hxext] using
      ((continuousOn_extChartAt_symm (I := I) c).continuousAt (hW.mem_nhds hz)).tendsto
  have hchart : scalarOnE (I := I) c f =ᶠ[𝓝 (extChartAt I c x)]
      (fun y => ρ ^ 2 - ‖toEuclidean (E := E) (y - extChartAt I c c)‖ ^ 2) := by
    filter_upwards [hfeq.comp_tendsto hsymm, hW.mem_nhds hz] with y hy hyW
    change f ((extChartAt I c).symm y) = _
    simp only [Function.comp_apply] at hy
    rw [hy]
    simp only [chartRadiusSq, (extChartAt I c).right_inv hyW]
  have hpartial (i : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) i (scalarOnE (I := I) c f) (extChartAt I c x) =
        -2 * (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)) i := by
    change fderiv ℝ (scalarOnE (I := I) c f) (extChartAt I c x) (chartModelBasis E i) = _
    rw [hchart.fderiv_eq]
    exact radial_partial _ _ ρ i
  change g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) = _
  rw [grad_norm_sq_chart g c (hf.mdifferentiable (by simp) x) hx]
  simp_rw [hpartial]
  simp only [chartInvGramOnE_def, (extChartAt I c).left_inv hxext]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


theorem exists_ancient_local_cubic_cutoff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (c : M) {U : Set M} (hU : U ∈ 𝓝 c) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ c ∈ K ∧
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ 0 < f c ∧
        (∀ x ∉ K, f x ≤ 0) ∧ ∃ C ℓ ρ : ℝ, 0 ≤ C ∧ 0 < ℓ ∧ 0 < ρ ∧
          ∀ t ∈ Icc a b, ∀ x, 0 < f x →
            -C ≤ heatOperatorWithDrift (flowG S) t (fun _ => 0) f x ∧
              4 * ℓ * (ρ ^ 2 - f x) ≤ (S.base.metric t).inner x
                (gradientAt (flowG S) t f x) (gradientAt (flowG S) t f x) := by
  classical
  obtain ⟨β, _, hβU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) c).mem_iff.mp hU
  let L : ℝ := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖
  let ρ : ℝ := β.rIn / (2 * (L + 1))
  have hL : 0 ≤ L := norm_nonneg _
  have hρ : 0 < ρ := div_pos β.rIn_pos (by positivity)
  have hρeq : 2 * (L + 1) * ρ = β.rIn := mul_div_cancel₀ _ (by positivity)
  have hsmall : L * ρ < β.rIn := by nlinarith
  let f : M → ℝ := fun x => β x * (ρ ^ 2 - chartRadiusSq (I := I) c x)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    simpa only [smul_eq_mul] using
      β.contMDiff_smul (contMDiffOn_const.sub (chartRadiusSq_smoothOn (I := I) c))
  have hK : IsCompact (tsupport β) := β.hasCompactSupport
  have hcK : c ∈ tsupport β := by
    apply subset_closure
    change β c ≠ 0
    rw [β.eq_one]
    exact one_ne_zero
  have hfout : ∀ x ∉ tsupport β, f x ≤ 0 := by
    intro x hx
    have hβx : β x = 0 := by
      by_contra hne
      exact hx (subset_closure (hne : x ∈ Function.support β))
    simp only [f, hβx, zero_mul, le_refl]
  have hpositive (x : M) (hfx : 0 < f x) :
      x ∈ tsupport β ∧ x ∈ (chartAt H c).source ∧
        f =ᶠ[𝓝 x] fun y => ρ ^ 2 - chartRadiusSq (I := I) c y := by
    have hpair : 0 < β x ∧ 0 < ρ ^ 2 - chartRadiusSq (I := I) c x :=
      (mul_pos_iff.mp hfx).resolve_right (fun h => (not_lt_of_ge β.nonneg h.1).elim)
    have hs : x ∈ Function.support β := ne_of_gt hpair.1
    have hxsource := β.support_subset_source hs
    have hnorm : ‖toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)‖ < ρ := by
      have hr : 0 < ρ ^ 2 -
          ‖toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)‖ ^ 2 := hpair.2
      nlinarith [norm_nonneg (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c))]
    have hdist : dist (extChartAt I c x) (extChartAt I c c) < β.rIn := by
      have hh := (toEuclidean (E := E)).symm.toContinuousLinearMap.le_opNorm
        (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c))
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hh
      rw [dist_eq_norm]
      exact hh.trans_lt ((mul_le_mul_of_nonneg_left hnorm.le hL).trans_lt hsmall)
    refine ⟨subset_closure hs, hxsource, ?_⟩
    filter_upwards [β.eventuallyEq_one_of_dist_lt hxsource hdist] with y hy
    simp only [f, hy, Pi.one_apply, one_mul]
  let W : Set E := extChartAt I c '' tsupport β
  have hW : IsCompact W := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := I) c).mono β.tsupport_subset_extChartAt_source)
  have hWt : W ⊆ (extChartAt I c).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (extChartAt I c).map_source (β.tsupport_subset_extChartAt_source hx)
  obtain ⟨ℓ, hℓ, hell⟩ := exists_uniform_ancient_chart_ellipticity (a := a)
    S hS hcarrier hregular c W hW hWt
  obtain ⟨C, hC, hbound⟩ := exists_uniform_solution_laplacian_bound (a := a)
    S hS hcarrier hregular hf (tsupport β) hK
  refine ⟨tsupport β, hK, hβU, hcK, f, hf, ?_, hfout, C, ℓ, ρ, hC, hℓ, hρ, ?_⟩
  · simpa only [f, β.eq_one, chartRadiusSq, sub_self, map_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), sub_zero, one_mul] using sq_pos_of_pos hρ
  · intro t ht x hfx
    obtain ⟨hxK, hxsource, heq⟩ := hpositive x hfx
    constructor
    · simpa only [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt] using
        (abs_le.mp (hbound t ht x hxK)).1
    · have hgrad := radial_gradient_formula (S.base.metric t) hf c x hxsource ρ heq
      have he := hell t ht (extChartAt I c x) ⟨x, hxK, rfl⟩
        (fun i => (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)) i)
      have hsum : ρ ^ 2 - f x =
          ∑ i, (toEuclidean (E := E) (extChartAt I c x - extChartAt I c c)) i ^ 2 := by
        rw [heq.self_of_nhds, sub_sub_cancel]
        exact EuclideanSpace.real_norm_sq_eq _
      change 4 * ℓ * (ρ ^ 2 - f x) ≤ (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) f x) (gradientFun (I := I) (S.base.metric t) f x)
      rw [hgrad, hsum]
      nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
