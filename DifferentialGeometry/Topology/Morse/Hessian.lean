import DifferentialGeometry.Analysis.Schauder.Holder.SecondOrderComposition
import DifferentialGeometry.Topology.Morse.CriticalPoint

open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Morse

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chartHessianAt_congr_eventuallyEq {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : chartHessianAt f x = chartHessianAt g x := by
  ext v
  change fderiv ℝ (fderiv ℝ f) x v v = fderiv ℝ (fderiv ℝ g) x v v
  rw [h.fderiv.fderiv_eq]

open DifferentialGeometry.Analysis.Schauder in
theorem chartHessianAt_comp_of_fderiv_eq_zero
    {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (hcrit : fderiv ℝ f (φ x) = 0) :
    chartHessianAt (f ∘ φ) x =
      (chartHessianAt f (φ x)).comp (fderiv ℝ φ x).toLinearMap := by
  have h := hessianCurryEquiv_iteratedFDeriv_two_comp hf hφ
  simp only [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv] at h
  ext v
  change fderiv ℝ (fderiv ℝ (f ∘ φ)) x v v =
    fderiv ℝ (fderiv ℝ f) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x v)
  rw [h]
  simp only [c2PullbackHessian, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, hcrit, zero_apply, zero_add]

variable {H H' : Type} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

section Boundaryless

variable [I.Boundaryless] [J.Boundaryless]

omit [J.Boundaryless] in
private theorem mfderiv_eq_fderiv_chart
    {f : M → N} {x : M} (hf : MDifferentiableAt I J f x) :
    mfderiv I J f x = fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x) := by
  classical
  change (if MDifferentiableAt I J f x then
    fderivWithin ℝ (writtenInExtChartAt I J x f) (Set.range I) (extChartAt I x x)
    else (0 : E →L[ℝ] F)) = _
  rw [if_pos hf, I.range_eq_univ, fderivWithin_univ]

theorem chartHessianAt_comp_mfderiv
    {c : M → N} {f : N → ℝ} {x : M}
    (hc : ContMDiffAt I J 2 c x) (hf : ContMDiffAt J 𝓘(ℝ) 2 f (c x))
    (hcrit : IsCriticalPointAt J f (c x)) :
    chartHessianAt (fun z => f (c ((extChartAt I x).symm z))) (extChartAt I x x) =
      (chartHessianAt (fun z => f ((extChartAt J (c x)).symm z))
        (extChartAt J (c x) (c x))).comp (mfderiv I J c x).toLinearMap := by
  let φ := writtenInExtChartAt I J x c
  let G := fun z => f ((extChartAt J (c x)).symm z)
  have hφ : ContDiffAt ℝ 2 φ (extChartAt I x x) := by
    simpa only [φ, writtenInExtChartAt, Function.comp_def, I.range_eq_univ, contDiffWithinAt_univ]
      using (contMDiffAt_iff.mp hc).2
  have hG : ContDiffAt ℝ 2 G (extChartAt J (c x) (c x)) := by
    simpa only [G, Function.comp_def, J.range_eq_univ, contDiffWithinAt_univ, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, Function.id_comp, id_eq] using (contMDiffAt_iff.mp hf).2
  have hφx : φ (extChartAt I x x) = extChartAt J (c x) (c x) := by
    simp only [φ, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  have heq : (fun z => f (c ((extChartAt I x).symm z))) =ᶠ[𝓝 (extChartAt I x x)]
      G ∘ φ := by
    have h := writtenInExtChartAt_comp (I := I) (I' := J) (I'' := 𝓘(ℝ))
      (g := f) (s := Set.univ) hc.continuousAt.continuousWithinAt
    simpa only [G, φ, Function.comp_def, Set.preimage_univ, Set.univ_inter, I.range_eq_univ, nhdsWithin_univ,
      writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp, id_eq] using h
  have hcritG : fderiv ℝ G (extChartAt J (c x) (c x)) = 0 := by
    exact (mfderiv_eq_fderiv_chart (hf.mdifferentiableAt (by norm_num))).symm.trans hcrit
  rw [chartHessianAt_congr_eventuallyEq heq,
    chartHessianAt_comp_of_fderiv_eq_zero (hφx.symm ▸ hG) hφ (hφx.symm ▸ hcritG),
    hφx, ← mfderiv_eq_fderiv_chart (hc.mdifferentiableAt (by norm_num))]
  rfl

theorem isNondegenerateCriticalPointAt_comp_diffeomorph_iff
    {r : ℕ∞ω} (c : Diffeomorph I J M N r) (hr : 2 ≤ r)
    {f : N → ℝ} {x : M} (hf : ContMDiffAt J 𝓘(ℝ) 2 f (c x)) :
    IsNondegenerateCriticalPointAt I (f ∘ c) x ↔
      IsNondegenerateCriticalPointAt J f (c x) := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  have hc := isCriticalPointAt_comp_diffeomorph_iff c hr0 (f := f) (x := x)
  by_cases hcrit : IsCriticalPointAt J f (c x)
  · simp only [IsNondegenerateCriticalPointAt, hc, hcrit, true_and]
    simp only [Function.comp_apply]
    rw [chartHessianAt_comp_mfderiv (c.contMDiffAt.of_le hr) hf hcrit]
    let L : E ≃ₗ[ℝ] F := (c.mfderivToContinuousLinearEquiv hr0 x).toLinearEquiv
    let Q := chartHessianAt (fun y => f ((extChartAt J (c x)).symm y))
      (extChartAt J (c x) (c x))
    change (QuadraticMap.associated (Q.comp L.toLinearMap)).SeparatingLeft ↔
      (QuadraticMap.associated Q).SeparatingLeft
    have hB : QuadraticMap.associated (Q.comp L.toLinearMap) =
        (L.symm.arrowCongr (L.symm.arrowCongr (LinearEquiv.refl ℝ ℝ)))
          (QuadraticMap.associated Q) := by
      ext u v
      simp [QuadraticMap.associated_apply]
    rw [hB]
    exact LinearMap.separatingLeft_congr_iff L.symm L.symm
  · simp only [IsNondegenerateCriticalPointAt, hc, hcrit, false_and]

theorem sigNeg_chartHessianAt_comp_diffeomorph
    {r : ℕ∞ω} (c : Diffeomorph I J M N r) (hr : 2 ≤ r)
    {f : N → ℝ} {x : M} (hf : ContMDiffAt J 𝓘(ℝ) 2 f (c x))
    (hcrit : IsCriticalPointAt J f (c x)) :
    _root_.sigNeg (chartHessianAt (fun z => f (c ((extChartAt I x).symm z)))
      (extChartAt I x x)) =
      _root_.sigNeg (chartHessianAt (fun z => f ((extChartAt J (c x)).symm z))
        (extChartAt J (c x) (c x))) := by
  apply QuadraticMap.Equivalent.sigNeg_eq
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  refine ⟨{ (c.mfderivToContinuousLinearEquiv hr0 x).toLinearEquiv with map_app' := ?_ }⟩
  intro v
  rw [chartHessianAt_comp_mfderiv (c.contMDiffAt.of_le hr) hf hcrit]
  rfl

end Boundaryless

theorem chartHessianAt_subtype
    (U : TopologicalSpace.Opens M) (f : M → ℝ) (x : U) :
    chartHessianAt (fun z => f (((extChartAt I x).symm z : U) : M)) (extChartAt I x x) =
      chartHessianAt (fun z => f ((extChartAt I (x : M)).symm z))
        (extChartAt I (x : M) (x : M)) := by
  have hp : extChartAt I x x = extChartAt I (x : M) (x : M) := rfl
  rw [← hp]
  apply chartHessianAt_congr_eventuallyEq
  let e := (chartAt H (x : M)).subtypeRestr (s := U) (⟨x⟩ : Nonempty U)
  have ht : I.symm (extChartAt I x x) ∈ e.target :=
    ((extChartAt I x).map_source (mem_extChartAt_source x)).2
  have hn := I.continuous_symm.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)
  filter_upwards [hn] with z hz
  exact congrArg f ((chartAt H (x : M)).subtypeRestr_symm_apply (⟨x⟩ : Nonempty U) hz)

theorem isNondegenerateCriticalPointAt_subtype_iff
    (U : TopologicalSpace.Opens M) {f : M → ℝ} {x : U} :
    IsNondegenerateCriticalPointAt I (fun y : U => f y) x ↔
      IsNondegenerateCriticalPointAt I f (x : M) := by
  simp only [IsNondegenerateCriticalPointAt, isCriticalPointAt_subtype_iff,
    chartHessianAt_subtype]

theorem isNondegenerateCriticalPointAt_congr_eventuallyEq {f g : M → ℝ} {x : M}
    (h : f =ᶠ[𝓝 x] g) :
    IsNondegenerateCriticalPointAt I f x ↔ IsNondegenerateCriticalPointAt I g x := by
  have hc : Filter.Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa only [ContinuousAt, extChartAt_to_inv] using continuousAt_extChartAt_symm (I := I) x
  have heq := h.comp_tendsto hc
  simp only [Function.comp_def] at heq
  simp only [IsNondegenerateCriticalPointAt, IsCriticalPointAt, h.mfderiv_eq,
    chartHessianAt_congr_eventuallyEq heq]
  rfl

end DifferentialGeometry.Topology.Morse
