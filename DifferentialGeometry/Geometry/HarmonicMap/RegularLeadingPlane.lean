import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientZero

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem smooth_chart_gradient
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (fun z (i : Fin (Module.finrank ℝ E)) =>
      chartComplexGradient (E := E) p U i z) s := by
  have hX : ContDiffOn ℝ ∞ (fun z => extChartAt 𝓘(ℝ, E) p (U z)) s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  apply contDiffOn_pi.mpr
  intro i
  have hc := (chartCoordCLM E i).contDiff.comp_contDiffOn hX
  have hd := hc.fderiv_of_isOpen (m := ∞) hs (by simp)
  have ha := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hb := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hp := (ha.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hb.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
  refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
  intro z _
  change (⟨fderiv ℝ (fun q => chartCoordCLM E i (extChartAt 𝓘(ℝ, E) p (U q))) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E i (extChartAt 𝓘(ℝ, E) p (U q))) z Complex.I / 2⟩ : ℂ) =
    Complex.equivRealProdCLM.symm _
  apply Complex.ext <;> simp [Function.comp_def,
    Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]

/-- At a regular point of the original conformal map, its original-metric
leading projection normalizes the actual chart derivative to the identity.
The same coefficient supplies a unit normal and a full graph splitting.
This theorem is applied before any seam reparametrization. -/
theorem chartLeadingPlaneProjection_regular_normalization_and_split
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd3 : Module.finrank ℝ E = 3)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a)) :
    let B : ℂ → (Fin (Module.finrank ℝ E) → ℂ) := fun z i => chartComplexGradient p U i z
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B a i).re)
    proj.comp (fderiv ℝ X a) = ContinuousLinearMap.id ℝ ℂ ∧
    ∃ N : E, Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) := by
  classical
  intro B Q proj X lift
  let F : ℂ → ℂ := fun z => proj (X z)
  have hUa := hU.contMDiffAt (hs.mem_nhds ha)
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hB : ContDiffAt ℝ 1 B a :=
    ((smooth_chart_gradient hs hU hchart).contDiffAt (hs.mem_nhds ha)).of_le (by simp)
  have hBne : B a ≠ 0 := by
    intro hzero
    have hgrad : ∀ i, chartComplexGradient p U i a = 0 := fun i => congrFun hzero i
    have hDzero := (chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
      (hUa.of_le (by simp)) (hchart a ha)).mp hgrad
    apply one_ne_zero (α := ℂ)
    apply hDa
    rw [hDzero]
    rfl
  have hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ (0 : ℕ) • B z := by
    filter_upwards [] with z
    simp only [pow_zero, one_smul]
    rfl
  obtain ⟨C, r, _, hr, _, _, herr⟩ :=
    chartComplexGradient_leading_projection_fderiv_error g hs (hU.of_le (by simp))
      hconformal ha (hchart a ha) hB hBne hfactor
  have hFa : fderiv ℝ F a = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    have hbound := herr a (Metric.mem_ball_self hr) v
    change ‖fderiv ℝ F a v - (a - a) ^ (0 : ℕ) * v‖ ≤
      C * ‖a - a‖ ^ (0 + 1) * ‖v‖ at hbound
    have hnorm : ‖fderiv ℝ F a v - v‖ ≤ 0 := by simpa only
      [sub_self, norm_zero, Nat.zero_add, pow_zero, pow_one, one_mul, mul_zero, zero_mul]
      using hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hF : ContDiffOn ℝ ∞ F s := proj.contDiff.comp_contDiffOn hX
  have hDF (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ F z = proj.comp (fderiv ℝ X z) :=
    (proj.hasFDerivAt.comp z ((hX.contDiffAt (hs.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt).fderiv
  have hnear : ∀ᶠ z in 𝓝 a, z ∈ s ∧ (fderiv ℝ F z).IsInvertible := by
    have hcont := (hF.continuousOn_fderiv_of_isOpen hs (by simp) a ha).continuousAt
      (hs.mem_nhds ha)
    have hset : {L : ℂ →L[ℝ] ℂ | L.IsInvertible} ∈ 𝓝 (fderiv ℝ F a) := by
      rw [hFa]
      exact (ContinuousLinearEquiv.refl ℝ ℂ).nhds
    filter_upwards [hs.mem_nhds ha, hcont hset] with z hzs hzinv
    exact ⟨hzs, hzinv⟩
  obtain ⟨V, hVsub, hVo, haV⟩ := mem_nhds_iff.mp hnear
  have hVs : V ⊆ s := fun z hz => (hVsub hz).1
  have hnull := chartComplexGradient_isotropic g (hUa.of_le (by simp))
    (hchart a ha) (hconformal a ha)
  obtain ⟨N, hNN, hPN, hsplit, _⟩ :=
    chartLeadingPlaneProjection_exists_graph_germs g hd3 hVo (hU.mono hVs) haV
      (fun z hz => hchart z (hVs hz)) hBne hnull
      (fun z hz _ => (hVsub hz).2)
  refine ⟨?_, N, hNN, hPN, hsplit⟩
  rw [← hDF a ha, hFa]

end DifferentialGeometry.Geometry
