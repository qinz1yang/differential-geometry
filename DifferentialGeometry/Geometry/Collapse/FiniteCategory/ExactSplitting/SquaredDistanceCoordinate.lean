import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SquaredDistanceChart
import DifferentialGeometry.Geometry.Metric.SplittingCoordinate

/-!
# LFR11, step S1: the Euclidean coordinate of an exact splitting is `C²`

Blueprint LFR11 (A:25566–25672), first paragraph of the proof. For a finite metric `g` of class
`C^{r+1}` (`2 ≤ r`) whose length distance is the ambient distance, and a distance isometry
`e : M ≃ᵢ F ×₂ Y` with `F` a real inner-product space, every coordinate `x ↦ ⟪(e x).fst, v⟫` is
`C²` (`contMDiff_inner_fst`; chart form `exists_contDiffOn_inner_fst_chart`).

Route: with `a_± = e⁻¹(u₀ ± s v, y₀)`, `⟪(e x).fst - u₀, v⟫ = (d(x,a₋)² - d(x,a₊)²)/(4s)`
(`GC.MetricGeometry.inner_fst_sub_eq_sq_dist_sub`), and the squared distance is `C²` near the
diagonal in charts (`FiniteSoul.exists_contDiffOn_sq_dist_chart`). Choosing `s` small puts
`(κ x₀, κ a_±)` in that neighbourhood. `C²` is all that the later bootstrap needs.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  {r : ℕ∞} {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MetricSpace Y]

/-- **LFR11 S1, chart form.** In the chart at `x₀`, `y ↦ ⟪(e (κ⁻¹ y)).fst, v⟫` is `C²` on an open
neighbourhood of `κ x₀` inside the chart target. -/
theorem exists_contDiffOn_inner_fst_chart
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) (x₀ : M) :
    ∃ U : Set E, IsOpen U ∧ extChartAt I x₀ x₀ ∈ U ∧ U ⊆ (extChartAt I x₀).target ∧
      ContDiffOn ℝ 2 (fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v) U := by
  obtain ⟨U₀, hU₀o, hmem, hsub, hQ⟩ := FiniteSoul.exists_contDiffOn_sq_dist_chart g hr hnorm x₀
  set κ := extChartAt I x₀ with hκ
  set u₀ : F := (e x₀).fst with hu₀
  set y₀ : Y := (e x₀).snd with hy₀
  have hex₀ : toLp 2 (u₀, y₀) = e x₀ := by
    apply (WithLp.equiv 2 _).injective
    rfl
  -- the auxiliary points as continuous functions of `s`
  set aP : ℝ → M := fun s => e.symm (toLp 2 (u₀ + s • v, y₀)) with haP
  set aM : ℝ → M := fun s => e.symm (toLp 2 (u₀ - s • v, y₀)) with haM
  have haP0 : aP 0 = x₀ := by simp [haP, hex₀]
  have haM0 : aM 0 = x₀ := by simp [haM, hex₀]
  have hcP : Continuous aP := e.symm.continuous.comp
    ((WithLp.prod_continuous_toLp 2 F Y).comp
      ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const))
  have hcM : Continuous aM := e.symm.continuous.comp
    ((WithLp.prod_continuous_toLp 2 F Y).comp
      ((continuous_const.sub (continuous_id.smul continuous_const)).prodMk continuous_const))
  -- the good set of parameters
  have hgood : ∀ a : ℝ → M, Continuous a → a 0 = x₀ →
      ∀ᶠ s in 𝓝 (0 : ℝ), a s ∈ κ.source ∧ ((κ x₀, κ (a s)) : E × E) ∈ U₀ := by
    intro a ha ha0
    have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), a s ∈ κ.source :=
      (ha.tendsto 0).eventually (by rw [ha0]; exact extChartAt_source_mem_nhds x₀)
    have h2 : Tendsto (fun s => ((κ x₀, κ (a s)) : E × E)) (𝓝 0) (𝓝 (κ x₀, κ x₀)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have hκc : ContinuousAt κ (a 0) := by rw [ha0]; exact continuousAt_extChartAt x₀
      have := hκc.tendsto.comp (ha.tendsto 0)
      rwa [ha0] at this
    exact h1.and (h2.eventually (hU₀o.mem_nhds hmem))
  obtain ⟨s, ⟨⟨hPs, hPU⟩, hMs, hMU⟩, hs0⟩ :=
    (((hgood aP hcP haP0).and (hgood aM hcM haM0)).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ) (a := 0)) |>.exists
  have hs : s ≠ 0 := hs0
  set Q : E × E → ℝ := fun z => dist (κ.symm z.1) (κ.symm z.2) ^ 2 with hQdef
  set U : Set E := {y | ((y, κ (aP s)) : E × E) ∈ U₀} ∩ {y | ((y, κ (aM s)) : E × E) ∈ U₀}
    with hUdef
  have hUo : IsOpen U :=
    (hU₀o.preimage (continuous_id.prodMk continuous_const)).inter
      (hU₀o.preimage (continuous_id.prodMk continuous_const))
  refine ⟨U, hUo, ⟨hPU, hMU⟩, fun y hy => (hsub hy.1).1, ?_⟩
  have hQP : ContDiffOn ℝ 2 (fun y => Q (y, κ (aP s))) U :=
    hQ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy => hy.1)
  have hQM : ContDiffOn ℝ 2 (fun y => Q (y, κ (aM s))) U :=
    hQ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy => hy.2)
  have hrhs : ContDiffOn ℝ 2
      (fun y => inner ℝ u₀ v + (Q (y, κ (aM s)) - Q (y, κ (aP s))) / (4 * s)) U :=
    contDiffOn_const.add ((hQM.sub hQP).div_const _)
  refine hrhs.congr fun y _ => ?_
  have hid := GC.MetricGeometry.inner_fst_sub_eq_sq_dist_sub e (κ.symm y) u₀ y₀ v hs
  rw [inner_sub_left] at hid
  have hP : κ.symm (κ (aP s)) = aP s := κ.left_inv hPs
  have hM : κ.symm (κ (aM s)) = aM s := κ.left_inv hMs
  simp only [hQdef, hP, hM]
  change inner ℝ (e (κ.symm y)).fst v =
    inner ℝ u₀ v + (dist (κ.symm y) (aM s) ^ 2 - dist (κ.symm y) (aP s) ^ 2) / (4 * s)
  rw [← hid]
  ring

/-- **LFR11 S1.** Every coordinate `x ↦ ⟪(e x).fst, v⟫` of an exact splitting is `C²`. -/
theorem contMDiff_inner_fst
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) :
    ContMDiff I 𝓘(ℝ, ℝ) 2 (fun x => inner ℝ (e x).fst v) := by
  intro x₀
  obtain ⟨U, hUo, hx₀U, -, hU⟩ := exists_contDiffOn_inner_fst_chart g hr hnorm e v x₀
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) 2
      ((fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v) ∘ extChartAt I x₀) x₀ :=
    ((hU.contDiffAt (hUo.mem_nhds hx₀U)).contMDiffAt).comp x₀ (contMDiffAt_extChartAt)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with x hx
  simp only [Function.comp_apply, (extChartAt I x₀).left_inv hx]

end DifferentialGeometry.Geometry.ExactSplitting
