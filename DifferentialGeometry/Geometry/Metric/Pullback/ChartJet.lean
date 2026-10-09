import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.Pullback.Local

/-!
# Chart representatives of pulled-back metrics at interior points

At an intrinsic interior point of the source (the source may have boundary), the chart
representative of the pull-back inner product `F^* g` at `y` is the chart representative of `g`
at `φ y` evaluated on `Dφ y`, where `φ` is `F` written in the two charts. The chart
representative of a smooth metric is smooth on the chart target.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Connection

section ChartDerivativeInterior

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-frame derivative identity at a point whose chart image is interior to the model
range (the source model may have boundary). -/
theorem trivToE_mfderiv_trivFromE_of_mem_interior
    {f : N → M} (a p : N) (b : M)
    (hp : p ∈ (chartAt HN a).source) (hpi : extChartAt IN a p ∈ interior (range IN))
    (hfp : f p ∈ (chartAt H b).source)
    (hf : MDifferentiableAt IN I f p) (v : EN) :
    trivToE (I := I) b (f p)
        (mfderiv IN I f p (trivFromE (I := IN) a p v)) =
      fderiv ℝ (fun z : EN => extChartAt I b (f ((extChartAt IN a).symm z)))
        (extChartAt IN a p) v := by
  have hp' : p ∈ (extChartAt IN a).source := by simpa using hp
  have hz := (extChartAt IN a).map_source hp'
  have hsymm := (extChartAt IN a).left_inv hp'
  have hmem : range IN ∈ 𝓝 (extChartAt IN a p) := mem_interior_iff_mem_nhds.mp hpi
  have hs : MDifferentiableAt (modelWithCornersSelf ℝ EN) IN
      (extChartAt IN a).symm (extChartAt IN a p) :=
    (mdifferentiableWithinAt_extChartAt_symm (I := IN) hz).mdifferentiableAt hmem
  have he : MDifferentiableAt I (modelWithCornersSelf ℝ E)
      (extChartAt I b) (f p) := mdifferentiableAt_extChartAt hfp
  have hfs : MDifferentiableAt IN (modelWithCornersSelf ℝ E)
      ((extChartAt I b) ∘ f) p := he.comp p hf
  have hchain := mfderiv_comp_apply
    (I := modelWithCornersSelf ℝ EN) (I' := IN)
    (I'' := modelWithCornersSelf ℝ E) (extChartAt IN a p)
    (g := (extChartAt I b) ∘ f) (f := (extChartAt IN a).symm)
    (hsymm.symm ▸ hfs) hs v
  rw [hsymm, mfderiv_comp_apply p he hf] at hchain
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt
    (𝕜 := ℝ) (I := I) hfp
  have hj := TangentBundle.symmL_trivializationAt (𝕜 := ℝ) (I := IN) hp
  rw [mfderivWithin_of_mem_nhds hmem] at hj
  change (trivializationAt E (TangentSpace I) b).continuousLinearMapAt ℝ (f p)
      (mfderiv IN I f p ((trivializationAt EN (TangentSpace IN) a).symmL ℝ p v)) = _
  rw [ht, hj]
  have hchainE := congrArg (NormedSpace.fromTangentSpace _) hchain
  rw [mfderiv_eq_fderiv] at hchainE
  change fderiv ℝ (fun z : EN => extChartAt I b (f ((extChartAt IN a).symm z)))
      (extChartAt IN a p) v =
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I b) (f p)
      (mfderiv IN I f p
        (mfderiv (modelWithCornersSelf ℝ EN) IN (extChartAt IN a).symm
          (extChartAt IN a p) v)) at hchainE
  exact hchainE.symm

/-- **Chart formula of a pull-back.** At `y` in the chart target at `x₀`, interior to the model
range, the chart representative of `F^* g` is `g`'s chart representative at `b`, evaluated at
`φ y` on `Dφ y`, where `φ z = extChartAt b (F ((extChartAt x₀).symm z))`. -/
theorem localPullInner_trivFromE_eq_chartMetricBilin (g : SmoothRiemannianMetric I M)
    (F : N → M) (x₀ : N) (b : M) {y : EN} (hy : y ∈ (extChartAt IN x₀).target)
    (hyi : y ∈ interior (range IN))
    (hFy : F ((extChartAt IN x₀).symm y) ∈ (chartAt H b).source)
    (hF : MDifferentiableAt IN I F ((extChartAt IN x₀).symm y)) (u v : EN) :
    localPullInner (I := IN) (J := I) g F ((extChartAt IN x₀).symm y)
        (trivFromE (I := IN) x₀ ((extChartAt IN x₀).symm y) u)
        (trivFromE (I := IN) x₀ ((extChartAt IN x₀).symm y) v) =
      chartMetricBilin g b (extChartAt I b (F ((extChartAt IN x₀).symm y)))
        (fderiv ℝ (fun z : EN => extChartAt I b (F ((extChartAt IN x₀).symm z))) y u)
        (fderiv ℝ (fun z : EN => extChartAt I b (F ((extChartAt IN x₀).symm z))) y v) := by
  set p := (extChartAt IN x₀).symm y with hpdef
  have hpsrc : p ∈ (chartAt HN x₀).source := by
    simpa only [extChartAt_source] using (extChartAt IN x₀).map_target hy
  have hpy : extChartAt IN x₀ p = y := (extChartAt IN x₀).right_inv hy
  have hpi : extChartAt IN x₀ p ∈ interior (range IN) := by rw [hpy]; exact hyi
  rw [localPullInner_apply, ← chartMetricBilin_trivToE g b (F p) hFy,
    trivToE_mfderiv_trivFromE_of_mem_interior x₀ p b hpsrc hpi hFy hF u,
    trivToE_mfderiv_trivFromE_of_mem_interior x₀ p b hpsrc hpi hFy hF v, hpy]

end ChartDerivativeInterior

section ChartMetricSmooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart representative of a smooth metric is smooth on the chart target. -/
theorem contDiffOn_chartMetricBilin_target (g : SmoothRiemannianMetric I M) (a : M) :
    ContDiffOn ℝ ∞ (chartMetricBilin g a) (extChartAt I a).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hEq (z : E) : chartMetricBilin g a z v w =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Operator.chartGramOnE g a i j z * Riemannian.Geodesic.chartCoord (E := E) i v *
          Riemannian.Geodesic.chartCoord (E := E) j w := by
    exact Riemannian.AlongCurve.inner_eq_chartGramOnE_bilinear_on_baseSet g a v w
  have hs : ContDiffOn ℝ ∞ (fun z : E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Operator.chartGramOnE g a i j z * Riemannian.Geodesic.chartCoord (E := E) i v *
          Riemannian.Geodesic.chartCoord (E := E) j w) (extChartAt I a).target := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact ((Operator.chartGramOnE_contDiffOn g a i j).mul contDiffOn_const).mul contDiffOn_const
  exact hs.congr (fun z _ => hEq z)

/-- At an intrinsic interior point, the chart representative of a smooth metric is smooth at the
chart image. -/
theorem contDiffAt_chartMetricBilin_of_isInteriorPoint (g : SmoothRiemannianMetric I M)
    {a : M} (ha : I.IsInteriorPoint a) :
    ContDiffAt ℝ ∞ (chartMetricBilin g a) (extChartAt I a a) :=
  (contDiffOn_chartMetricBilin_target g a).contDiffAt
    (mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp ha))

end ChartMetricSmooth

end DifferentialGeometry.Geometry
