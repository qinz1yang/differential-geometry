import DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry

section ChartMetric

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartMetricBilin (g : SmoothRiemannianMetric I M) (a : M) (z : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let p := (extChartAt I a).symm z
  let J := trivFromE (I := I) a p
  (((g.inner p).comp J).flip.comp J).flip

@[simp]
theorem chartMetricBilin_apply (g : SmoothRiemannianMetric I M)
    (a : M) (z u v : E) :
    chartMetricBilin g a z u v =
      g.inner ((extChartAt I a).symm z)
        (trivFromE (I := I) a ((extChartAt I a).symm z) u)
        (trivFromE (I := I) a ((extChartAt I a).symm z) v) := rfl

theorem chartMetricBilin_trivToE (g : SmoothRiemannianMetric I M)
    (a p : M) (hp : p ∈ (chartAt H a).source)
    (u v : TangentSpace I p) :
    chartMetricBilin g a (extChartAt I a p)
        (trivToE (I := I) a p u) (trivToE (I := I) a p v) =
      g.inner p u v := by
  have hp' : p ∈ (extChartAt I a).source := by simpa using hp
  have hb : p ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hp
  have heq : (extChartAt I a).symm (extChartAt I a p) = p :=
    (extChartAt I a).left_inv hp'
  change g.inner _ (trivFromE (I := I) a _ (trivToE (I := I) a p u))
    (trivFromE (I := I) a _ (trivToE (I := I) a p v)) = _
  rw [heq, trivFromE_trivToE (I := I) a hb,
    trivFromE_trivToE (I := I) a hb]

variable [FiniteDimensional ℝ E]

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

private theorem chartMetricBilin_eq_sum (g : SmoothRiemannianMetric I M)
    (a : M) (z v w : E) :
    chartMetricBilin g a z v w =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g a i j z * chartCoord (E := E) i v *
          chartCoord (E := E) j w := by
  exact inner_eq_chartGramOnE_bilinear_on_baseSet g a v w

theorem chartMetricBilin_hasDerivAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (a : M)
    {c V W : ℝ → E} {c' V' W' : E} {t : ℝ}
    (hc : HasDerivAt c c' t) (hV : HasDerivAt V V' t) (hW : HasDerivAt W W' t)
    (ht : c t ∈ (extChartAt I a).target) :
    HasDerivAt (fun s => chartMetricBilin g a (c s) (V s) (W s))
      (chartMetricBilin g a (c t)
          (V' + chartChristoffelContraction (I := I) g a c' (V t) (c t)) (W t) +
        chartMetricBilin g a (c t) (V t)
          (W' + chartChristoffelContraction (I := I) g a c' (W t) (c t))) t := by
  let gamma : ℝ → M := fun s => (extChartAt I a).symm (c s)
  have heq : Filter.EventuallyEq (nhds t) (chartCurve (I := I) a gamma) c := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target a).mem_nhds ht)] with s hs
    exact (extChartAt I a).right_inv hs
  have hcChart : HasDerivAt (chartCurve (I := I) a gamma) c' t :=
    hc.congr_of_eventuallyEq heq
  have htChart : chartCurve (I := I) a gamma t ∈ interior (extChartAt I a).target := by
    rw [heq.eq_of_nhds, (isOpen_extChartAt_target a).interior_eq]
    exact ht
  have hcompat := chartGramAlongCurve_hasDerivAt_covariant g a gamma V W
    (uPrime := fun _ => c') (Vprime := fun _ => V') (Wprime := fun _ => W')
    hcChart htChart hV hW
  simp only [heq.eq_of_nhds, ← chartMetricBilin_eq_sum] at hcompat
  apply hcompat.congr_of_eventuallyEq
  filter_upwards [heq] with s hs
  simp only [chartGramAlongCurve_def, hs, chartMetricBilin_eq_sum]

end ChartMetric

section ChartDerivative

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem trivToE_mfderiv_trivFromE
    {f : N → M} (a p : N) (b : M)
    (hp : p ∈ (chartAt HN a).source)
    (hfp : f p ∈ (chartAt H b).source)
    (hf : MDifferentiableAt IN I f p) (v : EN) :
    trivToE (I := I) b (f p)
        (mfderiv IN I f p (trivFromE (I := IN) a p v)) =
      fderiv ℝ (fun z : EN => extChartAt I b (f ((extChartAt IN a).symm z)))
        (extChartAt IN a p) v := by
  have hp' : p ∈ (extChartAt IN a).source := by simpa using hp
  have hz := (extChartAt IN a).map_source hp'
  have hsymm := (extChartAt IN a).left_inv hp'
  have hs : MDifferentiableAt (modelWithCornersSelf ℝ EN) IN
      (extChartAt IN a).symm (extChartAt IN a p) := by
    have hh := mdifferentiableWithinAt_extChartAt_symm (I := IN) hz
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := IN),
      mdifferentiableWithinAt_univ] at hh
    exact hh
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
  rw [ModelWithCorners.Boundaryless.range_eq_univ (I := IN), mfderivWithin_univ] at hj
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

theorem IsRiemannianIsometricImmersion.chartMetricBilin_pullback
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M}
    {f : N → M} (h : IsRiemannianIsometricImmersion gN gM f)
    (a p : N) (b : M) (hp : p ∈ (chartAt HN a).source)
    (hfp : f p ∈ (chartAt H b).source) (v w : EN) :
    chartMetricBilin gM b (extChartAt I b (f p))
        (fderiv ℝ (fun z : EN => extChartAt I b (f ((extChartAt IN a).symm z)))
          (extChartAt IN a p) v)
        (fderiv ℝ (fun z : EN => extChartAt I b (f ((extChartAt IN a).symm z)))
          (extChartAt IN a p) w) =
      chartMetricBilin gN a (extChartAt IN a p) v w := by
  rw [← trivToE_mfderiv_trivFromE a p b hp hfp
      (h.contMDiff.mdifferentiableAt (by simp)) v,
    ← trivToE_mfderiv_trivFromE a p b hp hfp
      (h.contMDiff.mdifferentiableAt (by simp)) w,
    chartMetricBilin_trivToE gM b (f p) hfp, h.inner_map]
  have hp' : (extChartAt IN a).symm (extChartAt IN a p) = p :=
    (extChartAt IN a).left_inv (by simpa using hp)
  change gN.inner p _ _ = gN.inner _ _ _
  rw [hp']
  rfl

theorem IsRiemannianIsometricImmersion.chartMetricBilin_pullback_eventually
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M}
    {f : N → M} (h : IsRiemannianIsometricImmersion gN gM f)
    (a : N) :
    ∀ᶠ z in nhds (extChartAt IN a a), ∀ v w : EN,
      chartMetricBilin gM (f a) (writtenInExtChartAt IN I a f z)
          (fderiv ℝ (writtenInExtChartAt IN I a f) z v)
          (fderiv ℝ (writtenInExtChartAt IN I a f) z w) =
        chartMetricBilin gN a z v w := by
  have hz : extChartAt IN a a ∈ (extChartAt IN a).target :=
    mem_extChartAt_target a
  have hcont : ContinuousAt (fun z => f ((extChartAt IN a).symm z))
      (extChartAt IN a a) :=
    h.continuous.continuousAt.comp (continuousAt_extChartAt_symm a)
  have hsrc : ∀ᶠ z in nhds (extChartAt IN a a),
      f ((extChartAt IN a).symm z) ∈ (chartAt H (f a)).source := by
    apply hcont.preimage_mem_nhds
    simpa only [extChartAt_to_inv] using
      (chartAt H (f a)).open_source.mem_nhds (mem_chart_source H (f a))
  filter_upwards [(isOpen_extChartAt_target a).mem_nhds hz, hsrc] with z hz hsrc
  intro v w
  have hp : (extChartAt IN a).symm z ∈ (chartAt HN a).source := by
    simpa using (extChartAt IN a).map_target hz
  have hid := h.chartMetricBilin_pullback a ((extChartAt IN a).symm z)
    (f a) hp hsrc v w
  rw [(extChartAt IN a).right_inv hz] at hid
  exact hid

end ChartDerivative

end DifferentialGeometry.Geometry
