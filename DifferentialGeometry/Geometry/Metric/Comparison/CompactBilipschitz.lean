import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

/-!
# Uniform diameter and volume bounds from a bilipschitz comparison on a closed manifold

On a compact connected manifold, every smooth metric has finite diameter and positive total volume.
If metrics `g` are uniformly bilipschitz to ONE fixed reference metric `gRef`
(`Λ⁻¹ gRef ≤ g ≤ Λ gRef` as quadratic forms, written `g ≤ Λ gRef` and `gRef ≤ Λ g`), then they have
a common diameter bound and a common positive lower bound for the total volume, depending only on
`gRef`, `Λ` and the dimension (`exists_uniform_diam_volume_of_bilipschitz`). This is the form in
which part A of the merged LFR50 design delivers the initial data (dispositions, LFR50 item 3).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance compactBilipschitzMeasurableM : MeasurableSpace M := borel M
private local instance compactBilipschitzBorelM : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- On a compact connected manifold every smooth metric has finite diameter. -/
theorem exists_riemannianEDistOf_le_of_compact [CompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) :
    ∃ d : ℝ, ∀ x y : M, riemannianEDistOf g x y ≤ ENNReal.ofReal d := by
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  have hc : IsCompact (Set.univ : Set M) := isCompact_univ
  let := inducedMetricSpace g
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hc.isBounded
  refine ⟨C, fun x y => ?_⟩
  rw [inducedMetricSpace_hmetric g x y]
  exact ENNReal.ofReal_le_ofReal (hC (mem_univ x) (mem_univ y))

/-- On a nonempty manifold every smooth metric has positive total volume. -/
theorem exists_pos_ofReal_le_riemannianVolumeMeasure_univ [Nonempty M]
    (g : SmoothRiemannianMetric I M) :
    ∃ v : ℝ, 0 < v ∧ ENNReal.ofReal v ≤ riemannianVolumeMeasure I M g Set.univ := by
  have := riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hpos : 0 < riemannianVolumeMeasure I M g Set.univ :=
    isOpen_univ.measure_pos _ univ_nonempty
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  refine ⟨r, by exact_mod_cast hr0, ?_⟩
  rw [ENNReal.ofReal_coe_nnreal]
  exact hr.le

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
/-- A quadratic comparison `h ≤ Q g` transports a diameter bound from `g` to `h`. -/
theorem riemannianEDistOf_le_of_inner_le_mul (g h : SmoothRiemannianMetric I M) {Q d : ℝ}
    (hQ : 0 < Q) (hcomp : ∀ (x : M) (v : TangentSpace I x), h.inner x v v ≤ Q * g.inner x v v)
    (hd : ∀ x y : M, riemannianEDistOf g x y ≤ ENNReal.ofReal d) (x y : M) :
    riemannianEDistOf h x y ≤ ENNReal.ofReal (Real.sqrt Q * (max d 0 + 1)) := by
  have hsub := riemannianBallOf_subset_of_inner_le_mul g h x (r := max d 0 + 1) hQ
    (fun q _ w => hcomp q w)
  have hy : y ∈ riemannianBallOf g x (max d 0 + 1) := by
    change riemannianEDistOf g x y < ENNReal.ofReal (max d 0 + 1)
    refine (hd x y).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    linarith [le_max_left d 0]
  exact (hsub hy).le

/-- A quadratic comparison `g ≤ Q h` transports a total-volume lower bound from `g` to `h`. -/
theorem ofReal_le_riemannianVolumeMeasure_univ_of_inner_le_mul (g h : SmoothRiemannianMetric I M)
    {Q v : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ (x : M) (w : TangentSpace I x), g.inner x w w ≤ Q * h.inner x w w)
    (hv : ENNReal.ofReal v ≤ riemannianVolumeMeasure I M g Set.univ) :
    ENNReal.ofReal (v / Real.sqrt (Q ^ Module.finrank ℝ E)) ≤
      riemannianVolumeMeasure I M h Set.univ := by
  have hvol := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le (I := I) (M := M)
    h g hQ MeasurableSet.univ (fun x _ w => hcomp x w)
  have hs : 0 < Real.sqrt (Q ^ Module.finrank ℝ E) := Real.sqrt_pos.2 (pow_pos hQ _)
  rw [← ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top]
  refine le_trans ?_ (hv.trans hvol)
  rw [← ENNReal.ofReal_mul hs.le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_div_cancel₀ _ hs.ne']

/-- **Uniform initial bounds from one reference metric.** Metrics uniformly bilipschitz to a
fixed `gRef` on a closed connected manifold have a common diameter bound and a common positive
lower bound for the total volume. -/
theorem exists_uniform_diam_volume_of_bilipschitz [CompactSpace M] [ConnectedSpace M]
    (gRef : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ d v : ℝ, 0 < v ∧ ∀ g : SmoothRiemannianMetric I M,
      (∀ (x : M) (w : TangentSpace I x),
        g.inner x w w ≤ Λ * gRef.inner x w w ∧ gRef.inner x w w ≤ Λ * g.inner x w w) →
      (∀ x y : M, riemannianEDistOf g x y ≤ ENNReal.ofReal d) ∧
        ENNReal.ofReal v ≤ riemannianVolumeMeasure I M g Set.univ := by
  obtain ⟨d, hd⟩ := exists_riemannianEDistOf_le_of_compact (I := I) gRef
  obtain ⟨v, hv, hvol⟩ := exists_pos_ofReal_le_riemannianVolumeMeasure_univ (I := I) gRef
  have hs : 0 < Real.sqrt (Λ ^ Module.finrank ℝ E) := Real.sqrt_pos.2 (pow_pos hΛ _)
  refine ⟨Real.sqrt Λ * (max d 0 + 1), v / Real.sqrt (Λ ^ Module.finrank ℝ E),
    div_pos hv hs, fun g hg => ⟨fun x y => ?_, ?_⟩⟩
  · exact riemannianEDistOf_le_of_inner_le_mul gRef g hΛ (fun z w => (hg z w).1) hd x y
  · exact ofReal_le_riemannianVolumeMeasure_univ_of_inner_le_mul gRef g hΛ
      (fun z w => (hg z w).2) hvol

end DifferentialGeometry
