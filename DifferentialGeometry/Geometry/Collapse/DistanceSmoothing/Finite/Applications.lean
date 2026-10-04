import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.LocalizedDistanceSmoothing

/-!
# LFR02 consumers: angular threshold and distance to a point

* `sqrt_finite_inner_sub_le_arccos`: for unit vectors of a finite-order metric the chord is at
  most the angle.
* `exists_localized_distance_smoothing_lfr02_of_arccos`: LFR02 with the angular-diameter
  hypothesis `arccos g_q(v, v') < min{1, ε}/100`.
* `exists_localized_point_distance_smoothing_lfr02`: LFR02 for `Y = {p}` (the form used by LFR24
  with target `{z₀}`, A:26902).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open Bundle.ContMDiffRiemannianMetric

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- For unit vectors of a finite-order metric the chord is at most the angle. -/
theorem sqrt_finite_inner_sub_le_arccos {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {q : M}
    {v v' : TangentSpace I q} (hv : g.inner q v v = 1) (hv' : g.inner q v' v' = 1) :
    Real.sqrt (g.inner q (v - v') (v - v')) ≤ Real.arccos (g.inner q v v') := by
  have hcs := abs_finite_inner_le g q v v'
  rw [hv, hv', Real.sqrt_one, mul_one] at hcs
  have hcos : Real.cos (Real.arccos (g.inner q v v')) = g.inner q v v' :=
    Real.cos_arccos (abs_le.mp hcs).1 (abs_le.mp hcs).2
  have hexp : g.inner q (v - v') (v - v') = 2 - 2 * g.inner q v v' := by
    simp only [map_sub, sub_apply, hv, hv', g.symm q v' v]
    ring
  have hbound := Real.one_sub_sq_div_two_le_cos (x := Real.arccos (g.inner q v v'))
  rw [hcos] at hbound
  rw [Real.sqrt_le_left (Real.arccos_nonneg _), hexp]
  linarith

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- LFR02 with the angular-diameter hypothesis `arccos g_q(v, v') < min{1, ε}/100`. -/
theorem exists_localized_distance_smoothing_lfr02_of_arccos [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {ε : ℝ} (hε : 0 < ε) {Y U C : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty) (hU : IsOpen U)
    (hUY : U ⊆ Yᶜ)
    (hdir : ∀ q ∈ U, ∀ v ∈ finiteMinimizingDirectionsTo g Y q,
      ∀ v' ∈ finiteMinimizingDirectionsTo g Y q, Real.arccos (g.inner q v v') < min 1 ε / 100)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - Metric.infDist x Y| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x Y) ∧
      (∀ x y, |(F x - Metric.infDist x Y) - (F y - Metric.infDist y Y)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      HasCompactSupport (fun x => F x - Metric.infDist x Y) ∧
      tsupport (fun x => F x - Metric.infDist x Y) ⊆ U ∧
      ∀ x ∈ O, ∀ v ∈ finiteMinimizingDirectionsTo g Y x, ∀ w : TangentSpace I x,
        |mvfderiv (I := I) F x w + g.inner x v w| ≤ ε / 25 * Real.sqrt (g.inner x w w) :=
  exists_localized_distance_smoothing_lfr02 g hr hnorm hε hY hYne hU hUY
    (fun q hq v hv v' hv' => (sqrt_finite_inner_sub_le_arccos g hv.1 hv'.1).trans_lt
      (hdir q hq v hv v' hv')) hC hCU he

/-- LFR02 for the distance to a point `p ∉ U`. -/
theorem exists_localized_point_distance_smoothing_lfr02 [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {ε : ℝ} (hε : 0 < ε) {p : M} {U C : Set M} (hU : IsOpen U) (hpU : p ∉ U)
    (hdiam : ∀ q ∈ U, ∀ v ∈ finiteMinimizingDirectionsTo g {p} q,
      ∀ v' ∈ finiteMinimizingDirectionsTo g {p} q,
        Real.sqrt (g.inner q (v - v') (v - v')) < min 1 ε / 100)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - dist x p| < e) ∧ (∀ x, x ∉ U → F x = dist x p) ∧
      (∀ x y, |(F x - dist x p) - (F y - dist y p)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      HasCompactSupport (fun x => F x - dist x p) ∧ tsupport (fun x => F x - dist x p) ⊆ U ∧
      ∀ x ∈ O, ∀ v ∈ finiteMinimizingDirectionsTo g {p} x, ∀ w : TangentSpace I x,
        |mvfderiv (I := I) F x w + g.inner x v w| ≤ ε / 25 * Real.sqrt (g.inner x w w) := by
  have h := exists_localized_distance_smoothing_lfr02 g hr hnorm hε isClosed_singleton
    (singleton_nonempty p) hU (Set.subset_compl_singleton_iff.mpr hpU) hdiam hC hCU he
  simp only [Metric.infDist_singleton] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
