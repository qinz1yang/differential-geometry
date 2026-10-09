import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LipschitzSmoothing

/-!
# LC28: localized distance smoothing

Blueprint 207A, LC28 (`input:collapse-distance-smoothing`, A:21143–21160; KL Cor. 3.16(1)–(3),(5)),
proved here (the blueprint lists it as a source-qualified input). For `ε > 0` the threshold is the
explicit `θ(ε) = ε / 4`, independent of the manifold, the metric and the data.

* `exists_localized_distance_smoothing` (LC28): `M` complete Riemannian without boundary, `Y`
  closed nonempty, `U ⊆ Yᶜ` open, and the initial unit velocities `V_q(Y)` of minimizing geodesics
  to nearest points of `Y` of chordal diameter `< ε / 4` at every `q ∈ U`. For every compact
  `C ⊆ U` and `e > 0` there are `F` and an open `O ⊇ C` with `F` smooth on `O`, `|F - d_Y| < e`,
  `F = d_Y` off `U`, `|(F - d_Y) x - (F - d_Y) y| ≤ ε dist x y` and `F` `(1 + ε)`-Lipschitz.
  The output clauses are exactly (o1)–(o4) of `build-logs/resume/sheet-W3-F4.md`, Addendum 1.
* `sqrt_inner_sub_le_arccos`: for unit vectors the chord is at most the angle, so an angular
  diameter bound implies the chordal one.
* `exists_localized_distance_smoothing_of_arccos`: the same with the angular hypothesis.
* `exists_theta_localized_distance_smoothing`: the `∀ ε ∃ θ` form (with `θ = ε / 4`).
* `exists_localized_point_distance_smoothing`: the case `Y = {p}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC28** (localized distance smoothing), with `θ(ε) = ε / 4`. -/
theorem exists_localized_distance_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε : ℝ} (hε : 0 < ε) {Y U C : Set M} (hY : IsClosed Y)
    (hYne : Y.Nonempty) (hU : IsOpen U) (hUY : U ⊆ Yᶜ)
    (hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm Y q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm Y q, Real.sqrt (g.inner q (v - v') (v - v')) < ε / 4)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - Metric.infDist x Y| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x Y) ∧
      (∀ x y, |(F x - Metric.infDist x Y) - (F y - Metric.infDist y Y)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F := by
  have hdisj : Disjoint U Y := Set.subset_compl_iff_disjoint_right.mp hUY
  have hloc : ∀ b ∈ U, ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧
        (∀ x ∈ W, |f' x - Metric.infDist x Y| ≤ η) ∧
        (∀ x ∈ W, ∀ x' ∈ W, |(f' x - Metric.infDist x Y) - (f' x' - Metric.infDist x' Y)| ≤
          3 * ε / 4 * dist x x') ∧
        (∀ x ∈ W, ∀ x' ∈ W, |f' x - f' x'| ≤ (3 * ε / 4 + 1) * dist x x') := by
    intro b hb
    obtain ⟨W, hWo, hbW, hWU, hWc, happ⟩ := exists_local_distance_approximation g hEnorm hY hYne
      hU hdisj (θ := ε / 4) (L := 3 * ε / 4) (by linarith) hdiam hb
    refine ⟨W, hWo, hbW, hWU, hWc, fun η hη => ?_⟩
    obtain ⟨f', hsm, hcl, hd⟩ := happ η hη
    refine ⟨f', hsm, hcl, hd, fun x hx x' hx' => ?_⟩
    have h1 := hd x hx x' hx'
    have h2 : |Metric.infDist x Y - Metric.infDist x' Y| ≤ 1 * dist x x' := by
      rw [← Real.dist_eq]; exact (Metric.lipschitz_infDist_pt Y).dist_le_mul x x'
    calc |f' x - f' x'| = |((f' x - Metric.infDist x Y) - (f' x' - Metric.infDist x' Y)) +
          (Metric.infDist x Y - Metric.infDist x' Y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ 3 * ε / 4 * dist x x' + 1 * dist x x' := add_le_add h1 h2
      _ = (3 * ε / 4 + 1) * dist x x' := by ring
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlipF⟩ :=
    exists_smoothing_of_local_approximations g hEnorm (Metric.lipschitz_infDist_pt Y) hU hC hCU
      (by positivity) hloc he (ε' := ε / 4) (by positivity)
  refine ⟨F, O, hO, hCO, hFO, hclose, hout, fun x y => ?_, ?_⟩
  · have := hdiff x y
    calc _ ≤ (3 * ε / 4 + ε / 4) * dist x y := this
      _ = ε * dist x y := by ring
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have hmax : max ((1 : ℝ≥0) : ℝ) (3 * ε / 4 + 1) = 3 * ε / 4 + 1 :=
      max_eq_right (by simp only [NNReal.coe_one, le_add_iff_nonneg_left]; positivity)
    have := hlipF x y
    rw [hmax] at this
    calc _ ≤ (3 * ε / 4 + 1 + ε / 4) * dist x y := this
      _ = (1 + ε) * dist x y := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- For unit vectors the chord is at most the angle. -/
theorem sqrt_inner_sub_le_arccos (g : SmoothRiemannianMetric I M) {q : M}
    {v v' : TangentSpace I q} (hv : g.inner q v v = 1) (hv' : g.inner q v' v' = 1) :
    Real.sqrt (g.inner q (v - v') (v - v')) ≤ Real.arccos (g.inner q v v') := by
  have hcs := abs_inner_le_sqrt_mul_sqrt g q v v'
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

/-- LC28 with the angular-diameter hypothesis `arccos ⟪v, v'⟫ < ε / 4`. -/
theorem exists_localized_distance_smoothing_of_arccos (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε : ℝ} (hε : 0 < ε) {Y U C : Set M} (hY : IsClosed Y)
    (hYne : Y.Nonempty) (hU : IsOpen U) (hUY : U ⊆ Yᶜ)
    (hdir : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm Y q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm Y q, Real.arccos (g.inner q v v') < ε / 4)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - Metric.infDist x Y| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x Y) ∧
      (∀ x y, |(F x - Metric.infDist x Y) - (F y - Metric.infDist y Y)| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F :=
  exists_localized_distance_smoothing g hEnorm hε hY hYne hU hUY
    (fun q hq v hv v' hv' => (sqrt_inner_sub_le_arccos g hv.1 hv'.1).trans_lt
      (hdir q hq v hv v' hv')) hC hCU he

/-- The `∀ ε ∃ θ` form of LC28 (lane W3-F6's requested shape), with `θ = ε / 4`. -/
theorem exists_theta_localized_distance_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ > 0, θ = ε / 4 ∧ ∀ (Y : Set M), Y.Nonempty → IsClosed Y → ∀ (U : Set M), IsOpen U →
      U ⊆ Yᶜ → (∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm Y q,
        ∀ v' ∈ minimizingDirectionsTo g hEnorm Y q, Real.arccos (g.inner q v v') < θ) →
      ∀ (C : Set M), IsCompact C → C ⊆ U → ∀ e > 0, ∃ F : M → ℝ,
        (∃ K, LipschitzWith K F) ∧ (∃ W, IsOpen W ∧ C ⊆ W ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W) ∧
        (∀ x, |F x - Metric.infDist x Y| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x Y) ∧
        LipschitzWith (Real.toNNReal ε) (fun x => F x - Metric.infDist x Y) := by
  refine ⟨ε / 4, by positivity, rfl, fun Y hYne hY U hU hUY hdir C hC hCU e he => ?_⟩
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hlip⟩ :=
    exists_localized_distance_smoothing_of_arccos g hEnorm hε hY hYne hU hUY hdir hC hCU he
  refine ⟨F, ⟨_, hlip⟩, ⟨O, hO, hCO, hFO⟩, hclose, hout, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal _ hε.le]
  exact hdiff x y

/-- LC28 for the distance to a point (`Y = {p}`), in the form consumed by LC30. -/
theorem exists_localized_point_distance_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {ε : ℝ} (hε : 0 < ε) {p : M} {U C : Set M} (hU : IsOpen U)
    (hpU : p ∉ U)
    (hdiam : ∀ q ∈ U, ∀ v ∈ minimizingDirectionsTo g hEnorm {p} q,
      ∀ v' ∈ minimizingDirectionsTo g hEnorm {p} q,
        Real.sqrt (g.inner q (v - v') (v - v')) < ε / 4)
    (hC : IsCompact C) (hCU : C ⊆ U) {e : ℝ} (he : 0 < e) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧ (∀ x, x ∉ U → F x = Metric.infDist x {p}) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F :=
  exists_localized_distance_smoothing g hEnorm hε isClosed_singleton (singleton_nonempty p) hU
    (Set.subset_compl_singleton_iff.mpr hpU) hdiam hC hCU he

end DifferentialGeometry.Geometry.Collapse
