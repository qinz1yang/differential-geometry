import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialPointSelection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open scoped _root_.Topology

private theorem anchoredSelectionFactor_bounds :
    0 < 1 - 1 / Real.sqrt 2 ∧ 1 - 1 / Real.sqrt 2 < 1 ∧
      (1 - (1 - 1 / Real.sqrt 2)) ^ 2 = 1 / 2 := by
  have hroot : 0 < Real.sqrt 2 := zero_lt_one.trans Real.one_lt_sqrt_two
  refine ⟨sub_pos.mpr ((div_lt_one hroot).2 Real.one_lt_sqrt_two), ?_, ?_⟩
  · linarith [one_div_pos.mpr hroot]
  · have heq : 1 - (1 - 1 / Real.sqrt 2) = 1 / Real.sqrt 2 := by ring
    rw [heq, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

section ProperMetric

variable {X : Type*} [MetricSpace X] [ProperSpace X]

private theorem exists_anchoredControlledBall
    {f : X → ℝ} (hf : Continuous f) (p : X) {D : ℝ} (hD : 0 ≤ D)
    (q : X) (hq : dist p q < D) (hfq : 0 < f q) :
    ∃ w : X,
      let sigma := D + 1 - dist p w
      let s := (1 - 1 / Real.sqrt 2) * sigma
      dist p w < D + 1 ∧ 0 < sigma ∧ 0 < s ∧ 0 < f w ∧
        (1 - 1 / Real.sqrt 2) ^ 2 * f q ≤ f w * s ^ 2 ∧
        ∀ z : X, dist w z < s → f z ≤ 2 * f w := by
  let eta : ℝ := 1 - 1 / Real.sqrt 2
  obtain ⟨heta_pos, heta_lt, heta_square⟩ := anchoredSelectionFactor_bounds
  change 0 < eta at heta_pos
  change eta < 1 at heta_lt
  change (1 - eta) ^ 2 = 1 / 2 at heta_square
  let F : X → ℝ := fun z => f z * (D + 1 - dist p z) ^ 2
  have hF : Continuous F :=
    hf.mul ((continuous_const.sub (continuous_const.dist continuous_id)).pow 2)
  have hRpos : 0 < D + 1 := by linarith only [hD]
  obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall p (D + 1)).exists_isMaxOn
    ⟨p, by simpa only [Metric.mem_closedBall, dist_self] using hRpos.le⟩
    hF.continuousOn
  let sigma : ℝ := D + 1 - dist p w
  have hwle : dist p w ≤ D + 1 := by
    simpa only [Metric.mem_closedBall, dist_comm] using hw
  have hsigma_nonneg : 0 ≤ sigma := sub_nonneg.mpr hwle
  have hqball : q ∈ Metric.closedBall p (D + 1) := by
    rw [Metric.mem_closedBall, dist_comm]
    linarith
  have hqslack : 1 ≤ D + 1 - dist p q := by linarith
  have hqslack_square : 1 ≤ (D + 1 - dist p q) ^ 2 := by
    nlinarith only [mul_self_le_mul_self zero_le_one hqslack]
  have hweight : f q ≤ f w * sigma ^ 2 := by
    have hmaxq : F q ≤ F w := hmax hqball
    exact (le_mul_of_one_le_right hfq.le hqslack_square).trans hmaxq
  have hsigma_pos : 0 < sigma := by
    by_contra hn
    have hz : sigma = 0 := le_antisymm (le_of_not_gt hn) hsigma_nonneg
    rw [hz, zero_pow (by decide), mul_zero] at hweight
    exact (not_le_of_gt hfq) hweight
  have hfw : 0 < f w :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos hsigma_pos)).mp (hfq.trans_le hweight)
  have hwinside : dist p w < D + 1 := sub_pos.mp hsigma_pos
  have hwidentity : dist p w + sigma = D + 1 := by
    dsimp only [sigma]
    ring
  refine ⟨w, hwinside, hsigma_pos, mul_pos heta_pos hsigma_pos, hfw, ?_, ?_⟩
  · calc
      eta ^ 2 * f q ≤ eta ^ 2 * (f w * sigma ^ 2) :=
        mul_le_mul_of_nonneg_left hweight (sq_nonneg eta)
      _ = f w * (eta * sigma) ^ 2 := by ring
  · intro z hz
    change dist w z < eta * sigma at hz
    by_cases hfz : 0 ≤ f z
    · have htri := dist_triangle p w z
      have hslack : (1 - eta) * sigma ≤ D + 1 - dist p z := by
        nlinarith only [htri, hz, hwidentity]
      have hslack_pos : 0 < (1 - eta) * sigma :=
        mul_pos (sub_pos.mpr heta_lt) hsigma_pos
      have hzball : z ∈ Metric.closedBall p (D + 1) := by
        rw [Metric.mem_closedBall, dist_comm]
        linarith only [hslack, hslack_pos]
      have hsquare : ((1 - eta) * sigma) ^ 2 ≤ (D + 1 - dist p z) ^ 2 := by
        nlinarith only [mul_self_le_mul_self hslack_pos.le hslack]
      rw [mul_pow, heta_square] at hsquare
      have hmaxz : f z * (D + 1 - dist p z) ^ 2 ≤ f w * sigma ^ 2 := hmax hzball
      have hprod := mul_le_mul_of_nonneg_left hsquare hfz
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hsigma_pos)).mp
      nlinarith only [hmaxz, hprod]
    · exact (lt_of_not_ge hfz).le.trans (by linarith only [hfw])

end ProperMetric

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [CompleteSpace E] in
theorem exists_anchoredSpatialPointSelection_riemannian
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    {f : M → ℝ} (hf : Continuous f) (p : M) {D : ℝ} (hD : 0 ≤ D)
    (q : M) (hq : (riemannianEDistOf (I := I) g p q).toReal < D) (hfq : 0 < f q) :
    let d := fun x y : M => (riemannianEDistOf (I := I) g x y).toReal
    ∃ w : M,
      let sigma := D + 1 - d p w
      let s := (1 - 1 / Real.sqrt 2) * sigma
      d p w < D + 1 ∧ 0 < sigma ∧ 0 < s ∧ 0 < f w ∧
        (1 - 1 / Real.sqrt 2) ^ 2 * f q ≤ f w * s ^ 2 ∧
        ∀ z : M, riemannianEDistOf (I := I) g w z < ENNReal.ofReal s →
          f z ≤ 2 * f w := by
  classical
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  let : ProperSpace M := by
    by_cases hz : Module.finrank ℝ E = 0
    · let : Subsingleton E := Module.finrank_zero_iff.mp hz
      let : Subsingleton H := I.injective.subsingleton
      let : DiscreteTopology H := inferInstance
      let : DiscreteTopology M := ChartedSpace.discreteTopology H M
      let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
      infer_instance
    · let : NeZero (Module.finrank ℝ E) := ⟨hz⟩
      exact properSpace_riemMetric (I := I) hcomplete.complete g hEnorm
  have hd (a b : M) : dist a b = (riemannianEDistOf (I := I) g a b).toReal := by
    rw [riemMetric_dist_eq (I := I),
      ← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
  have hqMetric : dist p q < D := by simpa only [hd] using hq
  obtain ⟨w, hw, hsigma, hs, hfw, hweight, hcontrol⟩ :=
    exists_anchoredControlledBall hf p hD q hqMetric hfq
  refine ⟨w, ?_, ?_, ?_, hfw, ?_, ?_⟩
  · simpa only [hd] using hw
  · simpa only [hd] using hsigma
  · simpa only [hd] using hs
  · simpa only [hd] using hweight
  · intro z hz
    apply hcontrol z
    simpa only [hd] using ENNReal.toReal_lt_of_lt_ofReal hz

theorem exists_anchoredScalarSpatialPointSelection
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {D : ℝ} (hD : 0 ≤ D) (q : M)
    (hq : (riemannianEDistOf (I := I) g p q).toReal < D)
    (hRq : 0 < metricScalarAt (I := I) g q) :
    let d := fun x y : M => (riemannianEDistOf (I := I) g x y).toReal
    ∃ w : M,
      let sigma := D + 1 - d p w
      let s := (1 - 1 / Real.sqrt 2) * sigma
      d p w < D + 1 ∧ 0 < sigma ∧ 0 < s ∧ 0 < metricScalarAt (I := I) g w ∧
        (1 - 1 / Real.sqrt 2) ^ 2 * metricScalarAt (I := I) g q ≤
          metricScalarAt (I := I) g w * s ^ 2 ∧
        ∀ z : M, riemannianEDistOf (I := I) g w z < ENNReal.ofReal s →
          metricScalarAt (I := I) g z ≤ 2 * metricScalarAt (I := I) g w := by
  exact exists_anchoredSpatialPointSelection_riemannian g hcomplete
    (metricScalar_smooth (I := I) g).continuous p hD q hq hRq

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
