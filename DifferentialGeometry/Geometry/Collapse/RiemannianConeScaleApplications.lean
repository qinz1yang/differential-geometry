import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Metric.InnerProductRadialCone
import DifferentialGeometry.Geometry.Metric.Approximation.Bilipschitz
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Consumers of the LC21–LC23 producers and bindings

* Euclidean three-space is its own cone at infinity (LC21 producers).
* A bounded space blown down by factors tending to zero collapses pointedly to the point, for
  arbitrary basepoints (`pointedGHConverges_punit_of_rescale`).
* A compact connected manifold with an arbitrary smooth metric (A2 induced metric): the constant
  sequence converges to itself, transfers to the point cone at a fixed enlarged scale (LC22
  binding, LC21 binding), and its blow-downs by the scales `α + 1` have cone scales in a bounded
  interval uniformly over all points (LC23 binding).
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

/-- A complete pointed space is the pointed limit of its constant sequence. -/
theorem pointedGHConverges_const {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (q : Y) :
    PointedGHConverges (fun _ : ℕ => q) q :=
  ⟨inferInstance, fun _ _ hε hεR =>
    Eventually.of_forall fun _ =>
      ⟨PointedBallApprox.ofIsometryEquiv (IsometryEquiv.refl _) q hε hεR⟩⟩

/-- A bounded space rescaled by factors `c j → 0` converges pointedly to the point, whatever the
basepoints. -/
theorem pointedGHConverges_punit_of_rescale {X : Type*} [m : MetricSpace X]
    (hb : Bornology.IsBounded (univ : Set X)) (c : ℕ → ℝ) (hc : ∀ j, 0 < c j)
    (hc0 : Tendsto c atTop (𝓝 0)) (z : ℕ → X) :
    @PointedGHConverges (fun _ : ℕ => X) (fun j => m.rescale (c j) (hc j)) PUnit _ z
      PUnit.unit := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  have hD : 0 ≤ Metric.diam (univ : Set X) := Metric.diam_nonneg
  have hev : ∀ᶠ j in atTop, c j * Metric.diam (univ : Set X) < ε := by
    have ht : Tendsto (fun j => c j * Metric.diam (univ : Set X)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hc0.mul_const (Metric.diam (univ : Set X))
    exact ht.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with j hj
  refine ⟨@PointedBallApprox.mk X PUnit (m.rescale (c j) (hc j)) _ (z j) PUnit.unit R ε hε hεR
    (fun _ => PUnit.unit) rfl ?_ ?_⟩
  · intro x x'
    rw [dist_self, zero_sub, abs_neg, MetricSpace.rescale_dist,
      abs_of_nonneg (mul_nonneg (hc j).le dist_nonneg)]
    have hd : dist x.val x'.val ≤ Metric.diam (univ : Set X) :=
      Metric.dist_le_diam_of_mem hb (mem_univ _) (mem_univ _)
    calc c j * dist x.val x'.val ≤ c j * Metric.diam (univ : Set X) :=
          mul_le_mul_of_nonneg_left hd (hc j).le
      _ < ε := hj
  · intro _ _
    refine ⟨⟨z j, ?_⟩, ?_⟩
    · change c j * dist (z j) (z j) ≤ R
      rw [dist_self, mul_zero]
      linarith
    · rw [dist_self]
      exact hε

/-- LC21 consumer: Euclidean three-space, with its inner-product cone data, is its own cone at
infinity at every scale. -/
theorem euclideanThree_cone_at_infinity (R : ℝ) (hR : 0 < R) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    Nonempty (@KleinerLottApprox (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))
      ((inferInstance : MetricSpace (EuclideanSpace ℝ (Fin 3))).rescale R⁻¹ (inv_pos.mpr hR)) _
      0 0 ε) :=
  (RadialConeData.ofInnerProductSpace
    (EuclideanSpace ℝ (Fin 3))).nonempty_kleinerLottApprox_rescale_self R hR hε hε1

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [ConnectedSpace M] [CompactSpace M]

/-- LC21 + LC22 bindings on a compact connected manifold with an arbitrary smooth metric (A2
induced metric): for every `0 < δ < 1` there is a scale `R` such that the constant sequence, with
metric tensor `R⁻² g`, eventually has actual Kleiner–Lott `δ`-maps to the point. -/
theorem compactManifold_rescaled_transfer_to_point (g : SmoothRiemannianMetric I M) (p : M)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    letI := inducedMetricSpace g
    ∃ R : ℝ, ∃ hR : 0 < R, ∀ᶠ _ : ℕ in atTop,
      (∀ a b, riemannianEDistOf (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) a b =
        ENNReal.ofReal (@dist M ((inducedMetricSpace g).rescale R⁻¹ (inv_pos.mpr hR)).toDist
          a b)) ∧
      Nonempty (@KleinerLottApprox M PUnit ((inducedMetricSpace g).rescale R⁻¹ (inv_pos.mpr hR))
        _ p PUnit.unit δ) := by
  let := inducedMetricSpace g
  have hcomplete : CompleteSpace M := complete_of_compact
  let ε := min (δ / 100) (1 / (2 * (2 * (δ⁻¹ + δ) + 4)))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨R₀, hR₀⟩ := exists_riemannian_point_cone_of_compactSpace g
    (inducedMetricSpace_hmetric g) p hε hε1
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨_, hG⟩ := hR₀ R hR (le_max_left _ _)
  obtain ⟨G⟩ := hG
  exact ⟨R, hR, eventually_riemannian_rescaled_approx_fixed_target (X := fun _ : ℕ => M)
    (fun _ => g) (fun _ => inducedMetricSpace_hmetric g) (pointedGHConverges_const p) R hR hδ
    hδone G⟩

/-- LC23 binding consumer: the blow-downs of a compact connected manifold with an arbitrary
smooth metric by the scales `ρ_α ≡ α + 1` collapse to the point; LC23 then gives, uniformly over
all points on a tail, a cone scale `s ∈ [T, V]` with an actual Kleiner–Lott `δ`-map from the
manifold with metric tensor `(s (α + 1))⁻² g` to the point. -/
theorem compactManifold_bounded_cone_scale (g : SmoothRiemannianMetric I M) {δ T : ℝ}
    (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    letI := inducedMetricSpace g
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧
        Nonempty (@KleinerLottApprox M PUnit ((inducedMetricSpace g).rescale
          (s * ((α : ℝ) + 1))⁻¹ (inv_pos.mpr (mul_pos hs (Nat.cast_add_one_pos α)))) _ p
          PUnit.unit δ) := by
  let := inducedMetricSpace g
  have hb : Bornology.IsBounded (univ : Set M) := isCompact_univ.isBounded
  have hpos (α : ℕ) : 0 < (α : ℝ) + 1 := Nat.cast_add_one_pos α
  obtain ⟨V, hTV, α₀, h⟩ := exists_riemannian_bounded_cone_scale (M := fun _ : ℕ => M)
    (fun _ => g) (fun _ => inducedMetricSpace_hmetric g) (fun α _ => (α : ℝ) + 1)
    (fun α _ => hpos α) (ι := Unit) (N := fun _ => PUnit) (C := fun _ => PUnit)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (fun a ha z => ⟨(), id, strictMono_id, by
      have hc0 : Tendsto (fun j => ((a j : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp ha))
      exact pointedGHConverges_punit_of_rescale hb (fun j => ((a j : ℝ) + 1)⁻¹)
        (fun j => inv_pos.mpr (hpos (a j))) hc0 z⟩)
    (fun _ ε hε hε1 => exists_kleinerLottApprox_rescale_point_of_compactSpace PUnit.unit hε hε1)
    hδ hδone hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, _, _, hk⟩ := h α hα p
  exact ⟨s, hs, hTs, hsV, hk⟩

end Manifold

end DifferentialGeometry.Geometry.Collapse
