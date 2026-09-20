import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff
import Mathlib.Topology.Order.Compact


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open Set Filter Bundle
open scoped ContDiff Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_le_radialDistanceCutoff_of_isCompact
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set M} (hK : IsCompact K)
    {ι : Type*} {l : Filter ι} {R : ι → ℝ} (hR : Tendsto R l atTop)
    {c : ℝ} (hc : c < 1) :
    ∀ᶠ i in l, ∀ x ∈ K, c ≤ radialDistanceCutoff g p (R i) x := by
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hed : Continuous (fun x => riemannianEDistOf g p x) :=
    continuous_const.edist continuous_id
  have hcont : ContinuousOn (fun x => (riemannianEDistOf g p x).toReal) K := by
    apply ENNReal.continuousOn_toReal.comp' hed.continuousOn
    intro x _
    exact riemannianEDistOf_ne_top g p x
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont
  have hlarge := hR.eventually (eventually_ge_atTop (max 1 (B / (1 - c))))
  filter_upwards [hlarge] with i hi x hx
  have hpos : 0 < R i := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hi)
  have hBR : B ≤ (1 - c) * R i := by
    simpa only [mul_comm] using
      (div_le_iff₀ (sub_pos.mpr hc)).mp ((le_max_right _ _).trans hi)
  have hdist : (riemannianEDistOf g p x).toReal ≤ (1 - c) * R i :=
    (hB (mem_image_of_mem _ hx)).trans hBR
  have hdiv : (riemannianEDistOf g p x).toReal / R i ≤ 1 - c :=
    (div_le_iff₀ hpos).mpr hdist
  exact (by linarith : c ≤ 1 - (riemannianEDistOf g p x).toReal / R i).trans
    (le_max_right _ _)


theorem exists_eventually_abs_le_mul_radialDistanceCutoff
    (g : SmoothRiemannianMetric I M) (p : M)
    {ψ : ℝ × M → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {η : ℝ → ℝ} (hη : ∀ t, 0 ≤ η t)
    (hηone : ∀ z ∈ tsupport ψ, η z.1 = 1)
    {ι : Type*} {l : Filter ι} {R : ι → ℝ} (hR : Tendsto R l atTop) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in l, ∀ z : ℝ × M,
      |ψ z| ≤ C * (η z.1 * radialDistanceCutoff g p (R i) z.2) := by
  obtain ⟨B, hB⟩ := hψc.bddAbove_image hψ.abs.continuousOn
  let C : ℝ := 2 * max 0 B
  refine ⟨C, by positivity, ?_⟩
  have hcut := eventually_le_radialDistanceCutoff_of_isCompact g p
    (hψc.image continuous_snd) hR (c := (1 / 2 : ℝ)) (by norm_num)
  have hpos := hR.eventually (eventually_gt_atTop 0)
  filter_upwards [hcut, hpos] with i hi hRi z
  by_cases hz : z ∈ tsupport ψ
  · rw [hηone z hz, one_mul]
    have hlocal := hi z.2 (mem_image_of_mem Prod.snd hz)
    have hbound : |ψ z| ≤ max 0 B :=
      (hB (mem_image_of_mem (fun y => |ψ y|) hz)).trans (le_max_right _ _)
    dsimp only [C]
    nlinarith [le_max_left (0 : ℝ) B]
  · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hη _)
      (radialDistanceCutoff_mem_Icc g p hRi z.2).1)

end DifferentialGeometry.Geometry.Riemannian
