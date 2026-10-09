import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChart

/-!
# Compactness of the WHOLE original circle and slim slabs (abstract charts)

Lane C14-FIBRE-PRE, class-(b) derived lemma of dispositions-task53 ("compactness of the whole
original circle / slim slabs"); review 53 §2.1, GAF07 row: "原始闭 `4.01ℓ` slab 的紧致性及位于 `5ℓ`
域内的余量". Blueprint GAF07 (B:6049–6170): "The SAME compact set
`Q_i = {p in the original chart : |η_i(p)| ≤ 4.01ℓ_i} ⋐ Y_i` contains ALL these inverse images,
with a strict interior buffer. Its compactness follows from the original proper circle bundle of
LFR07 or the whole proper slim bundle of LFR20."

Compactness comes from the charts' PROPER restrictions (no compact or proper ambient space is
assumed); the enclosure from LC83 / LFR20.2; the coordinate maps the closed slab ONTO the closed
ball (LC83's surjective restriction, LFR20's `surjective`).

* `CircleChart.isCompact_closedSlab_FPRE`, `CircleChart.closedSlab_subset_ball_FPRE`,
  `CircleChart.coord_image_closedSlab_FPRE`: `{x ∈ B(p, 200) | ‖η x‖ ≤ a}`, `a < 100`, is compact,
  lies in `B(p, 102)`, and `η` maps it onto `B̄(0, a)`.
* `SlimChart.isCompact_closedSlab_FPRE`, `SlimChart.closedSlab_subset_ball_FPRE`,
  `SlimChart.coord_image_closedSlab_FPRE`: `{x ∈ B(p, L) | |η x| ≤ a}`, `a < 905·10³Δ`, is compact,
  lies in `B(p, .91L)`, and `η` maps it onto `[-a, a]`.
* `CircleChart.gaf07_slab_buffer_FPRE` (`ℓ = 1`), `SlimChart.gaf07_slab_buffer_FPRE`
  (`ℓ = 10⁵Δ`): GAF07's `Q = {|η| ≤ 4.01ℓ}` is compact, contained in the open `Y = {|η| < 5ℓ}` of
  the chart, with a uniform metric buffer (`cthickening δ Q ⊆ Y`, `δ > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Circle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CircleChart

/-- **The whole closed circle slab is compact** (LC83's proper restriction): for `a < 100`,
`{x ∈ B(p, 200) | ‖η x‖ ≤ a}` is compact. -/
theorem isCompact_closedSlab_FPRE (c : CircleChart I M) {a : ℝ} (ha : a < 100) :
    IsCompact {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ a} := by
  set f := diskPreimageMap (ball c.center 200) isOpen_ball c.coord
    c.contMDiffOn_coord.continuousOn 100
  have hK : IsCompact {z : planeBallOpens 100 | ‖(z : ℝ²)‖ ≤ a} := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' {z : planeBallOpens 100 | ‖(z : ℝ²)‖ ≤ a} = closedBall 0 a := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [mem_closedBall, dist_zero_right]
        exact hz
      · intro hw
        rw [mem_closedBall, dist_zero_right] at hw
        exact ⟨⟨w, mem_planeBallOpens_iff.mpr (hw.trans_lt ha)⟩, hw, rfl⟩
    rw [himg]
    exact isCompact_closedBall 0 a
  have heq : Subtype.val '' (f ⁻¹' {z : planeBallOpens 100 | ‖(z : ℝ²)‖ ≤ a}) =
      {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ a} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2.1, hu⟩
    · rintro ⟨hx, hxa⟩
      have hxD : x ∈ diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100 := by
        refine ⟨hx, ?_⟩
        rw [mem_preimage, mem_ball, dist_zero_right]
        exact hxa.trans_lt ha
      exact ⟨⟨x, hxD⟩, hxa, rfl⟩
  rw [← heq]
  exact (c.isProperMap.isCompact_preimage hK).image continuous_subtype_val

/-- The whole closed circle slab (`a < 100`) lies in `B(p, 102)` (LC83's enclosure). -/
theorem closedSlab_subset_ball_FPRE (c : CircleChart I M) {a : ℝ} (ha : a < 100) :
    {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ a} ⊆ ball c.center 102 :=
  fun x hx => c.enclosure x hx.1 (hx.2.trans_lt ha)

/-- The circle coordinate maps the whole closed slab ONTO `B̄(0, a)` (`a < 100`; LC83's surjective
restriction). -/
theorem coord_image_closedSlab_FPRE (c : CircleChart I M) {a : ℝ} (ha : a < 100) :
    c.coord '' {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ a} = closedBall 0 a := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hx.2
  · intro hw
    rw [mem_closedBall, dist_zero_right] at hw
    obtain ⟨u, hu⟩ := c.surjective ⟨w, mem_planeBallOpens_iff.mpr (hw.trans_lt ha)⟩
    have hu' : c.coord u.1 = w := congrArg Subtype.val hu
    exact ⟨u.1, ⟨u.2.1, by rw [hu']; exact hw⟩, hu'⟩

/-- **GAF07's circle slab buffer** (`ℓ = 1`): `Q = {x ∈ B(p, 200) | ‖η x‖ ≤ 4.01}` is compact and
lies in `B(p, 102)`, `Y = {x ∈ B(p, 200) | ‖η x‖ < 5}` is open, `Q ⊆ Y`, and some closed
`δ`-thickening of `Q`, `δ > 0`, still lies in `Y`. -/
theorem gaf07_slab_buffer_FPRE (c : CircleChart I M) :
    IsCompact {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ 401 / 100} ∧
      {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ 401 / 100} ⊆ ball c.center 102 ∧
      IsOpen {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 5} ∧
      ∃ δ, 0 < δ ∧ cthickening δ {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ ≤ 401 / 100} ⊆
        {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 5} := by
  have hQ := c.isCompact_closedSlab_FPRE (a := 401 / 100) (by norm_num)
  have hY : IsOpen {x | x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 5} :=
    (c.contMDiffOn_coord.continuousOn.norm).isOpen_inter_preimage isOpen_ball isOpen_Iio
  refine ⟨hQ, c.closedSlab_subset_ball_FPRE (by norm_num), hY, ?_⟩
  exact hQ.exists_cthickening_subset_open hY fun x hx => ⟨hx.1, by linarith [hx.2]⟩

end CircleChart

end Circle

section Slim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

namespace SlimChart

/-- **The whole closed slim slab is compact** (LFR20's proper restriction): for `a < 905·10³Δ`,
`{x ∈ B(p, L) | |η x| ≤ a}` is compact. -/
theorem isCompact_closedSlab_FPRE (c : SlimChart g hEnorm Δ σ α) {a : ℝ}
    (ha : a < 905 * 10 ^ 3 * Δ) :
    IsCompact {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ a} := by
  set f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
    c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
  have hK : IsCompact {z : lineBallOpens (905 * 10 ^ 3 * Δ) | |(z : ℝ)| ≤ a} := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' {z : lineBallOpens (905 * 10 ^ 3 * Δ) | |(z : ℝ)| ≤ a} =
        Icc (-a) a := by
      ext t
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact abs_le.mp hz
      · intro ht
        have ht' : |t| ≤ a := abs_le.mpr ht
        exact ⟨⟨t, mem_lineBallOpens_iff.mpr (ht'.trans_lt ha)⟩, ht', rfl⟩
    rw [himg]
    exact isCompact_Icc
  have heq : Subtype.val '' (f ⁻¹' {z : lineBallOpens (905 * 10 ^ 3 * Δ) | |(z : ℝ)| ≤ a}) =
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ a} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(mem_realSlabOpens_iff.mp u.2).1, hu⟩
    · rintro ⟨hx, hxa⟩
      have hxS : x ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
          c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) :=
        mem_realSlabOpens_iff.mpr ⟨hx, hxa.trans_lt ha⟩
      exact ⟨⟨x, hxS⟩, hxa, rfl⟩
  rw [← heq]
  exact (c.isProperMap.isCompact_preimage hK).image continuous_subtype_val

/-- The whole closed slim slab (`a ≤ 905·10³Δ`) lies in `B(p, .91L)` (LFR20.2). -/
theorem closedSlab_subset_ball_FPRE (c : SlimChart g hEnorm Δ σ α) {a : ℝ}
    (ha : a ≤ 905 * 10 ^ 3 * Δ) :
    {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ a} ⊆ ball p (91 / 100 * (10 ^ 6 * Δ)) :=
  fun x hx => c.enclosure x hx.1 (hx.2.trans ha)

/-- The slim coordinate maps the whole closed slab ONTO `[-a, a]` (`a ≤ 905·10³Δ`; LFR20's
`surjective`). -/
theorem coord_image_closedSlab_FPRE (c : SlimChart g hEnorm Δ σ α) {a : ℝ}
    (ha : a ≤ 905 * 10 ^ 3 * Δ) :
    c.coord '' {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ a} = Icc (-a) a := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact abs_le.mp hx.2
  · intro ht
    obtain ⟨x, hx, hxt⟩ := c.surjective ⟨by linarith [ht.1], ht.2.trans ha⟩
    exact ⟨x, ⟨hx, by rw [hxt]; exact abs_le.mpr ht⟩, hxt⟩

/-- **GAF07's slim slab buffer** (`ℓ = 10⁵Δ`, `0 < Δ`): `Q = {x ∈ B(p, L) | |η x| ≤ 4.01ℓ}` is
compact and lies in `B(p, .91L)`, `Y = {x ∈ B(p, L) | |η x| < 5ℓ}` is open, `Q ⊆ Y`, and some closed
`δ`-thickening of `Q`, `δ > 0`, still lies in `Y`. -/
theorem gaf07_slab_buffer_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) :
    IsCompact {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ∧
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ⊆
        ball p (91 / 100 * (10 ^ 6 * Δ)) ∧
      IsOpen {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| < 5 * (10 ^ 5 * Δ)} ∧
      ∃ δ, 0 < δ ∧
        cthickening δ {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ⊆
          {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| < 5 * (10 ^ 5 * Δ)} := by
  have hQ := c.isCompact_closedSlab_FPRE (a := 401 / 100 * (10 ^ 5 * Δ)) (by nlinarith)
  have hY : IsOpen {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| < 5 * (10 ^ 5 * Δ)} :=
    (c.lipschitz.continuous.abs.continuousOn).isOpen_inter_preimage isOpen_ball isOpen_Iio
  refine ⟨hQ, c.closedSlab_subset_ball_FPRE (by nlinarith), hY, ?_⟩
  exact hQ.exists_cthickening_subset_open hY fun x hx => ⟨hx.1, by nlinarith [hx.2]⟩

end SlimChart

end Slim

end DifferentialGeometry.Geometry.Collapse
