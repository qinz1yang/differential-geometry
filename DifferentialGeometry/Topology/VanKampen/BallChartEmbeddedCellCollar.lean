import DifferentialGeometry.Topology.VanKampen.ConnectedSum
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem norm_smul_cellBoundary (b : CellBoundary 3) (r : ℝ) (hr : 0 ≤ r) :
    ‖r • (b : E3)‖ = r := by
  rw [norm_smul, Real.norm_of_nonneg hr, b.2, mul_one]

private theorem mem_ball_zero_one_iff (x : E3) :
    x ∈ Metric.ball (0 : E3) 1 ↔ ‖x‖ < 1 := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]

private def puncturedBallTwo : TopologicalSpace.Opens E3 :=
  ⟨{x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 2}, by
    have h1 : IsOpen {x : E3 | 0 < ‖x‖} := isOpen_lt continuous_const continuous_norm
    have h2 : IsOpen {x : E3 | ‖x‖ < 2} := isOpen_lt continuous_norm continuous_const
    simpa [Set.ofPred_and] using h1.inter h2⟩

private theorem radialHomeomorph_mem (p : CellBoundary 3 × Set.Ioo (-1 : ℝ) 1) :
    (1 + (p.2 : ℝ)) • (p.1 : E3) ∈ puncturedBallTwo := by
  have hpos : 0 < 1 + (p.2 : ℝ) := by linarith [p.2.2.1]
  have hlt : 1 + (p.2 : ℝ) < 2 := by linarith [p.2.2.2]
  exact ⟨by rw [norm_smul_cellBoundary p.1 _ hpos.le]; exact hpos,
    by rw [norm_smul_cellBoundary p.1 _ hpos.le]; exact hlt⟩

private theorem radialHomeomorph_direction_norm (x : E3) (hx : x ∈ puncturedBallTwo) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  have hpos : 0 < ‖x‖ := hx.1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
    inv_mul_cancel₀ (ne_of_gt hpos)]

private theorem radialHomeomorph_radius_mem (x : E3) (hx : x ∈ puncturedBallTwo) :
    (‖x‖ - 1) ∈ Set.Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

private def radialHomeomorph :
    (CellBoundary 3 × Set.Ioo (-1 : ℝ) 1) ≃ₜ puncturedBallTwo where
  toFun p := ⟨(1 + (p.2 : ℝ)) • (p.1 : E3), radialHomeomorph_mem p⟩
  invFun x :=
    (⟨‖(x : E3)‖⁻¹ • (x : E3), radialHomeomorph_direction_norm x x.2⟩,
      ⟨‖(x : E3)‖ - 1, radialHomeomorph_radius_mem x x.2⟩)
  left_inv p := by
    have hpos : 0 < 1 + (p.2 : ℝ) := by linarith [p.2.2.1]
    apply Prod.ext
    · apply Subtype.ext
      change ‖(1 + (p.2 : ℝ)) • (p.1 : E3)‖⁻¹ •
        ((1 + (p.2 : ℝ)) • (p.1 : E3)) = (p.1 : E3)
      rw [norm_smul_cellBoundary p.1 _ hpos.le, smul_smul,
        inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
    · apply Subtype.ext
      change ‖(1 + (p.2 : ℝ)) • (p.1 : E3)‖ - 1 = (p.2 : ℝ)
      rw [norm_smul_cellBoundary p.1 _ hpos.le]
      ring
  right_inv x := by
    have hrad : 1 + (‖(x : E3)‖ - 1) = ‖(x : E3)‖ := by ring
    apply Subtype.ext
    change (1 + (‖(x : E3)‖ - 1)) • (‖(x : E3)‖⁻¹ • (x : E3)) = (x : E3)
    rw [hrad, smul_smul, mul_inv_cancel₀ (ne_of_gt x.2.1), one_smul]
  continuous_toFun :=
    (by fun_prop : Continuous (fun p : CellBoundary 3 × Set.Ioo (-1 : ℝ) 1 =>
      (1 + (p.2 : ℝ)) • (p.1 : E3))).subtype_mk radialHomeomorph_mem
  continuous_invFun := by
    apply Continuous.prodMk
    · have hx : Continuous (fun x : puncturedBallTwo => (x : E3)) := continuous_subtype_val
      have hnorm : Continuous (fun x : puncturedBallTwo => ‖(x : E3)‖) :=
        continuous_norm.comp hx
      have hinv : Continuous (fun x : puncturedBallTwo => (‖(x : E3)‖)⁻¹) :=
        hnorm.inv₀ (fun x => ne_of_gt x.2.1)
      exact (hinv.smul hx).subtype_mk (fun x => radialHomeomorph_direction_norm x x.2)
    · exact ((continuous_norm.comp continuous_subtype_val).sub continuous_const).subtype_mk
        (fun x => radialHomeomorph_radius_mem x x.2)

private theorem puncturedBallTwo_subset_chart_source {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    (puncturedBallTwo : Set E3) ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  linarith [hx.2]

private noncomputable def chartPuncturedOpens {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) : TopologicalSpace.Opens M :=
  ⟨(c.chart : E3 → M) '' (puncturedBallTwo : Set E3),
    DifferentialGeometry.image_opens_isOpen c.chart (puncturedBallTwo_subset_chart_source c)⟩

private noncomputable def chartPuncturedMap {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) : puncturedBallTwo → chartPuncturedOpens c :=
  DifferentialGeometry.PartialDiffeomorph.opensMap c.chart (fun _ hx => hx)

private theorem chartPuncturedMap_isOpenEmbedding {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    IsOpenEmbedding (chartPuncturedMap c) :=
  DifferentialGeometry.PartialDiffeomorph.opensMap_isOpenEmb c.chart
    (puncturedBallTwo_subset_chart_source c) (fun _ hx => hx)

private noncomputable def ballChartCollarCore {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    CellBoundary 3 × Set.Ioo (-1 : ℝ) 1 → M :=
  fun p => (chartPuncturedMap c (radialHomeomorph p) : M)

private theorem ballChartCollarCore_isOpenEmbedding {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    IsOpenEmbedding (ballChartCollarCore c) :=
  ((chartPuncturedOpens c).isOpen.isOpenEmbedding_subtypeVal).comp
    ((chartPuncturedMap_isOpenEmbedding c).comp radialHomeomorph.isOpenEmbedding)

private noncomputable def ballChartCollarMap {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) : CellBoundary 3 × ℝ → M :=
  fun p => c.chart
    ((1 + ((TwoSidedCollar.realHomeomorphIoo 1 one_pos) p.2 : Set.Ioo (-1 : ℝ) 1) : ℝ) •
      (p.1 : E3))

private theorem one_add_radius_pos (t : ℝ) :
    0 < 1 + ((TwoSidedCollar.realHomeomorphIoo 1 one_pos t : Set.Ioo (-1 : ℝ) 1) : ℝ) := by
  have h := Set.mem_Ioo.mp ((TwoSidedCollar.realHomeomorphIoo 1 one_pos t : Set.Ioo (-1 : ℝ) 1).2)
  linarith [h.1]

private theorem one_add_radius_lt_one_iff (t : ℝ) :
    1 + ((TwoSidedCollar.realHomeomorphIoo 1 one_pos t : Set.Ioo (-1 : ℝ) 1) : ℝ) < 1 ↔ t < 0 := by
  have h1 : (1 + ((TwoSidedCollar.realHomeomorphIoo 1 one_pos t : Set.Ioo (-1 : ℝ) 1) : ℝ) < 1) ↔
      ((TwoSidedCollar.realHomeomorphIoo 1 one_pos t : Set.Ioo (-1 : ℝ) 1) : ℝ) < 0 := by
    constructor <;> intro h <;> linarith
  rw [h1]
  exact TwoSidedCollar.realHomeomorphIoo_neg_iff 1 one_pos t

private theorem one_add_radius_zero :
    1 + ((TwoSidedCollar.realHomeomorphIoo 1 one_pos (0 : ℝ) : Set.Ioo (-1 : ℝ) 1) : ℝ) = 1 := by
  rw [TwoSidedCollar.realHomeomorphIoo_zero]
  norm_num

private theorem ballChartCollarMap_isOpenEmbedding {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    IsOpenEmbedding (ballChartCollarMap c) :=
  (ballChartCollarCore_isOpenEmbedding c).comp
    (((Homeomorph.refl (CellBoundary 3)).prodCongr
      (TwoSidedCollar.realHomeomorphIoo 1 one_pos)).isOpenEmbedding)

private noncomputable def closedCellOfBallChart {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) : ClosedCell 3 → M :=
  fun d => c.chart (d : E3)

private theorem closedCellOfBallChart_mem_chart_source {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) (d : ClosedCell 3) :
    (d : E3) ∈ c.chart.source := by
  apply c.closedBall_subset_source
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  linarith [d.2]

private theorem closedCellOfBallChart_injective {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    Function.Injective (closedCellOfBallChart c) := by
  intro d e h
  exact Subtype.ext (c.chart.toPartialEquiv.injOn
    (closedCellOfBallChart_mem_chart_source c d)
    (closedCellOfBallChart_mem_chart_source c e) h)

private theorem closedCellOfBallChart_continuous {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    Continuous (closedCellOfBallChart c) :=
  c.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (closedCellOfBallChart_mem_chart_source c)

private theorem range_cellInteriorInclusion_three :
    Set.range (cellInteriorInclusion 3) = {d : ClosedCell 3 | ‖(d : E3)‖ < 1} := by
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hd
    exact ⟨⟨(d : E3), hd⟩, Subtype.ext rfl⟩

private theorem embeddedCellInteriorImage_closedCellOfBallChart {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    embeddedCellInteriorImage (closedCellOfBallChart c) = c.chart '' Metric.ball (0 : E3) 1 := by
  rw [embeddedCellInteriorImage, range_cellInteriorInclusion_three]
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(d : E3), (mem_ball_zero_one_iff _).mpr hd, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, le_of_lt ((mem_ball_zero_one_iff x).mp hx)⟩,
      (mem_ball_zero_one_iff x).mp hx, rfl⟩

private theorem chart_mem_chart_ball_iff {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) {x : E3}
    (hx : x ∈ c.chart.source) :
    c.chart x ∈ c.chart '' Metric.ball (0 : E3) 1 ↔ x ∈ Metric.ball (0 : E3) 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : x = y := c.chart.toPartialEquiv.injOn hx (c.ball_subset_source hy) hyx.symm
    rwa [hxy]
  · intro hx'
    exact ⟨x, hx', rfl⟩

private theorem ballChartCollarMap_mem_complement_iff {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) (p : CellBoundary 3 × ℝ) :
    ballChartCollarMap c p ∈ embeddedCellComplement (closedCellOfBallChart c) ↔ 0 ≤ p.2 := by
  have hsrc : (1 + ((TwoSidedCollar.realHomeomorphIoo 1 one_pos) p.2 : Set.Ioo (-1 : ℝ) 1) : ℝ) •
      (p.1 : E3) ∈ c.chart.source :=
    puncturedBallTwo_subset_chart_source c
      (radialHomeomorph_mem (p.1, (TwoSidedCollar.realHomeomorphIoo 1 one_pos) p.2))
  rw [ballChartCollarMap, embeddedCellComplement, Set.mem_compl_iff,
    embeddedCellInteriorImage_closedCellOfBallChart, chart_mem_chart_ball_iff c hsrc,
    mem_ball_zero_one_iff, norm_smul_cellBoundary p.1 _ (one_add_radius_pos p.2).le,
    one_add_radius_lt_one_iff]
  exact not_lt

private theorem ballChartCollarMap_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) (b : CellBoundary 3) :
    ballChartCollarMap c (b, 0) = closedCellOfBallChart c (cellBoundaryInclusion 3 b) := by
  rw [ballChartCollarMap, closedCellOfBallChart, one_add_radius_zero, one_smul]
  rfl

private theorem isImmersionOfComplement_cellInteriorInclusion :
    Manifold.IsImmersionOfComplement Unit (𝓡 3) (𝓡 3) ∞
      (Subtype.val : CellInterior 3 → E3) := by
  have : IsManifold (𝓡 3) ∞ (CellInterior 3) :=
    @Topology.IsOpenEmbedding.isManifold_singleton ℝ E3 E3 _ _ _ _
      (𝓡 3) ∞ (CellInterior 3) _ (cellInteriorNonempty 3) Subtype.val
      ((isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal)
  intro x
  let φ : OpenPartialHomeomorph (CellInterior 3) E3 := chartAt E3 x
  let ψ : OpenPartialHomeomorph E3 E3 := chartAt E3 (x : E3)
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt
    (ContinuousLinearEquiv.prodUnique ℝ E3 Unit) φ ψ ?_ ?_ ?_ ?_ ?_
  · exact mem_chart_source E3 x
  · exact mem_chart_source E3 (x : E3)
  · exact IsManifold.chart_mem_maximalAtlas x
  · exact IsManifold.chart_mem_maximalAtlas (x : E3)
  · intro z hz
    simp only [φ, ψ, Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      ContinuousLinearEquiv.prodUnique_apply]
    exact ((chartAt E3 x).extend (𝓡 3)).right_inv hz

private theorem isSmoothEmbedding_cellInteriorInclusion :
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (Subtype.val : CellInterior 3 → E3) :=
  ⟨isImmersionOfComplement_cellInteriorInclusion.isImmersion,
    Topology.IsEmbedding.subtypeVal⟩

private theorem isSmoothEmbedding_closedCellOfBallChart_interior {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (c : BallChart 3 (𝓡 3) M) :
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (embeddedCellInteriorMap (closedCellOfBallChart c)) := by
  have hsub : Set.range (Subtype.val : CellInterior 3 → E3) ⊆ c.chart.source := by
    rintro x ⟨a, rfl⟩
    exact c.ball_subset_source ((mem_ball_zero_one_iff (a : E3)).mpr a.2)
  change Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : CellInterior 3 => c.chart (x : E3))
  exact DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph c.chart
      isSmoothEmbedding_cellInteriorInclusion hsub

private noncomputable def ballChartTwoSidedCellCollar {M : Type u} [TopologicalSpace M]
    [ChartedSpace E3 M] (c : BallChart 3 (𝓡 3) M) :
    TwoSidedCellCollar (closedCellOfBallChart c) where
  toFun := ballChartCollarMap c
  isOpenEmbedding_toFun := ballChartCollarMap_isOpenEmbedding c
  zero_eq := ballChartCollarMap_zero c
  mem_complement_iff := ballChartCollarMap_mem_complement_iff c

noncomputable def smoothEmbeddedClosedThreeCellWithCollarOfBallChart {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (c : BallChart 3 (𝓡 3) M) : SmoothEmbeddedClosedThreeCellWithCollar M where
  toFun := closedCellOfBallChart c
  injective_toFun := closedCellOfBallChart_injective c
  continuous_toFun := closedCellOfBallChart_continuous c
  isSmoothEmbedding_interior := isSmoothEmbedding_closedCellOfBallChart_interior c
  twoSidedCollar := ballChartTwoSidedCellCollar c

theorem smoothEmbeddedClosedThreeCellWithCollarOfBallChart_complement {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (c : BallChart 3 (𝓡 3) M) :
    (smoothEmbeddedClosedThreeCellWithCollarOfBallChart c).complement = c.Punctured := by
  rw [SmoothEmbeddedClosedThreeCellWithCollar.complement,
    smoothEmbeddedClosedThreeCellWithCollarOfBallChart, embeddedCellComplement,
    embeddedCellInteriorImage_closedCellOfBallChart]
  rfl

theorem smoothEmbeddedClosedThreeCellWithCollarOfBallChart_boundaryMap {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (c : BallChart 3 (𝓡 3) M) (b : CellBoundary 3) :
    ((smoothEmbeddedClosedThreeCellWithCollarOfBallChart c).boundaryMap b : M) =
      c.boundaryMap ⟨(b : E3), by simpa [dist_eq_norm] using b.2⟩ := rfl

end DifferentialGeometry.Topology.ThreeManifold
