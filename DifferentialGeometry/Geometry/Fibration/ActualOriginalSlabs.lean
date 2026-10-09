import DifferentialGeometry.Geometry.Collapse.LocalExport.OriginalSlabCompactness
import DifferentialGeometry.Geometry.Fibration.ActualSlimSlabs
import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypesInhabitant

/-!
# The WHOLE original circle and slim slabs of the final family: compact, enclosed, buffered

Lane C14-FIBRE-PRE, class-(b) derived lemma of dispositions-task53; review 53 §2.1 (GAF07 row:
compact original closed `4.01ℓ` slab with margin inside the `5ℓ` domain). Physical units on the
final closed family `LocalChartPacketsC14Z` (projections `circle`, `slim`); the charts live at the
normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)`, whose topology is the same.

Circle charts (`ℓ = 1`, abstract kernels in `OriginalSlabCompactness.lean`; `η_j =
cgpCircleCoord`):
* `LocalChartPacketsC14Z.circle_closedSlab_FPRE`: for `a < 100`, the whole slab
  `{x ∈ B(j, 200ρ(j)) | ‖η_j x‖ ≤ a}` is compact, lies in `B(j, 102ρ(j))`, and `η_j` maps it onto
  `B̄(0, a)`.
* `LocalChartPacketsC14Z.isCompact_iUnion_circle_closedSlab_FPRE`: the union over all circle
  centres is compact.
* `LocalChartPacketsC14Z.circle_gaf07_buffer_FPRE`: `Q_j = {‖η_j‖ ≤ 4.01}` compact,
  `⊆ B(j, 102ρ(j))`, inside the open `Y_j = {‖η_j‖ < 5}` with a physical buffer `δ > 0`.
Slim charts (`ℓ = 10⁵Δ`; compactness from `isCompact_slimSlab_GAFS`, not re-proved):
* `LocalChartPacketsC14Z.slim_coord_image_closedSlab_FPRE`: for `a ≤ 905·10³Δ`, `η_j` maps the whole
  slab `{x ∈ B(j, 10⁶Δρ(j)) | |η_j x| ≤ a}` onto `[-a, a]`.
* `LocalChartPacketsC14Z.slim_gaf07_buffer_FPRE`: `Q_j = {|η_j| ≤ 4.01ℓ}` compact,
  `⊆ B(j, .91·10⁶Δρ(j))`, inside the open `Y_j = {|η_j| < 5ℓ}` with a physical buffer `δ > 0`.
* consumer `original_slabs_pempty_FPRE` on the inhabitant over `PEmpty`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The physical ball `B(j, kρ(j))` is the ball of radius `k` of the normalized metric at `j`. -/
theorem mem_ball_rescale_iff_FPRE {Z : Type*} {m : MetricSpace Z} {r : Z → ℝ} {j x : Z}
    (hj : 0 < r j) {k : ℝ} :
    x ∈ @ball Z (m.rescale (r j)⁻¹ (inv_pos.mpr hj)).toPseudoMetricSpace j k ↔
      x ∈ @ball Z m.toPseudoMetricSpace j (k * r j) := by
  change (r j)⁻¹ * @dist Z m.toDist x j < k ↔ @dist Z m.toDist x j < k * r j
  rw [inv_mul_lt_iff₀ hj]
  constructor <;> intro h <;> linarith

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- The circle slab facts in the normalized ball at `j` (kernels of `OriginalSlabCompactness`
applied to the chart of the final family; `η_j = cgpCircleCoord`). -/
theorem LocalChartPacketsC14Z.circle_closedSlab_normalized_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {j : X} (hj : j ∈ P.circle.centres) {a : ℝ} (ha : a < 100) :
    IsCompact {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace j 200 ∧
        ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} ∧
      {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace j 200 ∧
          ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} ⊆
        @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace j 102 ∧
      cgpCircleCoord P.toLocalChartFamily j hj ''
          {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace j 200 ∧
            ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} = closedBall 0 a ∧
      ContinuousOn (cgpCircleCoord P.toLocalChartFamily j hj)
        (@ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace j 200) := by
  have hc0 := P.circle.chart_center j hj
  let c := P.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc : c.center = j := hc0
  have h1 := c.isCompact_closedSlab_FPRE ha
  have h2 := c.closedSlab_subset_ball_FPRE ha
  have h3 := c.coord_image_closedSlab_FPRE ha
  have h4 := c.contMDiffOn_coord.continuousOn
  rw [hc] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- **The whole closed circle slab of the final family** (`a < 100`): compact, inside
`B(j, 102ρ(j))`, and mapped by `η_j` onto `B̄(0, a)`. -/
theorem LocalChartPacketsC14Z.circle_closedSlab_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {j : X} (hj : j ∈ P.circle.centres) {a : ℝ} (ha : a < 100) :
    IsCompact {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} ∧
      {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} ⊆
        ball j (102 * ρ j) ∧
      cgpCircleCoord P.toLocalChartFamily j hj ''
          {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} =
        closedBall 0 a := by
  have hr := hρ j
  obtain ⟨h1, h2, h3, -⟩ := P.circle_closedSlab_normalized_FPRE hj ha
  have hS : {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} =
      {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace j 200 ∧
        ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ a} := by
    ext x
    exact and_congr_left' (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]
    exact h1
  · intro x hx
    rw [hS] at hx
    exact (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 102)).mp (h2 hx)
  · rw [hS]
    exact h3

/-- The union of the whole closed circle slabs (`a < 100`) over all circle centres is compact. -/
theorem LocalChartPacketsC14Z.isCompact_iUnion_circle_closedSlab_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {a : ℝ} (ha : a < 100) :
    IsCompact (⋃ j : P.circle.centres,
      {x | x ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCircleCoord P.toLocalChartFamily j.1 j.2 x‖ ≤ a}) := by
  have := P.circle.finite_centres.to_subtype
  exact isCompact_iUnion fun j => (P.circle_closedSlab_FPRE j.2 ha).1

/-- **GAF07's circle slab buffer on the final family** (`ℓ = 1`): `Q_j = {x ∈ B(j, 200ρ(j)) |
‖η_j x‖ ≤ 4.01}` is compact and lies in `B(j, 102ρ(j))`; `Y_j = {x ∈ B(j, 200ρ(j)) | ‖η_j x‖ < 5}`
is open; some closed physical `δ`-thickening of `Q_j`, `δ > 0`, lies in `Y_j`. -/
theorem LocalChartPacketsC14Z.circle_gaf07_buffer_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {j : X} (hj : j ∈ P.circle.centres) :
    IsCompact {x | x ∈ ball j (200 * ρ j) ∧
        ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ 401 / 100} ∧
      {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ 401 / 100} ⊆
        ball j (102 * ρ j) ∧
      IsOpen {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ < 5} ∧
      ∃ δ, 0 < δ ∧ cthickening δ
          {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ ≤ 401 / 100} ⊆
        {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ < 5} := by
  have hr := hρ j
  obtain ⟨hQ, hsub, -⟩ := P.circle_closedSlab_FPRE hj (a := 401 / 100) (by norm_num)
  obtain ⟨-, -, -, h4⟩ := P.circle_closedSlab_normalized_FPRE hj (a := 401 / 100) (by norm_num)
  have hball : ball j (200 * ρ j) =
      @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace j 200 := by
    ext x
    exact (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).symm
  have hcont : ContinuousOn (cgpCircleCoord P.toLocalChartFamily j hj) (ball j (200 * ρ j)) := by
    rw [hball]
    exact h4
  have hY : IsOpen
      {x | x ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord P.toLocalChartFamily j hj x‖ < 5} :=
    hcont.norm.isOpen_inter_preimage isOpen_ball isOpen_Iio
  refine ⟨hQ, hsub, hY, ?_⟩
  exact hQ.exists_cthickening_subset_open hY fun x hx => ⟨hx.1, by linarith [hx.2]⟩

/-- **The slim coordinate maps the whole closed slab onto `[-a, a]`** (`a ≤ 905·10³Δ`; LFR20's
`surjective`, physical form). -/
theorem LocalChartPacketsC14Z.slim_coord_image_closedSlab_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {j : X} (hj : j ∈ P.slim.centres) {a : ℝ} (ha : a ≤ 905 * 10 ^ 3 * Δ) :
    (P.slim.centre j hj).coord ''
        {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ |(P.slim.centre j hj).coord x| ≤ a} =
      Icc (-a) a := by
  have hr := hρ j
  have hS : {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ |(P.slim.centre j hj).coord x| ≤ a} =
      {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace j (10 ^ 6 * Δ) ∧
        |(P.slim.centre j hj).coord x| ≤ a} := by
    ext x
    exact and_congr_left' (mem_ball_rescale_iff_FPRE (m := mX) hr (k := (10 ^ 6 * Δ))).symm
  rw [hS]
  let c := P.slim.centre j hj
  let Pk := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact Pk.coord_image_closedSlab_FPRE ha

/-- **GAF07's slim slab buffer on the final family** (`ℓ = 10⁵Δ`, `0 < Δ`): `Q_j = {x ∈
B(j, 10⁶Δρ(j)) | |η_j x| ≤ 4.01ℓ}` is compact (`isCompact_slimSlab_GAFS`) and lies in
`B(j, .91·10⁶Δρ(j))`; `Y_j = {x ∈ B(j, 10⁶Δρ(j)) | |η_j x| < 5ℓ}` is open; some closed physical
`δ`-thickening of `Q_j`, `δ > 0`, lies in `Y_j`. -/
theorem LocalChartPacketsC14Z.slim_gaf07_buffer_FPRE
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) (hΔ : 0 < Δ) {j : X} (hj : j ∈ P.slim.centres) :
    IsCompact {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
        |(P.slim.centre j hj).coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ∧
      {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
          |(P.slim.centre j hj).coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ⊆
        ball j (91 / 100 * (10 ^ 6 * Δ) * ρ j) ∧
      IsOpen {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
        |(P.slim.centre j hj).coord x| < 5 * (10 ^ 5 * Δ)} ∧
      ∃ δ, 0 < δ ∧ cthickening δ {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
          |(P.slim.centre j hj).coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ⊆
        {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
          |(P.slim.centre j hj).coord x| < 5 * (10 ^ 5 * Δ)} := by
  have hQ : IsCompact {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
      |(P.slim.centre j hj).coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} :=
    isCompact_slimSlab_GAFS P.toLocalChartFamily hΔ
      ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (by nlinarith)
  have hY : IsOpen {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
      |(P.slim.centre j hj).coord x| < 5 * (10 ^ 5 * Δ)} :=
    ((P.slim.centre j hj).contMDiffOn_coord.continuousOn.abs).isOpen_inter_preimage isOpen_ball
      isOpen_Iio
  refine ⟨hQ, fun x hx => (P.slim.centre j hj).dist_lt_of_abs_coord_le_ZERO hx.1
    (hx.2.trans (by nlinarith)), hY, ?_⟩
  exact hQ.exists_cthickening_subset_open hY fun x hx => ⟨hx.1, by nlinarith [hx.2]⟩

end Family

section Consumer

/-- The metric on `PEmpty` (the same term as the instance of `metricPEmpty_FAM`). -/
local instance metricSpacePEmpty_FPRE2 : MetricSpace PEmpty.{1} :=
  (MetricSpace.induced (PEmpty.elim : PEmpty.{1} → ℝ) (fun x => x.elim)
    inferInstance).replaceTopology (by ext s; simp only [Set.eq_empty_of_isEmpty s, isOpen_empty])

/-- The empty three-manifold (the same term as the instance of `metricPEmpty_FAM`). -/
local instance chartedSpacePEmpty_FPRE2 : ChartedSpace E3 PEmpty.{1} :=
  ChartedSpace.empty E3 PEmpty.{1}

/-- **Consumer on the structural inhabitant over `PEmpty`**: the final family over the empty
three-manifold has compact unions of whole closed circle slabs, and the circle and slim GAF07
buffers at every centre. -/
theorem original_slabs_pempty_FPRE (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) (hΔ : 0 < Δ) :
    ∃ P : LocalChartPacketsC14Z PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
        (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        manifoldOrientationPEmpty_FAMZ,
      IsCompact (⋃ j : P.circle.centres, {x | x ∈ ball j.1 (200 * (fun a : PEmpty.{1} => a.elim)
        j.1) ∧ ‖cgpCircleCoord P.toLocalChartFamily j.1 j.2 x‖ ≤ 401 / 100}) ∧
      (∀ j (hj : j ∈ P.slim.centres), ∃ δ, 0 < δ ∧ cthickening δ
          {x | x ∈ ball j (10 ^ 6 * Δ * (fun a : PEmpty.{1} => a.elim) j) ∧
            |(P.slim.centre j hj).coord x| ≤ 401 / 100 * (10 ^ 5 * Δ)} ⊆
        {x | x ∈ ball j (10 ^ 6 * Δ * (fun a : PEmpty.{1} => a.elim) j) ∧
          |(P.slim.centre j hj).coord x| < 5 * (10 ^ 5 * Δ)}) := by
  obtain ⟨P⟩ := nonempty_localChartPacketsC14Z_pempty_FAMZ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs ζ Λz manifoldOrientationPEmpty_FAMZ
  exact ⟨P, P.isCompact_iUnion_circle_closedSlab_FPRE (by norm_num),
    fun j hj => (P.slim_gaf07_buffer_FPRE hΔ hj).2.2.2⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
