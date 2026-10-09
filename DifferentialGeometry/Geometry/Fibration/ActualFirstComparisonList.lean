import DifferentialGeometry.Geometry.Fibration.ActualGlobalDerivativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsResidualApplications

/-!
# TCP01 (bindable part): whole two-stratum comparison lists and early buffers

Blueprint `master207B.tex`, TCP01 (`lem:fibration-first-comparison-list`, B:5250–5315), on the
final LC87 family `P : LocalChartPackets`, for a circle centre `p_i` with `R_i = ρ(p_i)` and
`D_i = B(p_i, 10R_i)`:

* `tcp01_row`: the circle, slim and edge indices whose ACTUAL closed supports meet `D_i` together
  with the meeting zero supports number at most the numerical `fc07ActiveBound` (independent of `Δ`
  and noncollapse); for `L = 10⁶Δ`, `LΛ < 10⁻⁵` every listed ratio `R_j/R_i` lies in
  `(99/100, 101/100)`; every listed original smooth coordinate is smooth on `D_i`; at most one zero
  support meets `D_i`, and `D_i` lies in its buffered shell with the original radial function smooth
  on an open neighbourhood of `D_i`; the circle coordinate's early quality: value error `< γ` and
  `(1 + γ)/R_i`-Lipschitz on `B(p_i, 200R_i)` (the long tests of packet (i) at derivative
  separation `201` on the far-test ball `B(p_i, 201·10⁴R_i) ⊇ B(p_i, 1000R_i)` are the field
  `CircleAdaptedCentre.test`); and `|η_i(q)| ≤ 8` on `B(p_i, 200R_i)` puts `q` in `B(p_i, 102R_i)`.
* `ratio_mem_Ioo_of_lipschitz_KA2`: the slow-scale ratio bound.

* `tcp01_rowR`: on `LocalChartPacketsR` (LC87b: LFR07's residual enclosure and LC62's local
  comparison) additionally every original point `|η_i| ≤ 8` of `B(p_i, 200R_i)` lies in `D_i`, and
  every meeting zero support has `s₀ = r₀/R_i ≥ T/20`.

NOT bound here: the Gram bound `‖Dη(Dη)* − I‖ < γ/4` (derivable from packet (i): two-sided singular
values from the Lipschitz bound and the long tests against the splitting's coverage; plan in
`build-logs/resume/sheet-C14-KA2.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- Slow variation of a `Λ`-Lipschitz scale: `d(j, p) ≤ c ρ(p)` and `Λc < 1/100` give
`ρ(j)/ρ(p) ∈ (99/100, 101/100)`. -/
theorem ratio_mem_Ioo_of_lipschitz_KA2 {Y : Type*} [PseudoMetricSpace Y] {ρ : Y → ℝ} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hρL : LipschitzWith (Real.toNNReal Λ) ρ) {j p : Y} (hp : 0 < ρ p) {c : ℝ}
    (hd : dist j p ≤ c * ρ p) (hc : Λ * c < 1 / 100) :
    ρ j / ρ p ∈ Ioo (99 / 100 : ℝ) (101 / 100) := by
  have hl := hρL.dist_le_mul j p
  rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hl
  have h1 : |ρ j - ρ p| ≤ Λ * c * ρ p := by
    calc |ρ j - ρ p| ≤ Λ * dist j p := hl
      _ ≤ Λ * (c * ρ p) := mul_le_mul_of_nonneg_left hd hΛ
      _ = Λ * c * ρ p := by ring
  have h2 : Λ * c * ρ p < 1 / 100 * ρ p := mul_lt_mul_of_pos_right hc hp
  obtain ⟨h3, h4⟩ := abs_le.mp h1
  constructor
  · rw [lt_div_iff₀ hp]
    linarith
  · rw [div_lt_iff₀ hp]
    linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNT_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNT_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCT_C14KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The first (`ℝ²`) component of the original normalized `(2, β₂)`-splitting of the circle
adapted packet (i) at `j`. -/
def circleSplitFst_KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : X) (hj : j ∈ P.circle.centres) : X → ℝ² :=
  let A := P.circleAdapted j hj
  let sp := A.split
  letI := A.instY
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  fun x => (sp.toFun x).fst

/-- The circle coordinate of the adapted packet (i): value error `< γ` against the SAME splitting
and the physical Lipschitz bound `(1 + γ)/ρ(j)` on `B(j, 200ρ(j))`. -/
theorem circleAdapted_physical_KA2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) {j : X} (hj : j ∈ P.circle.centres) :
    (∀ x ∈ ball j (200 * ρ j), ‖cgpCircleCoord P.toLocalChartFamily j hj x -
        circleSplitFst_KA2 P j hj x‖ < γ) ∧
      ∀ y ∈ ball j (200 * ρ j), ∀ z ∈ ball j (200 * ρ j),
        ‖cgpCircleCoord P.toLocalChartFamily j hj y - cgpCircleCoord P.toLocalChartFamily j hj z‖ ≤
          (1 + γ) / ρ j * dist y z := by
  have hrj := hρ j
  have hn : ∀ y ∈ ball j (200 * ρ j), (ρ j)⁻¹ * dist y j < 200 := fun y hy =>
    inv_mul_dist_lt_of_mem_ball_LC87 hrj hy
  have he : ∀ y z : X, ((Real.toNNReal (1 + γ) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      (1 + γ) / ρ j * dist y z := fun y z => by
    rw [Real.coe_toNNReal _ (by linarith)]
    field_simp
  let A := P.circleAdapted j hj
  have hadapt := A.adapted
  have hlip := A.lipschitz
  refine ⟨fun x hx => hadapt x (hn x hx), fun y hy z hz => ?_⟩
  have h := @LipschitzOnWith.dist_le_mul X ℝ²
    (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).toPseudoMetricSpace _ _ _ _ hlip y (hn y hy) z
    (hn z hz)
  have h' : ‖cgpCircleCoord P.toLocalChartFamily j hj y - cgpCircleCoord P.toLocalChartFamily j hj z‖
      ≤ ((Real.toNNReal (1 + γ) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) := by
    rw [← dist_eq_norm]
    exact h
  linarith [he y z]

/-- The circle chart's enclosure at physical scale: `|η_j(q)| < 100` on `B(j, 200ρ(j))` puts `q` in
`B(j, 102ρ(j))`. -/
theorem circle_enclosure_physical_KA2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ L.circle.centres) {q : X} (hq : q ∈ ball j (200 * ρ j))
    (hη : ‖cgpCircleCoord L j hj q‖ < 100) : q ∈ ball j (102 * ρ j) := by
  have hrj := hρ j
  have hc := L.circle.chart_center j hj
  have hn : (ρ j)⁻¹ * dist q j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hq
  have hgoal : (ρ j)⁻¹ * dist q j < 102 → q ∈ ball j (102 * ρ j) := fun h => by
    rw [mem_ball]
    rw [inv_mul_lt_iff₀ hrj] at h
    linarith
  apply hgoal
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  have hq' : q ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    change (ρ j)⁻¹ * @dist X mX.toDist q c.center < 200
    rw [hc']
    exact hn
  have h := c.enclosure q hq' hη
  change (ρ j)⁻¹ * @dist X mX.toDist q c.center < 102 at h
  rw [hc'] at h
  exact h

/-- **TCP01, bindable part** (`lem:fibration-first-comparison-list`) on `LocalChartPackets`, at a
circle centre `i` (`R_i = ρ(i)`, `D_i = B(i, 10R_i)`): the whole comparison list count, the listed
ratios in `(99/100, 101/100)`, the listed original coordinates smooth on `D_i`, the zero
assertions, the early circle-coordinate quality and the enclosure of `|η_i| ≤ 8` in
`B(i, 102R_i)`. -/
theorem tcp01_row
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hγ : 0 ≤ γ) {i : X}
    (hi : i ∈ P.circle.centres) :
    (({j | j ∈ P.circle.centres ∧
          (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard : ℝ) +
        {j | j ∈ P.slim.centres ∧
          (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        {j | j ∈ P.edge.centres ∧
          (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        (zeroMeetingList P.zero i 10).ncard ≤ fc07ActiveBound) ∧
    (∀ j (hj : j ∈ P.circle.centres), (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCircleCoord P.toLocalChartFamily j hj)
          (ball i (10 * ρ i))) ∧
    (∀ j (hj : j ∈ P.slim.centres), (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.slim.centre j hj).coord (ball i (10 * ρ i))) ∧
    (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ρ j / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.edge.coord j) (ball i (10 * ρ i))) ∧
    (∀ k ∈ zeroMeetingList P.zero i 10, ∀ k' ∈ zeroMeetingList P.zero i 10, k = k') ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      (∀ x ∈ ball i (10 * ρ i), 3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
        dist k x < 19 / 20 * (P.zero.zero k hk).radius) ∧
      ∃ O : Set X, IsOpen O ∧ ball i (10 * ρ i) ⊆ O ∧
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (P.zero.zero k hk).radial O) ∧
    (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x -
        circleSplitFst_KA2 P i hi x‖ < γ) ∧
    (∀ y ∈ ball i (200 * ρ i), ∀ z ∈ ball i (200 * ρ i),
      ‖cgpCircleCoord P.toLocalChartFamily i hi y - cgpCircleCoord P.toLocalChartFamily i hi z‖ ≤
        (1 + γ) / ρ i * dist y z) ∧
    (∀ q ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi q‖ ≤ 8 →
      q ∈ ball i (102 * ρ i)) := by
  obtain ⟨hcount, hC, hS, hE, hZ1, hZ2⟩ := fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT i
  have hri := hρ i
  have hΛ1 : Λ < 1 / 100000000000 := by nlinarith
  have hΔΛ : Δ * Λ < 1 / 100000000000 := by nlinarith
  obtain ⟨hA1, hA2⟩ := circleAdapted_physical_KA2 P hγ hi
  refine ⟨hcount, fun j hj hmeet => ?_, fun j hj hmeet => ?_, fun j hj hmeet => ?_, hZ1, hZ2,
    hA1, hA2, fun q hq hη => circle_enclosure_physical_KA2 P.toLocalChartFamily hi hq
      (by linarith)⟩
  · obtain ⟨-, hd, hsub, hsub', -⟩ := hC j hj hmeet
    refine ⟨ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale hri hd (by nlinarith), ?_⟩
    exact (cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).mono (hsub.trans hsub')
  · obtain ⟨hcm, -, hd, hsub, hsub', -⟩ := hS j hj hmeet
    exact ⟨ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale hri hd (by nlinarith),
      hcm.mono (hsub.trans hsub')⟩
  · obtain ⟨-, hd, hsub, hsub', -⟩ := hE j hj hmeet
    exact ⟨ratio_mem_Ioo_of_lipschitz_KA2 hΛ P.lipschitz_scale hri hd (by nlinarith),
      (P.edge.contMDiffOn_coord hj).mono (hsub.trans hsub')⟩

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNR_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_C14KA2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

omit [CompactSpace X] in
/-- The closed support of LC31's annular cutoff of a zero ball lies in the open ball of its radius
(`e < 1/10`). -/
theorem zero_tsupport_subset_ball_KA2 {N' C' : X → Type} [∀ a, MetricSpace (N' a)]
    [∀ a, ChartedSpace E3 (N' a)] [∀ a, MetricSpace (C' a)] {o' : ∀ a, C' a} {δ' εr' e' : ℝ}
    (Zb : ZeroModelBall 𝓘(ℝ, E3) X g N' C' o' δ' εr' e') (hεr : 0 ≤ 1 + εr') (he : e' < 1 / 10) :
    tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile (Zb.radial y)) ⊆
      ball Zb.center Zb.radius := by
  obtain ⟨-, -, -, hts, -⟩ := zeroModelBall_radial_facts_KA2 Zb hεr
  intro y hy
  have h := (hts hy).2
  have hr := Zb.radius_pos
  rw [mem_ball]
  rw [inv_mul_lt_iff₀ hr] at h
  nlinarith

/-- **TCP01** (`lem:fibration-first-comparison-list`) on `LocalChartPacketsR` (LC87 with LFR07's
residual enclosure and LC62's local comparison), at a circle centre `i`: every clause of
`tcp01_row`, and in addition every original point `|η_i| ≤ 8` of `B(i, 200R_i)` lies in
`D_i = B(i, 10R_i)` and every zero support meeting `D_i` has `s₀ = r₀/R_i ≥ T/20`. -/
theorem tcp01_rowR
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hγ : 0 ≤ γ) (hεr : 0 ≤ εr) {i : X}
    (hi : i ∈ P.circle.centres) :
    (∀ q ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi q‖ ≤ 8 →
      q ∈ ball i (10 * ρ i)) ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      T / 20 ≤ (P.zero.zero k hk).radius / ρ i) ∧
    (({j | j ∈ P.circle.centres ∧
          (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard : ℝ) +
        {j | j ∈ P.slim.centres ∧
          (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        {j | j ∈ P.edge.centres ∧
          (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty}.ncard +
        (zeroMeetingList P.zero i 10).ncard ≤ fc07ActiveBound) ∧
    (∀ k ∈ zeroMeetingList P.zero i 10, ∀ k' ∈ zeroMeetingList P.zero i 10, k = k') := by
  have hrow := tcp01_row P.toLocalChartPacketsD.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hγ
    hi
  have hΔΛ : Δ * Λ < 1 / 100000000000 := by nlinarith
  refine ⟨fun q hq h8 => ?_, fun k hk hmeet => ?_, hrow.1, hrow.2.2.2.2.1⟩
  · exact mem_ball.mpr (LocalChartPacketsR.dist_lt_of_norm_coord_le P hi (mem_ball.mp hq) h8)
  · obtain ⟨y, hy1, hy2⟩ := hmeet
    have hyb := zero_tsupport_subset_ball_KA2 (P.zero.zero k hk) (by linarith) (by linarith) hy1
    rw [P.zero.zero_center k hk] at hyb
    exact LocalChartPacketsR.zero_ratio_of_meets P (by nlinarith) (by nlinarith) hk ⟨y, hyb, hy2⟩

end DifferentialGeometry.Geometry.Collapse
