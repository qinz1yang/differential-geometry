import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyWithZero
import DifferentialGeometry.Geometry.Collapse.FiniteBlockMap
import DifferentialGeometry.Analysis.Calculus.Cutoff.BufferedEdgeCutoff
import DifferentialGeometry.Analysis.Calculus.AnnularCutoff

/-!
# CGP01: the actual original global block map `𝓔⁰`

Blueprint `master207B.tex`, CGP01 (`prop:fibration-source-profile-binding`, B:3879–3955), on the
actual LC87 local chart family `L : LocalChartFamily` and the LC80 zero family
`Z : ZeroModelFamily` (LC87 item 1), with FC01's block map (`FiniteBlockMap.lean`).

* `lc87EdgeTransition` (`χ_E(y) = 1 − value(1 + y)`): a smooth nondecreasing profile with the CFS22
  properties; the LC87 edge profiles ARE CGP01's: `edgeHeightProfile = 1 − χ_{8,9}`
  (`edgeHeightProfile_eq_one_sub_cfsRamp`), `edgeCoordinateProfile s = 1 − χ_{8,9}(|s|)`
  (`edgeCoordinateProfile_eq_one_sub_cfsRamp_abs`).
* `EdgeFamily.contMDiff_cutoff_of_margin`: an actual edge cutoff is smooth once its closed support is
  in the OPEN chart ball (its height factor is smooth through LFR38's collar charts,
  `EdgeFamily.contMDiffAt_height_of_collar`).
* `cgpGlobalMap L Z` (`𝓔⁰`, defined ONCE): tags = circle, slim, edge, zero centres and the two
  special tags `ρ`, `E'`; every coordinate space is `ℝ²` (scalar coordinates on the axis
  `planeAxis`, an isometry; FC01 has `ℝ¹` for these blocks); radii `ρ(j)` / zero radii / `ρ`;
  cutoffs = LC87's actual cutoffs, LC31's annular cutoffs `Φ ∘ radial`, `1`, and
  `z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i)` (`cgpEdgeMarker`), `t = F/ρ` (`cgpHeight`),
  `h = χ_{1/5,3/10} · (1 − χ_{8,9})` (`cgpEdgeH`). `cgpGlobalMap'` is the same map on
  `LocalChartFamilyWithZero` (through `toLocalChartFamily` and `zero`).
* `cgp01_row`: smoothness (`contMDiff_cgpGlobalMap`, FC01's construction check on the actual
  domains) and CFS23's original identities on the original domains.

Deviations: (1) circle and slim cutoffs are LC87's own profiles (plateau `8`, support `< 9`, resp.
`< 8.9` in `η/(10⁵Δ)`), not the blueprint's `1 − χ_{8,9}(|η|)` (accepted by the lead); the edge
profiles coincide with the blueprint's for `χ = χ_E`. (2) All coordinate spaces are `ℝ²`.
Input beyond the families: `hmargin` (closed edge supports inside the OPEN chart balls, LC87 packet
(iv) through `fc18_edge_row`'s enclosure) and the zero-shell tolerance `e ≤ 1/8`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

section Transition

/-- The increasing profile `χ_E(y) = 1 − value(1 + y)` of the LC87 edge profiles. -/
def lc87EdgeTransition (y : ℝ) : ℝ := 1 - CutoffProfile.value (1 + y)

theorem lc87EdgeTransition_contDiff : ContDiff ℝ ∞ lc87EdgeTransition :=
  contDiff_const.sub (CutoffProfile.contDiff.comp (contDiff_const.add contDiff_id))

theorem lc87EdgeTransition_eq_zero {y : ℝ} (hy : y ≤ 0) : lc87EdgeTransition y = 0 := by
  rw [lc87EdgeTransition, CutoffProfile.one_of_le_one (by linarith), sub_self]

theorem lc87EdgeTransition_eq_one {y : ℝ} (hy : 1 ≤ y) : lc87EdgeTransition y = 1 := by
  rw [lc87EdgeTransition, CutoffProfile.zero_of_two_le (by linarith), sub_zero]

theorem lc87EdgeTransition_mem_Icc (y : ℝ) : lc87EdgeTransition y ∈ Icc (0 : ℝ) 1 := by
  have h := CutoffProfile.mem_Icc (1 + y)
  rw [lc87EdgeTransition]
  constructor <;> linarith [h.1, h.2]

theorem lc87EdgeTransition_monotone : Monotone lc87EdgeTransition := fun a b hab => by
  have := CutoffProfile.antitone_value (show 1 + a ≤ 1 + b by linarith)
  rw [lc87EdgeTransition, lc87EdgeTransition]
  linarith

theorem abs_deriv_lc87EdgeTransition_le (y : ℝ) :
    |deriv lc87EdgeTransition y| ≤ max 1 CutoffProfile.derivBound := by
  have hd : HasDerivAt lc87EdgeTransition (-(deriv CutoffProfile.value (1 + y) * 1)) y := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 y := (hasDerivAt_id y).const_add 1
    have h2 := ((CutoffProfile.contDiff.differentiable (by simp)) (1 + y)).hasDerivAt.comp y h1
    exact h2.const_sub 1
  rw [hd.deriv, abs_neg, mul_one]
  exact (CutoffProfile.abs_deriv_le_derivBound (1 + y)).trans (le_max_right _ _)

theorem descendingIntervalProfile_eq_one_sub_cfsRamp (a b x : ℝ) :
    descendingIntervalProfile a b x = 1 - cfsRamp lc87EdgeTransition a b x := by
  rw [descendingIntervalProfile, cfsRamp, lc87EdgeTransition, sub_sub_cancel]

/-- The LC87 edge height profile is `g = 1 − χ_{8,9}` for `χ = χ_E`. -/
theorem edgeHeightProfile_eq_one_sub_cfsRamp (x : ℝ) :
    edgeHeightProfile x = 1 - cfsRamp lc87EdgeTransition 8 9 x :=
  descendingIntervalProfile_eq_one_sub_cfsRamp 8 9 x

/-- The LC87 edge coordinate profile is `f(s) = 1 − χ_{8,9}(|s|)` for `χ = χ_E`. -/
theorem edgeCoordinateProfile_eq_one_sub_cfsRamp_abs (s : ℝ) :
    edgeCoordinateProfile s = 1 - cfsRamp lc87EdgeTransition 8 9 |s| := by
  have h0 : ∀ t : ℝ, t ≤ 8 → cfsRamp lc87EdgeTransition 8 9 t = 0 := fun t ht =>
    cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ht
  have hdef : edgeCoordinateProfile s =
      (1 - cfsRamp lc87EdgeTransition 8 9 (-s)) * (1 - cfsRamp lc87EdgeTransition 8 9 s) := by
    rw [edgeCoordinateProfile, intervalPlateauProfile, descendingIntervalProfile_eq_one_sub_cfsRamp,
      descendingIntervalProfile_eq_one_sub_cfsRamp, neg_neg, neg_neg]
  rw [hdef]
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs, h0 (-s) (by linarith), sub_zero, one_mul]
  · rw [abs_of_nonpos hs, h0 s (by linarith), sub_zero, mul_one]

end Transition

section EdgeSmooth

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- The actual edge coordinate is smooth on the physical chart ball `B(j, 100Δρ(j))`. -/
theorem EdgeFamily.contMDiffOn_coord
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X} (hj : j ∈ F.centres) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.coord j) (ball j (100 * Δ * ρ j)) := by
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hsub : ∀ x ∈ ball j (100 * Δ * ρ j), (ρ j)⁻¹ * @dist X mX.toDist x j ≤ 100 * Δ := by
    intro x hx
    exact (inv_mul_dist_lt_of_mem_ball_LC87 hrj hx).le
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  refine C.contMDiffOn_coord.mono fun x hx => C.closedBall_subset_domain ?_
  rw [hc']
  exact hsub x hx

/-- On the physical chart ball the actual edge cutoff is its formula
`f(η_j/Δ) · g(F/(ρΔ))`. -/
theorem EdgeFamily.cutoff_eq_formula
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X} (hj : j ∈ F.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) :
    F.cutoff j x = edgeCoordinateProfile (F.coord j x / Δ) *
      edgeHeightProfile (F.smoothing x / ρ x / Δ) := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : Fs x / ρ j / (Δ * (ρ x / ρ j)) = Fs x / ρ x / Δ := by
    field_simp
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  unfold EdgeFamily.cutoff
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  change (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun y => edgeCoordinateProfile (C.coord y.val / Δ) *
        edgeHeightProfile (Fs y.val / ρ j / (Δ * (ρ y.val / ρ j)))) 0
      (⟨x, hmem⟩ : ball C.center (100 * Δ)).val =
    edgeCoordinateProfile (C.coord x / Δ) * edgeHeightProfile (Fs x / ρ x / Δ)
  rw [Subtype.val_injective.extend_apply]
  simp only [hq]

/-- The actual normalized height `F/ρ` is smooth near every collar point of an edge chart
(LFR38's collar recorded in `EdgeChart.collar`). -/
theorem EdgeFamily.contMDiffAt_height_of_collar
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X} (hj : j ∈ F.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (hcoord : |F.coord j x| ≤ 10 * Δ)
    (h1 : Δ / 10 ≤ F.smoothing x / ρ x) (h2 : F.smoothing x / ρ x ≤ 10 * Δ) :
    ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => F.smoothing y / ρ y) x := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : ∀ y, Fs y / ρ j / (ρ y / ρ j) = Fs y / ρ y := fun y => by
    have := hρ y
    field_simp
  unfold EdgeFamily.coord at hcoord
  rw [dite_eq_left hj] at hcoord
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  have hcoord' : |C.coord x| ≤ 10 * Δ := hcoord
  have h1' : Δ / 10 ≤ Fs x / ρ j / (ρ x / ρ j) := by rw [hq]; exact h1
  have h2' : Fs x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by rw [hq]; exact h2
  obtain ⟨-, -, hJ, -⟩ := C.collar x hmem hcoord' h1' h2'
  have hpos : (0 : ℝ) < 300 * (ρ x / ρ j) := by positivity
  have hopen : IsOpen (ball x (300 * (ρ x / ρ j))) := isOpen_ball
  have hJx := hJ.contMDiffAt (hopen.mem_nhds (mem_ball_self hpos))
  have hproj := ContMDiffAt.comp x
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contMDiff.contMDiffAt)
    hJx
  refine hproj.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  change Fs y / ρ y = Fs y / ρ j / (ρ y / ρ j)
  exact (hq y).symm

/-- **The actual edge cutoff is smooth** as soon as its closed support lies in the OPEN chart ball
`B(j, 100Δρ(j))` (the zero-extension margin of LC87 packet (iv)); the height factor is smooth
through the collar charts where it varies. -/
theorem EdgeFamily.contMDiff_cutoff_of_margin
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hρc : Continuous ρ) {j : X} (hm : tsupport (F.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.cutoff j) := by
  by_cases hj : j ∈ F.centres
  swap
  · have h0 : F.cutoff j = fun _ => 0 := by
      funext x
      unfold EdgeFamily.cutoff
      rw [dite_eq_right hj]
      rfl
    rw [h0]
    exact contMDiff_const
  intro x
  by_cases hx : x ∈ tsupport (F.cutoff j)
  swap
  · have h0 : F.cutoff j =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  have hxb := hm hx
  have hball : ball j (100 * Δ * ρ j) ∈ 𝓝 x := isOpen_ball.mem_nhds hxb
  have heq : F.cutoff j =ᶠ[𝓝 x] fun y => edgeCoordinateProfile (F.coord j y / Δ) *
      edgeHeightProfile (F.smoothing y / ρ y / Δ) := by
    filter_upwards [hball] with y hy
    exact F.cutoff_eq_formula hj hy
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hcoordAt : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.coord j) x :=
    (F.contMDiffOn_coord hj).contMDiffAt hball
  have hprof : ContDiff ℝ ∞ fun t : ℝ => edgeCoordinateProfile (t / Δ) :=
    edgeProfiles_contDiff.1.comp (contDiff_id.div_const Δ)
  have hhprof : ContDiff ℝ ∞ fun t : ℝ => edgeHeightProfile (t / Δ) :=
    edgeProfiles_contDiff.2.1.comp (contDiff_id.div_const Δ)
  have hA : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => edgeCoordinateProfile (F.coord j y / Δ)) x :=
    hprof.contMDiff.contMDiffAt.comp x hcoordAt
  have hsc : Continuous fun y => F.smoothing y / ρ y / Δ :=
    (F.lipschitz_smoothing.continuous.div hρc fun y => (hρ y).ne').div_const Δ
  by_cases h8 : F.smoothing x / ρ x / Δ < 8
  · have hB : (fun y => edgeHeightProfile (F.smoothing y / ρ y / Δ)) =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [hsc.continuousAt.eventually (gt_mem_nhds h8)] with y hy
      exact descendingIntervalProfile_one (by norm_num) hy.le
    exact hA.mul (contMDiffAt_const.congr_of_eventuallyEq hB)
  by_cases h9 : 9 < F.smoothing x / ρ x / Δ
  · have hB : (fun y => edgeHeightProfile (F.smoothing y / ρ y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hsc.continuousAt.eventually (lt_mem_nhds h9)] with y hy
      exact descendingIntervalProfile_zero (by norm_num) hy.le
    exact hA.mul (contMDiffAt_const.congr_of_eventuallyEq hB)
  rw [not_lt] at h8 h9
  by_cases hcx : |F.coord j x| ≤ 9 * Δ
  · have hFx : F.smoothing x / ρ x = Δ * (F.smoothing x / ρ x / Δ) := by
      field_simp
    have hH := F.contMDiffAt_height_of_collar hj hxb (by linarith)
      (by rw [hFx]; nlinarith) (by rw [hFx]; nlinarith)
    exact hA.mul (hhprof.contMDiff.contMDiffAt.comp x hH)
  · rw [not_le] at hcx
    have hcc : ContinuousAt (F.coord j) x := hcoordAt.continuousAt
    have hA0 : (fun y => edgeCoordinateProfile (F.coord j y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      rcases lt_abs.mp hcx with hpos | hneg
      · filter_upwards [hcc.eventually (lt_mem_nhds hpos)] with y hy
        refine intervalPlateauProfile_zero_right (by norm_num) ?_
        rw [le_div_iff₀ hΔ]
        linarith
      · have hneg' : F.coord j x < -(9 * Δ) := by linarith
        filter_upwards [hcc.eventually (gt_mem_nhds hneg')] with y hy
        refine intervalPlateauProfile_zero_left (by norm_num) ?_
        rw [div_le_iff₀ hΔ]
        linarith
    have hprod0 : (fun y => edgeCoordinateProfile (F.coord j y / Δ) *
        edgeHeightProfile (F.smoothing y / ρ y / Δ)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hA0] with y hy
      rw [hy, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq hprod0

end EdgeSmooth

section GlobalMap

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The isometric axis `s ↦ (s, 0)` of `ℝ²` (scalar coordinates of FC01's blocks). -/
def planeAxis : ℝ →L[ℝ] ℝ² :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))

theorem planeAxis_apply (t : ℝ) : planeAxis t = t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :=
  rfl

theorem norm_planeAxis (t : ℝ) : ‖planeAxis t‖ = |t| := by
  have h1 : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 := by simp
  rw [planeAxis_apply, norm_smul, h1, mul_one, Real.norm_eq_abs]

/-- The `E'` height profile `h(u) = χ_{1/5,3/10}(u) (1 − χ_{8,9}(u))` of CGP01 (for `χ = χ_E`). -/
def cgpEdgeH (u : ℝ) : ℝ :=
  cfsRamp lc87EdgeTransition (1 / 5) (3 / 10) u * (1 - cfsRamp lc87EdgeTransition 8 9 u)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The tags of `𝓔⁰`: circle, slim, edge and zero centres, and the two special tags
(`false` = `ρ`, `true` = `E'`). -/
abbrev CGPTag (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) : Type :=
  L.circle.finite_centres.toFinset ⊕ L.slim.finite_centres.toFinset ⊕
    L.edge.finite_centres.toFinset ⊕ Z.finite_centres.toFinset ⊕ Bool

/-- The normalized edge height `t = F/ρ` of the ONE shared smoothing. -/
def cgpHeight (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (x : X) : ℝ :=
  L.edge.smoothing x / ρ x

/-- The sum `Σ_{i ∈ I_e} ζ_i` of the actual edge cutoffs. -/
def cgpEdgeSum (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (x : X) : ℝ :=
  ∑ j : L.edge.finite_centres.toFinset, L.edge.cutoff j x

/-- The `E'` marker `z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i)` of CGP01. -/
def cgpEdgeMarker (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (x : X) : ℝ :=
  cgpEdgeH (cgpHeight L x / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L x)

/-- The block radii `R_i`. -/
def cgpRadius (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) : CGPTag L Z → X → ℝ
  | .inl j => fun _ => ρ j
  | .inr (.inl j) => fun _ => ρ j
  | .inr (.inr (.inl j)) => fun _ => ρ j
  | .inr (.inr (.inr (.inl i))) => fun _ =>
      (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius
  | .inr (.inr (.inr (.inr _))) => ρ

/-- The block cutoffs `ζ_i` (LC87's actual cutoffs, LC31's annular cutoffs, `1`, `z₀`). -/
def cgpCutoff (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) : CGPTag L Z → X → ℝ
  | .inl j => L.circle.cutoff j
  | .inr (.inl j) => L.slim.cutoff j
  | .inr (.inr (.inl j)) => L.edge.cutoff j
  | .inr (.inr (.inr (.inl i))) => fun x =>
      Calculus.annularCutoff Calculus.cutoffProfile ((Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial x)
  | .inr (.inr (.inr (.inr false))) => fun _ => 1
  | .inr (.inr (.inr (.inr true))) => cgpEdgeMarker L

/-- The block coordinates `η_i` (scalar coordinates on the axis of `ℝ²`). -/
def cgpCoord (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) : CGPTag L Z → X → ℝ²
  | .inl j =>
      let c := L.circle.chart j.1 ((Set.Finite.mem_toFinset _).mp j.2)
      letI := mX.rescale (ρ j.1)⁻¹ (inv_pos.mpr (hρ j.1))
      c.coord
  | .inr (.inl j) => fun x =>
      planeAxis ((L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord x)
  | .inr (.inr (.inl j)) => fun x => planeAxis (L.edge.coord j x)
  | .inr (.inr (.inr (.inl i))) => fun x =>
      planeAxis ((Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial x)
  | .inr (.inr (.inr (.inr false))) => fun _ => 0
  | .inr (.inr (.inr (.inr true))) => fun x => planeAxis (cgpHeight L x)

/-- **CGP01: the actual original global block map `𝓔⁰ = F`** (FC01's block map on the actual LC87
families and the LC80 zero family, with the source profiles). Defined ONCE on the pair
`(L, Z)`; `cgpGlobalMap'` is the same map on `LocalChartFamilyWithZero`. -/
def cgpGlobalMap (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) :
    X → BlockSpace (fun _ : CGPTag L Z => ℝ²) :=
  blockMap (cgpRadius L Z) (cgpCutoff L Z) (cgpCoord L Z)

section Domains

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The open collar region where the `E'` height is smooth. -/
def cgpEdgeDomain : Set X :=
  {x | ∃ j ∈ L.edge.centres, x ∈ ball j (100 * Δ * ρ j) ∧ |L.edge.coord j x| < 10 * Δ ∧
    Δ / 10 < cgpHeight L x ∧ cgpHeight L x < 10 * Δ}

/-- The open smooth domains `U_i` of the blocks. -/
def cgpDomain : CGPTag L Z → Set X
  | .inl j => ball j.1 (200 * ρ j.1)
  | .inr (.inl j) => ball j.1 (10 ^ 6 * Δ * ρ j.1)
  | .inr (.inr (.inl j)) => ball j.1 (100 * Δ * ρ j.1)
  | .inr (.inr (.inr (.inl i))) =>
      Classical.choose (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
  | .inr (.inr (.inr (.inr false))) => univ
  | .inr (.inr (.inr (.inr true))) => cgpEdgeDomain L

theorem continuous_cgpHeight : Continuous (cgpHeight L) :=
  L.edge.lipschitz_smoothing.continuous.div L.contMDiff_scale.continuous fun x => (hρ x).ne'

theorem isOpen_cgpEdgeDomain : IsOpen (cgpEdgeDomain L) := by
  have h : cgpEdgeDomain L = ⋃ j ∈ L.edge.centres, (ball j (100 * Δ * ρ j) ∩
      L.edge.coord j ⁻¹' Ioo (-(10 * Δ)) (10 * Δ)) ∩
      cgpHeight L ⁻¹' Ioo (Δ / 10) (10 * Δ) := by
    ext x
    simp only [cgpEdgeDomain, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_Ioo,
      abs_lt, exists_prop]
    constructor
    · rintro ⟨j, hj, hx, ⟨h1, h2⟩, h3, h4⟩
      exact ⟨j, hj, ⟨hx, h1, h2⟩, h3, h4⟩
    · rintro ⟨j, hj, ⟨hx, h1, h2⟩, h3, h4⟩
      exact ⟨j, hj, hx, ⟨h1, h2⟩, h3, h4⟩
  rw [h]
  refine isOpen_biUnion fun j hj => IsOpen.inter ?_ (isOpen_Ioo.preimage (continuous_cgpHeight L))
  exact (L.edge.contMDiffOn_coord hj).continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioo

end Domains

section Pieces

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

theorem continuous_cgpEdgeSum (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (cgpEdgeSum L) := by
  unfold cgpEdgeSum
  refine contMDiff_finsetSum fun j _ => ?_
  exact L.edge.contMDiff_cutoff_of_margin hΔ L.contMDiff_scale.continuous
    (hmargin j.1 ((Set.Finite.mem_toFinset _).mp j.2))

/-- Where the edge sum is at least `1/2`, some actual edge cutoff is nonzero. -/
theorem exists_edge_cutoff_ne_zero_of_half_le {x : X} (hx : 1 / 2 ≤ cgpEdgeSum L x) :
    ∃ j ∈ L.edge.centres, L.edge.cutoff j x ≠ 0 := by
  have hne : cgpEdgeSum L x ≠ 0 := by linarith
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨j.1, (Set.Finite.mem_toFinset _).mp j.2, hj⟩

theorem cgpEdgeH_contDiff : ContDiff ℝ ∞ cgpEdgeH :=
  (contDiff_cfsRamp lc87EdgeTransition_contDiff _ _).mul
    (contDiff_const.sub (contDiff_cfsRamp lc87EdgeTransition_contDiff _ _))

theorem cgpEdgeH_eq_zero_of_le {u : ℝ} (hu : u ≤ 1 / 5) : cgpEdgeH u = 0 := by
  rw [cgpEdgeH, cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) hu,
    zero_mul]

theorem cgpEdgeH_eq_zero_of_ge {u : ℝ} (hu : 9 ≤ u) : cgpEdgeH u = 0 := by
  rw [cgpEdgeH, cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hu,
    sub_self, mul_zero]

/-- A point with an active edge cutoff and height in `[Δ/5, 9Δ]` lies in the collar domain. -/
theorem mem_cgpEdgeDomain_of (hΔ : 0 < Δ) {j x : X} (hjx : L.edge.cutoff j x ≠ 0)
    (h1 : Δ / 5 ≤ cgpHeight L x) (h2 : cgpHeight L x ≤ 9 * Δ) : x ∈ cgpEdgeDomain L := by
  obtain ⟨hj, hball, hcoord, -⟩ := L.edge.mem_of_cutoff_ne_zero hΔ hjx
  have hrj := hρ j
  refine ⟨j, hj, ?_, by linarith, by linarith, by linarith⟩
  have h := (inv_mul_lt_iff₀ hrj).mp hball
  rw [mem_ball]
  linarith

/-- The `E'` marker `z₀` is smooth on all of `X` and its closed support lies in the collar
domain. -/
theorem contMDiff_cgpEdgeMarker (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (cgpEdgeMarker L) := by
  have hsum := continuous_cgpEdgeSum L hΔ hmargin
  have hht := continuous_cgpHeight L
  intro x
  by_cases hx : cgpEdgeSum L x < 1 / 2
  · have h0 : cgpEdgeMarker L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hsum.continuous.continuousAt.eventually (gt_mem_nhds hx)] with y hy
      rw [cgpEdgeMarker, cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy)
        (by norm_num) hy.le, mul_zero]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  rw [not_lt] at hx
  obtain ⟨j, -, hjx⟩ := exists_edge_cutoff_ne_zero_of_half_le L hx
  have hcont : Continuous fun y => cgpHeight L y / Δ := hht.div_const Δ
  by_cases hlow : cgpHeight L x / Δ < 1 / 5
  · have h0 : cgpEdgeMarker L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hlow)] with y hy
      rw [cgpEdgeMarker, cgpEdgeH_eq_zero_of_le hy.le, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  by_cases hhigh : 9 < cgpHeight L x / Δ
  · have h0 : cgpEdgeMarker L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hhigh)] with y hy
      rw [cgpEdgeMarker, cgpEdgeH_eq_zero_of_ge hy.le, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  rw [not_lt] at hlow hhigh
  have h1 : Δ / 5 ≤ cgpHeight L x := by
    rw [le_div_iff₀ hΔ] at hlow
    linarith
  have h2 : cgpHeight L x ≤ 9 * Δ := by
    rw [div_le_iff₀ hΔ] at hhigh
    linarith
  obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ := mem_cgpEdgeDomain_of L hΔ hjx h1 h2
  have hH : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (cgpHeight L) x :=
    L.edge.contMDiffAt_height_of_collar hk hxk hck.le hk1.le hk2.le
  have hA : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => cgpEdgeH (cgpHeight L y / Δ)) x :=
    (cgpEdgeH_contDiff.comp (contDiff_id.div_const Δ)).contMDiff.contMDiffAt.comp x hH
  have hB : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L y)) x :=
    (contDiff_cfsRamp lc87EdgeTransition_contDiff _ _).contMDiff.contMDiffAt.comp x (hsum x)
  exact hA.mul hB

theorem tsupport_cgpEdgeMarker_subset (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    tsupport (cgpEdgeMarker L) ⊆ cgpEdgeDomain L := by
  have hsum := (continuous_cgpEdgeSum L hΔ hmargin).continuous
  have hht := continuous_cgpHeight L
  let S : Set X := {x | Δ / 5 ≤ cgpHeight L x ∧ cgpHeight L x ≤ 9 * Δ ∧ 1 / 2 ≤ cgpEdgeSum L x}
  have hS : IsClosed S :=
    (isClosed_le continuous_const hht).inter ((isClosed_le hht continuous_const).inter
      (isClosed_le continuous_const hsum))
  have hsupp : Function.support (cgpEdgeMarker L) ⊆ S := by
    intro x hx
    have hx' : cgpEdgeMarker L x ≠ 0 := hx
    rw [cgpEdgeMarker] at hx'
    have hH : cgpEdgeH (cgpHeight L x / Δ) ≠ 0 := left_ne_zero_of_mul hx'
    have hR : cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum L x) ≠ 0 :=
      right_ne_zero_of_mul hx'
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlt
      apply hH
      refine cgpEdgeH_eq_zero_of_le ?_
      rw [div_le_iff₀ hΔ]
      linarith [not_le.mp hlt]
    · by_contra hlt
      apply hH
      refine cgpEdgeH_eq_zero_of_ge ?_
      rw [le_div_iff₀ hΔ]
      linarith [not_le.mp hlt]
    · by_contra hlt
      exact hR (cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num)
        (not_le.mp hlt).le)
  intro x hx
  obtain ⟨h1, h2, h3⟩ := closure_minimal hsupp hS hx
  obtain ⟨j, -, hjx⟩ := exists_edge_cutoff_ne_zero_of_half_le L h3
  exact mem_cgpEdgeDomain_of L hΔ hjx h1 h2

end Pieces

/-- **CGP01, smoothness**: with LC87's packet-(iv) margin `hmargin` (closed edge supports inside the
OPEN chart balls) and the zero-shell tolerance `e ≤ 1/8`, the actual global block map is smooth;
every block's closed support lies in its open smooth domain (FC01's construction check). -/
theorem contMDiff_cgpGlobalMap
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 0 < Δ) (he : e ≤ 1 / 8)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z) := by
  have hplane : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ²) ∞ planeAxis := planeAxis.contMDiff
  refine contMDiff_blockMap (U := cgpDomain L Z) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    (fun i => ?_) (fun i => ?_)
  · -- open domains
    rcases i with j | j | j | i | bb
    · exact isOpen_ball
    · exact isOpen_ball
    · exact isOpen_ball
    · exact (Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1).1
    · cases bb
      · exact isOpen_univ
      · exact isOpen_cgpEdgeDomain L
  · -- smooth coordinates
    rcases i with j | j | j | i | bb
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      have hc := L.circle.chart_center j.1 hj
      have hrj := hρ j.1
      let c := L.circle.chart j.1 hj
      let mR : MetricSpace X := mX.rescale (ρ j.1)⁻¹ (inv_pos.mpr (hρ j.1))
      have hc' : c.center = j.1 := hc
      change ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ c.coord (@ball X mX.toPseudoMetricSpace j.1
        (200 * ρ j.1))
      refine c.contMDiffOn_coord.mono fun x hx => ?_
      have hd := @inv_mul_dist_lt_of_mem_ball_LC87 X mX ρ j.1 x 200 hrj hx
      change (ρ j.1)⁻¹ * @dist X mX.toDist x c.center < 200
      rw [hc']
      exact hd
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact hplane.comp_contMDiffOn (L.slim.centre j.1 hj).contMDiffOn_coord
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact hplane.comp_contMDiffOn (L.edge.contMDiffOn_coord hj)
    · have hO := Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
      exact hplane.comp_contMDiffOn hO.2.2
    · cases bb
      · exact contMDiffOn_const
      · refine hplane.comp_contMDiffOn fun x hx => ?_
        obtain ⟨k, hk, hxk, hck, h1, h2⟩ := hx
        exact (L.edge.contMDiffAt_height_of_collar hk hxk hck.le h1.le h2.le).contMDiffWithinAt
  · -- smooth cutoffs
    rcases i with j | j | j | i | bb
    · exact L.circle.contMDiff_cutoff j.1 ((Set.Finite.mem_toFinset _).mp j.2)
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      change ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.cutoff j.1)
      unfold SlimFamily.cutoff
      rw [dite_eq_left hj]
      exact (L.slim.centre j.1 hj).contMDiff_cutoff
    · exact L.edge.contMDiff_cutoff_of_margin hΔ L.contMDiff_scale.continuous
        (hmargin j.1 ((Set.Finite.mem_toFinset _).mp j.2))
    · have hspec :=
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.2.2.2.2.2.2.2.2.2.2
      exact hspec.choose_spec.2.2.1
    · cases bb
      · exact contMDiff_const
      · exact contMDiff_cgpEdgeMarker L hΔ hmargin
  · -- smooth radii
    rcases i with j | j | j | i | bb
    · exact contMDiff_const
    · exact contMDiff_const
    · exact contMDiff_const
    · exact contMDiff_const
    · cases bb
      · exact L.contMDiff_scale
      · exact L.contMDiff_scale
  · -- closed supports inside the domains
    rcases i with j | j | j | i | bb
    · exact L.circle.tsupport_subset_ball j.1 ((Set.Finite.mem_toFinset _).mp j.2)
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      obtain ⟨h1, h2, h3, -⟩ := fc18_slim_row L hΔ hj
      exact h1.trans (h2.trans h3)
    · exact hmargin j.1 ((Set.Finite.mem_toFinset _).mp j.2)
    · have hO := Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
      have hspec :=
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.2.2.2.2.2.2.2.2.2.2
      have hts := hspec.choose_spec.2.2.2.2.2.1
      refine hts.trans (fun x hx => hO.2.1 ⟨?_, ?_⟩)
      · linarith [hx.1]
      · linarith [hx.2]
    · cases bb
      · exact subset_univ _
      · exact tsupport_cgpEdgeMarker_subset L hΔ hmargin

section Identities

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The tag of the scale block. -/
abbrev cgpScaleTag : CGPTag L Z := .inr (.inr (.inr (.inr false)))

/-- The tag of the `E'` block. -/
abbrev cgpEdgeTag : CGPTag L Z := .inr (.inr (.inr (.inr true)))

/-- The tag of the edge block at `j`. -/
abbrev cgpEdgeBlockTag (j : L.edge.finite_centres.toFinset) : CGPTag L Z := .inr (.inr (.inl j))

theorem cgpGlobalMap_scale (p : X) : (cgpGlobalMap L Z p (cgpScaleTag L Z)).snd = ρ p := by
  change ρ p * 1 = ρ p
  rw [mul_one]

theorem cgpGlobalMap_edgeMarker (p : X) :
    (cgpGlobalMap L Z p (cgpEdgeTag L Z)).snd = ρ p * cgpEdgeMarker L p :=
  rfl

theorem cgpGlobalMap_edgeCoord (p : X) :
    (cgpGlobalMap L Z p (cgpEdgeTag L Z)).fst =
      (ρ p * cgpEdgeMarker L p) • planeAxis (cgpHeight L p) :=
  rfl

theorem cgpGlobalMap_edgeBlock (j : L.edge.finite_centres.toFinset) (p : X) :
    (cgpGlobalMap L Z p (cgpEdgeBlockTag L Z j)).fst =
        (ρ j * L.edge.cutoff j p) • planeAxis (L.edge.coord j p) ∧
      (cgpGlobalMap L Z p (cgpEdgeBlockTag L Z j)).snd = ρ j * L.edge.cutoff j p :=
  ⟨rfl, rfl⟩

theorem cgpHeight_nonneg (p : X) : 0 ≤ cgpHeight L p :=
  div_nonneg (L.edge.smoothing_nonneg p) (hρ p).le

theorem cgpEdgeH_mem_Icc (u : ℝ) : cgpEdgeH u ∈ Icc (0 : ℝ) 1 := by
  have h1 := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc (1 / 5) (3 / 10) u
  have h2 := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc 8 9 u
  rw [cgpEdgeH]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- `h = g = 1 − χ_{8,9}` on `[3/10, ∞)`. -/
theorem cgpEdgeH_eq_of_le {u : ℝ} (hu : 3 / 10 ≤ u) :
    cgpEdgeH u = 1 - cfsRamp lc87EdgeTransition 8 9 u := by
  rw [cgpEdgeH, cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hu,
    one_mul]

theorem cgpEdgeCutoff_mem_Icc (hΔ : 0 < Δ) (j x : X) : L.edge.cutoff j x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : L.edge.cutoff j x = 0
  · rw [h]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨hj, hball, -, -⟩ := L.edge.mem_of_cutoff_ne_zero hΔ h
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
    rw [mem_ball]
    linarith
  rw [L.edge.cutoff_eq_formula hj hx]
  have h1 := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9 (L.edge.coord j x / Δ)
  have h2 := descendingIntervalProfile_mem_Icc 8 9 (L.edge.smoothing x / ρ x / Δ)
  change intervalPlateauProfile (-9) (-8) 8 9 (L.edge.coord j x / Δ) *
    descendingIntervalProfile 8 9 (L.edge.smoothing x / ρ x / Δ) ∈ Icc (0 : ℝ) 1
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem cgpEdgeMarker_mem_Icc (p : X) : cgpEdgeMarker L p ∈ Icc (0 : ℝ) 1 := by
  have h1 := cgpEdgeH_mem_Icc (cgpHeight L p / Δ)
  have h2 := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc (1 / 2) 1 (cgpEdgeSum L p)
  rw [cgpEdgeMarker]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The `E'` block of `𝓔⁰` is `(ρ t z₀, ρ z₀)` with `‖x'‖ = ρ t z₀` (CFS23's block identity). -/
theorem norm_cgpGlobalMap_edgeCoord (p : X) :
    ‖(cgpGlobalMap L Z p (cgpEdgeTag L Z)).fst‖ = ρ p * cgpHeight L p * cgpEdgeMarker L p := by
  rw [cgpGlobalMap_edgeCoord, norm_smul, norm_planeAxis, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hρ p).le (cgpEdgeMarker_mem_Icc L p).1),
    abs_of_nonneg (cgpHeight_nonneg L p)]
  ring

/-- **CFS23's joint edge identity on the original domain**: on the chart ball, where
`|η_j| < 8Δ`, the actual edge cutoff is `g(t/Δ) = 1 − χ_{8,9}(t/Δ)`. -/
theorem cgp01_edge_identity {j : X} (hj : j ∈ L.edge.centres) {p : X}
    (hp : p ∈ ball j (100 * Δ * ρ j)) (hη : |L.edge.coord j p| < 8 * Δ) (hΔ : 0 < Δ) :
    L.edge.cutoff j p = 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight L p / Δ) := by
  rw [L.edge.cutoff_eq_formula hj hp, edgeCoordinateProfile_eq_one_sub_cfsRamp_abs,
    edgeHeightProfile_eq_one_sub_cfsRamp]
  have h0 : cfsRamp lc87EdgeTransition 8 9 |L.edge.coord j p / Δ| = 0 := by
    refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
    rw [abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ]
    linarith
  rw [h0, sub_zero, one_mul]
  rfl

/-- Outside the chart ball the actual edge cutoff vanishes (CFS23's `ζ_i = 0` off `U_i`). -/
theorem edgeCutoff_eq_zero_of_not_mem (hΔ : 0 < Δ) {j p : X}
    (hp : p ∉ ball j (100 * Δ * ρ j)) : L.edge.cutoff j p = 0 := by
  by_contra h
  obtain ⟨-, hball, -, -⟩ := L.edge.mem_of_cutoff_ne_zero hΔ h
  apply hp
  have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
  rw [mem_ball]
  linarith

end Identities

/-- **CGP01** (`prop:fibration-source-profile-binding`) on the actual LC87 families and LC80 zero
family: the global block map `𝓔⁰ = cgpGlobalMap L Z` (FC01 with the source profiles) is smooth,
its scale block is `ρ`, its `E'` block is `(ρ t z₀, ρ z₀)` with `t = F/ρ ≥ 0` and
`z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i) ∈ [0, 1]`, `h ∈ [0, 1]`, `h = 1 − χ_{8,9}` on `[3/10, ∞)`,
every edge block is `(R_j ζ_j η_j, R_j ζ_j)` with `ζ_j ∈ [0, 1]` zero off its chart ball, and on the
chart ball where `|η_j| < 8Δ` the joint identity `ζ_j = 1 − χ_{8,9}(t/Δ)` holds (`χ = χ_E`, the
increasing profile of CFS22). Input beyond the families: the edge zero-extension margin `hmargin`
(LC87 packet (iv)) and the zero-shell tolerance `e ≤ 1/8`. -/
theorem cgp01_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 0 < Δ) (he : e ≤ 1 / 8)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z) ∧
      (∀ p, (cgpGlobalMap L Z p (cgpScaleTag L Z)).snd = ρ p) ∧
      (∀ p, ‖(cgpGlobalMap L Z p (cgpEdgeTag L Z)).fst‖ =
          ρ p * cgpHeight L p * cgpEdgeMarker L p ∧
        (cgpGlobalMap L Z p (cgpEdgeTag L Z)).snd = ρ p * cgpEdgeMarker L p) ∧
      (∀ p, 0 ≤ cgpHeight L p) ∧
      (∀ p, cgpEdgeMarker L p = cgpEdgeH (cgpHeight L p / Δ) *
        cfsRamp lc87EdgeTransition (1 / 2) 1
          (∑ j : L.edge.finite_centres.toFinset, L.edge.cutoff j p)) ∧
      (∀ u, cgpEdgeH u ∈ Icc (0 : ℝ) 1) ∧
      (∀ u, 3 / 10 ≤ u → cgpEdgeH u = 1 - cfsRamp lc87EdgeTransition 8 9 u) ∧
      (∀ (j : L.edge.finite_centres.toFinset) p,
        (cgpGlobalMap L Z p (cgpEdgeBlockTag L Z j)).fst =
            (ρ j * L.edge.cutoff j p) • planeAxis (L.edge.coord j p) ∧
          (cgpGlobalMap L Z p (cgpEdgeBlockTag L Z j)).snd = ρ j * L.edge.cutoff j p) ∧
      (∀ j p, L.edge.cutoff j p ∈ Icc (0 : ℝ) 1) ∧
      (∀ j p, p ∉ ball j (100 * Δ * ρ j) → L.edge.cutoff j p = 0) ∧
      (∀ j ∈ L.edge.centres, ∀ p ∈ ball j (100 * Δ * ρ j), |L.edge.coord j p| < 8 * Δ →
        L.edge.cutoff j p = 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight L p / Δ)) :=
  ⟨contMDiff_cgpGlobalMap L Z hΔ he hmargin, cgpGlobalMap_scale L Z,
    fun p => ⟨norm_cgpGlobalMap_edgeCoord L Z p, cgpGlobalMap_edgeMarker L Z p⟩,
    cgpHeight_nonneg L, fun _ => rfl, cgpEdgeH_mem_Icc, fun _ hu => cgpEdgeH_eq_of_le hu,
    cgpGlobalMap_edgeBlock L Z, fun j p => cgpEdgeCutoff_mem_Icc L hΔ j p,
    fun _ _ hp => edgeCutoff_eq_zero_of_not_mem L hΔ hp,
    fun _ hj _ hp hη => cgp01_edge_identity L hj hp hη hΔ⟩

end GlobalMap

section Wrapper

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc δ εr e T V : ℝ}

/-- The model metrics of the zero kind, as a named local instance. -/
local instance instMetricN_C14KA
    (W : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (a : X) : MetricSpace (W.N a) :=
  W.instMetricN a

/-- The model charts of the zero kind, as a named local instance. -/
local instance instChartedN_C14KA
    (W : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (a : X) : ChartedSpace E3 (W.N a) :=
  W.instChartedN a

/-- The cone metrics of the zero kind, as a named local instance. -/
local instance instMetricC_C14KA
    (W : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (a : X) : MetricSpace (W.C a) :=
  W.instMetricC a

/-- The SAME map `𝓔⁰` on `LocalChartFamilyWithZero` (through its two projections). -/
abbrev cgpGlobalMap'
    (W : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V) :
    X → BlockSpace (fun _ : CGPTag W.toLocalChartFamily W.zero => ℝ²) :=
  cgpGlobalMap W.toLocalChartFamily W.zero

/-- CGP01's smoothness on `LocalChartFamilyWithZero`. -/
theorem contMDiff_cgpGlobalMap'
    (W : LocalChartFamilyWithZero X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc δ εr e T V)
    (hΔ : 0 < Δ) (he : e ≤ 1 / 8)
    (hmargin : ∀ j ∈ W.edge.centres, tsupport (W.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag W.toLocalChartFamily W.zero => ℝ²)) ∞
      (cgpGlobalMap' W) :=
  contMDiff_cgpGlobalMap W.toLocalChartFamily W.zero hΔ he hmargin

end Wrapper

end DifferentialGeometry.Geometry.Collapse
