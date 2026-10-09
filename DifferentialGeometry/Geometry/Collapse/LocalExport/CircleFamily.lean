import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart
import DifferentialGeometry.Geometry.Collapse.CirclePacketTwoStratum

/-!
# LC87 items 2–3, circle kind: the circle family as data

Blueprint row LC87 (`def:collapse-local-export-certificate`, master207A) lists, among the finite
families of a local-collapse export, the LC83 circle charts with their buffered domains, proper
restrictions and fibre types (item 2), and the LC86 covers, overlap bound, cutoffs with supports
strictly inside their smooth domains and the stratum exhaustion (item 3). For the circle kind
these are produced by LPA03/LPA06 on the two-stratum (`eventually_circle_packets_two_stratum`,
F8-NEW2). This module records them as one data object built on the shared `CircleChart`
(`LocalExport/CircleChart.lean`, normalized scale: the chart at `j` lives on the metric
`ρ(j)⁻¹ d`).

* `CircleFamily I X ρ hρ β`: a finite set of two-stratum centres with disjoint `ρ/3`-balls whose
  balls `B(j, 2ρ(j))` absorb every `B(p, ρ(p))` of the two-stratum; at each centre a circle chart
  centred there and a smooth cutoff with values in `[0, 1]`, equal to one where `‖η_j‖ ≤ 8` and on
  the physical ball `B(j, 2ρ(j))`, nonzero only where `‖η_j‖ < 9`, with closed support inside the
  chart's bundle domain and inside `B(j, 200ρ(j))`; the support multiplicity is at most the
  numerical constant `V₋(6·10⁶ + 2/3)/V₋(1/3)` (curvature `-(1/(2·10⁶))²`).
* `eventually_nonempty_circleFamily`: the producer on one late tail of the closed standing
  sequence, with one LC02 scale `ρ`.

The zero, edge and slim families of LC87 (LC80, LC84, LC85) and the chart-overlap comparisons of
item 4 are not produced in the tree; this is the circle part only.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u

section Data

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (X : Type u) [mX : MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- **LC87 items 2–3, circle kind.** A finite family of LC83 circle charts on the two-stratum of a
positive scale `ρ`, with cutoffs, cover and support multiplicity. DATA with proofs of its fields. -/
structure CircleFamily (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) where
  centres : Set X
  finite_centres : centres.Finite
  centres_subset : centres ⊆ scaledSplittingStratum.{u, 0} ρ hρ β 2
  disjoint_centres : centres.PairwiseDisjoint (fun p => ball p (ρ p / 3))
  covers : ∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρ β 2, ∃ j ∈ centres,
    ball p (ρ p) ⊆ ball j (2 * ρ j)
  /-- The circle chart at a centre, at normalized scale. -/
  chart : (j : X) → j ∈ centres →
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    CircleChart I X
  chart_center : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (chart j hj).center = j
  /-- The cutoff at a centre (`Φ_{8,9}` of the chart's coordinate). -/
  cutoff : X → X → ℝ
  contMDiff_cutoff : ∀ j ∈ centres, ContMDiff I 𝓘(ℝ, ℝ) ∞ (cutoff j)
  cutoff_mem_Icc : ∀ j ∈ centres, ∀ x, cutoff j x ∈ Icc (0 : ℝ) 1
  cutoff_eq_one : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x ∈ ball j 200, ‖(chart j hj).coord x‖ ≤ 8 → cutoff j x = 1
  coord_lt_of_cutoff_ne_zero : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x, cutoff j x ≠ 0 → x ∈ ball j 200 ∧ ‖(chart j hj).coord x‖ < 9
  tsupport_subset_domain : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    tsupport (cutoff j) ⊆ (diskPreimageOpens (ball (chart j hj).center 200) isOpen_ball
      (chart j hj).coord (chart j hj).contMDiffOn_coord.continuousOn 100 : Set X)
  plateau : ∀ j ∈ centres, ∀ x ∈ ball j (2 * ρ j), cutoff j x = 1
  tsupport_subset_ball : ∀ j ∈ centres, tsupport (cutoff j) ⊆ ball j (200 * ρ j)
  multiplicity : ∀ x : X, ((centres ∩ {j | x ∈ tsupport (cutoff j)}).ncard : ℝ) ≤
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

end Data

section Producer

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Producer of the circle family.** With the constants of `eventually_circle_packets_two_stratum`
fixed in its order, on one late tail of the closed standing sequence there is one LC02 scale `ρ` and
a circle family on its two-stratum. -/
theorem eventually_nonempty_circleFamily (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ → ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≤ a₂ →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (CircleFamily I (X i) ρ hρpos β) := by
  classical
  obtain ⟨a₂, ha₂, h⟩ := eventually_circle_packets_two_stratum.{uE, uH, u} (E := E) (H := H)
    (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβ hββ₀ σ hσ hσ1 hσa Λ hΛ hΛsmall => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h β hβ hββ₀ σ hσ hσ1 hσa Λ hΛ hΛsmall
  refine ⟨w₀, hw₀, fun w hw hww₀ hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h w hw hww₀ hwc X g hmetric α hα hstand] with i hi
  obtain ⟨ρ, hρpos, hsm, hlip, hb, -, hpt, J, hfin, hJS, hdisj, hcov, hmult⟩ := hi
  have hdata : ∀ j ∈ J, ∃ c : (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
      CircleChart I (X i)), ∃ ζ : X i → ℝ,
      (letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
        c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζ x = 1) ∧
        (∀ x, ζ x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
        tsupport ζ ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100 : Set (X i))) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ (∀ x, ζ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball j (2 * ρ j), ζ x = 1) ∧ tsupport ζ ⊆ ball j (200 * ρ j) := by
    intro j hj
    obtain ⟨C, mC, c, -, -, -, -, -, Y, mY, a, F, η, hη, hrank, hp0, hlip2, -, h102, h2, -,
      hbundle, -, ζ, hζ, -, hζ01, hplat8, hne, -, hdom, hball, hphys⟩ := hpt j (hJS hj)
    obtain ⟨-, -, hprop, hsurj, hfib, htriv⟩ := hbundle
    let _ := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
    refine ⟨{
      center := j
      coord := η
      contMDiffOn_coord := hη
      rank := hrank
      lipschitz := hlip2
      coord_center := hp0
      enclosure := h102
      zero_enclosure := h2
      isProperMap := hprop
      surjective := hsurj
      fibres := hfib
      trivial := htriv }, ζ, ⟨rfl, hplat8, hne, hdom⟩, hζ, hζ01, fun x hx => (hball hx).2, hphys⟩
  choose c ζ hc using hdata
  refine ⟨ρ, hρpos, hsm, hlip, hb, ⟨{
    centres := J
    finite_centres := hfin
    centres_subset := hJS
    disjoint_centres := hdisj
    covers := hcov
    chart := c
    chart_center := fun j hj => (hc j hj).1.1
    cutoff := fun j => if hj : j ∈ J then ζ j hj else 0
    contMDiff_cutoff := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).2.1
    cutoff_mem_Icc := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).2.2.1
    cutoff_eq_one := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).1.2.1
    coord_lt_of_cutoff_ne_zero := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).1.2.2.1
    tsupport_subset_domain := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).1.2.2.2
    plateau := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).2.2.2.1
    tsupport_subset_ball := fun j hj => by rw [dite_eq_left hj]; exact (hc j hj).2.2.2.2
    multiplicity := fun x => ?_ }⟩⟩
  refine le_trans ?_ (hmult x)
  have hsub : J ∩ {j | x ∈ tsupport (if hj : j ∈ J then ζ j hj else 0)} ⊆
      J ∩ {j | x ∈ ball j (2000000 * ρ j)} := by
    rintro j ⟨hj, hx⟩
    rw [mem_ofPred_eq, dite_eq_left hj] at hx
    refine ⟨hj, ball_subset_ball ?_ ((hc j hj).2.2.2.2 hx)⟩
    linarith [hρpos j]
  exact_mod_cast Set.ncard_le_ncard hsub (hfin.subset inter_subset_left)

end Producer

end DifferentialGeometry.Geometry.Collapse
