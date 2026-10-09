import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyApplications
import DifferentialGeometry.Geometry.Fibration.FinitePacketSupport

/-!
# LC87 → chapter 14: the FC07 / FC12 / FC27 hypotheses from the local chart family

Blueprint `master207B.tex`: FC07 (B:352, "For the closed-carrier LC87 data …"; its proof decomposition
B:388–405 uses the enlarged-ball count for all active supports, FC12's support buffers and the plateau
of every cutoff), FC12 (B:738, `finite_packet_support_scale_buffer`: actual support scale,
original-domain inclusion and complement-distance margin; binding matrix B:1530–1540, "Two-stratum:
original centered chart; FC12", "Edge/slim: FC18 and FC12, with rescaled radii"), FC27 (B:1658: the
edge thresholds `7Δ, 8Δ` for BOTH `|η_i|` and `η_{E'}`, the slim thresholds `7·10⁵Δ, 8·10⁵Δ`, and the
coordinate coverage from LC84/LC85).

* `CircleFamily.tsupport_cutoff_subset_closedBall`: the closed support of a circle cutoff lies in
  `B̄(j, 102ρ(j))` (the chart's enclosure), strictly inside its smooth domain `B(j, 200ρ(j))`.
* `LocalChartFamily.circle_support_scale_buffer`, `LocalChartFamily.slim_support_scale_buffer`: FC12's
  kernel `finite_packet_support_scale_buffer` on the ACTUAL circle (`C = 102`, `b = 200`) and slim
  (`C = 0.91·10⁶Δ`, `b = 10⁶Δ`, smooth coordinate on the domain) supports of the family, for every
  test ball `B(p, Rρ(p))` they meet.
* FC27, slim kind: `SlimCentre.cutoff_eq_one_of_abs_coord_le` (plateau `|η_j| ≤ 8·10⁵Δ`),
  `SlimCentre.abs_coord_le_of_mem_tsupport` (support in `|η_j| ≤ 89·10⁴Δ`),
  `SlimCentre.Icc_subset_image_coord` (coverage `[-905·10³Δ, 905·10³Δ] ⊆ η_j(B(j, 10⁶Δρ(j)))`).
* FC27, edge kind: `EdgeFamily.coord` (the chart's `η_j`), `EdgeFamily.cutoff_eq_one_of_le`: the edge
  cutoff is one on `{x ∈ B(j, 100Δρ(j)) | |η_j| ≤ 8Δ, F/ρ ≤ 8Δ}`.

The edge FC12 buffer is NOT derived: `EdgeChart` records the coordinate's smooth domain only as an open
set containing `B̄(j, 100Δ)` (no quantitative margin beyond the support); that margin belongs to LC84
item 4 / FC18.
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Circle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : Type*} [mX : MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}

/-- The closed support of a circle cutoff lies in `B̄(j, 102ρ(j))`. -/
theorem CircleFamily.tsupport_cutoff_subset_closedBall (F : CircleFamily I X ρ hρ β) {j : X}
    (hj : j ∈ F.centres) : tsupport (F.cutoff j) ⊆ closedBall j (102 * ρ j) := by
  refine (closure_mono ?_).trans closure_ball_subset_closedBall
  intro x hx
  have h1 := F.coord_lt_of_cutoff_ne_zero j hj x hx
  have hc := F.chart_center j hj
  let c := F.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  have h1' : x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 9 := by
    rw [hc']
    exact h1
  have h2 : x ∈ ball c.center 102 := c.enclosure x h1'.1 (by linarith [h1'.2])
  rw [hc'] at h2
  have h3 : (ρ j)⁻¹ * @dist X mX.toDist x j < 102 := h2
  rw [inv_mul_lt_iff₀ (hρ j)] at h3
  change @dist X mX.toDist x j < 102 * ρ j
  linarith

end Circle

section Family

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

namespace SlimCentre

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- FC27 (slim): the slim cutoff is one where `|η_j| ≤ 8·10⁵Δ` in `B(j, 10⁶Δρ(j))`. -/
theorem cutoff_eq_one_of_abs_coord_le (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) {x : X}
    (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (hc : |c.coord x| ≤ 8 * 10 ^ 5 * Δ) : c.cutoff x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.cutoff_eq_one x hd hc

/-- FC27 (slim): on the closed support of the slim cutoff `|η_j| ≤ 89·10⁴Δ`. -/
theorem abs_coord_le_of_mem_tsupport (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) {x : X}
    (hx : x ∈ tsupport c.cutoff) : |c.coord x| ≤ 89 * 10 ^ 4 * Δ := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact (P.tsupport_cutoff hx).2

/-- FC27 (slim coverage): `[-905·10³Δ, 905·10³Δ] ⊆ η_j(B(j, 10⁶Δρ(j)))`. -/
theorem Icc_subset_image_coord (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) :
    Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) ⊆ c.coord '' ball j (10 ^ 6 * Δ * ρ j) := by
  have hball : ∀ x, (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ → x ∈ ball j (10 ^ 6 * Δ * ρ j) := by
    intro x hx
    rw [inv_mul_lt_iff₀ (hρ j)] at hx
    rw [mem_ball]
    linarith
  intro t ht
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  obtain ⟨x, hx, hxt⟩ := P.surjective ht
  exact ⟨x, hball x hx, hxt⟩

end SlimCentre

namespace EdgeFamily

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

open Classical in
/-- The tangential coordinate `η_j` of the edge chart at `j` (zero off the centres). -/
def coord (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (j : X) : X → ℝ :=
  if hj : j ∈ F.centres then
    let C := F.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    C.coord
  else 0

/-- FC27 (edge): the edge cutoff is one on `{x ∈ B(j, 100Δρ(j)) | |η_j| ≤ 8Δ, F/ρ ≤ 8Δ}`. -/
theorem cutoff_eq_one_of_le (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ F.centres) {x : X} (hx : x ∈ ball j (100 * Δ * ρ j))
    (hη : |F.coord j x| ≤ 8 * Δ) (hF : F.smoothing x / ρ x ≤ 8 * Δ) : F.cutoff j x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hF' : Fs x / ρ x ≤ 8 * Δ := hF
  have hq : Fs x / ρ j / (Δ * (ρ x / ρ j)) = Fs x / ρ x / Δ := by
    field_simp
  have hh : edgeHeightProfile (Fs x / ρ j / (Δ * (ρ x / ρ j))) = 1 := by
    rw [hq]
    refine descendingIntervalProfile_one (by norm_num) ?_
    rw [div_le_iff₀ hΔ]
    linarith
  unfold coord at hη
  rw [dite_eq_left hj] at hη
  unfold cutoff
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
  have hη' : |C.coord x| ≤ 8 * Δ := hη
  have hcp : edgeCoordinateProfile (C.coord x / Δ) = 1 := by
    refine (edgeProfiles_plateaus (x := C.coord x / Δ)).1 ⟨?_, ?_⟩
    · rw [le_div_iff₀ hΔ]
      linarith [(abs_le.mp hη').1]
    · rw [div_le_iff₀ hΔ]
      linarith [(abs_le.mp hη').2]
  change (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun y => edgeCoordinateProfile (C.coord y.val / Δ) *
        edgeHeightProfile (Fs y.val / ρ j / (Δ * (ρ y.val / ρ j)))) 0
      (⟨x, hmem⟩ : ball C.center (100 * Δ)).val = 1
  rw [Subtype.val_injective.extend_apply]
  simp only [hcp, hh, mul_one]

end EdgeFamily

namespace LocalChartFamily

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- **FC12 on the actual circle supports.** For a circle centre `j` whose closed cutoff support
meets `B(p, Rρ(p))`: comparable scales, the test ball inside `B(j, (102 + 4R)ρ(j))`, which lies in the
chart's smooth domain `B(j, 200ρ(j))`, with complement-distance margin `(98 - 4R)ρ(j)`. -/
theorem circle_support_scale_buffer
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΛ : 0 ≤ Λ)
    {j : X} (hj : j ∈ L.circle.centres) {p : X} {R : ℝ} (hR : 0 < R)
    (hbudget : Λ * max R 102 ≤ 1 / 4) (hgap : 4 * R < 98)
    (hmeet : (tsupport (L.circle.cutoff j) ∩ ball p (R * ρ p)).Nonempty) :
    ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (R + 2 * 102) * ρ p ∧
      ball p (R * ρ p) ⊆ ball j ((102 + 4 * R) * ρ j) ∧
      ball j ((102 + 4 * R) * ρ j) ⊆ ball j (200 * ρ j) ∧
      ∀ x ∈ ball p (R * ρ p), (ball j (200 * ρ j))ᶜ.Nonempty →
        (200 - 102 - 4 * R) * ρ j ≤ infDist x (ball j (200 * ρ j))ᶜ :=
  DifferentialGeometry.Geometry.Fibration.finite_packet_support_scale_buffer L.lipschitz_scale
    (hρ p) (hρ j) hR (by norm_num) (by rwa [Real.coe_toNNReal _ hΛ]) (by linarith)
    (L.circle.tsupport_cutoff_subset_closedBall hj) subset_rfl hmeet

/-- **FC12 on the actual slim supports.** For a slim centre `j` whose closed cutoff support meets
`B(p, Rρ(p))`: comparable scales, the test ball inside `B(j, (0.91·10⁶Δ + 4R)ρ(j))`, which lies in
`B(j, 10⁶Δρ(j))` where `η_j` is smooth, with complement-distance margin. -/
theorem slim_support_scale_buffer
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΛ : 0 ≤ Λ)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.slim.centres) {p : X} {R : ℝ} (hR : 0 < R)
    (hbudget : Λ * max R (91 / 100 * (10 ^ 6 * Δ)) ≤ 1 / 4)
    (hgap : 4 * R < 10 ^ 6 * Δ - 91 / 100 * (10 ^ 6 * Δ))
    (hmeet : (tsupport (L.slim.cutoff j) ∩ ball p (R * ρ p)).Nonempty) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.centre j hj).coord (ball j (10 ^ 6 * Δ * ρ j)) ∧
      ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (R + 2 * (91 / 100 * (10 ^ 6 * Δ))) * ρ p ∧
      ball p (R * ρ p) ⊆ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * R) * ρ j) ∧
      ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * R) * ρ j) ⊆ ball j (10 ^ 6 * Δ * ρ j) ∧
      ∀ x ∈ ball p (R * ρ p), (ball j (10 ^ 6 * Δ * ρ j))ᶜ.Nonempty →
        (10 ^ 6 * Δ - 91 / 100 * (10 ^ 6 * Δ) - 4 * R) * ρ j ≤
          infDist x (ball j (10 ^ 6 * Δ * ρ j))ᶜ := by
  have hS : tsupport (L.slim.cutoff j) ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
    unfold SlimFamily.cutoff
    rw [dite_eq_left hj]
    exact (L.slim.centre j hj).tsupport_cutoff_subset
  exact ⟨(L.slim.centre j hj).contMDiffOn_coord,
    DifferentialGeometry.Geometry.Fibration.finite_packet_support_scale_buffer L.lipschitz_scale
      (hρ p) (hρ j) hR (by positivity) (by rwa [Real.coe_toNNReal _ hΛ]) hgap hS subset_rfl hmeet⟩

end LocalChartFamily

end Family

end DifferentialGeometry.Geometry.Collapse
