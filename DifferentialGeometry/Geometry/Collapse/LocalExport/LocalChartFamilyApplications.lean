import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyProducer

/-!
# LC87 items 2–3: cutoffs, plateaus and the joint multiplicity of the local chart family

Consumers of `LocalChartFamily` (LPA06, master207A:30586–30659: "The circle, edge and slim cutoffs
equal one on their respective covering balls; all cutoffs have closed supports strictly within their
smooth domains … The nonzero-family support multiplicity is bounded by one numerical constant …
Sum three such bounds for the three families").

* `SlimChart.abs_coord_lt_of_dist_lt`, `SlimChart.cutoff_eq_one_of_dist_lt` (abstract, normalized):
  `|η| < 3Δ` and cutoff one on `B(p, 2Δ)`.
* `SlimCentre.coord`, `SlimCentre.cutoff` (the packet's coordinate and cutoff as functions on `X`),
  `SlimCentre.abs_coord_lt`, `SlimCentre.cutoff_eq_one` (on the PHYSICAL covering ball
  `B(j, 2Δρ(j))`), `SlimCentre.tsupport_cutoff_subset` (`⊆ B̄(j, 0.91·10⁶Δρ(j))`),
  `SlimCentre.contMDiffOn_coord` (smooth on `B(j, 10⁶Δρ(j))`), `SlimCentre.contMDiff_cutoff`,
  `SlimCentre.cutoff_mem_Icc`.
* `SlimFamily.cutoff`, `EdgeFamily.cutoff` (the edge cutoff `Φ(η/Δ) ψ(F/(Δρ))` of the chart),
  `EdgeFamily.cutoff_eq_one` (on `B(j, 3Δρ(j))`), `EdgeFamily.tsupport_cutoff_subset`
  (`⊆ B̄(j, 100Δρ(j))`).
* `LocalChartFamily.exists_cutoff_eq_one`: every point lies in the zero stratum or in the plateau of a
  circle, slim or edge cutoff.
* `LocalChartFamily.support_multiplicity`: at every point the number of active circle, slim and edge
  supports is at most the sum of the three numerical constants.
* `eventually_localChartFamily_plateaus_and_multiplicity`: both, on the producer's tail.
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

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

/-- On `B(p, 2Δ)` the slim coordinate is smaller than `3Δ`. -/
theorem SlimChart.abs_coord_lt_of_dist_lt (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) {x : M} (hx : dist x p < 2 * Δ) : |c.coord x| < 3 * Δ := by
  have hK : ((Real.toNNReal (1 + σ) : NNReal) : ℝ) = 1 + σ := Real.coe_toNNReal _ (by linarith)
  have hlip := c.lipschitz.dist_le_mul x p
  rw [hK, c.coord_center, Real.dist_eq, sub_zero] at hlip
  have h1 : (1 + σ) * dist x p ≤ (1 + σ) * (2 * Δ) :=
    mul_le_mul_of_nonneg_left hx.le (by linarith)
  have h2 : (1 + σ) * dist x p < 3 * Δ ∨ (1 + σ) * dist x p ≤ (1 + σ) * (2 * Δ) := Or.inr h1
  rcases h2 with h2 | h2
  · linarith
  · have h3 : (1 + σ) * dist x p < (1 + σ) * (2 * Δ) :=
      mul_lt_mul_of_pos_left hx (by linarith)
    nlinarith

/-- On `B(p, 2Δ)` the slim cutoff is one. -/
theorem SlimChart.cutoff_eq_one_of_dist_lt (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) {x : M} (hx : dist x p < 2 * Δ) : c.cutoff x = 1 := by
  have hc := c.abs_coord_lt_of_dist_lt hΔ hσ hσ1 hx
  refine c.cutoff_eq_one x (mem_ball.mpr (by nlinarith)) (by nlinarith)

end Abstract

/-- A physical ball of radius `k ρ(j)` is the normalized ball of radius `k`. -/
theorem inv_mul_dist_lt_of_mem_ball_LC87 {X : Type*} [MetricSpace X] {ρ : X → ℝ} {j x : X}
    {k : ℝ} (hj : 0 < ρ j) (hx : x ∈ ball j (k * ρ j)) : (ρ j)⁻¹ * dist x j < k := by
  rw [inv_mul_lt_iff₀ hj]
  have := mem_ball.mp hx
  linarith

section Family

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

namespace SlimCentre

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- The slim coordinate `η_j` of the packet, as a function on `X`. -/
def coord (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) : X → ℝ :=
  let P := c.packet
  letI := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  P.coord

/-- The LC85 cutoff of the packet, as a function on `X`. -/
def cutoff (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) : X → ℝ :=
  let P := c.packet
  letI := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  P.cutoff

/-- On the physical covering ball `B(j, 2Δρ(j))` the slim coordinate is smaller than `3Δ`. -/
theorem abs_coord_lt (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hΔ : 0 < Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) {x : X} (hx : x ∈ ball j (2 * (Δ * ρ j))) : |c.coord x| < 3 * Δ := by
  have hd : (ρ j)⁻¹ * dist x j < 2 * Δ :=
    inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) (by rwa [← mul_assoc] at hx)
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
  exact P.abs_coord_lt_of_dist_lt hΔ hσs (by linarith) hd

/-- The slim cutoff is one on the physical covering ball `B(j, 2Δρ(j))`. -/
theorem cutoff_eq_one (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hΔ : 0 < Δ) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) {x : X} (hx : x ∈ ball j (2 * (Δ * ρ j))) : c.cutoff x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 2 * Δ :=
    inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) (by rwa [← mul_assoc] at hx)
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
  exact P.cutoff_eq_one_of_dist_lt hΔ hσs (by linarith) hd

/-- The closed support of the slim cutoff lies in the physical ball `B̄(j, 0.91·10⁶Δρ(j))`. -/
theorem tsupport_cutoff_subset (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) :
    tsupport c.cutoff ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
  intro x hx
  have hr := hρ j
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
  have h := (P.tsupport_cutoff hx).1
  have h' : (ρ j)⁻¹ * @dist X mX.toDist x j ≤ 91 / 100 * (10 ^ 6 * Δ) := h
  rw [inv_mul_le_iff₀ hr] at h'
  change @dist X mX.toDist x j ≤ 91 / 100 * (10 ^ 6 * Δ) * ρ j
  linarith

/-- The slim coordinate is smooth on the physical ball `B(j, 10⁶Δρ(j))`. -/
theorem contMDiffOn_coord (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ c.coord (ball j (10 ^ 6 * Δ * ρ j)) := by
  have hr := hρ j
  have hsub : ball j (10 ^ 6 * Δ * ρ j) ⊆
      {x | (ρ j)⁻¹ * dist x j ≤ 10 ^ 6 * Δ} := fun x hx =>
    (inv_mul_dist_lt_of_mem_ball_LC87 hr hx).le
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
  exact P.contMDiffOn_coord.mono (hsub.trans P.closedBall_subset_domain)

/-- The slim cutoff is smooth. -/
theorem contMDiff_cutoff (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ c.cutoff := by
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
  exact P.contMDiff_cutoff

/-- The slim cutoff takes values in `[0, 1]`. -/
theorem cutoff_mem_Icc (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (x : X) :
    c.cutoff x ∈ Icc (0 : ℝ) 1 := by
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
  exact P.cutoff_mem_Icc x

end SlimCentre

open Classical in
/-- The slim cutoff at `j` (zero off the centres). -/
def SlimFamily.cutoff {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    (S : SlimFamily X g hmetric ρ hρ β Δ σs K) (j : X) : X → ℝ :=
  if hj : j ∈ S.centres then (S.centre j hj).cutoff else 0

namespace EdgeFamily

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

open Classical in
/-- The edge cutoff `Φ(η_j/Δ) ψ(F/(Δρ))` of the chart at `j` (normalized at `j`; zero off the
centres). -/
def cutoff (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (j : X) : X → ℝ :=
  if hj : j ∈ F.centres then
    let C := F.chart j hj
    let Fs := F.smoothing
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (Subtype.val : ball C.center (100 * Δ) → X).extend
      (fun x => edgeCoordinateProfile (C.coord x.val / Δ) *
        edgeHeightProfile (Fs x.val / ρ j / (Δ * (ρ x.val / ρ j)))) 0
  else 0

/-- The edge cutoff is one on the physical ball `B(j, 3Δρ(j))`. -/
theorem cutoff_eq_one (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ F.centres) {x : X} (hx : dist x j < 3 * Δ * ρ j) : F.cutoff j x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 3 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
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
  have hmem : x ∈ ball C.center (3 * Δ) := by
    rw [hc']
    exact hd
  exact C.cutoff_eq_one hmem

/-- The closed support of the edge cutoff lies in the physical ball `B̄(j, 100Δρ(j))`. -/
theorem tsupport_cutoff_subset (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    (j : X) : tsupport (F.cutoff j) ⊆ closedBall j (100 * Δ * ρ j) := by
  by_cases hj : j ∈ F.centres
  · refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro x hx
    by_contra hxb
    apply hx
    have hd : ¬ (ρ j)⁻¹ * dist x j < 100 * Δ := by
      intro h
      apply hxb
      have h' := (inv_mul_lt_iff₀ (hρ j)).mp h
      rw [mem_ball]
      linarith
    have hc := F.chart_center j hj
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
    let kR : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    have hc' : C.center = j := hc
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨a, ha⟩
    apply hd
    have hx' : x ∈ ball C.center (100 * Δ) := ha ▸ a.2
    rw [hc'] at hx'
    exact hx'
  · have h0 : F.cutoff j = 0 := by
      unfold cutoff
      rw [dite_eq_right hj]
    rw [h0, tsupport_zero]
    exact empty_subset _

end EdgeFamily

namespace LocalChartFamily

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- **LPA06's plateau exhaustion.** Every point lies in the zero stratum or in the plateau
(cutoff `= 1`) of a circle, slim or edge cutoff of the family. -/
theorem exists_cutoff_eq_one
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (x : X) :
    x ∈ scaledSplittingStratum.{u, 0} ρ hρ β 0 ∨
      (∃ j ∈ L.circle.centres, L.circle.cutoff j x = 1) ∨
      (∃ j ∈ L.slim.centres, L.slim.cutoff j x = 1) ∨
      ∃ j ∈ L.edge.centres, L.edge.cutoff j x = 1 := by
  rcases L.exhaustion x with h0 | ⟨j, hj, hx⟩ | ⟨j, hj, hx⟩ | ⟨j, hj, hx⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨j, hj, L.circle.plateau j hj x hx⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨j, hj, ?_⟩))
    unfold SlimFamily.cutoff
    rw [dite_eq_left hj]
    exact (L.slim.centre j hj).cutoff_eq_one hΔ hσs hσs1 hx
  · refine Or.inr (Or.inr (Or.inr ⟨j, hj, L.edge.cutoff_eq_one hj ?_⟩))
    have hr := hρ j
    nlinarith

/-- **LPA06's joint multiplicity.** At every point the number of active circle, slim and edge
supports is at most the sum of the three numerical constants. -/
theorem support_multiplicity
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (x : X) :
    ((L.circle.centres ∩ {j | x ∈ tsupport (L.circle.cutoff j)}).ncard : ℝ) +
      ((L.slim.centres ∩ {j | x ∈ tsupport (L.slim.cutoff j)}).ncard : ℝ) +
      ((L.edge.centres ∩ {j | x ∈ tsupport (L.edge.cutoff j)}).ncard : ℝ) ≤
    2 * (modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
        modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) +
      modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
          (4 * (1 + 2 * 2000000 + 1 / 3)) /
        modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3) := by
  have hc := L.circle.multiplicity x
  have hsl : ((L.slim.centres ∩ {j | x ∈ tsupport (L.slim.cutoff j)}).ncard : ℝ) ≤
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
        modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
    refine le_trans ?_ (L.slim.multiplicity x)
    have hsub : L.slim.centres ∩ {j | x ∈ tsupport (L.slim.cutoff j)} ⊆
        L.slim.centres ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))} := by
      rintro j ⟨hj, hx⟩
      rw [mem_ofPred_eq] at hx
      unfold SlimFamily.cutoff at hx
      rw [dite_eq_left hj] at hx
      have hb := (L.slim.centre j hj).tsupport_cutoff_subset hx
      refine ⟨hj, mem_ball.mpr ?_⟩
      have hb' := mem_closedBall.mp hb
      have hr := hρ j
      nlinarith
    exact_mod_cast Set.ncard_le_ncard hsub (L.slim.finite_centres.subset inter_subset_left)
  have hed : ((L.edge.centres ∩ {j | x ∈ tsupport (L.edge.cutoff j)}).ncard : ℝ) ≤
      modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
          (4 * (1 + 2 * 2000000 + 1 / 3)) /
        modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3) := by
    refine le_trans ?_ (L.edge.multiplicity x)
    have hsub : L.edge.centres ∩ {j | x ∈ tsupport (L.edge.cutoff j)} ⊆
        L.edge.centres ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))} := by
      rintro j ⟨hj, hx⟩
      rw [mem_ofPred_eq] at hx
      have hb := L.edge.tsupport_cutoff_subset j hx
      refine ⟨hj, mem_ball.mpr ?_⟩
      have hb' := mem_closedBall.mp hb
      have hr := hρ j
      nlinarith
    exact_mod_cast Set.ncard_le_ncard hsub (L.edge.finite_centres.subset inter_subset_left)
  linarith

end LocalChartFamily

end Family

section Tail

open DifferentialGeometry.Geometry.Comparison.Toponogov DifferentialGeometry.Geometry.Curvature

/-- **Consumer of `eventually_nonempty_localChartFamily`.** On ONE tail, in the blueprint parameter
order, there is a local chart family whose circle, slim and edge plateaus together with the zero
stratum exhaust the manifold, and whose active nonzero supports have at most the sum of the three
numerical multiplicity constants at every point. -/
theorem eventually_localChartFamily_plateaus_and_multiplicity
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T V : ℝ, 0 < T → 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ∃ L : LocalChartFamily (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K σc μ b s b' s' ε γc βc,
        ∀ x : X i, (x ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          (∃ j ∈ L.circle.centres, L.circle.cutoff j x = 1) ∨
          (∃ j ∈ L.slim.centres, L.slim.cutoff j x = 1) ∨
          ∃ j ∈ L.edge.centres, L.edge.cutoff j x = 1) ∧
        ((L.circle.centres ∩ {j | x ∈ tsupport (L.circle.cutoff j)}).ncard : ℝ) +
          ((L.slim.centres ∩ {j | x ∈ tsupport (L.slim.cutoff j)}).ncard : ℝ) +
          ((L.edge.centres ∩ {j | x ∈ tsupport (L.edge.cutoff j)}).ncard : ℝ) ≤
        2 * (modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) +
          modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
              (4 * (1 + 2 * 2000000 + 1 / 3)) /
            modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartFamily.{u, 0} hσs hσs1 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbs hbc hbb₁ hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ',
    fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  filter_upwards [h T V hT hTΛ hTV X g hmetric α hα hstand hder o] with i hi
  obtain ⟨ρ, hρpos, -, ⟨L⟩, -⟩ := hi
  exact ⟨ρ, hρpos, L, fun x => ⟨L.exists_cutoff_eq_one hΔpos hσs.le hσs1 x,
    L.support_multiplicity hΔpos x⟩⟩

end Tail

end DifferentialGeometry.Geometry.Collapse
