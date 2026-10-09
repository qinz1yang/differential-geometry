import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyBindings
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderAdapters
import DifferentialGeometry.Geometry.Metric.WeakEdgeLocalization

/-!
# FC18 (slim), FC14 and FC17 on the actual LC87 local chart family

Blueprint `master207B.tex`: FC14 (`lem:fibration-weak-edge-domain`, B:839), FC17
(`lem:fibration-padded-edge`, B:1139), FC18 (`prop:fibration-support-enclosures`, B:1199). The
actual data are LC87's `LocalChartFamily` (`LocalExport/LocalChartFamily.lean`): one smooth
`Λ`-Lipschitz scale `ρ`, the slim family (LC85 packets), the strong-edge family with ONE shared
smoothing `F` of the distance to the closed weak edge set and an LC84 `EdgeChart` at every centre.

* `fc18_slim_row` (FC18 (i)): the closed support of every actual slim cutoff lies in
  `B̄(j, 910000Δρ(j)) ⊆ B(j, 950000Δρ(j)) ⊆ B(j, 10⁶Δρ(j))`, where `η_j` is smooth.
* `fc14_row` (FC14): the weak-edge alternative for the actual normalized height
  `v = F/ρ`; in case (i) every actual edge cutoff equals its coordinate factor `f(η_j/Δ)`.
* `fc17_row` (FC17): at every actual strong-edge centre `j` the original composite
  `Q = (u, h)` of KL (9.5) (LFR30's strip map of the centre's two KL maps) is pointed, has
  `h ≥ 0`, distortion `≤ τΔ` on `B(j, 200Δ)` (normalized metric `d/ρ(j)`), covers the strip,
  and EVERY point of the closed weak edge set in `B(j, 120Δ)` has `h < Δ/10` (even `≤ τΔ`).
  Producer: LFR32 `coarse_border_of_physical_lipschitz_scale`.

Deviation (FC18 (i)): the enclosure radius is LFR20's `0.91·10⁶Δ` (LC87 `tsupport_cutoff_subset`)
instead of the blueprint's `901002Δ`; both lie strictly inside `950000Δ`.
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

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- **FC18 (i)** on the actual slim family. -/
theorem fc18_slim_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.slim.centres) :
    tsupport (L.slim.cutoff j) ⊆ closedBall j (910000 * Δ * ρ j) ∧
      closedBall j (910000 * Δ * ρ j) ⊆ ball j (950000 * Δ * ρ j) ∧
      ball j (950000 * Δ * ρ j) ⊆ ball j (10 ^ 6 * Δ * ρ j) ∧
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.centre j hj).coord (ball j (10 ^ 6 * Δ * ρ j)) := by
  have hrj := hρ j
  have hS : tsupport (L.slim.cutoff j) ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
    unfold SlimFamily.cutoff
    rw [dite_eq_left hj]
    exact (L.slim.centre j hj).tsupport_cutoff_subset
  have heq : 91 / 100 * (10 ^ 6 * Δ) * ρ j = 910000 * Δ * ρ j := by ring
  rw [heq] at hS
  refine ⟨hS, closedBall_subset_ball ?_, ball_subset_ball ?_,
    (L.slim.centre j hj).contMDiffOn_coord⟩
  · have := mul_pos hΔ hrj
    nlinarith
  · have := mul_pos hΔ hrj
    nlinarith

/-- The actual edge cutoff at `j` equals its coordinate factor `f(η_j/Δ)` wherever the actual
normalized height `F/ρ` is at most `8Δ`. -/
theorem EdgeFamily.cutoff_eq_coordinateProfile_of_le
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) {j : X}
    (hj : j ∈ F.centres) {x : X} (hx : x ∈ ball j (100 * Δ * ρ j))
    (hF : F.smoothing x / ρ x ≤ 8 * Δ) :
    F.cutoff j x = DifferentialGeometry.Analysis.edgeCoordinateProfile (F.coord j x / Δ) := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hF' : Fs x / ρ x ≤ 8 * Δ := hF
  have hq : Fs x / ρ j / (Δ * (ρ x / ρ j)) = Fs x / ρ x / Δ := by
    field_simp
  have hh : DifferentialGeometry.Analysis.edgeHeightProfile
      (Fs x / ρ j / (Δ * (ρ x / ρ j))) = 1 := by
    rw [hq]
    refine DifferentialGeometry.Analysis.descendingIntervalProfile_one (by norm_num) ?_
    rw [div_le_iff₀ hΔ]
    linarith
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
      (fun y => DifferentialGeometry.Analysis.edgeCoordinateProfile (C.coord y.val / Δ) *
        DifferentialGeometry.Analysis.edgeHeightProfile
          (Fs y.val / ρ j / (Δ * (ρ y.val / ρ j)))) 0
      (⟨x, hmem⟩ : ball C.center (100 * Δ)).val =
    DifferentialGeometry.Analysis.edgeCoordinateProfile (C.coord x / Δ)
  rw [Subtype.val_injective.extend_apply]
  simp only [hh, mul_one]

/-- **FC14** on the actual edge family: for the ONE shared smoothing `F` (`(1+ε)`-Lipschitz,
`ε ≤ 1`) and the actual scale, the weak-edge alternative holds on `D = B(p, Rρ(p))`; in case (i)
every actual edge cutoff whose chart domain contains a point of `D` equals its coordinate factor
there. -/
theorem fc14_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {p q : X} {R : ℝ} (hR : 0 < R) (hΔR : 120 * R ≤ Δ)
    (hsmall : Δ * Λ ≤ 1 / 100) (hRsmall : R * Λ ≤ 1 / 4) (hq : q ∈ ball p (R * ρ p))
    (hvq : L.edge.smoothing q / ρ q ≤ 9 * Δ) {A : Set X}
    (hnear : infDist p A ≤ 30 * Δ * ρ p) :
    (∀ x ∈ ball p (R * ρ p), L.edge.smoothing x / ρ x < 3 * Δ / 20 ∧
      ∀ j ∈ L.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
        L.edge.cutoff j x =
          DifferentialGeometry.Analysis.edgeCoordinateProfile (L.edge.coord j x / Δ)) ∨
    (∃ y ∈ ball p (R * ρ p), 3 * Δ / 20 ≤ L.edge.smoothing y / ρ y) ∧
      ∀ x ∈ ball p (R * ρ p),
        L.edge.smoothing x / ρ x ∈ Icc (Δ / 10) (181 * Δ / 20) ∧
          infDist x A / ρ x < 50 * Δ := by
  have hΔ : 0 < Δ := by linarith
  have hK : ((Real.toNNReal (1 + ε) : NNReal) : ℝ) ≤ 2 := by
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith
  have hsmall' : Δ * ((Real.toNNReal Λ : NNReal) : ℝ) ≤ 1 / 100 := by
    rwa [Real.coe_toNNReal _ hΛ]
  have hRsmall' : R * ((Real.toNNReal Λ : NNReal) : ℝ) ≤ 1 / 4 := by
    rwa [Real.coe_toNNReal _ hΛ]
  rcases GC.MetricGeometry.weak_edge_quotient_alternative L.edge.lipschitz_smoothing
      L.lipschitz_scale hK L.edge.smoothing_nonneg hρ hR hΔR hsmall' hRsmall' hq hvq
      hnear with hlow | hhigh
  · left
    intro x hx
    refine ⟨hlow x hx, fun j hj hxj => ?_⟩
    exact L.edge.cutoff_eq_coordinateProfile_of_le hΔ hj hxj (by linarith [hlow x hx])
  · exact Or.inr hhigh

/-- **FC17** on the actual edge family: at every strong-edge centre `j` the original composite
`Q = (u, h)` of its two KL maps (normalized metric `d/ρ(j)`) is pointed, has `h ≥ 0`, distortion
at most `τΔ` on `B(j, 200Δ)`, covers the strip `[-100Δ, 100Δ] × [0, 100Δ]` to error `τΔ`, and every
point of the closed weak edge set `E'` (each point at its own scale) in `B(j, 120Δ)` has
`h < Δ/10`; the parameter inequalities are those of LFR32. -/
theorem fc17_row (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (hΛ : 0 ≤ Λ) {j : X} (hj : j ∈ L.edge.centres) {τ : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ)
    (hτsmall : τ < 1 / 10000) (hscale : Λ < 1 / (1000000 * Δ))
    (hend : Λ < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧ (∀ x, 0 ≤ (Q x).snd) ∧
      (∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
        |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ) ∧
      (∀ y : WithLp 2 (ℝ × ℝ), |y.fst| ≤ 100 * Δ → y.snd ∈ Icc 0 (100 * Δ) →
        ∃ x, (ρ j)⁻¹ * dist x j < 200 * Δ ∧ dist (Q x) y < τ * Δ) ∧
      ∀ z ∈ closure {y : X | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
          y Δ b' s'}, (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10 := by
  obtain ⟨Y, mY, q, C, hC, hlen, ⟨F⟩, ⟨G⟩⟩ := L.edge.strong j hj
  have hscale' : ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / (1000000 * Δ) := by
    rwa [Real.coe_toNNReal _ hΛ]
  have hend' : ((Real.toNNReal Λ : NNReal) : ℝ) < s' / (100000000 * Δ ^ 2) := by
    rwa [Real.coe_toNNReal _ hΛ]
  have hcb := @GC.MetricGeometry.coarse_border_of_physical_lipschitz_scale X Y mX mY j q C b s hC
    Δ τ b' s' (Real.toNNReal Λ) ρ L.lipschitz_scale hρ F G hΔ hτ hτsmall hscale' hend'
    hb'domain hs'domain hb'error hs'error hsb' hss' hbs hlen.le
  dsimp only at hcb
  obtain ⟨-, -, h0, hnn, hdist, hcov, hlow, -⟩ := hcb
  refine ⟨(letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); F.stripMap G), h0, hnn,
    fun x y hx hy => hdist x hx y hy, fun y hy1 hy2 => ?_, fun z hz hzj => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := hcov y hy1 hy2
    exact ⟨x, hx, hxy⟩
  · have h := hlow z ⟨hz, (show (ρ j)⁻¹ * dist z j < 190 * Δ by linarith)⟩
    have hτΔ : τ * Δ < Δ / 10 := by nlinarith
    exact lt_of_le_of_lt h hτΔ

end DifferentialGeometry.Geometry.Collapse
