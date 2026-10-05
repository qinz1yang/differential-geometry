import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarBFR
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConorm

/-!
# BCG07: the first three edge-collar exits on the complete final boundary family (lane BCG7-COLLAR)

External draft 61 §5.2 and disposition D61-10: the identification of a whole disk-boundary circle
of `edgeB` with a whole circle fibre is split into four exits

`edgeB_collar_eligible → edgeB_collar_twoStratum → edgeB_collar_coveredByCircle →
  wholeDiskBoundary_eq_wholeCircleFiber`.

The first three do not read the final map `E`; they are stated here on the complete final boundary
family `LocalPacketsOnBFRZ` (lane BFAM-ZD), through its projections only (`edgeB`, `edgeB_domain`,
`rank_le_two`, the LFR38 collar of the revised edge charts, and the eligible cover of the SAME
circle family `circle.covers`). The fourth needs `E` (the global equation and the
open-and-closed argument on the compact connected circle) and is not here.

* `LocalPacketsOnBFRZ.edgeB_collar_eligible_BC7C` (exit 1, from `edgeB_domain` and the buffer
  `100Δρ_j < 1000Δρ_j`): every revised edge centre `j` lies in `Ue₁`, and every point of its collar
  ball `d(x, j) < 100Δρ_j` lies in the circle-eligible region `U₁` and has no 3-splitting at
  tolerance `β 3` (`rank_le_two` on `U₁`);
* `LocalPacketsOnBFRZ.edgeB_collar_twoStratum_BC7C` (exit 2, the same chart's LFR38 collar and
  no-three): a point of the LFR38 collar band of a revised edge chart (`d(x, j) < 100Δρ_j`,
  `|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ F_s(x)/ρ(x) ≤ 10Δ`) lies in the two-stratum (`3βc ≤ β 2 < 1`);
* `LocalPacketsOnBFRZ.edgeB_collar_coveredByCircle_BC7C` (exit 3, the eligible cover of the SAME
  circle family; NOT a consequence of `edgeB_domain` alone): such a point lies in `U₁` and in the
  plateau of a selected circle centre `a`: `B(x, ρ(x)) ⊆ B(a, 2ρ(a))`, `d(x, a) < 2ρ(a)`,
  `‖η_a(x)‖ < 2(1 + γ)` and the circle cutoff of `a` is `1` at `x`;
* `LocalPacketsOnBFRZ.edgeB_edp06Band_twoStratum_BC7C`,
  `LocalPacketsOnBFRZ.edgeB_edp06Band_coveredByCircle_BC7C`: the same at EDP06's band
  (`|η_j(x)| < 4.01Δ`, `|F_s(x)/ρ(x) − 4Δ| < h ≤ 1/1000`, `Δ ≥ 1`), which lies in the LFR38 band.

The numerical side condition `3βc ≤ β 2` is a relation between the family's parameters; at the
register it is supplied by register V4 (`BoundaryEdgeCollarRegisterBC7C`), never as a late
hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **Exit 1: the edge collar is circle-eligible** (BCG01's buffer, `edgeB_domain`): every revised
edge centre `j` lies in `Ue₁`, and every point `x` of its collar ball `d(x, j) < 100Δρ_j` lies in
the circle-eligible region `U₁` (the whole packet domain `B(j, 1000Δρ_j)` does) and has no
3-splitting at tolerance `β 3` in `ρ(x)⁻¹ d` (`rank_le_two`). -/
theorem LocalPacketsOnBFRZ.edgeB_collar_eligible_BC7C
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) {j : X} (hj : j ∈ F.edgeB.centres) :
    j ∈ Ue₁ ∧ ∀ x, dist x j < 100 * Δ * ρ j → x ∈ U₁ ∧
      ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3) := by
  refine ⟨F.edgeB.centres_subset hj, fun x hx => ?_⟩
  have hd := dist_nonneg (x := x) (y := j)
  exact F.toLocalPacketsOnBFR.edgeB_domain_no_three_BCG5 j hj x (by linarith)

/-- **Exit 2: the LFR38 collar band is two-stratum** (the same chart's collar certificate and the
no-three input of exit 1): at a revised edge centre `j`, a point `x` with `d(x, j) < 100Δρ_j`,
`|η_j(x)| ≤ 10Δ` and `Δ/10 ≤ F_s(x)/ρ(x) ≤ 10Δ` lies in the two-stratum (`3βc ≤ β 2 < 1`). -/
theorem LocalPacketsOnBFRZ.edgeB_collar_twoStratum_BC7C
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1)
    {j : X} (hj : j ∈ F.edgeB.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := F.edgeB.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F.edgeB.smoothing x / ρ x) (hF2 : F.edgeB.smoothing x / ρ x ≤ 10 * Δ) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 :=
  F.edgeB.collar_two_stratum_BCG4 h3βc hβ2 hj hx hη hF1 hF2
    ((F.edgeB_collar_eligible_BC7C hj).2 x hx).2

/-- **Exit 3: the LFR38 collar band is covered by the SAME circle family** (its eligible cover of
`U₁`, exits 1–2): at a revised edge centre `j`, a point `x` of the collar band lies in `U₁` and in
the plateau of a selected circle centre `a`: `B(x, ρ(x)) ⊆ B(a, 2ρ(a))`, `d(x, a) < 2ρ(a)`,
`‖η_a(x)‖ < 2(1 + γ)` (normalized at `a`) and `cutoff_a(x) = 1` (`3βc ≤ β 2 < 1`, `0 ≤ γ`). -/
theorem LocalPacketsOnBFRZ.edgeB_collar_coveredByCircle_BC7C
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ)
    {j : X} (hj : j ∈ F.edgeB.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := F.edgeB.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F.edgeB.smoothing x / ρ x) (hF2 : F.edgeB.smoothing x / ρ x ≤ 10 * Δ) :
    x ∈ U₁ ∧ ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
      dist x a < 2 * ρ a ∧
      (let c := F.circle.chart a ha
       letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
       ‖c.coord x‖ < 2 * (1 + γ)) ∧ F.circle.cutoff a x = 1 := by
  have hxU := ((F.edgeB_collar_eligible_BC7C hj).2 x hx).1
  have h2 := F.edgeB_collar_twoStratum_BC7C h3βc hβ2 hj hx hη hF1 hF2
  obtain ⟨a, ha, hsub, hxa, hc⟩ := F.toLocalPacketsOn.circle_chart_of_two_BCG4 hγ hxU h2
  exact ⟨hxU, a, ha, hsub, hxa, hc, F.circle.plateau a ha x (mem_ball.mpr hxa)⟩

/-- **Exit 2 at EDP06's band**: at a revised edge centre `j`, a point `x` with `d(x, j) < 100Δρ_j`,
`|η_j(x)| < 4.01Δ` and `|F_s(x)/ρ(x) − 4Δ| < h ≤ 1/1000` lies in the two-stratum
(`3βc ≤ β 2 < 1`, `Δ ≥ 1`; EDP06's band lies in the LFR38 band). -/
theorem LocalPacketsOnBFRZ.edgeB_edp06Band_twoStratum_BC7C
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hΔ : 1 ≤ Δ) {h : ℝ}
    (hh : h ≤ 1 / 1000) {j : X} (hj : j ∈ F.edgeB.centres) {x : X}
    (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := F.edgeB.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| < 401 / 100 * Δ)
    (ht : |F.edgeB.smoothing x / ρ x - 4 * Δ| < h) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 := by
  obtain ⟨hη', hF1, hF2⟩ := edp06_band_mem_band_EDP6 hΔ hh hη ht
  exact F.edgeB_collar_twoStratum_BC7C h3βc hβ2 hj hx hη' hF1 hF2

/-- **Exit 3 at EDP06's band**: a point of EDP06's band at a revised edge centre `j` lies in `U₁`
and in the plateau of a selected circle centre `a` of the SAME circle family
(`B(x, ρ(x)) ⊆ B(a, 2ρ(a))`, `d(x, a) < 2ρ(a)`, `‖η_a(x)‖ < 2(1 + γ)`, `cutoff_a(x) = 1`;
`3βc ≤ β 2 < 1`, `0 ≤ γ`, `Δ ≥ 1`). -/
theorem LocalPacketsOnBFRZ.edgeB_edp06Band_coveredByCircle_BC7C
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ)
    (hΔ : 1 ≤ Δ) {h : ℝ} (hh : h ≤ 1 / 1000) {j : X} (hj : j ∈ F.edgeB.centres) {x : X}
    (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := F.edgeB.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| < 401 / 100 * Δ)
    (ht : |F.edgeB.smoothing x / ρ x - 4 * Δ| < h) :
    x ∈ U₁ ∧ ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
      dist x a < 2 * ρ a ∧
      (let c := F.circle.chart a ha
       letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
       ‖c.coord x‖ < 2 * (1 + γ)) ∧ F.circle.cutoff a x = 1 := by
  obtain ⟨hη', hF1, hF2⟩ := edp06_band_mem_band_EDP6 hΔ hh hη ht
  exact F.edgeB_collar_coveredByCircle_BC7C h3βc hβ2 hγ hj hx hη' hF1 hF2

end DifferentialGeometry.Geometry.Collapse
