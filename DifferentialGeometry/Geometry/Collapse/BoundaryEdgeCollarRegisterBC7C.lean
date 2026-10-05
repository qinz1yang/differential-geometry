import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarExitsBC7C

/-!
# BCG07's edge-collar exits at every boundary register V4 (lane BCG7-COLLAR, consumer)

Disposition D61-10: EDP06's request `3βc ≤ β₂` comes from register V4 (`βc` chosen right after
`β₂`, `ClosedLaterV4.three_mul_βc_le_β₂_VAL6`), never as a late hypothesis. Every boundary
register V4 carries the closed later choice `R.later`, hence all of EDP06's numerical side
conditions. This file discharges them for the edge-collar exits on the complete final boundary
family taken AT THE REGISTER'S VALUES (`βc = R.later.circle.βc`, `γ = R.later.circle.γ`,
`Δ = R.later.excl.Δ`, `β 2 = R.later.excl.β₂`):

* `BoundaryRegisterV4.edp06_side_BC7C`: `3βc ≤ β₂`, `β₂ < 1`, `0 ≤ γ`, `1 ≤ Δ` at every boundary
  register V4;
* `LocalPacketsOnBFRZ.edgeB_collar_twoStratum_V4_BC7C`,
  `LocalPacketsOnBFRZ.edgeB_collar_coveredByCircle_V4_BC7C`: exits 2 and 3 (LFR38 band) with no
  numerical hypothesis;
* `LocalPacketsOnBFRZ.edgeB_edp06Band_coveredByCircle_V4_BC7C`: exit 3 at EDP06's band
  (`h ≤ 1/1000`) with no other numerical hypothesis;
* consumer `exists_boundaryRegisterV4_edgeB_collar_BC7C`: for every boundary early data and
  threshold record there is a boundary register V4 at whose values every complete final boundary
  family has exits 1–3 on every revised edge collar.
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

/-- **EDP06's numerical side conditions at every boundary register V4**: the collar request
`3βc ≤ β₂` (register V4), `β₂ < 1`, `0 ≤ γ` and `1 ≤ Δ`, read off the register's closed later
choice. -/
theorem BoundaryRegisterV4.edp06_side_BC7C {D : BoundaryEarlyData} {T : BoundaryThresholdsV4 D}
    (R : BoundaryRegisterV4 D T) :
    3 * R.later.circle.βc ≤ R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 ∧ 0 ≤ R.later.circle.γ ∧
      1 ≤ R.later.excl.Δ := by
  refine ⟨R.later.three_mul_βc_le_β₂_VAL6, ?_, R.later.γ_pos.le, ?_⟩
  · have := R.later.β₂_lt_audit_VAL6
    linarith
  · have := R.later.hundred_lt_Δ_VAL6
    linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc Lmax τ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
  {D : BoundaryEarlyData} {Tb : BoundaryThresholdsV4 D}

/-- **Exit 2 at a boundary register V4**: on the complete final boundary family at the register's
values, every point of the LFR38 collar band of a revised edge chart is two-stratum. -/
theorem LocalPacketsOnBFRZ.edgeB_collar_twoStratum_V4_BC7C (R : BoundaryRegisterV4 D Tb)
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β R.later.excl.Δ σs K σc μ b s b' s' ε γc
      R.later.circle.βc Lmax τ R.later.circle.γ δ εr e T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hβ : β 2 = R.later.excl.β₂) {j : X} (hj : j ∈ F.edgeB.centres) {x : X}
    (hx : dist x j < 100 * R.later.excl.Δ * ρ j)
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
      |c.coord x| ≤ 10 * R.later.excl.Δ)
    (hF1 : R.later.excl.Δ / 10 ≤ F.edgeB.smoothing x / ρ x)
    (hF2 : F.edgeB.smoothing x / ρ x ≤ 10 * R.later.excl.Δ) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 := by
  obtain ⟨h3, hβ2, -, -⟩ := R.edp06_side_BC7C
  rw [← hβ] at h3 hβ2
  exact F.edgeB_collar_twoStratum_BC7C h3 hβ2 hj hx hη hF1 hF2

/-- **Exit 3 at a boundary register V4**: on the complete final boundary family at the register's
values, every point of the LFR38 collar band of a revised edge chart lies in `U₁` and in the plateau
of a selected circle centre of the same family, with no numerical hypothesis. -/
theorem LocalPacketsOnBFRZ.edgeB_collar_coveredByCircle_V4_BC7C (R : BoundaryRegisterV4 D Tb)
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β R.later.excl.Δ σs K σc μ b s b' s' ε γc
      R.later.circle.βc Lmax τ R.later.circle.γ δ εr e T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hβ : β 2 = R.later.excl.β₂) {j : X} (hj : j ∈ F.edgeB.centres) {x : X}
    (hx : dist x j < 100 * R.later.excl.Δ * ρ j)
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
      |c.coord x| ≤ 10 * R.later.excl.Δ)
    (hF1 : R.later.excl.Δ / 10 ≤ F.edgeB.smoothing x / ρ x)
    (hF2 : F.edgeB.smoothing x / ρ x ≤ 10 * R.later.excl.Δ) :
    x ∈ U₁ ∧ ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
      dist x a < 2 * ρ a ∧
      (let c := F.circle.chart a ha
       letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
       ‖c.coord x‖ < 2 * (1 + R.later.circle.γ)) ∧ F.circle.cutoff a x = 1 := by
  obtain ⟨h3, hβ2, hγ, -⟩ := R.edp06_side_BC7C
  rw [← hβ] at h3 hβ2
  exact F.edgeB_collar_coveredByCircle_BC7C h3 hβ2 hγ hj hx hη hF1 hF2

/-- **Exit 3 at EDP06's band at a boundary register V4**: on the complete final boundary family at
the register's values, every point of EDP06's band at a revised edge centre
(`|η_j(x)| < 4.01Δ`, `|F_s(x)/ρ(x) − 4Δ| < h ≤ 1/1000`) is two-stratum, lies in `U₁` and in the
plateau of a selected circle centre of the same family. -/
theorem LocalPacketsOnBFRZ.edgeB_edp06Band_coveredByCircle_V4_BC7C (R : BoundaryRegisterV4 D Tb)
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β R.later.excl.Δ σs K σc μ b s b' s' ε γc
      R.later.circle.βc Lmax τ R.later.circle.γ δ εr e T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hβ : β 2 = R.later.excl.β₂) {h : ℝ} (hh : h ≤ 1 / 1000) {j : X}
    (hj : j ∈ F.edgeB.centres) {x : X} (hx : dist x j < 100 * R.later.excl.Δ * ρ j)
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
      |c.coord x| < 401 / 100 * R.later.excl.Δ)
    (ht : |F.edgeB.smoothing x / ρ x - 4 * R.later.excl.Δ| < h) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 ∧ x ∈ U₁ ∧
      ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
      dist x a < 2 * ρ a ∧
      (let c := F.circle.chart a ha
       letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
       ‖c.coord x‖ < 2 * (1 + R.later.circle.γ)) ∧ F.circle.cutoff a x = 1 := by
  obtain ⟨h3, hβ2, hγ, hΔ⟩ := R.edp06_side_BC7C
  rw [← hβ] at h3 hβ2
  exact ⟨F.edgeB_edp06Band_twoStratum_BC7C h3 hβ2 hΔ hh hj hx hη ht,
    F.edgeB_edp06Band_coveredByCircle_BC7C h3 hβ2 hγ hΔ hh hj hx hη ht⟩

/-- **Consumer: exits 1–3 at an actual boundary register V4.** For every boundary early data and
threshold record there is a boundary register V4 such that every complete final boundary family at
its values has, at every revised edge centre `j`: `j ∈ Ue₁`; every collar point `d(x, j) < 100Δρ_j`
lies in `U₁`; every point of the LFR38 collar band lies in the two-stratum and in a circle chart of
the same family with `cutoff_a(x) = 1`. -/
theorem exists_boundaryRegisterV4_edgeB_collar_BC7C (D : BoundaryEarlyData)
    (Tb : BoundaryThresholdsV4 D) :
    ∃ R : BoundaryRegisterV4 D Tb,
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc Lmax τ δ εr e T V vs ζ Λz : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β R.later.excl.Δ σs K σc μ b s b' s' ε γc
          R.later.circle.βc Lmax τ R.later.circle.γ δ εr e T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM),
        β 2 = R.later.excl.β₂ → ∀ j (hj : j ∈ F.edgeB.centres), j ∈ Ue₁ ∧
          ∀ x, dist x j < 100 * R.later.excl.Δ * ρ j → x ∈ U₁ ∧
            ((let c := F.edgeB.chart j hj
              let hMc : CompleteSpace X := ‹CompleteSpace X›
              letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
              letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
              letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
                radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
              letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
                radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
              letI : CompleteSpace X :=
                (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
              |c.coord x| ≤ 10 * R.later.excl.Δ) →
            R.later.excl.Δ / 10 ≤ F.edgeB.smoothing x / ρ x →
            F.edgeB.smoothing x / ρ x ≤ 10 * R.later.excl.Δ →
            x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 ∧
              ∃ a ∈ F.circle.centres, dist x a < 2 * ρ a ∧ F.circle.cutoff a x = 1) := by
  obtain ⟨R⟩ := exists_boundaryRegisterV4 D Tb
  refine ⟨R, fun X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc Lmax τ δ εr e T V vs ζ
    Λz U₁ U₂ Ue₁ Ue₂ oM F hβ j hj => ⟨(F.edgeB_collar_eligible_BC7C hj).1, fun x hx =>
      ⟨((F.edgeB_collar_eligible_BC7C hj).2 x hx).1, fun hη hF1 hF2 => ?_⟩⟩⟩
  obtain ⟨-, a, ha, -, hxa, -, hcut⟩ := F.edgeB_collar_coveredByCircle_V4_BC7C R hβ hj hx hη hF1 hF2
  exact ⟨F.edgeB_collar_twoStratum_V4_BC7C R hβ hj hx hη hF1 hF2, a, ha, hxa, hcut⟩

end DifferentialGeometry.Geometry.Collapse
