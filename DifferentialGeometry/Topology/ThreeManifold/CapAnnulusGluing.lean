import DifferentialGeometry.Topology.Diffeomorph.IntervalGerm
import DifferentialGeometry.Topology.ThreeManifold.CapBoundaryCylinder
import DifferentialGeometry.Topology.ThreeManifold.TubeReparametrization
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

noncomputable section

open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

private theorem exists_radius_diffeomorph (L : ℝ) (hL : 0 < L) :
    ∃ ρ : ℝ ≃ₘ[ℝ] ℝ,
      ρ (L / 4) = 0 ∧ ρ L = 1 ∧ (∀ r, 0 < deriv ρ r) ∧
      ρ '' Icc (L / 4) L = Icc 0 1 ∧
      ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
        (∀ t, |t| ≤ δ → -ρ (L / 4 * (1 + t)) = -(L / 4) * t ∧
          ρ (L / 4 * (1 - t)) = -(L / 4) * t) ∧
        ∀ r, L - ε ≤ r → ρ r = r - L + 1 := by
  obtain ⟨ρ, hzero, hone, hpos, himage, δ₀, ε, hδ₀, hε, hlo, hhi⟩ :=
    Diffeomorph.exists_interval_diffeomorph_eq_translation_near_endpoints
      (by linarith : L / 4 < L) (by norm_num : (0 : ℝ) < 1)
  refine ⟨ρ, hzero, hone, hpos, himage, δ₀ / (L / 4), ε,
    div_pos hδ₀ (by positivity), hε, ?_, hhi⟩
  intro t ht
  have hprod : L / 4 * |t| ≤ δ₀ := by
    have h := (le_div_iff₀ (by positivity : 0 < L / 4)).mp ht
    nlinarith
  have hleft : |L / 4 * (1 + t) - L / 4| ≤ δ₀ := by
    rw [show L / 4 * (1 + t) - L / 4 = L / 4 * t by ring,
      abs_mul, abs_of_pos (by positivity : 0 < L / 4)]
    exact hprod
  have hright : |L / 4 * (1 - t) - L / 4| ≤ δ₀ := by
    rw [show L / 4 * (1 - t) - L / 4 = -(L / 4 * t) by ring,
      abs_neg, abs_mul, abs_of_pos (by positivity : 0 < L / 4)]
    exact hprod
  rw [hlo _ hleft, hlo _ hright]
  constructor <;> ring

private def annulusSeamCoordinate (ρ : ℝ → ℝ) (L t : ℝ) : ℝ :=
  if 0 ≤ t then -ρ (L / 4 * (1 + t)) else ρ (L / 4 * (1 - t))

private theorem annulusSeamCoordinate_eventuallyEq (ρ : ℝ → ℝ) (L δ : ℝ)
    (hδ : 0 < δ)
    (hρ : ∀ t, |t| ≤ δ → -ρ (L / 4 * (1 + t)) = -(L / 4) * t ∧
      ρ (L / 4 * (1 - t)) = -(L / 4) * t) :
    annulusSeamCoordinate ρ L =ᶠ[𝓝 0] (fun t => -(L / 4) * t) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
  have habs : |t| ≤ δ := (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht : |t| < δ).le
  unfold annulusSeamCoordinate
  split_ifs
  · exact (hρ t habs).1
  · exact (hρ t habs).2

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local notation "PI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

private def seamReparametrization (L : ℝ) (hL : 0 < L) :
    (S2 × ℝ) ≃ₘ⟮PI, PI⟯ (S2 × ℝ) :=
  (Manifold.sphereAntipodalDiffeomorph (E := E3) (n := 2)).prodCongr
    ((LinearEquiv.smulOfNeZero ℝ ℝ (-(L / 4)) (neg_ne_zero.mpr (div_ne_zero (ne_of_gt hL) (by norm_num)))).toContinuousLinearEquiv.toDiffeomorph)

private def annulusSeamMap (a : T.Index)
    (Ψ : (S2 × unitInterval) ≃ₘ⟮CI, CI⟯ (S2 × unitInterval)) (L : ℝ) (ρ : ℝ → ℝ)
    (p : S2 × ℝ) : M.Carrier :=
  T.reparametrizedTube a Ψ (-p.1, annulusSeamCoordinate ρ L p.2)

private theorem annulusSeamMap_eventuallyEq (a : T.Index)
    (Ψ : (S2 × unitInterval) ≃ₘ⟮CI, CI⟯ (S2 × unitInterval)) (L : ℝ) (hL : 0 < L)
    (ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, |t| ≤ δ → -ρ (L / 4 * (1 + t)) = -(L / 4) * t ∧
      ρ (L / 4 * (1 - t)) = -(L / 4) * t) (z : S2) :
    annulusSeamMap T a Ψ L ρ =ᶠ[𝓝 (z, (0 : ℝ))]
      (T.reparametrizedTube a Ψ) ∘ seamReparametrization L hL := by
  have h := (annulusSeamCoordinate_eventuallyEq ρ L δ hδ hρ).comp_tendsto
    (continuous_snd.tendsto (z, (0 : ℝ)))
  filter_upwards [h] with p hp
  change T.reparametrizedTube a Ψ (-p.1, annulusSeamCoordinate ρ L p.2) = _
  change annulusSeamCoordinate ρ L p.2 = -(L / 4) * p.2 at hp
  rw [hp]
  rfl

private theorem isLocalDiffeomorphAt_annulusSeamMap (a : T.Index)
    (Ψ : (S2 × unitInterval) ≃ₘ⟮CI, CI⟯ (S2 × unitInterval)) (L : ℝ) (hL : 0 < L)
    (ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, |t| ≤ δ → -ρ (L / 4 * (1 + t)) = -(L / 4) * t ∧
      ρ (L / 4 * (1 - t)) = -(L / 4) * t) (z : S2) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞ (annulusSeamMap T a Ψ L ρ) (z, 0) := by
  have h := (seamReparametrization L hL).isLocalDiffeomorph (z, (0 : ℝ))
  have ht := T.isLocalDiffeomorphAt_reparametrizedTube a Ψ
    (p := seamReparametrization L hL (z, 0)) (by change -(L / 4) * 0 ∈ Ioo (-1 : ℝ) 1; norm_num)
  have hc := h.comp (𝓡 3) M.Carrier ht
  exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
    (annulusSeamMap_eventuallyEq T a Ψ L hL ρ δ hδ hρ z) hc

theorem isLocalDiffeomorphAt_annulus_seam_of_eventuallyEq (a : T.Index)
    (Ψ : (S2 × unitInterval) ≃ₘ⟮CI, CI⟯ (S2 × unitInterval)) (L : ℝ) (hL : 0 < L)
    (ρ : ℝ → ℝ) (hρ : ρ =ᶠ[𝓝 (L / 4)] (fun r => r - L / 4)) (z : S2) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞
      (fun p : S2 × ℝ => T.reparametrizedTube a Ψ
        (-p.1, if 0 ≤ p.2 then -ρ (L / 4 * (1 + p.2)) else ρ (L / 4 * (1 - p.2))))
      (z, 0) := by
  obtain ⟨ε, hε, heq⟩ := Metric.eventually_nhds_iff.mp hρ
  refine isLocalDiffeomorphAt_annulusSeamMap T a Ψ L hL ρ
    (ε / (2 * (L / 4))) (by positivity) ?_ z
  intro t ht
  have hprod : L / 4 * |t| ≤ ε / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (L / 4))).mp ht
    nlinarith
  have hp : dist (L / 4 * (1 + t)) (L / 4) < ε := by
    rw [Real.dist_eq, show L / 4 * (1 + t) - L / 4 = L / 4 * t by ring,
      abs_mul, abs_of_pos (by positivity : 0 < L / 4)]
    linarith
  have hm : dist (L / 4 * (1 - t)) (L / 4) < ε := by
    rw [Real.dist_eq, show L / 4 * (1 - t) - L / 4 = -(L / 4 * t) by ring,
      abs_neg, abs_mul, abs_of_pos (by positivity : 0 < L / 4)]
    linarith
  rw [heq hp, heq hm]
  constructor <;> ring

theorem exists_annulus_seam_localDiffeomorph (a : T.Index)
    (Ψ : (S2 × unitInterval) ≃ₘ⟮CI, CI⟯ (S2 × unitInterval)) (L : ℝ) (hL : 0 < L) :
    ∃ ρ : ℝ ≃ₘ[ℝ] ℝ,
      ρ (L / 4) = 0 ∧ ρ L = 1 ∧ (∀ r, 0 < deriv ρ r) ∧
      ρ '' Icc (L / 4) L = Icc 0 1 ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ r, L - ε ≤ r → ρ r = r - L + 1) ∧
      ∀ z : S2, IsLocalDiffeomorphAt PI (𝓡 3) ∞
        (fun p : S2 × ℝ => T.reparametrizedTube a Ψ
          (-p.1, if 0 ≤ p.2 then -ρ (L / 4 * (1 + p.2)) else ρ (L / 4 * (1 - p.2))))
        (z, 0) := by
  obtain ⟨ρ, hzero, hone, hpos, himage, δ, ε, hδ, hε, hseam, houter⟩ :=
    exists_radius_diffeomorph L hL
  exact ⟨ρ, hzero, hone, hpos, himage, ⟨ε, hε, houter⟩,
    isLocalDiffeomorphAt_annulusSeamMap T a Ψ L hL ρ δ hδ hseam⟩

end DifferentialGeometry.Topology.SphericalTubeSystem
