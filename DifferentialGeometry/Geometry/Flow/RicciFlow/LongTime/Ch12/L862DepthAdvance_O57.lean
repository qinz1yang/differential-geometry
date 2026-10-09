import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroLowPoint_S33
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83Core_CX7

/-!
# CH12-O57 G3a: max-depth advance and the bottom-volume → KL83.1 → child adapter

Two pieces of `step866_v3_of_contracts_O57` (`[FROZEN] CH12-O57 G2`, R5 D-R5-3/D-R5-4, S4):

* `depth_advance_O57`: the max-depth argument of Sublemma 86.6 without an attained supremum.  If
  the depth set `𝒟 ⊆ [0, ∞)` contains `0`, is downward closed, and every `d ∈ 𝒟` with `d < τ₀`
  extends by a *uniform* `c > 0` (chosen before the frontier, R5 S2), then every `d ∈ [0, τ₀)`
  lies in `𝒟` (Archimedean induction).
* `child_select_O57`: the 82.1(2) bottom volume `vol B_v(p, r/4) ≥ w (r/4)³/10` (the second
  conjunct of `kl82_1_O36`) and `sec ≥ -r⁻²` on `B_v(p, r)` give, via KL83.1
  (`almost_euclidean_subball_CX7` at `w/10`, radius `r/4`), a centre `y ∈ B_v(p, r/4)` such that
  every child radius `r' ≤ θ r` satisfies the Child hypotheses (sectional `-r'⁻²`, `(1-ε)`-Euclidean
  sub-balls); `θ := min {1/4, θ₈₃/4}` depends only on `w, ε` (R5 D-R5-3: θ before `∀ τ₁ τ₂`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Max-depth advance (R5 S4): uniform extension length `c` ⇒ every depth below `τ₀`. -/
theorem depth_advance_O57 (𝒟 : Set ℝ) {τ₀ c : ℝ} (hc : 0 < c) (h0 : (0 : ℝ) ∈ 𝒟)
    (hdown : ∀ d ∈ 𝒟, ∀ d' : ℝ, 0 ≤ d' → d' ≤ d → d' ∈ 𝒟)
    (hstep : ∀ d ∈ 𝒟, d < τ₀ → ∃ e ∈ 𝒟, d + c ≤ e) :
    ∀ d : ℝ, 0 ≤ d → d < τ₀ → d ∈ 𝒟 := by
  have key : ∀ n : ℕ, ∀ d : ℝ, 0 ≤ d → d ≤ n * c → d < τ₀ → d ∈ 𝒟 := by
    intro n
    induction n with
    | zero =>
      intro d hd0 hdn _
      have hd : d = 0 := le_antisymm (by simpa using hdn) hd0
      exact hd ▸ h0
    | succ n ih =>
      intro d hd0 hdn hdτ
      by_cases hle : d ≤ n * c
      · exact ih d hd0 hle hdτ
      · rw [not_le] at hle
        have hn0 : 0 ≤ (n : ℝ) * c := by positivity
        have hmem := ih ((n : ℝ) * c) hn0 le_rfl (by linarith)
        obtain ⟨e, he, hce⟩ := hstep _ hmem (by linarith)
        push_cast at hdn
        exact hdown e he d hd0 (by linarith)
  intro d hd0 hdτ
  obtain ⟨n, hn⟩ := Archimedean.arch d hc
  exact key n d hd0 (by simpa [nsmul_eq_mul] using hn) hdτ

/-- Bottom volume (82.1(2), radius `r/4`) → KL83.1 → the Child hypotheses at every radius
`r' ≤ θ r`, with `θ` depending on `w, ε` only. -/
theorem child_select_O57 {w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧
      ∀ (H : ObservedHistory.{u}) (v : Icc (0 : ℝ) H.horizon) (p : (H.stageAt v).Carrier)
        (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v) p r,
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage v) v) p (r / 4) →
        ∃ y : (H.stageAt v).Carrier,
          y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v) p (r / 4) ∧
          ∀ r' : ℝ, 0 < r' → r' ≤ θ * r →
            (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v) y r',
              SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r' ^ 2)⁻¹)) ∧
            (∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v) y r',
              ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
                ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
                  ballVolume (H.stageMetric (H.activeStage v) v) z ρ) := by
  obtain ⟨θ₀, hθ₀, hG1⟩ := almost_euclidean_subball_CX7.{u} (w / 10) (by positivity) ε hε
  refine ⟨min (1 / 4) (θ₀ / 4), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro H v p r hr hsec hvol
  set g := H.stageMetric (H.activeStage v) v
  have hr4 : 0 < r / 4 := by positivity
  have hsec4 : ∀ q ∈ riemannianBallOf g p (r / 4),
      SectionalBoundedBelowAt g q (-((r / 4) ^ 2)⁻¹) := by
    intro q hq
    refine (hsec q (riemannianBallOf_mono g p (by linarith) hq)).mono ?_
    have h1 : (r ^ 2)⁻¹ ≤ ((r / 4) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith)
    linarith
  have hvol' : ENNReal.ofReal (w / 10 * (r / 4) ^ 3) ≤ ballVolume g p (r / 4) := by
    have he : w / 10 * (r / 4) ^ 3 = w * (r / 4) ^ 3 / 10 := by ring
    rw [he]; exact hvol
  obtain ⟨y, hysub, hyvol⟩ := hG1 _ g p (r / 4) hr4 hsec4 hvol'
  have hθr : ∀ r' : ℝ, r' ≤ min (1 / 4) (θ₀ / 4) * r → r' ≤ θ₀ * (r / 4) := by
    intro r' h
    have := mul_le_mul_of_nonneg_right (min_le_right (1 / 4 : ℝ) (θ₀ / 4)) hr.le
    linarith
  have hr'r : ∀ r' : ℝ, r' ≤ min (1 / 4) (θ₀ / 4) * r → r' ≤ r := by
    intro r' h
    have := mul_le_mul_of_nonneg_right (min_le_left (1 / 4 : ℝ) (θ₀ / 4)) hr.le
    linarith
  refine ⟨y, hysub (mem_riemannianBallOf_self_S33 g y (by positivity)), fun r' hr' hr'θ => ⟨?_, ?_⟩⟩
  · intro q hq
    have hq1 : q ∈ riemannianBallOf g y (θ₀ * (r / 4)) :=
      riemannianBallOf_mono g y (hθr r' hr'θ) hq
    have hq2 : q ∈ riemannianBallOf g p r :=
      riemannianBallOf_mono g p (by linarith) (hysub hq1)
    refine (hsec q hq2).mono ?_
    have h1 : (r ^ 2)⁻¹ ≤ (r' ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hr'.le (hr'r r' hr'θ) 2)
    linarith
  · intro z hz ρ hρ hρr'
    exact hyvol z (riemannianBallOf_mono g y (hθr r' hr'θ) hz) ρ hρ
      (hρr'.trans (hθr r' hr'θ))

end GC.LongTime.Ch12
