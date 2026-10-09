import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SingleTimeHLow_O81

set_option autoImplicit false

/-! # CH12-O81 G2: P-small producer of `hthickW'` ([FROZEN] CH12-O74 G3 / [FROZEN] CH12-O81).

`thickWB_small_O81 F H a : ∃ w₁ > 0, ∀ wstar ≤ w₁, <thickWB_shape_O74 F H wstar a body>` — closed.
Constants: `N := max 10000 (|a| + 1)`, `δ := N⁻¹` (`≤ 1/10000`, `a + 1 ≤ δ⁻¹`), `ε₀ := δ`, `R₀ := N`
(`B(base, 2N) ⊆ B(base, 4R'')`), `T₀ := 1`, `k₀ := 2`, `w₁ := w` of `hlow_single_O81 F H (a + 1)`;
`wstar ≤ w₁` gives `ofReal (wstar r³) ≤ ofReal (w₁ r³)`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **G2 ([FROZEN] CH12-O81 = (P-small) of [FROZEN] CH12-O74 G3).** -/
theorem thickWB_small_O81 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (a : ℝ) :
    ∃ w₁ : ℝ, 0 < w₁ ∧ ∀ wstar : ℝ, wstar ≤ w₁ →
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (a + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r := by
  set N : ℝ := max 10000 (|a| + 1) with hN
  have hN1 : (10000 : ℝ) ≤ N := le_max_left _ _
  have hNa : a + 1 ≤ N :=
    (by have := le_abs_self a; linarith : a + 1 ≤ |a| + 1).trans (le_max_right _ _)
  have hNpos : 0 < N := by linarith
  obtain ⟨w, hw, hlow⟩ := hlow_single_O81 F H (a + 1)
  refine ⟨w, hw, fun wstar hws => ⟨N⁻¹, N, 1, 2, inv_pos.mpr hNpos, one_pos,
    fun s hs q R'' hR'' hsm hinj hck y hy => ?_⟩⟩
  have hδ : 0 < N⁻¹ := inv_pos.mpr hNpos
  have hδ1 : N⁻¹ ≤ 1 / 10000 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hN1
  have hsub : riemannianBallOf H.metric H.basepoint (2 * (N⁻¹)⁻¹) ⊆
      riemannianBallOf H.metric H.basepoint (4 * R'') :=
    riemannianBallOf_mono _ _ (by rw [inv_inv]; linarith)
  obtain ⟨r, hr, hcr, hvol⟩ := hlow N⁻¹ hδ hδ1 (by rw [inv_inv]; exact hNa) s
    (lt_of_lt_of_le one_pos hs) q (hsm.mono hsub) (hinj.mono hsub)
    (fun k hk p hp => hck k hk p (hsub hp)) y hy
  refine ⟨r, hr, hcr, le_trans (ENNReal.ofReal_le_ofReal ?_) hvol⟩
  exact mul_le_mul_of_nonneg_right hws (by positivity)

end GC.LongTime.Ch12
