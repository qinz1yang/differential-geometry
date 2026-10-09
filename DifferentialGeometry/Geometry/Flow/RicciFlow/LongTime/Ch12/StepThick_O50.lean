import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEndParts_O32

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-! CH12-O50 GB: the thickness conjunct of P2 from `hthickW` (`thickW_shape_O40` body, inline)
and the isotopy facts (bijective slices, identity off `B(4R)`): `E (μ, ·)` maps `B(a)` into
`B(4R')` when `4R ≤ 4R'` and `a ≤ 4R'`. -/

/-- **GB.** P2's last conjunct, for any track `f` satisfying the P2 hypothesis at `(ε', R', k')`
with `R₀ ≤ R'`, `ε' ≤ ε₀`, `k₀ ≤ k'`, `T₀ ≤ t`. -/
theorem step_thick_O50 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (hthickW :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (4 * R''), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
    ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ 0 < T₀ ∧
      ∀ (t t₂ : ℝ) (ht : 0 < t), T₀ ≤ t → ∀ (R R' ε' : ℝ) (k' : ℕ), R₀ ≤ R' → ε' ≤ ε₀ →
      k₀ ≤ k' → R ≤ R' → a ≤ 4 * R' →
      ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
        (∀ s (hs : s ∈ Icc t t₂),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
          Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
          ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
      ∀ E : ℝ × H.Carrier → H.Carrier, (∀ μ, Function.Bijective (fun p => E (μ, p))) →
        (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * R) → E (μ, p) = p) →
        (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r) := by
  obtain ⟨ε₀, R₀, T₀, k₀, hε₀, hT₀, hth⟩ := hthickW
  refine ⟨ε₀, R₀, T₀, k₀, hε₀, hT₀,
    fun t t₂ ht hTt R R' ε' k' hR₀ hε' hk' hRR' ha f hf E hbij hsupp => ?_⟩
  intro s hs μ y hy
  have hmem : E (μ, y) ∈ riemannianBallOf H.metric H.basepoint (4 * R') := by
    by_cases hyB : y ∈ riemannianBallOf H.metric H.basepoint (4 * R)
    · have hin : E (μ, y) ∈ riemannianBallOf H.metric H.basepoint (4 * R) := by
        by_contra hn
        have h1 : E (μ, y) = y := (hbij μ).1 (hsupp μ (E (μ, y)) hn)
        exact hn (by rw [h1]; exact hyB)
      exact riemannianBallOf_mono H.metric H.basepoint (by linarith) hin
    · rw [hsupp μ y hyB]
      exact riemannianBallOf_mono H.metric H.basepoint ha hy
  obtain ⟨hsm, -, herr⟩ := hf s hs
  exact hth s (le_trans hTt hs.1) (f s hs) R' hR₀ hsm
    (fun k'' hk'' p hp => lt_of_lt_of_le (herr k'' (le_trans hk'' hk') p hp) hε') (E (μ, y)) hmem

end GC.LongTime.Ch12
