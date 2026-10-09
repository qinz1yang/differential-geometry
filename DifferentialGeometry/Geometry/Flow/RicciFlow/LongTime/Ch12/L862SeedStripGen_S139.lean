import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862SeedsKL82_O42
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Glue_O12
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm

/-!
# CH12-S139 G1: `child_to_seedStrip866` on a general observed history

From the Good window of the selected child (a trace `X` of `y` on `[v - τ₁ r'², v]` with
`isTracedRegion w (X w) (κ r') (τ₂ r'²) (K r'⁻²)` at every `w` of it), its sectional bound and
its near-Euclidean volume at the top time `v`, produce the seed strip `[v - ℓ r'², v]`
(top = `v` exactly, `ℓ ≤ τ₁`) with seed radius `σ r'` and volume `w_* (σ r')³`.

Route (no new analysis): shrink to the radius `ρ₀ = μ r'` (`μ` depends on `ε,K,κ,τ₁,τ₂` only), so
that the Good window `[v - τ₁ r'², v]` and the traced regions of radius `κ r'`, depth `τ₂ r'²`
and bound `K r'⁻²` contain every hypothesis of `seeds_from_kl82_O42` (traces to the bottom
`a₀ = v - τ₀ ρ₀²`, `|Rm| ≤ K r'⁻²` hence `sec ≥ -(ρ₀²)⁻¹` on `B_w(X(w), ρ₀)`, bottom volume
`≥ w ρ₀³` from the top near-Euclid clause); the KL82.1 seed lemma then gives the normalised
parabolic seed and the volume `c₁ (α ρ₀)³` at every `w ∈ [v - c ρ₀², v]`, i.e. the volume
transfer along time.  Constants: `σ = α μ`, `ℓ = c μ²`, `w_* = c₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- The constants of the seed strip: `μ` depends on `ε,K,κ,τ₁,τ₂` (through `τ₀, α` of KL82.1 at
`w = (1-ε) ω₃`) only. -/
theorem seedStrip_gen_S139 (ε K κ τ₁ τ₂ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hK : 0 < K)
    (hκ : 0 < κ) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    ∃ σ ℓ wst : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < ℓ ∧ ℓ ≤ τ₁ ∧ 0 < wst ∧
      ∀ (N : ObservedHistory.{u}) {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      ∀ (v : Icc (0 : ℝ) N.horizon),
        (∀ v' : Icc (0 : ℝ) N.horizon, v' ≤ v → ∀ x,
          curvatureOperatorLowerBoundAt (N.stageMetric (N.activeStage v') v') x
            (metricAlgebraicCurvatureTensorAt (N.stageMetric (N.activeStage v') v') x)
            (Phi (metricScalarAt (N.stageMetric (N.activeStage v') v') x))) →
        ∀ (y : (N.stageAt v).Carrier) (r' : ℝ), 0 < r' →
        (∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v) y r',
          SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r' ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v) y r',
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage v) v) z ρ) →
        (∃ (a : Icc (0 : ℝ) N.horizon) (hav : a ≤ v)
          (X : BackwardPointTrace N (N.activeStage a) (N.activeStage v) (N.activeStage_mono hav) y),
          (a : ℝ) = v - τ₁ * r' ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a ≤ w) (hwv : w ≤ v),
            N.isTracedRegion w
              (X.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv))
              (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹)) →
        ∃ (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ v)
          (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage v) (N.activeStage_mono ha') y),
          (a' : ℝ) = v - ℓ * r' ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwv : w ≤ v),
            hasSmallParabolicCurvature N w
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv))
              (σ * r') ∧
            ENNReal.ofReal (wst * (σ * r') ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage w) w)
                (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv))
                (σ * r') := by
  have hω : 0 < euclideanUnitBallVolume 3 := euclideanUnitBallVolume_pos 3
  have hw : 0 < (1 - ε) * euclideanUnitBallVolume 3 := mul_pos (by linarith) hω
  obtain ⟨τ₀, α, c, c₁, hτ₀, hτ₀1, hα, hc, hcτ, hc₁, hseed⟩ := seeds_from_kl82_O42.{u} hw
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = min κ (min 1 (min (1 / α) (min (τ₁ / τ₀)
      (min (τ₂ / τ₀) (1 / K))))) := ⟨_, rfl⟩
  have hμpos : 0 < μ := by
    rw [hμdef]
    exact lt_min hκ (lt_min one_pos (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))))
  have hμκ : μ ≤ κ := by rw [hμdef]; exact min_le_left _ _
  have hμ1 : μ ≤ 1 := by rw [hμdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hμα : μ ≤ 1 / α := by
    rw [hμdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμτ₁ : μ ≤ τ₁ / τ₀ := by
    rw [hμdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hμτ₂ : μ ≤ τ₂ / τ₀ := by
    rw [hμdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hμK : μ ≤ 1 / K := by
    rw [hμdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  -- arithmetic of the constants
  have hμ2 : μ ^ 2 ≤ μ := by nlinarith
  have hτ₀μ₁ : τ₀ * μ ^ 2 ≤ τ₁ := by
    have h1 : τ₀ * μ ≤ τ₁ := by
      have := mul_le_mul_of_nonneg_left hμτ₁ hτ₀.le
      rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hμ2 hτ₀.le]
  have hτ₀μ₂ : τ₀ * μ ^ 2 ≤ τ₂ := by
    have h1 : τ₀ * μ ≤ τ₂ := by
      have := mul_le_mul_of_nonneg_left hμτ₂ hτ₀.le
      rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hμ2 hτ₀.le]
  have hKμ : K * μ ^ 2 ≤ 1 := by
    have h1 : K * μ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hμK hK.le
      rwa [mul_one_div_cancel hK.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left hμ2 hK.le]
  have hσ1 : α * μ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hμα hα.le
    rwa [mul_one_div_cancel hα.ne'] at this
  refine ⟨α * μ, c * μ ^ 2, c₁, mul_pos hα hμpos, hσ1, mul_pos hc (by positivity),
    ?_, hc₁, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hcτ (sq_nonneg μ)).trans hτ₀μ₁
  intro N Phi hPhi v hpin y r' hr' hsec hvol hgood
  obtain ⟨a, hav, X, haeq, hG⟩ := hgood
  have hρ0 : 0 < μ * r' := mul_pos hμpos hr'
  have hr2 : 0 < r' ^ 2 := by positivity
  have hρ0r' : μ * r' ≤ r' := mul_le_of_le_one_left hr'.le hμ1
  have hρ0κ : μ * r' ≤ κ * r' := mul_le_mul_of_nonneg_right hμκ hr'.le
  -- the depth `τ₀ ρ₀²` of the KL82.1 window, inside the Good window and inside the traced depth
  have hd1 : τ₀ * (μ * r') ^ 2 ≤ τ₁ * r' ^ 2 := by
    have e : τ₀ * (μ * r') ^ 2 = (τ₀ * μ ^ 2) * r' ^ 2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hτ₀μ₁ hr2.le
  have hd2 : τ₀ * (μ * r') ^ 2 ≤ τ₂ * r' ^ 2 := by
    have e : τ₀ * (μ * r') ^ 2 = (τ₀ * μ ^ 2) * r' ^ 2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hτ₀μ₂ hr2.le
  have hd0 : 0 ≤ τ₀ * (μ * r') ^ 2 := by positivity
  let a₀ : Icc (0 : ℝ) N.horizon :=
    ⟨(v : ℝ) - τ₀ * (μ * r') ^ 2, by have := a.2.1; rw [haeq] at this; linarith,
      by have := v.2.2; linarith⟩
  have haa₀ : a ≤ a₀ := by
    change (a : ℝ) ≤ (v : ℝ) - τ₀ * (μ * r') ^ 2
    rw [haeq]; linarith
  have ha₀v : a₀ ≤ v := by
    change (v : ℝ) - τ₀ * (μ * r') ^ 2 ≤ v
    linarith
  let X₀ := X.restrictFirst (N.activeStage_mono haa₀) (N.activeStage_mono ha₀v)
  -- Good at a time `w` of `[a₀, v]`: every point of `B_w(X(w), ρ₀)` traces to `a₀` with `Rm ≤ K r'⁻²`
  have hG' : ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a₀ ≤ w) (hwv : w ≤ v),
      ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage w) w)
          (X₀.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv)) (μ * r'),
        ∃ A : BackwardPointTrace N (N.activeStage a₀) (N.activeStage w) (N.activeStage_mono haw) q,
          A.isRmBoundedBy (hat := haw) (K * (r' ^ 2)⁻¹) := by
    intro w haw hwv q hq
    have haw' : a ≤ w := haa₀.trans haw
    obtain ⟨-, -, b, hbw, hbeq, htr⟩ := hG w haw' hwv
    obtain ⟨A, hA⟩ := htr q (riemannianBallOf_mono _ _ hρ0κ hq)
    have hba₀ : b ≤ a₀ := by
      change (b : ℝ) ≤ (v : ℝ) - τ₀ * (μ * r') ^ 2
      have : (w : ℝ) ≤ v := hwv
      rw [hbeq]; linarith
    exact ⟨A.restrictFirst (N.activeStage_mono hba₀) (N.activeStage_mono haw),
      hA.restrictFirst A hba₀ haw⟩
  -- `sec ≥ -(ρ₀²)⁻¹` on `B_w(X(w), ρ₀)` from the Rm bound of the trace
  have hsec' : ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a₀ ≤ w) (hwv : w ≤ v),
      ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage w) w)
          (X₀.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv)) (μ * r'),
        SectionalBoundedBelowAt (N.stageMetric (N.activeStage w) w) q (-((μ * r') ^ 2)⁻¹) := by
    intro w haw hwv q hq
    have haw' : a ≤ w := haa₀.trans haw
    obtain ⟨-, -, b, hbw, hbeq, htr⟩ := hG w haw' hwv
    obtain ⟨A, hA⟩ := htr q (riemannianBallOf_mono _ _ hρ0κ hq)
    have h1 := hA.1 w hbw le_rfl
    have h2 : A.point (N.activeStage w) (N.activeStage_mono hbw) (N.activeStage_mono le_rfl)
        = q := A.endpoint_eq
    rw [h2] at h1
    have hKr : 0 ≤ K * (r' ^ 2)⁻¹ := by positivity
    have h3 : Real.sqrt (normSq0S (N.stageMetric (N.activeStage w) w) q 4
        (metricRm04At (N.stageMetric (N.activeStage w) w) q)) ≤ K * (r' ^ 2)⁻¹ :=
      Real.sqrt_le_iff.mpr ⟨hKr, h1⟩
    have h4 := sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le
      (N.stageMetric (N.activeStage w) w) q h3
    refine h4.mono (neg_le_neg ?_)
    have e : ((μ * r') ^ 2)⁻¹ = (K * (r' ^ 2)⁻¹) * (1 / (K * μ ^ 2)) := by
      field_simp
    rw [e]
    have hKμpos : 0 < K * μ ^ 2 := by positivity
    have : 1 ≤ 1 / (K * μ ^ 2) := by
      rw [le_div_iff₀ hKμpos]; linarith
    exact le_mul_of_one_le_right hKr this
  have hvol₀ : ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * (μ * r') ^ 3) ≤
      ballVolume (N.stageMetric (N.activeStage v) v) y (μ * r') :=
    hvol y (mem_ball_self_O12 _ y hr') (μ * r') hρ0 hρ0r'
  have hmain := hseed N v y (μ * r') (K * (r' ^ 2)⁻¹) a₀ ha₀v X₀ hPhi hpin hρ0 rfl
    (fun w haw hwv => hG' w haw hwv) (fun w haw hwv => hsec' w haw hwv) hvol₀
  -- the strip `[v - c μ² r'², v]` and its trace
  have hcμ : c * μ ^ 2 * r' ^ 2 ≤ τ₁ * r' ^ 2 :=
    mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hcτ (sq_nonneg μ)).trans hτ₀μ₁)
      hr2.le
  have hcd : c * (μ * r') ^ 2 ≤ τ₀ * (μ * r') ^ 2 :=
    mul_le_mul_of_nonneg_right hcτ (sq_nonneg _)
  have hcd0 : 0 ≤ c * μ ^ 2 * r' ^ 2 := by positivity
  let a' : Icc (0 : ℝ) N.horizon :=
    ⟨(v : ℝ) - c * μ ^ 2 * r' ^ 2, by have := a.2.1; rw [haeq] at this; linarith,
      by have := v.2.2; linarith⟩
  have haa' : a ≤ a' := by
    change (a : ℝ) ≤ (v : ℝ) - c * μ ^ 2 * r' ^ 2
    rw [haeq]; linarith
  have ha'v : a' ≤ v := by
    change (v : ℝ) - c * μ ^ 2 * r' ^ 2 ≤ v
    linarith
  have ha₀a' : a₀ ≤ a' := by
    change (v : ℝ) - τ₀ * (μ * r') ^ 2 ≤ (v : ℝ) - c * μ ^ 2 * r' ^ 2
    have e : c * μ ^ 2 * r' ^ 2 = c * (μ * r') ^ 2 := by ring
    rw [e]; linarith
  refine ⟨a', ha'v, X.restrictFirst (N.activeStage_mono haa') (N.activeStage_mono ha'v), rfl, ?_⟩
  intro w haw hwv
  have haw₀ : a₀ ≤ w := ha₀a'.trans haw
  have hwin : (v : ℝ) - c * (μ * r') ^ 2 ≤ w := by
    have e : c * μ ^ 2 * r' ^ 2 = c * (μ * r') ^ 2 := by ring
    have : (a' : ℝ) ≤ w := haw
    change (v : ℝ) - c * μ ^ 2 * r' ^ 2 ≤ w at this
    rw [e] at this; exact this
  obtain ⟨hs, hv⟩ := hmain w haw₀ hwv hwin
  have e1 : α * μ * r' = α * (μ * r') := mul_assoc α μ r'
  rw [e1]
  exact ⟨hs, hv⟩

end GC.LongTime.Ch12
