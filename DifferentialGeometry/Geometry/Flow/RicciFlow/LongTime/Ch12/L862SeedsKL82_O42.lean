import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862EnlargeTower_O37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimMain_O36

/-!
# CH12-O42 G1a: K-independent seeds from `kl82_1_O36`

`seeds_from_kl82_O42` builds the KL84.1(c) seed (`hasSmallParabolicCurvature` at scale `α r0`
plus a volume lower bound `c₁ (α r0)³`) directly from the hypotheses of `kl82_1_O36`.
The constants `τ₀ α c c₁` depend on `w` only: the a-priori trace bound `K` enters only the
trace hypothesis of `kl82_1_O36`, whose constants do not depend on it (lead ruling (1) of the
O42 brief; replaces `seeds_of_traced_family_CX12`, whose `α` depends on `K`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open GC.LongTime

namespace GC.LongTime.Ch12

universe u

/-- Arithmetic of the seed scale: `(α r)² ≤ r²/σ²` when `α σ = 1/8`. -/
private theorem seed_depth_O42 {α σ r : ℝ} (hσ : 0 < σ) (h : α * σ = 1 / 8) :
    (α * r) ^ 2 ≤ r ^ 2 / σ ^ 2 := by
  have e : (α * r) ^ 2 = (α * σ) ^ 2 * (r ^ 2 / σ ^ 2) := by field_simp
  have hX : 0 ≤ r ^ 2 / σ ^ 2 := by positivity
  rw [e, h]
  linarith only [hX]

/-- Arithmetic of the seed bound: `8√3 (σ/r)² ≤ ((√3 α r)²)⁻¹` when `α σ = 1/8`. -/
private theorem seed_bound_O42 {α σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (h : α * σ = 1 / 8) :
    8 * Real.sqrt 3 * (σ / r) ^ 2 ≤ ((Real.sqrt 3 * (α * r)) ^ 2)⁻¹ := by
  have e : (Real.sqrt 3 * (α * r)) ^ 2 = 3 * (α * σ) ^ 2 * (r / σ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; field_simp
  have e2 : (3 * (1 / 8 : ℝ) ^ 2 * (r / σ) ^ 2)⁻¹ = 64 / 3 * (σ / r) ^ 2 := by
    field_simp; ring
  rw [e, h, e2]
  have h3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  exact mul_le_mul_of_nonneg_right (by linarith only [h3]) (sq_nonneg _)

/-- KL84.1(c) seeds with constants depending on `w` only, from the premises of `kl82_1_O36`. -/
theorem seeds_from_kl82_O42 {w : ℝ} (hw : 0 < w) :
    ∃ τ₀ α c c₁ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < α ∧ 0 < c ∧ c ≤ τ₀ ∧ 0 < c₁ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
        Perelman.AdmissiblePinchingFunction Phi →
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
        0 < r0 → (a : ℝ) = top - τ₀ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - c * r0 ^ 2 ≤ v →
          hasSmallParabolicCurvature H v
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (α * r0) ∧
          ENNReal.ofReal (c₁ * (α * r0) ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (α * r0) := by
  obtain ⟨τ₀, K₀, hτ₀, hτ₀1, hK₀, hkl⟩ := kl82_1_O36.{u} w hw
  obtain ⟨csd, hcsd, hsd⟩ := seed_scale_down_S21.{u}
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = K₀ / τ₀ + 2 / τ₀ + 100 := ⟨_, rfl⟩
  have hKσ : K₀ / τ₀ ≤ σ := by have : 0 < 2 / τ₀ := by positivity
                               linarith
  have h2σ : 2 / τ₀ ≤ σ := by have : 0 < K₀ / τ₀ := by positivity
                              linarith
  have h100 : 100 ≤ σ := by have : 0 < K₀ / τ₀ := by positivity
                            have : 0 < 2 / τ₀ := by positivity
                            linarith
  have hσ : 0 < σ := by linarith
  have hσ1 : 1 ≤ σ := by linarith
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 / (8 * σ) := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; positivity
  have hασ : α * σ = 1 / 8 := by rw [hαdef]; field_simp
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = csd * (w / 10) := ⟨_, rfl⟩
  refine ⟨τ₀, α, τ₀ / 4, c₁, hτ₀, hτ₀1, hα, by positivity, by linarith, by rw [hc₁def]; positivity, ?_⟩
  intro H top x0 r0 K a hat X Phi hPhi hpin hr0 ha hSF hsec hvol v hav hvt hv
  have hr2 : 0 < r0 ^ 2 := by positivity
  have hαr : 0 < α * r0 := by positivity
  have hαr4 : α * r0 ≤ r0 / 4 := by
    have : α ≤ 1 / 4 := by
      rw [hαdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  -- the kl82 output on the full window `[a, top]`
  obtain ⟨hscal, -⟩ := hkl H top x0 r0 τ₀ K a hat X hPhi hpin hr0 hτ₀ le_rfl ha hSF hsec hvol
  constructor
  · -- hasSmall via `kl82_blowup_traced_O36` at `ts = v`, `Q = (σ / r0)²`, `T = 1`, `Aa = α σ`
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = (σ / r0) ^ 2 := ⟨_, rfl⟩
    have hσr : 0 < σ / r0 := by positivity
    have hQ : 0 < Q := by rw [hQdef]; positivity
    have hsQ : Real.sqrt Q = σ / r0 := by rw [hQdef]; exact Real.sqrt_sq hσr.le
    have hTQ : 1 / Q = r0 ^ 2 / σ ^ 2 := by rw [hQdef]; field_simp
    have hσ2 : r0 ^ 2 / σ ^ 2 ≤ τ₀ * r0 ^ 2 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 2 ≤ τ₀ * σ := by
        have := mul_le_mul_of_nonneg_left h2σ hτ₀.le
        rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
      have h2 : σ ≤ σ ^ 2 := by nlinarith
      have h3 : 2 * σ ≤ τ₀ * σ ^ 2 := by nlinarith
      nlinarith
    have hτr : 0 ≤ τ₀ * r0 ^ 2 := by positivity
    have has_mem : (v : ℝ) - r0 ^ 2 / σ ^ 2 ∈ Icc (0 : ℝ) H.horizon := by
      constructor
      · have := a.2.1
        linarith
      · have := v.2.2
        have : 0 ≤ r0 ^ 2 / σ ^ 2 := by positivity
        linarith
    obtain ⟨as, hasdef⟩ : ∃ as : Icc (0 : ℝ) H.horizon, (as : ℝ) = (v : ℝ) - r0 ^ 2 / σ ^ 2 :=
      ⟨⟨_, has_mem⟩, rfl⟩
    have has : a ≤ as := by
      change (a : ℝ) ≤ (as : ℝ)
      rw [hasdef]
      linarith
    have hasv : as ≤ v := by
      change (as : ℝ) ≤ v
      rw [hasdef]
      have : 0 ≤ r0 ^ 2 / σ ^ 2 := by positivity
      linarith
    have hκQ : (r0 ^ 2)⁻¹ ≤ Q := by
      rw [hQdef, div_pow, div_eq_mul_inv]
      have : (1 : ℝ) ≤ σ ^ 2 := by nlinarith
      nlinarith [inv_pos.mpr hr2]
    have hmarg : (0 : ℝ) + (α * σ + 16 * 1 + 1) / Real.sqrt Q < r0 / 4 := by
      rw [hsQ, hασ, zero_add, div_div_eq_mul_div, div_lt_div_iff₀ hσ (by norm_num)]
      linarith [mul_le_mul_of_nonneg_left h100 hr0.le]
    have hself : riemannianEDistOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono (has.trans hasv))
          (H.activeStage_mono hvt))
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          ENNReal.ofReal 0 := by
      rw [ENNReal.ofReal_zero]; exact (riemannianEDistOf_self _ _).le
    have hscal' : ∀ (v' : Icc (0 : ℝ) H.horizon) (hav' : as ≤ v') (hvt' : v' ≤ v),
        ∀ z : (H.stageAt v').Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage v') v')
            (X.point (H.activeStage v') (H.activeStage_mono (has.trans hav'))
              (H.activeStage_mono (hvt'.trans hvt))) z < ENNReal.ofReal (r0 / 4) →
          metricScalarAt (H.stageMetric (H.activeStage v') v') z ≤ 4 * Q := by
      have hQ' : Q = σ ^ 2 * (r0 ^ 2)⁻¹ := by rw [hQdef, div_pow, div_eq_mul_inv]
      have h1 : σ ≤ σ ^ 2 := by nlinarith only [hσ1]
      have hK : K₀ * τ₀⁻¹ ≤ 4 * σ ^ 2 := by
        calc K₀ * τ₀⁻¹ = K₀ / τ₀ := (div_eq_mul_inv _ _).symm
          _ ≤ 4 * σ ^ 2 := by linarith only [hKσ, h1, sq_nonneg σ]
      have hbd : K₀ * τ₀⁻¹ * (r0 ^ 2)⁻¹ ≤ 4 * Q := by
        rw [hQ']
        calc K₀ * τ₀⁻¹ * (r0 ^ 2)⁻¹ ≤ 4 * σ ^ 2 * (r0 ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr hr2.le)
          _ = 4 * (σ ^ 2 * (r0 ^ 2)⁻¹) := by ring
      intro v' hav' hvt' z hz
      have hlow : (top : ℝ) - 3 / 4 * τ₀ * r0 ^ 2 ≤ v' := by
        have : (as : ℝ) ≤ v' := hav'
        rw [hasdef] at this
        linarith only [this, hv, hσ2]
      exact (hscal v' (has.trans hav') (hvt'.trans hvt) hlow z hz).trans hbd
    obtain ⟨htr, -⟩ := kl82_blowup_traced_O36 H hat X hr0 hSF hsec has hasv hvt hQ hκQ one_pos
      (by positivity : 0 < α * σ) le_rfl
      (by rw [hTQ, hasdef]; ring) hself hmarg (by linarith) hscal'
    refine hasSmall_of_traced_S23 htr hαr ?_ ?_ (by positivity) ?_
    · rw [hsQ, div_div_eq_mul_div]
      exact le_of_eq (by field_simp)
    · rw [hTQ]; exact seed_depth_O42 hσ hασ
    · have hK0 := seed_bound_O42 (r := r0) hσ hr0 hασ
      rwa [← hQdef] at hK0
  · -- volume at `v`
    have hsecr : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (r0 / 4),
        SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-((r0 / 4) ^ 2)⁻¹) := by
      intro q hq
      refine (hsec v hav hvt q (riemannianBallOf_mono _ _ (by linarith only [hr0]) hq)).mono ?_
      have h16 : (r0 / 4) ^ 2 ≤ r0 ^ 2 := by
        rw [div_pow]; linarith only [hr2]
      exact neg_le_neg (inv_anti₀ (by positivity) h16)
    by_cases heq : v = top
    · subst heq
      have hsec0 : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v) x0 r0,
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹) := by
        have := hsec v hav hvt
        rwa [X.endpoint_eq] at this
      obtain ⟨-, hv'⟩ := hsd _ (H.stageMetric (H.activeStage v) v) x0 w r0 (α * r0) hw hαr
        (by linarith) hsec0 hvol
      rw [X.endpoint_eq]
      refine (ENNReal.ofReal_le_ofReal ?_).trans hv'
      rw [hc₁def]
      have : 0 < (α * r0) ^ 3 := by positivity
      linarith only [mul_pos (mul_pos hcsd hw) this]
    · have hlt : (v : ℝ) < top := lt_of_le_of_ne hvt (fun h => heq (Subtype.ext h))
      have hτpos : 0 < ((top : ℝ) - v) / r0 ^ 2 := div_pos (by linarith) hr2
      have hτle : ((top : ℝ) - v) / r0 ^ 2 ≤ τ₀ := by
        have hτr : 0 ≤ τ₀ * r0 ^ 2 := by positivity
        rw [div_le_iff₀ hr2]; linarith only [hv, hτr]
      obtain ⟨-, hvolv⟩ := hkl H top x0 r0 (((top : ℝ) - v) / r0 ^ 2) K v hvt
        (X.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)) hPhi hpin hr0
        hτpos hτle (by field_simp; ring)
        (fun v' hvv' hv't q hq => by
          obtain ⟨A, hA⟩ := hSF v' (hav.trans hvv') hv't q hq
          exact ⟨A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvv'),
            hA.restrictFirst A hav hvv'⟩)
        (fun v' hvv' hv't q hq => hsec v' (hav.trans hvv') hv't q hq) hvol
      obtain ⟨-, hv'⟩ := hsd _ (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
        (w / 10) (r0 / 4) (α * r0) (by positivity) hαr hαr4 hsecr (by
          rw [show w / 10 * (r0 / 4) ^ 3 = w * (r0 / 4) ^ 3 / 10 by ring]
          exact hvolv)
      rw [hc₁def]
      refine (ENNReal.ofReal_le_ofReal (le_of_eq ?_)).trans hv'
      ring

end GC.LongTime.Ch12
