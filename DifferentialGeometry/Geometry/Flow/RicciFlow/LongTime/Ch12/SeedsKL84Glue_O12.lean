import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84GlueTrace_O12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.W2Assembly_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83Core_CX7

/-!
# CH12-O12: KL84.2 ⇒ `hG2` (G2d glue)

`hG2_of_kl82_O12 Hp hdec hKL82 hG2c` produces the hypothesis `hG2` of `W2_of_G2_CX2`
(W2Assembly_CX2.lean l.24–49) verbatim from
* `hKL82`: the Lean rendering of the frozen `kl82_1_O9` (KL Lemma 82.1), see
  `[FROZEN] CH12-O12` in DELIVERIES;
* `hG2c`: the frozen G2c (KL Lemma 86.2 + Prop 86.1 in traced-family form);
* G1 = KL83.1 (`almost_euclidean_subball_CX7`, proved) and the Bishop–Gromov
  scale-down `seed_scale_down_S21` (proved).

Construction: `y` = centre of a (1-ε)-Euclidean subball `B(y, θ r) ⊆ B(p, r)` (G1);
`r0 = θ r`; G2c gives a traced family `X` on `[t - τ₁ r0², t]`; `yv := X(v)`;
small parabolic curvature at radius `σκθ r` from the traced region at `v`; volume at
`v < t` from KL82.1(2) applied with top `t`, initial time `v`, radius `r1 = κ r0`
(hypotheses from the restricted traced family), followed by Bishop–Gromov scale-down;
at `v = t` directly from G1; the backward trace is `X.restrictFirst`.

Source: Kleiner–Lott, G&T 12 (2008), Lemma 82.1, Lemma 83.1, Prop 84.2/86.1,
Lemma 86.2 (as recorded in DELIVERIES [RESULT] CH12-O6; the book itself is not on this
machine).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem le_inv_of_mul_le_one_O12 {x y : ℝ} (hy : 0 < y) (h : x * y ≤ 1) : x ≤ y⁻¹ := by
  calc x = x * y * y⁻¹ := by field_simp
    _ ≤ 1 * y⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hy.le)
    _ = y⁻¹ := one_mul _

theorem mem_ball_self_O12 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ riemannianBallOf g p r := by
  change riemannianEDistOf g p p < ENNReal.ofReal r
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr hr

/-- KL84.2 in the exact `hG2` shape of `W2_of_G2_CX2`, from KL82.1 (`hKL82`, frozen
O9/O12 shape) and KL Lemma 86.2 in traced-family form (`hG2c`, frozen O9/O12 shape). -/
theorem hG2_of_kl82_O12 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hKL82 : ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ 0 < K₀ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0),
        0 < r0 → 0 < τ → τ ≤ τ₀ → (a : ℝ) = top - τ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            (∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) ∧
              SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (r0 / 2),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K₀ * τ⁻¹ * (r0 ^ 2)⁻¹) ∧
        ENNReal.ofReal (euclideanUnitBallVolume 3 * (r0 / 2) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 2))
    (hG2c : ∃ ε C₁ K τ₁ τ₂ b T : ℝ, 0 < ε ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧ 0 < b ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (r0 / 8) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹)) :
    ∀ w : ℝ, 0 < w → ∃ a c c₁ Λ₀ b₀ T₀ : ℝ,
      0 < a ∧ 2 * a ^ 2 < c ∧ 0 < c₁ ∧ 1 ≤ Λ₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, T₀ ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b₀ * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume
          (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ₀ * (Hp.records n i).nominalRadius h ≤ r) →
        ∃ y ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          ∀ v : Icc (0 : ℝ) s.history.horizon, s.time - c * r ^ 2 ≤ v.val →
          ∃ yv : (s.history.stageAt v).Carrier,
            (v.val = s.time → HEq yv y) ∧
            hasSmallParabolicCurvature s.history v yv (a * r) ∧
            ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
            ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
                (s.history.activeStage (sliceTop_S8 s))
                (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) y,
              A.point (s.history.activeStage v) le_rfl
                (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv := by
  intro w hw
  obtain ⟨ε, C₁, K, τ₁, τ₂, b, T, hε, hC₁, hK, hτ₁, hτ₂, hb, hT, hc⟩ := hG2c
  have hω : 0 < euclideanUnitBallVolume 3 := euclideanUnitBallVolume_pos 3
  set ϖ := euclideanUnitBallVolume 3 with hϖdef
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'half : ε' ≤ 1 / 2 := min_le_right _ _
  have hhalf : ϖ / 2 ≤ (1 - ε') * ϖ := by
    have h1 := mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ 1 - ε') hω.le
    linarith
  obtain ⟨θ₀, hθ₀, hG1⟩ := almost_euclidean_subball_CX7.{u} w hw ε' hε'pos
  set θ : ℝ := min θ₀ 1 with hθdef
  have hθ : 0 < θ := lt_min hθ₀ one_pos
  have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
  have hθ1 : θ ≤ 1 := min_le_right _ _
  obtain ⟨τ₀, K₀, hτ₀, _, hkl⟩ := hKL82 (ϖ / 2) (by positivity)
  obtain ⟨csd, hcsd, hsd⟩ := seed_scale_down_S21.{u}
  set κ : ℝ := min (1 / 8) (min τ₂ (1 / (K + 1))) with hκdef
  have hκ : 0 < κ := lt_min (by norm_num) (lt_min hτ₂ (by positivity))
  have hκ8 : κ ≤ 1 / 8 := min_le_left _ _
  have hκτ₂ : κ ≤ τ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hκK1 : κ ≤ 1 / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hκK : κ * K ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right hκK1 (by linarith : (0 : ℝ) ≤ K + 1)
    rw [one_div, inv_mul_cancel₀ (by linarith : (K + 1) ≠ 0)] at h1
    have h2 := mul_le_mul_of_nonneg_left (by linarith : K ≤ K + 1) hκ.le
    linarith
  have hκ1 : κ ≤ 1 := by linarith
  have hκ2K : κ ^ 2 * K ≤ 1 := by
    calc κ ^ 2 * K = κ * (κ * K) := by ring
      _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hκK hκ.le
      _ ≤ 1 := by linarith
  have hκ2τ : κ ^ 2 ≤ τ₂ := by
    calc κ ^ 2 = κ * κ := sq κ
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hκ1 hκ.le
      _ ≤ τ₂ := by linarith
  have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le hκ1
  set m : ℝ := min τ₀ (min τ₁ τ₂) with hmdef
  have hm : 0 < m := lt_min hτ₀ (lt_min hτ₁ hτ₂)
  have hmτ₀ : m ≤ τ₀ := min_le_left _ _
  have hmτ₁ : m ≤ τ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hmτ₂ : m ≤ τ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hκm1 : κ ^ 2 * m ≤ τ₁ := by
    have := mul_le_mul_of_nonneg_right hκ2 hm.le
    linarith
  have hκm2 : κ ^ 2 * m ≤ τ₂ := by
    have := mul_le_mul_of_nonneg_right hκ2 hm.le
    linarith
  set σ : ℝ := min (1 / 2) (m / 4) with hσdef
  have hσ : 0 < σ := lt_min (by norm_num) (by positivity)
  have hσ2 : σ ≤ 1 / 2 := min_le_left _ _
  have hσm : σ ≤ m / 4 := min_le_right _ _
  have hσ2m : σ ^ 2 ≤ m / 8 := by
    calc σ ^ 2 = σ * σ := sq σ
      _ ≤ (1 / 2) * σ := mul_le_mul_of_nonneg_right hσ2 hσ.le
      _ ≤ m / 8 := by linarith
  have hσsq : σ ^ 2 ≤ 1 / 4 := by
    calc σ ^ 2 = σ * σ := sq σ
      _ ≤ (1 / 2) * (1 / 2) := mul_le_mul hσ2 hσ2 hσ.le (by norm_num)
      _ = 1 / 4 := by norm_num
  have hσκ : σ * κ ≤ 1 / 16 := by
    have := mul_le_mul hσ2 hκ8 hκ.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hσκτ : σ ^ 2 * κ ^ 2 ≤ τ₂ := by
    have := mul_le_mul_of_nonneg_right hσsq (sq_nonneg κ)
    linarith
  have h3σκK : 3 * σ ^ 2 * (κ ^ 2 * K) ≤ 1 := by
    have := mul_le_mul hσsq hκ2K (by positivity) (by norm_num)
    linarith
  set c₁ : ℝ := min (csd * (ϖ / 10)) (ϖ / 2) with hc₁def
  have hc₁ : 0 < c₁ := lt_min (by positivity) (by positivity)
  have hc₁sd : c₁ ≤ csd * (ϖ / 10) := min_le_left _ _
  have hc₁ϖ : c₁ ≤ (1 - ε') * ϖ := (min_le_right _ _).trans hhalf
  refine ⟨σ * κ * θ, (κ * θ) ^ 2 * m, c₁, C₁ / θ, b / θ, T, by positivity, ?_, hc₁,
    (one_le_div hθ).2 (hθ1.trans hC₁), by positivity, hT, ?_⟩
  · have hkt : 0 < (κ * θ) ^ 2 := by positivity
    have e : 2 * (σ * κ * θ) ^ 2 = 2 * σ ^ 2 * (κ * θ) ^ 2 := by ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_right hσ2m hkt.le, mul_pos hm hkt]
  intro s hs p r hr hrb hsec hvol hrec
  obtain ⟨y, hysub, hyvol⟩ := hG1 _
    (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r hr hsec hvol
  have hr0 : 0 < θ * r := mul_pos hθ hr
  have hθr : θ * r ≤ θ₀ * r := mul_le_mul_of_nonneg_right hθθ₀ hr.le
  have hr0r : θ * r ≤ r := (mul_le_mul_of_nonneg_right hθ1 hr.le).trans_eq (one_mul r)
  have hyB : y ∈ riemannianBallOf
      (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) y (θ₀ * r) :=
    mem_ball_self_O12 _ y (mul_pos hθ₀ hr)
  have hyp := hysub hyB
  obtain ⟨a, hat, X, haeq, hTF⟩ := hc s hs y (θ * r) hr0
    (by
      calc θ * r ≤ θ * (b / θ * Real.sqrt s.time) := mul_le_mul_of_nonneg_left hrb hθ.le
        _ = b * Real.sqrt s.time := by field_simp)
    (fun n i hi h => by
      have h1 := mul_le_mul_of_nonneg_left (hrec n i hi h) hθ.le
      calc C₁ * (Hp.records n i).nominalRadius h
          = θ * (C₁ / θ * (Hp.records n i).nominalRadius h) := by field_simp
        _ ≤ θ * r := h1)
    (fun q hq => (hsec q (hysub (riemannianBallOf_mono _ _ hθr hq))).mono (by
      have h1 : (r ^ 2)⁻¹ ≤ ((θ * r) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hr0.le hr0r 2)
      linarith))
    (fun z hz ρ hρ hρr => by
      refine (ENNReal.ofReal_le_ofReal ?_).trans
        (hyvol z (riemannianBallOf_mono _ _ hθr hz) ρ hρ (hρr.trans hθr))
      have h1 : 1 - ε ≤ 1 - ε' := by linarith
      have h3 : 0 ≤ ϖ * ρ ^ 3 := by positivity
      linarith [mul_le_mul_of_nonneg_right h1 h3])
  refine ⟨y, hyp, fun v hv => ?_⟩
  have hvt : v ≤ sliceTop_S8 s := v.property.2
  have hvR : (v : ℝ) ≤ s.time := v.property.2
  have hθr2 : 0 < (θ * r) ^ 2 := by positivity
  have ewin : (κ * θ) ^ 2 * m * r ^ 2 = (κ ^ 2 * m) * (θ * r) ^ 2 := by ring
  have hav : a ≤ v := by
    change (a : ℝ) ≤ v
    rw [haeq]
    linarith [mul_le_mul_of_nonneg_right hκm1 hθr2.le]
  have hTFv := hTF v hav hvt
  have hK0 : 0 ≤ K * ((θ * r) ^ 2)⁻¹ := by positivity
  refine ⟨X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
      (s.history.activeStage_mono hvt), ?_, ?_, ?_,
    X.restrictFirst (s.history.activeStage_mono hav) (s.history.activeStage_mono hvt), rfl⟩
  · intro hvt'
    have hveq : v = sliceTop_S8 s := Subtype.ext hvt'
    subst hveq
    exact heq_of_eq X.endpoint_eq
  · refine hasSmall_of_traced_S23 hTFv (by positivity) ?_ ?_ hK0 ?_
    · have := mul_le_mul_of_nonneg_right hσκ hr0.le
      linarith
    · calc (σ * κ * θ * r) ^ 2 = (σ ^ 2 * κ ^ 2) * (θ * r) ^ 2 := by ring
        _ ≤ τ₂ * (θ * r) ^ 2 := mul_le_mul_of_nonneg_right hσκτ hθr2.le
    · refine le_inv_of_mul_le_one_O12 (by positivity) ?_
      have e : K * ((θ * r) ^ 2)⁻¹ * (Real.sqrt 3 * (σ * κ * θ * r)) ^ 2 =
          3 * σ ^ 2 * (κ ^ 2 * K) := by
        rw [show (Real.sqrt 3 * (σ * κ * θ * r)) ^ 2 = 3 * (σ * κ * θ * r) ^ 2 by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]]
        field_simp
      rw [e]
      exact h3σκK
  · by_cases hvt' : (v : ℝ) = s.time
    · have hveq : v = sliceTop_S8 s := Subtype.ext hvt'
      subst hveq
      have he : X.point (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hav)
          (s.history.activeStage_mono hvt) = y := X.endpoint_eq
      rw [he]
      refine (ENNReal.ofReal_le_ofReal ?_).trans
        (hyvol y hyB (σ * κ * θ * r) (by positivity) ?_)
      · have h3 : 0 ≤ (σ * κ * θ * r) ^ 3 := by positivity
        linarith [mul_le_mul_of_nonneg_right hc₁ϖ h3]
      · have := mul_le_mul_of_nonneg_right hσκ hr0.le
        linarith
    · have hvlt : (v : ℝ) < s.time := lt_of_le_of_ne hvR hvt'
      have hr1 : 0 < κ * (θ * r) := by positivity
      have hr1sq : 0 < (κ * (θ * r)) ^ 2 := by positivity
      have hτpos : 0 < (s.time - v) / (κ * (θ * r)) ^ 2 := div_pos (by linarith) hr1sq
      have hτle : (s.time - v) / (κ * (θ * r)) ^ 2 ≤ τ₀ := by
        rw [div_le_iff₀ hr1sq]
        have e : (κ * θ) ^ 2 * m * r ^ 2 = m * (κ * (θ * r)) ^ 2 := by ring
        linarith [mul_le_mul_of_nonneg_right hmτ₀ hr1sq.le]
      have hKr1 : K * ((θ * r) ^ 2)⁻¹ ≤ ((κ * (θ * r)) ^ 2)⁻¹ := by
        refine le_inv_of_mul_le_one_O12 hr1sq ?_
        have e : K * ((θ * r) ^ 2)⁻¹ * (κ * (θ * r)) ^ 2 = κ ^ 2 * K := by
          field_simp
        rw [e]
        exact hκ2K
      have hr1le : κ * (θ * r) ≤ 1 / 8 * (θ * r) := mul_le_mul_of_nonneg_right hκ8 hr0.le
      have hr1ρ : κ * (θ * r) ≤ θ * r / 8 := by linarith
      have hwin : ((sliceTop_S8 s : Icc (0 : ℝ) s.history.horizon) : ℝ) - τ₂ * (θ * r) ^ 2 ≤ v := by
        change s.time - τ₂ * (θ * r) ^ 2 ≤ v
        linarith [mul_le_mul_of_nonneg_right hκm2 hθr2.le]
      have hinputs := kl82_inputs_of_traced_family_O12 (hat := hat) X hK0 hr1ρ hKr1 hTF v hav hvt hwin
      have htopvol : ENNReal.ofReal (ϖ / 2 * (κ * (θ * r)) ^ 3) ≤ ballVolume
          (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) y
          (κ * (θ * r)) := by
        refine (ENNReal.ofReal_le_ofReal ?_).trans
          (hyvol y hyB (κ * (θ * r)) hr1 (by linarith))
        have h3 : 0 ≤ (κ * (θ * r)) ^ 3 := by positivity
        linarith [mul_le_mul_of_nonneg_right hhalf h3]
      obtain ⟨_, hvolv⟩ := hkl s.history (sliceTop_S8 s) y (κ * (θ * r))
        ((s.time - v) / (κ * (θ * r)) ^ 2) (K * ((θ * r) ^ 2)⁻¹) v hvt
        (X.restrictFirst (s.history.activeStage_mono hav) (s.history.activeStage_mono hvt))
        hr1 hτpos hτle (by
          change (v : ℝ) = s.time - _
          field_simp
          ring) hinputs htopvol
      have hsecv : ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
          (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
            (s.history.activeStage_mono hvt)) (κ * (θ * r) / 2),
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage v) v) q
            (-((κ * (θ * r) / 2) ^ 2)⁻¹) := by
        intro q hq
        refine (sectional_of_traced_O12 hTFv hK0 q
          (riemannianBallOf_mono _ _ (by linarith) hq)).mono ?_
        have h1 : ((κ * (θ * r)) ^ 2)⁻¹ ≤ ((κ * (θ * r) / 2) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (by rw [div_pow]; linarith)
        linarith
      have har : σ * κ * θ * r ≤ κ * (θ * r) / 2 := by
        have := mul_le_mul_of_nonneg_right hσ2 hr1.le
        linarith
      obtain ⟨_, hvol'⟩ := hsd _ (s.history.stageMetric (s.history.activeStage v) v)
        (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
          (s.history.activeStage_mono hvt))
        (ϖ / 10) (κ * (θ * r) / 2) (σ * κ * θ * r) (by positivity) (by positivity)
        har hsecv (by
          rw [show ϖ / 10 * (κ * (θ * r) / 2) ^ 3 = ϖ * (κ * (θ * r) / 2) ^ 3 / 10 by ring]
          exact hvolv)
      refine (ENNReal.ofReal_le_ofReal ?_).trans hvol'
      have h3 : 0 ≤ (σ * κ * θ * r) ^ 3 := by positivity
      linarith [mul_le_mul_of_nonneg_right hc₁sd h3]

end GC.LongTime.Ch12
