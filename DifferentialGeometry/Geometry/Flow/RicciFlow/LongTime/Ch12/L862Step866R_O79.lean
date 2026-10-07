import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Step866V3_O63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862DepthReachR_O77
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862GoodR_O79

/-!
# CH12-O79 G3b: `step866_v3_of_contracts_R_O79 : hSTEP866 v3` on the region contract (R6, V3-R⁺)

Statement = `[FROZEN] CH12-O79 G3` (`build-logs/ch12/scratch/FrozenO79G3.lean`): binders `hSeed`
(O63's, = `frozen_seedStrip_O57`), `hUR` (`frozen_UR_O77`), `hKL82R` (regional KL82 on `Reg_O77`
with one common `τ₈₂`: bottom volumes at every depth `≤ τ₈₂` and the `M_ε` corollary at depth
`τ₈₂/2`; producer O78 ∘ `regInput_of_reg_O77`); conclusion = hSTEP866 v3 (O63, verbatim).
Constant chain (D-R6-3; no `B → τ₆`, no `B → K₆` edge): `w := (1−ε)ω₃`, `(τ₈₂, M) := hKL82R w`,
`θ := child_select_O57`, `D := τ₈₂/2`, `τ₆ := min (D/8) (log 2/(36 M))`,
`K₆ := max {200, 2M, 10/τ₁, 10/τ₂}`, `κ₆ := 1/40`, `(σ_c, ℓ_c, w_*) := hSeed ε K κ τ₁ τ₂`,
`(B, c, C₀, b₀, T₀) := hUR (σ_c θ) (ℓ_c θ²) w_*`, `C₆ := C₀`, `Λ₆ := τ₁ + τ₂ + 2`,
`b₆ := min b₀ ½`, `T₆ := T₀`.
The `[FROZEN] CH12-O79 G3` binder `hdepth` (`frozen_depthReachR_O77`) is discharged by O77's
`depth_reach_R_O77` (delivered).
Route: `depth_reach_R_O77` (O63 skeleton on `Reg_O77`, `hExt` = KL83.1 selection + Child IH + `hSeed` +
`hUR`, exactly as O63) reaches the fixed depth `D`; `hKL82R` improves the region
`[u − D r²/2, u] × B(X v, r/4)` to `|Rm| ≤ M r⁻²`; the outgoing `r`-ball inclusion of
`RegEvent_O77` is the event barrier; `good_of_improved_R_O79` (S130 at scale `r/80`) gives `Good`.
The O42 `σ_f`-tail of O63 is retired (review R6 §4.3–4.5).
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

/-- **G3b** (`[FROZEN] CH12-O79 G3`): Sublemma 86.6 (hSTEP866 v3) on the region contract. -/
theorem step866_v3_of_contracts_R_O79 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hSeed : ∀ ε K κ τ₁ τ₂ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < K → 0 < κ → 0 < τ₁ → 0 < τ₂ →
      ∃ σ ℓ wst : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < ℓ ∧ ℓ ≤ τ₁ ∧ 0 < wst ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (v : Icc (0 : ℝ) N.horizon) (y : (N.stageAt v).Carrier) (r' : ℝ), 0 < r' →
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
                (σ * r'))
    (hUR : ∀ σ ℓ wst : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst →
      ∃ B c C₀ b₀ T₀ : ℝ, 0 < B ∧ 0 < c ∧ c ≤ ℓ ∧ 1 ≤ C₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₀ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (x : (N.stageAt u).Carrier) (r : ℝ), 0 < r → r ≤ b₀ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon) (hau : a ≤ u)
        (X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x),
        (u : ℝ) - r ^ 2 ≤ a →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((a : ℝ) - c * r ^ 2) a →
          ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r) →
        Reg_O77 N hau X r →
        ∀ y : (N.stageAt a).Carrier,
        y ∈ riemannianBallOf (N.stageMetric (N.activeStage a) a)
            (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau)) (r / 2) →
        (∃ (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
          (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
          (a' : ℝ) = a - ℓ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
            hasSmallParabolicCurvature N w
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r) ∧
            ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage w) w)
                (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
                (σ * r)) →
        ∃ (ae : Icc (0 : ℝ) N.horizon) (haa : ae ≤ a)
          (Z : BackwardPointTrace N (N.activeStage ae) (N.activeStage a) (N.activeStage_mono haa)
            (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau))),
          (ae : ℝ) = a - c * r ^ 2 ∧
          Reg_O77 N (haa.trans hau) (X.concat Z) r ∧
          ∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hva : v ≤ a),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono (hva.trans hau))) r,
              metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ B / r ^ 2)
    (hKL82R : ∀ w : ℝ, 0 < w → ∃ τ₈₂ M : ℝ, 0 < τ₈₂ ∧ τ₈₂ ≤ 1 ∧ 0 < M ∧
      (∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
          (r0 τ : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
            (H.activeStage_mono hat) x0),
          0 < r0 → 0 < τ → τ ≤ τ₈₂ → (a : ℝ) = top - τ * r0 ^ 2 →
          Reg_O77 H hat X r0 →
          ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
          ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
            ballVolume (H.stageMetric (H.activeStage a) a)
              (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4)) ∧
      (∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
          (r0 : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
            (H.activeStage_mono hat) x0),
          0 < r0 → (a : ℝ) = top - τ₈₂ / 2 * r0 ^ 2 →
          Reg_O77 H hat X r0 →
          ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
            (top : ℝ) - τ₈₂ / 2 * r0 ^ 2 / 2 ≤ v →
            ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
                (r0 / 4),
              Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
                  (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ M / r0 ^ 2)) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ θ τ₆ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < τ₆ ∧
      ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₆ → 0 < τ₂ → τ₂ ≤ τ₆ →
      ∃ K₆ : ℝ, 0 < K₆ ∧ ∀ K : ℝ, K₆ ≤ K →
      ∃ κ₆ : ℝ, 0 < κ₆ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₆ →
      ∃ C₆ Λ₆ : ℝ, 1 ≤ C₆ ∧ τ₁ + τ₂ ≤ Λ₆ ∧ ∀ C : ℝ, C₆ ≤ C → ∀ Λ : ℝ, Λ₆ ≤ Λ →
      ∃ b₆ : ℝ, 0 < b₆ ∧ ∀ b : ℝ, 0 < b → b ≤ b₆ →
      ∃ T₆ : ℝ, ∀ T : ℝ, T₆ ≤ T →
     (∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), T ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
        (0 < (u : ℝ) ∧ (u : ℝ) ∉ F.observation.eventTimes) →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) (r : ℝ), 0 < r → Hp.parameters.neckRadius (u : ℝ) < r →
        r ≤ b * Real.sqrt u →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u →
          ∀ h, C * (Hp.records m i).nominalRadius h ≤ r) →
        (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) q (-(r ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x r,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
          (y : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r' : ℝ), v ≤ u →
          (u : ℝ) - Λ * r ^ 2 ≤ v - Λ * r' ^ 2 → θ * Hp.parameters.neckRadius (u : ℝ) ≤ r' →
          r' ≤ θ * r → (0 < (v : ℝ) ∧ (v : ℝ) ∉ F.observation.eventTimes) → r' ≤ b * Real.sqrt v →
          (∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) q (-(r' ^ 2)⁻¹)) →
          (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) y r',
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
              ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
                ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage v) v) z ρ) →
          (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ v)
            (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
              ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hau) y),
            (a : ℝ) = v - τ₁ * r' ^ 2 ∧
            ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ v),
              (sliceTowerHistory_CX2 s).isTracedRegion w
                (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                  ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
                (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹))) →
        (∃ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x),
          (a : ℝ) = u - τ₁ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a ≤ w) (hwu : w ≤ u),
            (sliceTowerHistory_CX2 s).isTracedRegion w
              (X.point ((sliceTowerHistory_CX2 s).activeStage w) ((sliceTowerHistory_CX2 s).activeStage_mono haw)
                ((sliceTowerHistory_CX2 s).activeStage_mono hwu))
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) := by
  intro ε hε hε2
  have hω : 0 < euclideanUnitBallVolume 3 := euclideanUnitBallVolume_pos 3
  have hw : 0 < (1 - ε) * euclideanUnitBallVolume 3 := mul_pos (by linarith) hω
  obtain ⟨τ₈₂, M, hτ₈₂, hτ₈₂1, hM, hvolR, himpR⟩ := hKL82R _ hw
  obtain ⟨θ, hθ, hθ4, hsel⟩ := child_select_O57.{u} hw hε
  obtain ⟨Phi, hPhi, hpinch⟩ := pinching_prefix_O37 Hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hθ2 : θ ^ 2 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hθ.le hθ4 2
    norm_num at this ⊢
    linarith
  refine ⟨θ, min (τ₈₂ / 2 / 8) (Real.log 2 / (36 * M)), hθ, by linarith,
    lt_min (by positivity) (by positivity), ?_⟩
  intro τ₁ τ₂ hτ₁ hτ₁6 hτ₂ hτ₂6
  obtain ⟨hτ₁D, -⟩ := le_min_iff.mp hτ₁6
  obtain ⟨hτ₂D, hτ₂M⟩ := le_min_iff.mp hτ₂6
  have hK6 : 0 < max (max 200 (2 * M)) (max (10 / τ₁) (10 / τ₂)) :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 200 (2 * M)).trans (le_max_left _ _))
  refine ⟨max (max 200 (2 * M)) (max (10 / τ₁) (10 / τ₂)), hK6, fun K hKK => ?_⟩
  have hK : 0 < K := lt_of_lt_of_le hK6 hKK
  have hMK : M ≤ K :=
    le_trans (by linarith) (((le_max_right 200 (2 * M)).trans (le_max_left _ _)).trans hKK)
  refine ⟨1 / 40, by norm_num, fun κ hκ hκb => ?_⟩
  obtain ⟨σc, ℓc, wst, hσc, hσc1, hℓc, hℓcτ, hwst, hSeed1⟩ :=
    hSeed ε K κ τ₁ τ₂ hε hε2 hK hκ hτ₁ hτ₂
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Bu, c, C₀, b₀, T₀, -, hc, hcℓ, hC₀, hb₀, -, hU1⟩ :=
    hUR (σc * θ) (ℓc * θ ^ 2) wst (mul_pos hσc hθ) ((mul_le_of_le_one_right hσc.le hθ1).trans hσc1)
      (by positivity) hwst
  have hcτ₁ : c ≤ τ₁ := hcℓ.trans
    ((mul_le_of_le_one_right hℓc.le (by nlinarith)).trans hℓcτ)
  refine ⟨C₀, τ₁ + τ₂ + 2, hC₀, by linarith, fun C hC Λ hΛ => ?_⟩
  refine ⟨min b₀ (1 / 2), lt_min hb₀ (by norm_num), fun b hb hb6 => ?_⟩
  obtain ⟨hba, hbb⟩ : b ≤ b₀ ∧ b ≤ 1 / 2 := le_min_iff.mp hb6
  refine ⟨T₀, fun T hT0 => ?_⟩
  intro s hTs u hTu hus hreg x r hr hneck hrb hguard hsec hvol hIH
  have hu0 : 0 ≤ (u : ℝ) := u.2.1
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2u : r ^ 2 ≤ (u : ℝ) / 4 := by
    have h1 : r ^ 2 ≤ (b * Real.sqrt u) ^ 2 := pow_le_pow_left₀ hr.le hrb 2
    rw [mul_pow, Real.sq_sqrt hu0] at h1
    have hb2 : b ^ 2 ≤ 1 / 4 := by
      have := pow_le_pow_left₀ hb.le hbb 2
      norm_num at this ⊢
      linarith
    have hb2u : b ^ 2 * u ≤ 1 / 4 * u := mul_le_mul_of_nonneg_right hb2 hu0
    linarith
  have hru : r ^ 2 < u := by linarith [hreg.1]
  have hΛ2 : 2 ≤ Λ := by linarith
  have hΛr : 2 * r ^ 2 ≤ Λ * r ^ 2 := mul_le_mul_of_nonneg_right hΛ2 hr2.le
  have hΛr0 : 0 ≤ Λ * r ^ 2 := by linarith
  have hfin : (F.observation.eventTimes ∩ Ioc 0 (u : ℝ)).Finite := by
    rw [F.observation.eventTimes_inter u hu0]
    exact ObservedHistory.eventTimes_finite _
  have hvolr := hvol x (mem_ball_self_O12 _ x hr) r hr le_rfl
  have hvol4 : ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * (r / 4) ^ 3 / 10) ≤
      ballVolume ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage u) u) x (r / 4) :=
    (ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ (1 - ε) * euclideanUnitBallVolume 3 * (r / 4) ^ 3 := by positivity
      linarith)).trans
      (hvol x (mem_ball_self_O12 _ x hr) (r / 4) (by positivity) (by linarith))
  -- depth reach on `Reg_O77` (τ' := τ₈₂) to the fixed depth `D := τ₈₂/2`
  obtain ⟨a, hau, X, ha, hReg⟩ :=
    @depth_reach_R_O77 ((1 - ε) * euclideanUnitBallVolume 3) τ₈₂ hτ₈₂ hτ₈₂1
      (fun H top x0 r0 τ a hat X _ _ _ hr0 hτ hττ ha hRegA hvt =>
        hvolR H top x0 r0 τ a hat X hr0 hτ hττ ha hRegA hvt)
      (sliceTowerHistory_CX2 s) F.observation.eventTimes Phi u hPhi
      (fun v hv => hpinch s v ((Subtype.coe_le_coe.mpr hv).trans hus)) hfin hreg.2 x r c hr hc hru
      hsec hvolr hvol4 (fun a hau X hrega hlow hRegA hvolb => by
        -- KL83.1 selection at the bottom, the Child IH, the seed strip and `(U-R)`
        obtain ⟨y, hy, hchild⟩ := hsel (sliceTowerHistory_CX2 s) a
          (X.point ((sliceTowerHistory_CX2 s).activeStage a) le_rfl
            ((sliceTowerHistory_CX2 s).activeStage_mono hau)) r hr (hRegA.1 a le_rfl hau) hvolb
        have hθr : 0 < θ * r := mul_pos hθ hr
        obtain ⟨hcs, hce⟩ := hchild (θ * r) hθr le_rfl
        have hwin : (u : ℝ) - Λ * r ^ 2 ≤ a - Λ * (θ * r) ^ 2 := by
          have h1 : Λ * r ^ 2 * θ ^ 2 ≤ Λ * r ^ 2 * (1 / 16) :=
            mul_le_mul_of_nonneg_left hθ2 hΛr0
          have e : Λ * (θ * r) ^ 2 = Λ * r ^ 2 * θ ^ 2 := by ring
          rw [e]
          linarith
        have hθu : θ * Real.sqrt u ≤ Real.sqrt a := by
          have e : Real.sqrt (θ ^ 2 * u) = θ * Real.sqrt u := by
            rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ.le]
          rw [← e]
          apply Real.sqrt_le_sqrt
          linarith [mul_le_mul_of_nonneg_right hθ2 hu0]
        have hbs : θ * r ≤ b * Real.sqrt a :=
          calc θ * r ≤ θ * (b * Real.sqrt u) := mul_le_mul_of_nonneg_left hrb hθ.le
            _ = b * (θ * Real.sqrt u) := by ring
            _ ≤ b * Real.sqrt a := mul_le_mul_of_nonneg_left hθu hb.le
        have hgood := hIH a y (θ * r) hau hwin (mul_le_mul_of_nonneg_left hneck.le hθ.le) le_rfl
          hrega hbs hcs hce
        obtain ⟨a', ha', Y, ha'eq, hY⟩ := hSeed1 s a y (θ * r) hθr hcs hce hgood
        have hcut : ∀ m (i : Fin (F.tower.history m).eventCount),
            (F.tower.history m).time i.succ ∈ Icc ((a : ℝ) - c * r ^ 2) a →
            ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r := by
          intro m i hi h
          have hcr : c * r ^ 2 ≤ τ₁ * r ^ 2 := mul_le_mul_of_nonneg_right hcτ₁ hr2.le
          have hau' : (a : ℝ) ≤ u := hau
          have hΛτ : (τ₁ + 1) * r ^ 2 ≤ Λ * r ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hr2.le
          have hi1 := hi.1
          have hi' : (F.tower.history m).time i.succ ∈ Icc ((u : ℝ) - Λ * r ^ 2) u :=
            ⟨by linarith, hi.2.trans hau'⟩
          have hn := (Hp.records m i).nominal_pos h
          have hg := hguard m i hi' h
          have hCn := mul_le_mul_of_nonneg_right hC hn.le
          linarith
        obtain ⟨ae, haa, Z, hae, hReg', -⟩ :=
          hU1 s u (hT0.trans hTu) hus x r hr
            (hrb.trans (mul_le_mul_of_nonneg_right hba (Real.sqrt_nonneg _))) a hau X hlow hcut
            hRegA y (riemannianBallOf_mono _ _ (by linarith) hy)
            ⟨a', ha', Y, by rw [ha'eq]; ring, fun w haw hwa => by
              rw [mul_assoc σc θ r]; exact hY w haw hwa⟩
        exact ⟨ae, haa, Z, hae, hReg'⟩) (τ₈₂ / 2) (by positivity) (by linarith)
  -- regional KL82: the improved region `[u − D r²/2, u] × B(X v, r/4)`
  have himp := himpR (sliceTowerHistory_CX2 s) u x r a hau X hr ha hReg hvolr
  have hDr : 0 ≤ τ₈₂ / 2 * r ^ 2 / 2 := by positivity
  have ha₁0 : (a : ℝ) ≤ (u : ℝ) - τ₈₂ / 2 * r ^ 2 / 2 := by rw [ha]; linarith
  let a₁ : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨(u : ℝ) - τ₈₂ / 2 * r ^ 2 / 2, a.2.1.trans ha₁0, (sub_le_self _ hDr).trans u.2.2⟩
  have haa₁ : a ≤ a₁ := ha₁0
  have ha₁u : a₁ ≤ u := show (u : ℝ) - τ₈₂ / 2 * r ^ 2 / 2 ≤ u from sub_le_self _ hDr
  have hlog : 36 * M * τ₂ ≤ Real.log 2 := by
    have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 36 * M)).mp hτ₂M
    linarith
  have hwin1 : (a₁ : ℝ) + (τ₁ + τ₂) * r ^ 2 ≤ u := by
    have h1 : τ₁ * r ^ 2 ≤ τ₈₂ / 2 / 8 * r ^ 2 := mul_le_mul_of_nonneg_right hτ₁D hr2.le
    have h2 : τ₂ * r ^ 2 ≤ τ₈₂ / 2 / 8 * r ^ 2 := mul_le_mul_of_nonneg_right hτ₂D hr2.le
    have h3 : 0 ≤ τ₈₂ * r ^ 2 := by positivity
    change (u : ℝ) - τ₈₂ / 2 * r ^ 2 / 2 + (τ₁ + τ₂) * r ^ 2 ≤ u
    nlinarith
  exact good_of_improved_R_O79 (sliceTowerHistory_CX2 s) ha₁u
    (X.restrictFirst ((sliceTowerHistory_CX2 s).activeStage_mono haa₁)
      ((sliceTowerHistory_CX2 s).activeStage_mono ha₁u))
    hr hM hτ₁ hτ₂ hlog hwin1 hκ hκb hMK
    (fun v hav hvu q hq => himp v (haa₁.trans hav) hvu hav q hq)
    (fun i hf hl => by
      obtain ⟨_, _, hball, _⟩ := hReg.2.2 i
        (((sliceTowerHistory_CX2 s).activeStage_mono haa₁).trans hf) hl
      exact (riemannianBallOf_mono _ _ (by linarith) ).trans hball)

end GC.LongTime.Ch12
