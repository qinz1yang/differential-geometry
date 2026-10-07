import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862DepthReach_O63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862EnlargeKL82_O42
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862UnscathedRegion_S111
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862EnlargeTower_O37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Glue_O12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreA2Inputs_O45
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparison

/-!
# CH12-O63 G2: `hSTEP866 v3` from the two production contracts (`[FROZEN] CH12-O63`)

`step866_v3_of_contracts_O63 Hp hSeed hU : hSTEP866 v3` (`[FROZEN v3] CH12-O57`, text = hSTEP
binder of `hBS_O57`), with `hSeed` = `child_to_seedStrip866` and `hU` = `hUnscathed866`
(`[FROZEN] CH12-O57 G2`, binder types of `frozen_seedStrip_O57` / `frozen_hU_O57`, verbatim).
Inside the STEP: `depth_reach_O63` at `w := (1-ε)ω₃` with the extension step `hExt` built from
the bottom volume → `child_select_O57` (θ) → Child IH at `(a, y, θ r)` → `hSeed` (child radius
`θ r`) → `hU` (`σ := σ_c θ`, `ℓ := ℓ_c θ²`); final depth `τ₀ᴼ (σ_f r)²`, `σ_f := τ'/2`; then the
S111 tail (`enlarged_rm_kl82_O42` + `traced_region_S111`) on radius `σ_f r`.
Constants (v3 order): `τ₆ := min (c_O σ_f²/4) (σ_f²/(64(B_O+16)))`, `K₆ := B_O/σ_f²`,
`κ₆ := σ_f/4`, `C₆ := C₀`, `Λ₆ := τ₁+τ₂+2`, `b₆ := min b₀ (min (1/2) (ρ_O/2))`,
`T₆ := max T₀ (2 T_O)`.
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

/-- **G2** (`[FROZEN] CH12-O63`): Sublemma 86.6 in the v3 constant order from the two production
contracts of the hG2c leaf. -/
theorem step866_v3_of_contracts_O63 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hU : ∀ σ ℓ wst : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst →
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
        (∃ K' : ℝ, ∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
            ∃ A' : BackwardPointTrace N (N.activeStage a) (N.activeStage v)
                (N.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K') →
        (∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
            SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) →
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
          (∃ K'' : ℝ, ∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) r,
              ∃ A' : BackwardPointTrace N (N.activeStage ae) (N.activeStage v)
                  (N.activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K'') ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) r,
              SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hva : v ≤ a),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                (Z.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hva)) r,
              metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ B / r ^ 2)) :
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
  obtain ⟨τ', hτ', hτ'1, hreach⟩ := depth_reach_O63.{u} hw
  obtain ⟨θ, hθ, hθ4, hsel⟩ := child_select_O57.{u} hw hε
  obtain ⟨τ₀, c₀, T₁, ρ, B₀, hτ₀, hτ₀1, hc₀, hcτ, hT₁, hρ, hB₀, henl⟩ :=
    enlarged_rm_kl82_O42.{u} Hp 1 one_pos hw
  obtain ⟨Phi, hPhi, hpinch⟩ := pinching_prefix_O37 Hp
  have hσ : 0 < τ' / 2 := half_pos hτ'
  have hσ1 : τ' / 2 ≤ 1 := by linarith
  have hBp : 0 < B₀ + 16 := by linarith
  have hθ2 : θ ^ 2 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hθ.le hθ4 2
    norm_num at this ⊢
    linarith
  refine ⟨θ, min (c₀ * (τ' / 2) ^ 2 / 4) ((τ' / 2) ^ 2 / (64 * (B₀ + 16))), hθ, by linarith,
    lt_min (by positivity) (by positivity), ?_⟩
  intro τ₁ τ₂ hτ₁ hτ₁6 hτ₂ hτ₂6
  obtain ⟨hτ₁b, -⟩ := le_min_iff.mp hτ₁6
  obtain ⟨hτ₂b, hτ₂c⟩ := le_min_iff.mp hτ₂6
  refine ⟨B₀ / (τ' / 2) ^ 2, by positivity, fun K hKB => ?_⟩
  have hK : 0 < K := lt_of_lt_of_le (by positivity) hKB
  refine ⟨τ' / 2 / 4, by positivity, fun κ hκ hκb => ?_⟩
  obtain ⟨σc, ℓc, wst, hσc, hσc1, hℓc, hℓcτ, hwst, hSeed1⟩ :=
    hSeed ε K κ τ₁ τ₂ hε hε2 hK hκ hτ₁ hτ₂
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Bu, c, C₀, b₀, T₀, -, hc, hcℓ, hC₀, hb₀, -, hU1⟩ :=
    hU (σc * θ) (ℓc * θ ^ 2) wst (mul_pos hσc hθ) ((mul_le_of_le_one_right hσc.le hθ1).trans hσc1)
      (by positivity) hwst
  have hcτ₁ : c ≤ τ₁ := hcℓ.trans
    ((mul_le_of_le_one_right hℓc.le (by linarith)).trans hℓcτ)
  refine ⟨C₀, τ₁ + τ₂ + 2, hC₀, by linarith, fun C hC Λ hΛ => ?_⟩
  refine ⟨min b₀ (min (1 / 2) (ρ / 2)), lt_min hb₀ (lt_min (by norm_num) (by positivity)),
    fun b hb hb6 => ?_⟩
  obtain ⟨hba, hbb, hbc⟩ : b ≤ b₀ ∧ b ≤ 1 / 2 ∧ b ≤ ρ / 2 := by
    simp only [le_min_iff] at hb6
    exact ⟨hb6.1, hb6.2.1, hb6.2.2⟩
  refine ⟨max T₀ (2 * T₁), fun T hT => ?_⟩
  obtain ⟨hT0, hT1⟩ := max_le_iff.mp hT
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
  have hdf : τ₀ * (τ' / 2) ^ 2 < τ' := by
    have h1 : τ₀ * (τ' / 2) ^ 2 ≤ (τ' / 2) ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hτ₀1
    have h2 : (τ' / 2) ^ 2 ≤ τ' / 4 :=
      calc (τ' / 2) ^ 2 = τ' * τ' / 4 := by ring
        _ ≤ τ' * 1 / 4 := by gcongr
        _ = τ' / 4 := by ring
    linarith
  obtain ⟨a, hau, X, ha, ⟨K', hfam⟩, hsecF⟩ :=
    hreach (sliceTowerHistory_CX2 s) F.observation.eventTimes Phi u hPhi
      (fun v hv => hpinch s v ((Subtype.coe_le_coe.mpr hv).trans hus)) hfin hreg.2 x r c hr hc hru
      hsec hvolr hvol4 (fun a hau X hrega hlow hfamA hsecA hvolb => by
        -- KL83.1 selection at the bottom, the Child IH, the seed strip and the extension
        obtain ⟨y, hy, hchild⟩ := hsel (sliceTowerHistory_CX2 s) a
          (X.point ((sliceTowerHistory_CX2 s).activeStage a) le_rfl
            ((sliceTowerHistory_CX2 s).activeStage_mono hau)) r hr (hsecA a le_rfl hau) hvolb
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
        obtain ⟨ae, haa, Z, hae, hfam', hsec', -⟩ :=
          hU1 s u (hT0.trans hTu) hus x r hr
            (hrb.trans (mul_le_mul_of_nonneg_right hba (Real.sqrt_nonneg _))) a hau X hlow hcut
            hfamA hsecA y (riemannianBallOf_mono _ _ (by linarith) hy)
            ⟨a', ha', Y, by rw [ha'eq]; ring, fun w haw hwa => by
              rw [mul_assoc σc θ r]; exact hY w haw hwa⟩
        exact ⟨ae, haa, Z, hae, hfam', hsec'⟩) (τ₀ * (τ' / 2) ^ 2) (by positivity) hdf
  -- the S111 tail on the sub-family of radius `σ_f r`, `σ_f := τ'/2`
  have hσr : τ' / 2 * r ≤ r := mul_le_of_le_one_left hr.le hσ1
  have hr0 : 0 < τ' / 2 * r := mul_pos hσ hr
  have ha0 : (a : ℝ) = u - τ₀ * (τ' / 2 * r) ^ 2 := by rw [ha]; ring
  have hinv : -((τ' / 2 * r) ^ 2)⁻¹ ≤ -(r ^ 2)⁻¹ := by
    have h1 : (τ' / 2 * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr0.le hσr 2
    have h2 := inv_anti₀ (by positivity) h1
    linarith
  have hSF : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ u),
      ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
          (X.point ((sliceTowerHistory_CX2 s).activeStage v) ((sliceTowerHistory_CX2 s).activeStage_mono hav)
            ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) (τ' / 2 * r),
        ∃ A' : BackwardPointTrace (sliceTowerHistory_CX2 s) ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
            ((sliceTowerHistory_CX2 s).activeStage_mono hav) q, A'.isRmBoundedBy (hat := hav) K' :=
    fun v hav hvt q hq => hfam v hav hvt q (riemannianBallOf_mono _ _ hσr hq)
  have hsecU : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ u),
      ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
          (X.point ((sliceTowerHistory_CX2 s).activeStage v) ((sliceTowerHistory_CX2 s).activeStage_mono hav)
            ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) (τ' / 2 * r),
        SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q
          (-((τ' / 2 * r) ^ 2)⁻¹) :=
    fun v hav hvt q hq => sectionalBoundedBelowAt_mono_O45 _ _
      (hsecF v hav hvt q (riemannianBallOf_mono _ _ hσr hq)) hinv
  have hvol0 : ENNReal.ofReal (((1 - ε) * euclideanUnitBallVolume 3) * (τ' / 2 * r) ^ 3) ≤
      ballVolume ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u) x (τ' / 2 * r) :=
    hvol x (mem_ball_self_O12 _ x hr) (τ' / 2 * r) hr0 hσr
  have hrm : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ u),
      (u : ℝ) - c₀ * (τ' / 2 * r) ^ 2 ≤ v →
      ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
          (X.point ((sliceTowerHistory_CX2 s).activeStage v) ((sliceTowerHistory_CX2 s).activeStage_mono hav) ((sliceTowerHistory_CX2 s).activeStage_mono hvt))
          (20 * (1 * (τ' / 2 * r))),
        Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
          (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤
            B₀ / (τ' / 2 * r) ^ 2 := by
    intro v hav hvt hv q hq
    obtain ⟨hTv, hrv⟩ := window_S111 hu0 hr hσ hσ1 hcτ hτ₀1 hb hbb hbc hρ hrb hT₁ hT1 hTu
      v.2.1 hv
    exact henl s u hus a hau x X (τ' / 2 * r) K' hr0 ha0 hSF hsecU hvol0 v hav hvt hv hTv hrv q hq
  have h1 : τ₁ * r ^ 2 ≤ c₀ * (τ' / 2 * r) ^ 2 / 4 :=
    calc τ₁ * r ^ 2 ≤ c₀ * (τ' / 2) ^ 2 / 4 * r ^ 2 :=
          mul_le_mul_of_nonneg_right hτ₁b (sq_nonneg r)
      _ = c₀ * (τ' / 2 * r) ^ 2 / 4 := by ring
  have h2 : τ₂ * r ^ 2 ≤ c₀ * (τ' / 2 * r) ^ 2 / 4 :=
    calc τ₂ * r ^ 2 ≤ c₀ * (τ' / 2) ^ 2 / 4 * r ^ 2 :=
          mul_le_mul_of_nonneg_right hτ₂b (sq_nonneg r)
      _ = c₀ * (τ' / 2 * r) ^ 2 / 4 := by ring
  have hcX : c₀ * (τ' / 2 * r) ^ 2 ≤ τ₀ * (τ' / 2 * r) ^ 2 :=
    mul_le_mul_of_nonneg_right hcτ (sq_nonneg _)
  have hcX0 : 0 ≤ c₀ * (τ' / 2 * r) ^ 2 := by positivity
  have ha'ge : (a : ℝ) ≤ (u : ℝ) - τ₁ * r ^ 2 := by rw [ha0]; linarith
  let a' : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
    ⟨(u : ℝ) - τ₁ * r ^ 2, a.2.1.trans ha'ge, (sub_le_self _ (by positivity)).trans u.2.2⟩
  have haa' : a ≤ a' := ha'ge
  have ha'u : a' ≤ u := show (u : ℝ) - τ₁ * r ^ 2 ≤ u from sub_le_self _ (by positivity)
  refine ⟨a', ha'u, X.restrictFirst ((sliceTowerHistory_CX2 s).activeStage_mono haa') ((sliceTowerHistory_CX2 s).activeStage_mono ha'u),
    rfl, ?_⟩
  intro w haw hwu
  have hKb : B₀ / (τ' / 2 * r) ^ 2 ≤ K * (r ^ 2)⁻¹ := by
    have e : B₀ / (τ' / 2 * r) ^ 2 = B₀ / (τ' / 2) ^ 2 * (r ^ 2)⁻¹ := by
      rw [mul_pow]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hKB (by positivity)
  have hδs : τ₂ * r ^ 2 ≤ (τ' / 2 * r) ^ 2 / (64 * (B₀ + 16)) :=
    calc τ₂ * r ^ 2 ≤ (τ' / 2) ^ 2 / (64 * (B₀ + 16)) * r ^ 2 :=
          mul_le_mul_of_nonneg_right hτ₂c (sq_nonneg r)
      _ = (τ' / 2 * r) ^ 2 / (64 * (B₀ + 16)) := by rw [mul_pow]; ring
  have hac : (a : ℝ) ≤ (u : ℝ) - c₀ * (τ' / 2 * r) ^ 2 := by rw [ha0]; linarith
  have hwcond : (u : ℝ) - c₀ * (τ' / 2 * r) ^ 2 + τ₂ * r ^ 2 ≤ w := by
    have hw' : (a' : ℝ) ≤ w := haw
    have h3 : (a' : ℝ) = (u : ℝ) - τ₁ * r ^ 2 := rfl
    linarith
  have hκr4 : κ * r ≤ τ' / 2 * r / 4 :=
    calc κ * r ≤ τ' / 2 / 4 * r := mul_le_mul_of_nonneg_right hκb hr.le
      _ = τ' / 2 * r / 4 := by ring
  exact traced_region_S111 (sliceTowerHistory_CX2 s) hau X hr0 hB₀ (by positivity)
    (mul_pos hκ hr) hκr4 hδs hKb hac hSF hrm w (haa'.trans haw) hwu hwcond

end GC.LongTime.Ch12
