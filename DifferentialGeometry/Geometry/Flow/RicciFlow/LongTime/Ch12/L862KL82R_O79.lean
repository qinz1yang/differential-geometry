import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HG2cR_O79
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82RegMain_O78
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862RegEvent_O77

/-!
# CH12-O79 G4: `hKL82R_O79` (producer of the `hKL82R` binder of `[FROZEN] CH12-O79 G3`) and the
closed hG2c leaf `hG2c_R_closed_O79`

`hKL82R_O79 : <hKL82R binder, verbatim>`: O78's `kl82_1_R_O78` at `w` gives ONE `τ₀ =: τ₈₂`
(`K₀ =: K₈₂`); (i) the bottom volume at every depth `τ ≤ τ₈₂` is its second conjunct after
`regInput_of_reg_O77` (Reg ⇒ O78's Reg-input: (Reg-ev r0), (Reg-fin K), (Reg-sec)); (ii) the `M_ε`
corollary at depth `τ₈₂/2` is O78's `kl82_improved_rm_R_O78` argument, redone here with the same
`τ₀` (that theorem's own `∃` hides the identification `τ₈₂ = τ₀`):
`R ≤ K₀ (τ₀/2)⁻¹ r0⁻²` on `[top − 3/8 τ₀ r0², top] ⊇ [top − τ₀ r0²/4, top]`, `sec ≥ −r0⁻²`,
`rm_normSq_le_of_sec_O30` ⇒ `|Rm| ≤ M r0⁻²`, `M := 2√3 (K₀/τ₀ + 2)`.
`step866_v3_R_O79 Hp hdec hprof : hSTEP866 v3` (no KL82 / U-R / depth binder) and
`hG2c_R_closed_O79 Hp hdec hP2 hprof := hG2c_R_O79 Hp hdec hP2 hprof hKL82R_O79` — the hG2c leaf
(A13-8) with only the `hG2c_v4_O69` inputs `hdec`, `hP2`, `hprof`.
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

/-- **G4a**: regional KL82 on `Reg_O77` with one common `τ₈₂` (bottom volumes + `M_ε` bound). -/
theorem hKL82R_O79 :
    ∀ w : ℝ, 0 < w → ∃ τ₈₂ M : ℝ, 0 < τ₈₂ ∧ τ₈₂ ≤ 1 ∧ 0 < M ∧
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
                  (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ M / r0 ^ 2) := by
  intro w hw
  obtain ⟨τ₀, K₀, hτ₀, hτ₀1, hK₀, hmain⟩ := kl82_1_R_O78.{u} w hw
  refine ⟨τ₀, 2 * Real.sqrt 3 * (K₀ / τ₀ + 2), hτ₀, hτ₀1, by positivity, ?_, ?_⟩
  · intro H top x0 r0 τ a hat X hr0 hτ hττ ha hReg hvol
    obtain ⟨hev, ⟨K, hfin⟩, hsec⟩ := regInput_of_reg_O77 H hat X hReg
    exact (hmain H top x0 r0 τ K a hat X hr0 hτ hττ ha (hev r0 le_rfl) hfin hsec hvol).2
  · intro H top x0 r0 a hat X hr0 ha hReg hvol v hav hvt hv q hq
    obtain ⟨hev, ⟨K, hfin⟩, hsec⟩ := regInput_of_reg_O77 H hat X hReg
    have hD : 0 < τ₀ / 2 := by positivity
    obtain ⟨h1, -⟩ := hmain H top x0 r0 (τ₀ / 2) K a hat X hr0 hD (by linarith) ha
      (hev r0 le_rfl) hfin hsec hvol
    have hp : 0 ≤ τ₀ * r0 ^ 2 := by positivity
    have hv' : (top : ℝ) - 3 / 4 * (τ₀ / 2) * r0 ^ 2 ≤ v := by nlinarith
    have hR := h1 v hav hvt hv' q hq
    have hqr0 : q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0 :=
      riemannianBallOf_mono _ _ (by linarith) hq
    have hRm := rm_normSq_le_of_sec_O30 _ q (κ := (r0 ^ 2)⁻¹)
      (Λ := K₀ * (τ₀ / 2)⁻¹ * (r0 ^ 2)⁻¹) (by positivity) (by positivity) (hsec v hav hvt q hqr0) hR
    have hc : 0 ≤ 2 * Real.sqrt 3 * (K₀ * (τ₀ / 2)⁻¹ * (r0 ^ 2)⁻¹ / 2 + 2 * (r0 ^ 2)⁻¹) := by
      positivity
    refine (Real.sqrt_le_sqrt hRm).trans (le_of_eq ?_)
    rw [Real.sqrt_sq hc]
    have hτ₀' : τ₀ ≠ 0 := hτ₀.ne'
    have hr0' : r0 ≠ 0 := hr0.ne'
    field_simp

/-- **G4b**: `hSTEP866 v3` on the region contract with NO KL82 / U-R / depth binder:
`step866_v3_of_contracts_R_O79 Hp (hSeed_S139 Hp) (hUR_O79 Hp hdec hprof) hKL82R_O79`. -/
theorem step866_v3_R_O79 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) :
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
              (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹))) :=
  step866_v3_of_contracts_R_O79 Hp (hSeed_S139 Hp) (hUR_O79 Hp hdec hprof) hKL82R_O79

/-- **G4c**: the closed hG2c leaf on the region contract. -/
theorem hG2c_R_closed_O79 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) :
    ∃ ε C₁ K τ₁ τ₂ κ₀ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      0 < κ₀ ∧ 0 < b ∧ (τ₁ + τ₂) * b ^ 2 ≤ 1 / 2 ∧ 0 < T ∧
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
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) :=
  hG2c_R_O79 Hp hdec hP2 hprof hKL82R_O79

end GC.LongTime.Ch12
