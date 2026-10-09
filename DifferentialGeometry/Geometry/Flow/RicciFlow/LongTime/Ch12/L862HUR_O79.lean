import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862StripR_O79
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HU_O69
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862RegEvent_O77

/-!
# CH12-O79 G3a: `hUR_O79 : (U-R)` (`[FROZEN] CH12-O77 U-R`, verbatim)

Statement = binder type of `frozen_UR_O77` (`build-logs/ch12/scratch/FrozenO77.lean`).
No inline input beyond `hdec`, `hprof`: the region is produced by O77's `reg_of_outgoing_O77`
(sectional clause + finite scalar bound + outgoing inclusions at the events of `(a, u]` ⇒ `Reg_O77`;
its event clause is O77's incoming/outgoing adapter `regEvent_of_outgoing_O77`).
Proof: `strip_R_O79` (O79 G1, closed from `Hp hdec hprof` by `seedStrip_big_O69`,
`hscale_of_prof_S119`, `hrc_of_hdec_S118`) gives the new centre line `Z` on `[a − c r², a]` ending
at `X(a)` with `|Rm|, R ≤ B/r²`, `sec ≥ −r⁻²` on `B_v(Z v, 20 r)` and the outgoing `20r`-ball
inclusion at its events.  `reg_of_outgoing_O77` is applied to the WHOLE concatenated trace `X.concat Z` on
`[ae, u]`: sec / finite scalar bound / outgoing inclusion on `[ae, a]` from the strip, on `[a, u]`
from `Reg_O77 N hau X r` (its event clause carries the outgoing `r`-ball inclusion); no separate
concatenation lemma for `Reg` is needed.  The new-strip scalar bound is the strip's.
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

/-- **G3a**: the `(U-R)` producer (`[FROZEN] CH12-O77 U-R`), closed from `Hp hdec hprof`. -/
theorem hUR_O79 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) :
    ∀ σ ℓ wst : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst →
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
              metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ B / r ^ 2 := by
  intro σ ℓ wst hσ hσ1 hℓ hwst
  obtain ⟨B, c, C₀, b₀, T₀, hB, hc, hcℓ, hC₀, hb₀, hT₀, hS⟩ :=
    strip_R_O79 Hp (seedStrip_big_O69 Hp) ((hscale_of_prof_S119.{u}).choose_spec.2 Hp hprof)
      (hrc_of_hdec_S118 Hp hdec) σ ℓ wst hσ hσ1 hℓ hwst
  refine ⟨B, c, C₀, b₀, T₀, hB, hc, hcℓ, hC₀, hb₀, hT₀, ?_⟩
  intro s N u hTu hus x r hr hrb a hau X hua hbud hReg y hy hseed
  obtain ⟨ae, haa, Z, hae, hZ, hZout⟩ := hS s u hTu hus r hr hrb a hau hua
    (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau)) hbud y hy hseed
  obtain ⟨hsecX, ⟨KX, hfinX⟩, hevX⟩ := hReg
  have hr20 : r ≤ 20 * r := by linarith
  have hZr : ∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hva : v ≤ a),
      ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
          (Z.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hva)) r,
        Real.sqrt (normSq0S (N.stageMetric (N.activeStage v) v) q 4
            (metricRm04At (N.stageMetric (N.activeStage v) v) q)) ≤ B / r ^ 2 ∧
          metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ B / r ^ 2 ∧
          SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹) :=
    fun v hav hva q hq => hZ v hav hva q (riemannianBallOf_mono _ _ hr20 hq)
  refine ⟨ae, haa, Z, hae, reg_of_outgoing_O77 N (haa.trans hau) (X.concat Z) ?_ ?_ ?_, ?_⟩
  · intro v hav hvu q hq
    rcases le_total v a with hva | hav'
    · rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ (N.activeStage_mono hva)] at hq
      exact (hZr v hav hva q hq).2.2
    · rw [BackwardPointTrace.concat_point_of_ge X Z _ _ _ (N.activeStage_mono hav')] at hq
      exact hsecX v hav' hvu q hq
  · refine ⟨max KX (B / r ^ 2), fun v hav hvu q hq => ?_⟩
    rcases le_total v a with hva | hav'
    · rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ (N.activeStage_mono hva)] at hq
      exact (hZr v hav hva q hq).2.1.trans (le_max_right _ _)
    · rw [BackwardPointTrace.concat_point_of_ge X Z _ _ _ (N.activeStage_mono hav')] at hq
      exact (hfinX v hav' hvu q hq).trans (le_max_left _ _)
  · intro i hf hl
    by_cases hia : i.succ ≤ N.activeStage a
    · rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ hia]
      exact (riemannianBallOf_mono _ _ hr20).trans (hZout i hf hia)
    · have hai : N.activeStage a ≤ i.castSucc := Fin.le_castSucc_iff.mpr (lt_of_not_ge hia)
      rw [BackwardPointTrace.concat_point_of_ge X Z _ _ _ (hai.trans i.castSucc_lt_succ.le)]
      obtain ⟨_, _, hball, _⟩ := hevX i hai hl
      exact hball
  · intro v hav hva q hq
    rw [BackwardPointTrace.concat_point_of_le X Z _ _ _ (N.activeStage_mono hva)] at hq
    exact (hZr v hav hva q hq).2.1

end GC.LongTime.Ch12
