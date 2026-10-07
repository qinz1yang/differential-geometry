import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HUParts_O71

/-!
# CH12-O71 G3: `hU_of_parts_O71` in the exact `[FROZEN v2b] CH12-O69 hU` text
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

/-- `hU_of_parts_O71` in the exact text of `[FROZEN v2b] CH12-O69 hU`
(`frozen_hU_v2b_O69`, scratch/FrozenO69v2b.lean): the last conjunct (new-strip `R ≤ B/r²`) is
dropped. -/
theorem hU_v2b_of_parts_O71 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hBig : ∀ σ ℓ wst A : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst → 0 < A →
      ∃ B T₁ b₁ : ℝ, 0 < B ∧ 0 < T₁ ∧ 0 < b₁ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₁ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (r : ℝ), 0 < r → r ≤ b₁ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon), a ≤ u → (u : ℝ) - r ^ 2 ≤ a →
      ∀ (y : (N.stageAt a).Carrier) (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
        (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
        (a' : ℝ) = a - ℓ * r ^ 2 →
        (∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
          hasSmallParabolicCurvature N w
            (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
            (σ * r) ∧
          ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
            ballVolume (N.stageMetric (N.activeStage w) w)
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r)) →
        ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage w) w)
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa)) (A * r),
            Real.sqrt (normSq0S (N.stageMetric (N.activeStage w) w) q 4
              (metricRm04At (N.stageMetric (N.activeStage w) w) q)) ≤ B / r ^ 2 ∧
            metricScalarAt (N.stageMetric (N.activeStage w) w) q ≤ B / r ^ 2 ∧
            SectionalBoundedBelowAt (N.stageMetric (N.activeStage w) w) q (-(r ^ 2)⁻¹))
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
    (hrc : ∃ Trc : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
      Trc ≤ (F.tower.history n).toHistory.time i.succ →
      Hp.parameters.recenterConstant *
        Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2) :
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
        (∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) (20 * r),
            Real.sqrt (normSq0S (N.stageMetric (N.activeStage v) v) q 4
              (metricRm04At (N.stageMetric (N.activeStage v) v) q)) ≤ B / r ^ 2) →
        (∀ (i : Fin N.eventCount) (hf : N.activeStage a ≤ i.castSucc)
            (hl : i.succ ≤ N.activeStage u) (U : Set (N.stage i.succ).Carrier),
          U ⊆ riemannianBallOf (N.event i).outputMetric
            (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
          (∀ y ∈ U, metricScalarAt (N.event i).outputMetric y ≤ (9 * B) / r ^ 2) →
          ∀ (x' : (N.event i).incoming.terminalRegularOpen) (y : (N.stage i.succ).Carrier),
            y ∈ U → (N.event i).RegularCrossing x'.val y →
            U ⊆ interior (range (N.event i).oldOutput)) →
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
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) (20 * r),
              Real.sqrt (normSq0S (N.stageMetric (N.activeStage v) v) q 4
                (metricRm04At (N.stageMetric (N.activeStage v) v) q)) ≤ B / r ^ 2) ∧
          (∀ (i : Fin N.eventCount) (hf : N.activeStage ae ≤ i.castSucc)
              (hl : i.succ ≤ N.activeStage u) (U : Set (N.stage i.succ).Carrier),
            U ⊆ riemannianBallOf (N.event i).outputMetric
              ((X.concat Z).point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) →
            IsPreconnected U →
            (∀ y ∈ U, metricScalarAt (N.event i).outputMetric y ≤ (9 * B) / r ^ 2) →
            ∀ (x' : (N.event i).incoming.terminalRegularOpen) (y : (N.stage i.succ).Carrier),
              y ∈ U → (N.event i).RegularCrossing x'.val y →
              U ⊆ interior (range (N.event i).oldOutput)) ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) r,
              SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) := by
  intro σ ℓ wst h1 h2 h3 h4
  obtain ⟨B, c, C₀, b₀, T₀, hB, hc, hcℓ, hC₀, hb₀, hT₀, H⟩ :=
    hU_of_parts_O71 Hp hBig hscale hrc σ ℓ wst h1 h2 h3 h4
  refine ⟨B, c, C₀, b₀, T₀, hB, hc, hcℓ, hC₀, hb₀, hT₀, ?_⟩
  intro s N u hTu hus x r hr hrb a hau X hua hbud h1a h1b h1c y hy hseed
  obtain ⟨ae, haa, Z, he, ha, hb, hc', -⟩ :=
    H s u hTu hus x r hr hrb a hau X hua hbud h1a h1b h1c y hy hseed
  exact ⟨ae, haa, Z, he, ha, hb, hc'⟩

end GC.LongTime.Ch12
