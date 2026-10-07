import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Step866V3_O63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HbsPack_O57

/-!
# CH12-O63 G2: `hG2c` (κ-cert form) from the two production contracts

`hG2c_v3_O63 Hp hdec hP2 hscale hSeed hU := hG2c_O57 Hp hdec hP2 hscale
(step866_v3_of_contracts_O63 Hp hSeed hU)`: the conclusion is the `[FROZEN v3] CH12-O28` κ-cert
target (= `hG2c` binder of `A13_of_supplies_S124`); `hSeed` / `hU` are the binder types of
`frozen_seedStrip_O57` / `frozen_hU_O57` (`[FROZEN] CH12-O57 G2`), verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal

namespace GC.LongTime.Ch12

universe u

/-- `hG2c` in κ-cert form from Sublemma 86.3 (S94 inputs) and the two production contracts
`child_to_seedStrip866` (`hSeed`) and `hUnscathed866` (`hU`) of `[FROZEN] CH12-O57 G2`. -/
theorem hG2c_v3_O63 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
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
  hG2c_O57 Hp hdec hP2 hscale (step866_v3_of_contracts_O63 Hp hSeed hU)

end GC.LongTime.Ch12
