import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SingleModelExplicit_S72
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HpiEndS_O32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HliftBridgeV2_S97

set_option autoImplicit false

/-! # CH12-S72 G3: `hone_S72` = `hone_S4_S72` + EP (escape persistence, binder) — [FROZEN] CH12-S72 NEWESC-fin

`hone_S72`'s conclusion is [FROZEN] CH12-O21 G0 with the NEWESC conjunct weakened to the finitely many old
radii `Rold i` (lead ruling): `∀ i : Fin old, ∃ T, ∀ t ≥ T, map t basepoint ∉ mold i t '' B(Rold i)`.
Inputs: `hLTF04`, `hEndSfam` (hEnd-S, [FROZEN] CH12-O32, quantified over the data `old … H S Φ`) and
`hEP` (escape persistence, new content, lane S83): once `S.point i` escapes (ESC, `i ≥ J0`), the explicit
dyadic physical map started at slice `i` (`smoothedPhysicalMap_CX5`) escapes `B(Rold i')` for large `t`. -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem hone_S72 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (K : ℕ) (wstar a : ℝ)
    (hLTF04 : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H'.Carrier)
        (f : H'.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H'.metric H'.basepoint (2 * R') ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ k' + 3 → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (2 * R'),
          ckErr_S45 H' (postMetric F.observation t) t⁻¹ f j p < δ') →
        ∃ fs : (s : ℝ) → s ∈ Icc t (2 * t) → H'.Carrier → (postStage F.observation s).Carrier,
          (∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'), fs t ⟨le_rfl, by linarith⟩ p = f p) ∧
          ∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            Set.InjOn (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            (∀ j : ℕ, j ≤ k' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
              ckErr_S45 H' (postMetric F.observation s) s⁻¹ (fs s hs) j p < ε') ∧
            ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
              (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : a ≤ s) (_ : s < b)
              (_ : b ≤ (F.tower.history n).horizon)
              (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
                first ≤ (F.tower.history n).toHistory.activeStage r ∧
                  (F.tower.history n).toHistory.activeStage r ≤ last)
              (φ : H'.Carrier →
                (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H'.metric H'.basepoint (R')) ∧
              ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
                (hrs : (r : ℝ) ∈ Icc t (2 * t)),
                ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
                  HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) (fs r hrs p))
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((Hp.records n i).static b).neck.scale / 2 ≤
          metricScalarAt ((Hp.records n i).static b).witness.metric
            (((Hp.records n i).static b).witness.cap z))
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (T : ℝ) (ρ : ℕ → ℝ) (η : ℕ → ℝ) (ν : ℕ → ℕ)
      (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
        H.Carrier → (postStage F.observation t).Carrier),
      Tendsto η atTop (𝓝 0) → Tendsto ν atTop atTop →
      (∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) →
      ∃ J1 : ℕ, ∀ j, J1 ≤ j → ∀ (t : ℝ) (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          metricScalarAt (postMetric F.observation t) (f j t ht p) ≤ 0)
    (hEndSfam : ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
      (C : MetricConvergenceData Φ)
      (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k),
      IsWThickSequence_S13 S wstar → (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) → (∀ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar → PointedSmoothConverges_S13 S' H' →
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
        ∀ Tr' : HyperbolicTruncation H', ∃ Tr : HyperbolicTruncation H, Tr.count ≤ Tr'.count) →
      ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧ Filter.Tendsto β Filter.atTop (nhds 0) ∧
      (∃ I : ℕ, ∀ i : ℕ, I ≤ i →
        ∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sliceApprox_O32 S H Φ i) U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ i x) ∧
          ∀ k : ℕ, k ≤ ⌈(β (S.slices i).time)⁻¹⌉₊ →
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹),
            ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
              (sliceApprox_O32 S H Φ i) k p < β (S.slices i).time) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ (ε' R' : ℝ) (k' : ℕ), 0 < ε' ∧ 0 < R' ∧
        ε' ≤ ε ∧ R ≤ R' ∧ k ≤ k' ∧ ∃ Te : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Te ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < β t) →
        ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'), f t h0 p = g₁ p) →
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
        ∃ (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < β t₂) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E ∧
          (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E (μ, p)) ∧
            Function.Bijective (fun p => E (μ, p))) ∧
          (∀ p, E (0, p) = p) ∧
          (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * R) → E (μ, p) = p) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
            let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
            H.metric.inner (E (μ, p)) v v ≤ ε ^ 2) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
            ckErr_S45 H H.metric 1 (fun x => E (μ, x)) i p ≤ ε) ∧
          (∀ (h1 : t₂ ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), f t₂ h1 (E (1, p)) = g₂ p) ∧
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r))
    (hEP : ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id),
      IsWThickSequence_S13 S wstar → (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
      ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
        ∀ θ : ℝ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) 1) → (∀ s, s ≤ 7 / 4 → θ s = 0) →
        (∀ s, 15 / 8 ≤ s → θ s = 1) →
        ∀ (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
                  ((∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
        Filter.Tendsto ρ Filter.atTop Filter.atTop ∧ (∀ j, 0 < ρ j) ∧
        Monotone ν ∧ Filter.Tendsto ν Filter.atTop Filter.atTop ∧
        (∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j)) ∧
        (∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
          Function.Bijective (fun p => E j (μ, p))) ∧
        (∀ j p, E j (0, p) = p) ∧
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
          let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
          H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2) ∧
        (∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j) ∧
        (∀ j (h1 : 2 ^ (j + 1) * T ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
            (h2 : 2 ^ (j + 1) * T ∈ Icc (2 ^ (j + 1) * T) (2 ^ (j + 1 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * ρ j),
            f j _ h1 (E j (1, p)) = f (j + 1) _ h2 p) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) ∧
        (∃ J₀ : ℕ, ∀ j, J₀ ≤ j → ∀ (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (φ : H.Carrier →
            (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
            (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
              HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ p)) (f j r hrs p)) ∧
        (∀ j t (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (μ : ℝ),
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin old), ∃ T' : ℝ, ∀ t (hTt : T ≤ t) (hi' : sold i' ≤ t), T' ≤ t →
              smoothedPhysicalMap_CX5 H T hT θ f E t hTt H.basepoint ∉
                mold i' t hi' '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')) :
    ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F),
      IsWThickSequence_S13 S wstar → PointedSmoothConverges_S13 S H → (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) → (∀ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar → PointedSmoothConverges_S13 S' H' →
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
        ∀ Tr' : HyperbolicTruncation H', ∃ Tr : HyperbolicTruncation H, Tr.count ≤ Tr'.count) →
    ∃ (start : ℝ) (hstart : 0 < start) (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × H.Carrier))
      (map : (t : ℝ) → start ≤ t → H.Carrier → (postStage F.observation t).Carrier),
      (∀ t, start ≤ t → 0 < α t) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : start ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => map t ht x)) ∧
      (∀ t, start ≤ t →
        riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ (map t ht) k p < α t) ∧
      (∀ Ω' : TopologicalSpace.Opens (ℝ × H.Carrier), Ω' ≤ Ω →
        ∀ t (_ht : start ≤ t), ∀ x ∈ sourceSlice_CX5 Ω' t,
          Nonempty (PersistentModelPatch F H start α (sourceSlice_CX5 Ω') map t x)) ∧
      (∀ t (ht : start ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
          (postMetric F.observation t)) (map t ht y) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (hstart.trans_le ht)) (postMetric F.observation t)) (map t ht y) r) ∧
      (∀ i : Fin old, ∃ T : ℝ, ∀ t (hn : start ≤ t) (hi : sold i ≤ t), T ≤ t →
        map t hn H.basepoint ∉
          mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (Rold i)) := by
  classical
  obtain ⟨Trc, hTrc⟩ := hrc_of_hdec_S118 Hp hdec
  intro old Hold sold mold Rold H S hW hPSC hESC hMIN
  obtain ⟨Φ, C, hcan⟩ := hPSC
  obtain ⟨β, Tth, I, h⟩ := hpi03_discrete_from_endS_O32 F H wstar a S Φ hLTF04
    (hEndSfam old Hold sold mold Rold H S Φ C hcan hW hESC hMIN)
  obtain ⟨J0, hJ0⟩ := hEP old Hold sold mold Rold H S Φ hW hESC
  obtain ⟨i, hiI, hiT⟩ : ∃ i : ℕ, max I J0 ≤ i ∧ max (max Tth 1) Trc < (S.slices i).time := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (S.times_tendsto.eventually_gt_atTop (max (max Tth 1) Trc))
    exact ⟨max (max I J0) N, le_max_left _ _, hN _ (le_max_right _ _)⟩
  have hTpos : 0 < (S.slices i).time := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ((le_max_left _ _).trans hiT.le))
  have hTth : Tth ≤ (S.slices i).time := (le_max_left _ _).trans ((le_max_left _ _).trans hiT.le)
  have hTrcle : Trc ≤ (S.slices i).time := (le_max_right _ _).trans hiT.le
  obtain ⟨f, E, η, ρ, ν, hconj, hanchor⟩ := h i ((le_max_left _ _).trans hiI) _ rfl hTpos hTth
  obtain ⟨hη, hηt, hρm, hρ, hρpos, hνm, hν, hE, hEb, hE0, hsupp, hispeed, hEclose, hend, hacc, hlift0,
    hthick⟩ := hconj
  obtain ⟨J1, hneg1⟩ := hneg H _ ρ η ν f hηt hν hacc
  have hlift0I := hlift0_of_Ico_tail_S118 Hp H hTpos ρ hρpos f hscale
    (fun n i' hle => hTrc n i' (hTrcle.trans hle)) J1 hneg1 hlift0
  obtain ⟨θ, start, hTs, α, Ω, map, hmap, hθr, hθ0, hθ1, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    singleModelExplicit_S72 F K H wstar a hTpos f E η ρ ν hη hηt hρm hρ hρpos hν hE hEb hE0 hsupp hispeed
      hEclose hend hacc J1 hlift0I hthick
  have hEPc := hJ0 i ((le_max_right _ _).trans hiI) _ rfl hTpos θ hθr hθ0 hθ1 f E η ρ ν
    ⟨hη, hηt, hρm, hρ, hρpos, hνm, hν, hE, hEb, hE0, hsupp, hispeed, hEclose, hend, hacc, ⟨J1, hlift0I⟩, hthick⟩
    hanchor
  refine ⟨start, hTpos.trans_le hTs, α, Ω, map, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun i' => ?_⟩
  obtain ⟨T', hT'⟩ := hEPc i'
  exact ⟨T', fun t hn hi ht => by rw [hmap t hn]; exact hT' t (hTs.trans hn) hi ht⟩

end GC.LongTime.Ch12
