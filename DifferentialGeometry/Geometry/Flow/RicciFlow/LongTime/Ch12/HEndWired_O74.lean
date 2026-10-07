import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAnchor_O60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L1Assembly_O62
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepWrap_O74

set_option autoImplicit false

/-! # CH12-O74 G2: `hEnd_wired_O74` = `hEnd_O74` with `hHPS01 := hps01_O62`, `Tr := (hHG03 H).some`,
`hanchor := hanchor_O60 …` (copy of `hEnd_wired_S143` with the bounded window binder `hthickW'`).

`hEnd_wired_O74 F H wstar a S Φ C hcan old Hold sold mold hHG03 hHG06 hMIN hold hNewLim hthickW'`
:= `hEnd_O74 F H wstar a S Φ C hcan hHG06 hps01_O62 (hHG03 H).some hthickW'
      (hanchor_O60 F H wstar old Hold sold mold hHG03 hHG06 hMIN hold hNewLim)`.

Remaining explicit inputs: as `hEnd_wired_S143`, except `hthickW` (`thickW_shape_O40`, unsatisfiable for cusped `H`,
S143 F1) is replaced by `hthickW'` (`[FROZEN] CH12-O74` `thickWB_shape_O74`: `InjOn q` premise, window `B(a + 1)`).
Binder texts cut verbatim by `scratch/o74/gen_wired.py` from `HAnchor_O60.lean` / `StepWrap_O74.lean`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Bundle
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

section CX3
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem hEnd_wired_O74 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
    (C : MetricConvergenceData Φ)
    (hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hHG06 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
            ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η)
    (hMIN : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
      IsWThickSequence_S13 S' wstar → PointedSmoothConverges_S13 S' H' →
      (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
      ∀ Tr' : HyperbolicTruncation H', ∃ Tr : HyperbolicTruncation H, Tr.count ≤ Tr'.count)
    (hold : ∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
      (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
      (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t) ∧
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧ ∃ T : ℝ,
        ∀ (i : Fin old) (t : ℝ) (hi : sold i ≤ t), T ≤ t →
        ∀ (q : H.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ), R ≤ R'' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
        (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
        ∀ z ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i t)⁻¹ / 2),
          mold i t hi z = q H.basepoint →
        ∃ e : H.Carrier ≃ (Hold i).Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p)
    (hNewLim : ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
      ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
      ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
      (∀ m, ∃ R'' : ℝ, R ≤ R'' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        Set.InjOn (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        ∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε) →
      (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
        q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
          (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
          (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
            ∃ U : TopologicalSpace.Opens H'.Carrier,
              riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
              ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) ∧
          ∃ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
            riemannianClosedBallOf H.metric H.basepoint ξ⁻¹ ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) ∧
            ∀ k : ℕ, k ≤ n' + 1 → ∀ p ∈ riemannianClosedBallOf H.metric H.basepoint ξ⁻¹,
              ckErr_O19 H H'.metric 1 f k p < ξ / 3) (hthickW' :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (a + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
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
              (f s hs (E (μ, y))) r) :=
  hEnd_O74 F H wstar a S Φ C hcan hHG06 hps01_O62 (hHG03 H).some hthickW'
    (hanchor_O60 F H wstar old Hold sold mold hHG03 hHG06 hMIN hold hNewLim)

end CX3

end GC.LongTime.Ch12
