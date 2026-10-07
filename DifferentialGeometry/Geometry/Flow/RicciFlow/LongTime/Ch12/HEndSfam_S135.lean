import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepWrap_O54
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoneS83_S129

set_option autoImplicit false

/-! # CH12-S135 G3: `hEndSfam_of_O54_S135` = the `hEndSfam` binder of `hone_S129` (v2 shape, `∀ wstar`, `a := 1`) from `hEnd_O54`.

`hEndSfam wstar hw old Hold sold mold Rold H S Φ C hcan _hW _hold _hMIN := hEnd_O54 F H wstar 1 S Φ C hcan hHG06 hHPS01 Tr hthickW hanchor`
with `Tr := (hHG03 H).some`, `hthickW := hthickWF wstar hw H` (the `hthickW` text of `hEnd_O54` with `wstar` and `H` quantified;
`0 < wstar` is a premise), `hanchor := hanchorF H` (the `hanchor` text of `hEnd_O54`, `∀ H`).  The three trailing premises of the
`hEndSfam` binder (`IsWThickSequence`, old-model condition, `hMIN`) are not consumed (as in `AxO54G3`).  Binder texts cut from
`HoneS83_S129.lean` l.80-146 and `StepWrap_O54.lean` l.230-295 by `scratch/s135/gen_g3.py`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter Topology
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

theorem hEndSfam_of_O54_S135 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
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
    (hHPS01 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
      (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
      ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
      ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
        O ⊆ riemannianBallOf H.metric o R ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (e : H.Carrier ≃ H'.Carrier),
          ContMDiff (𝓡 3) (𝓡 3) ∞ e → ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm →
          (∀ p, localPullInner H'.metric e p = H.metric.inner p) →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
            ckErr_O19 H H'.metric 1 f j p < δ) →
          (∀ p ∈ riemannianBallOf H.metric o R,
            riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal θ) →
          (∀ p ∈ O, riemannianEDistOf H.metric p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
          e '' O ⊆ f '' (U : Set H.Carrier) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
          (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn f U (e p)) <
            ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)))
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hthickWF : ∀ wstar : ℝ, 0 < wstar → ∀ H : FiniteVolumeHyperbolicModel.{u},
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (4 * R''), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r)
    (hanchorF : ∀ H : FiniteVolumeHyperbolicModel.{u},
  ∃ βw : ℝ → ℝ, (∀ t, 0 < βw t) ∧ Filter.Tendsto βw Filter.atTop (nhds 0) ∧
    ∃ (ε₁ R₁ : ℝ) (k₁ : ℕ), 0 < ε₁ ∧ 0 < R₁ ∧ ∃ T₁ : ℝ, ∀ t₂ : ℝ, T₁ ≤ t₂ →
      ∀ (q : H.Carrier → (postStage F.observation t₂).Carrier) (R'' : ℝ), R₁ ≤ R'' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      (∀ k'' : ℕ, k'' ≤ k₁ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ q k'' p < ε₁) →
      ∃ (φ : H.Carrier → (postStage F.observation t₂).Carrier)
        (U' : TopologicalSpace.Opens H.Carrier) (y₀ : H.Carrier),
        riemannianBallOf H.metric y₀ (4 * (βw t₂)⁻¹) ⊆ U' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
        (∀ k : ℕ, k ≤ ⌈(βw t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric y₀ (4 * (βw t₂)⁻¹),
          ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ φ k p < βw t₂) ∧
        φ y₀ = q H.basepoint) :
    ∀ wstar : ℝ, 0 < wstar → ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (_Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
      (C : MetricConvergenceData Φ)
      (_hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k),
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
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r) :=
  fun wstar hw _old _Hold _sold _mold _Rold H S Φ C hcan _ _ _ =>
    hEnd_O54 F H wstar 1 S Φ C hcan hHG06 hHPS01 (hHG03 H).some (hthickWF wstar hw H) (hanchorF H)

end CX3

end GC.LongTime.Ch12
