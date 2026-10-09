import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoldRig_O66

set_option autoImplicit false

/-! # CH12-O66 G3: `hold_O66` and the hEndSfam v3 producer

`hold_O66`: the `hold` binder of `hanchor_O60` (`[FROZEN] CH12-O60` text verbatim) from the OLD-GOOD
premise of `[FROZEN v3] CH12-O66 hEndSfam` + `holdRig_O66`.  `hEndSfam_v3_O66`: the v3 family
(`fun old Hold sold mold Rold H S Φ C hcan hgo hW hESC hMIN => hEnd_O54 … (hanchor_O60 … (hold_O66 …)
(hNewLimF …))`); residual binders hHG03/hHG06/hHPS01 (top level), hPRrev, hthickWF, hNewLimF (O68). -/
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace GC.LongTime.Ch12

/-- G3: `hold` of `hanchor_O60` (FrozenO60 text verbatim). -/
theorem hold_O66 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
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
    (hPRrev : ∀ (H H' : FiniteVolumeHyperbolicModel.{u}),
      (∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation H'), Tr'.count < Tr.count) →
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric H.basepoint R ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
            ckErr_O19 H H'.metric 1 f j p < ε) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧ ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    (hgo : ∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
      (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
      (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t))
    :
  ∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
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
          ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p
    := by
  obtain ⟨α, hαpos, hα0, hgood⟩ := hgo
  exact ⟨α, hαpos, hα0, hgood,
    holdRig_O66 F H old Hold sold mold hHG06 hPRrev α hαpos hα0 hgood⟩

/-- G3: `[FROZEN v3] CH12-O66 hEndSfam` producer: v3 = v2 (HoneFin_S72 l.76-142) with the OLD-GOOD
premise inserted after `hcan`.  Residual binders: hHG03/hHG06/hHPS01 (top level), `hPRrev`
(new, this freeze), `hthickWF` (hEnd_O54's hthickW, ∀ H), `hNewLimF` (`[FROZEN] CH12-O60` hNewLim, ∀
old data and H; producer O68). -/
theorem hEndSfam_v3_O66 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (wstar a : ℝ)
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
    (hPRrev : ∀ (H H' : FiniteVolumeHyperbolicModel.{u}),
      (∀ (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation H'), Tr'.count < Tr.count) →
      ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianBallOf H.metric H.basepoint R ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
            ckErr_O19 H H'.metric 1 f j p < ε) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧ ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    (hthickWF : ∀ H : FiniteVolumeHyperbolicModel.{u},
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
    (hNewLimF : ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u})
      (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (H : FiniteVolumeHyperbolicModel.{u}),
      ∀ (ξ : ℝ) (n' : ℕ), 0 < ξ → ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧
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
                ckErr_O19 H H'.metric 1 f k p < ξ / 3)
    :
  ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (_Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
      (C : MetricConvergenceData Φ)
      (_hcan : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k),
      (∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
        (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
        (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
          riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
          ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
            ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
            ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t)) →
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
              (f s hs (E (μ, y))) r)
    := by
  intro old Hold sold mold Rold H S Φ C hcan hgo hW hESC hMIN
  exact hEnd_O54 F H wstar a S Φ C hcan hHG06 hHPS01 (hHG03 H).some (hthickWF H)
    (hanchor_O60 F H wstar old Hold sold mold hHG03 hHG06 hMIN
      (hold_O66 F H old Hold sold mold hHG06 hPRrev hgo) (hNewLimF old Hold sold mold H))

end GC.LongTime.Ch12
