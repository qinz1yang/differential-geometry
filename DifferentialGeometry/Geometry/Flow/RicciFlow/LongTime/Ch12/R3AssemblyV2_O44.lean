import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HstepV2_O44

set_option autoImplicit false

/-! # CH12-O44 G3: R3 assembly v2 ([FROZEN] CH12-O44).

* `exists_disjoint_family_of_steps_O44`: text of `exists_disjoint_family_of_steps_O41` with the hstep
  binder at [FROZEN v2] (INV2 with β) and `Single` carrying INV2 instead of INV1.
* `hfam_O44`: text of `hfam_O41` with the `hstep` binder replaced by HLOW;
  `hstep := hstep_O44 F K hHG03 HLOW`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set MeasureTheory
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness Function
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- G3: R3 from hone-fin' (v3, a := 1), HDd for old families, hstep v2 (INV2) and hvolw. -/
theorem exists_disjoint_family_of_steps_O44 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hone : ∀ wstar : ℝ, 0 < wstar →
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
    (∃ L : Fin old → ℝ, (∀ i', 0 < L i') ∧ ∃ Tb : ℝ,
      ∀ (i' : Fin old) (t : ℝ) (ht0 : 0 < t) (hi : sold i' ≤ t), Tb ≤ t →
        ∀ q ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i') \
            riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i'),
          ∀ r : ℝ, 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) (mold i' t hi q) =
              ENNReal.ofReal r →
            ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) (mold i' t hi q) r <
              ENNReal.ofReal (wstar * r ^ 3)) →
    (∀ (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id),
      ∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (ρ j) → E j (μ, p) = p) ∧
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
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
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
          ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin old) (r t : ℝ) (hr : T ≤ r) (ht : T ≤ t) (hri : sold i' ≤ r) (hti : sold i' ≤ t), r ≤ t → t ≤ 2 * r →
              smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint ∈
                mold i' t hti '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i') →
              smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint ∈
                mold i' r hri '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')) →
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
      (∀ t (ht : start ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
          (postMetric F.observation t)) (map t ht y) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (hstart.trans_le ht)) (postMetric F.observation t)) (map t ht y) r) ∧
      (∀ i : Fin old, ∃ T : ℝ, ∀ t (hn : start ≤ t) (hi : sold i ≤ t), T ≤ t →
        map t hn H.basepoint ∉
          mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (Rold i)))
    (hDold : ∀ wstar : ℝ, 0 < wstar →
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →
        ∀ (Rold : Fin count → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F),
          IsWThickSequence_S13 S wstar →
    (∀ (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id),
      ∀ (L : Fin count → ℝ), (∀ i', 0 < L i') → ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (ρ j) → E j (μ, p) = p) ∧
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
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
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
          ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin count) (r t : ℝ) (hr : T ≤ r) (ht : T ≤ t) (hri : start i' ≤ r) (hti : start i' ≤ t), r ≤ t → t ≤ 2 * r →
              smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint ∈
                map i' t hti '' riemannianBallOf (model i').metric (model i').basepoint (Rold i' - L i') →
              smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint ∈
                map i' r hri '' riemannianBallOf (model i').metric (model i').basepoint (Rold i')))
    (hextract : ∀ w : ℝ, ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w)
    (hstep : ∀ wstar : ℝ, 0 < wstar →
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →
        (∀ i, (∃ (β : ℝ → ℝ) (Ω' : TopologicalSpace.Opens (ℝ × (model i).Carrier)),
      (∀ t, start i ≤ t → 0 < β t) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
      (∀ t (ht : start i ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 Ω' t)) ∧
      (∀ t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω' t => map i t ht x)) ∧
      (∀ t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint (2 * (β t)⁻¹) ⊆
        sourceSlice_CX5 Ω' t) ∧
      (∀ t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(β t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (β t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < β t) ∧
      (∀ t, start i ≤ t → (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier) ⊆
        riemannianBallOf (model i).metric (model i).basepoint (2 * β t)⁻¹))) →
              (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) →
        ∃ R0 : Fin count → ℝ, ∀ (H : FiniteVolumeHyperbolicModel.{u}) (sH : ℝ) (hsH : 0 < sH)
          (αH : ℝ → ℝ) (ΩH : TopologicalSpace.Opens (ℝ × H.Carrier))
          (mapH : (t : ℝ) → sH ≤ t → H.Carrier → (postStage F.observation t).Carrier),
          (        (∀ t, sH ≤ t → 0 < αH t) ∧ AntitoneOn αH (Ici sH) ∧
        (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε) ∧
        (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) ∧
        (∀ t (ht : sH ≤ t),
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 ΩH t => mapH t ht x)) ∧
        (∀ t, sH ≤ t →
          riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) ∧
        (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αH t) ∧
        (∀ Ω' : TopologicalSpace.Opens (ℝ × H.Carrier), Ω' ≤ ΩH →
          ∀ t (_ht : sH ≤ t), ∀ x ∈ sourceSlice_CX5 Ω' t,
            Nonempty (PersistentModelPatch F H sH αH (sourceSlice_CX5 Ω') mapH t x)) ∧
        (∀ t (ht : sH ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
            (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r)) →
          (∀ i : Fin count, ∃ T : ℝ, ∀ t (hn : sH ≤ t) (hi : start i ≤ t), T ≤ t →
            mapH t hn H.basepoint ∉
              map i t hi '' riemannianBallOf (model i).metric (model i).basepoint (R0 i)) →
          ∃ (αn : ℝ → ℝ) (Ωn : TopologicalSpace.Opens (ℝ × H.Carrier)),
            (∀ t, sH ≤ t → 0 < αn t) ∧ AntitoneOn αn (Ici sH) ∧
            (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αn t < ε) ∧
            (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 Ωn t)) ∧
            (∀ t (ht : sH ≤ t),
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ωn t => mapH t ht x)) ∧
            (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αn t)⁻¹) ⊆ sourceSlice_CX5 Ωn t) ∧
            (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αn t)⁻¹⌉₊ →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αn t)⁻¹),
                ckErr_O21 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αn t) ∧
            (∀ t (_ht : sH ≤ t), ∀ x ∈ sourceSlice_CX5 Ωn t,
              Nonempty (PersistentModelPatch F H sH αn (sourceSlice_CX5 Ωn) mapH t x)) ∧
            (∃ (β : ℝ → ℝ) (Ω' : TopologicalSpace.Opens (ℝ × (H).Carrier)),
      (∀ t, sH ≤ t → 0 < β t) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
      (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 Ω' t)) ∧
      (∀ t (ht : sH ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω' t => mapH t ht x)) ∧
      (∀ t, sH ≤ t → riemannianBallOf (H).metric (H).basepoint (2 * (β t)⁻¹) ⊆
        sourceSlice_CX5 Ω' t) ∧
      (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(β t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (H).metric (H).basepoint (2 * (β t)⁻¹),
          ckErr_O21 (H) (postMetric F.observation t) t⁻¹ (mapH t ht) k p < β t) ∧
      (∀ t, sH ≤ t → (sourceSlice_CX5 Ωn t : Set (H).Carrier) ⊆
        riemannianBallOf (H).metric (H).basepoint (2 * β t)⁻¹)) ∧
            ∃ Td : ℝ, ∀ t (i : Fin count) (hi : start i ≤ t) (hn : sH ≤ t), Td ≤ t →
              Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
                (mapH t hn '' (sourceSlice_CX5 Ωn t : Set H.Carrier)))
    (hvolw : ∃ v V : ℝ, 0 < v ∧ 0 ≤ V ∧
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →       (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) →
        ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (A : Fin count → Set X),
          (∀ i, MeasurableSet (A i)) ∧ Pairwise (Disjoint on A) ∧
          (∀ i, ENNReal.ofReal (v / 2) ≤ μ (A i)) ∧ μ univ ≤ ENNReal.ofReal V) :
  ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
      (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
      (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
      (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x)) ∧
      (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) ∧
      (∀ w : ℝ, 0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
        ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
          S.point j ∉ sliceCast_CX4 (S.slices j) ''
            (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R))
 := by
  classical
  obtain ⟨v, V, hv0, hV0, hvol⟩ := hvolw
  let Y := Σ H : FiniteVolumeHyperbolicModel.{u}, Σ s : ℝ, (ℝ → ℝ) × TopologicalSpace.Opens (ℝ × H.Carrier) ×
    ((t : ℝ) → s ≤ t → H.Carrier → (postStage F.observation t).Carrier)
  let Single : Y → Prop := fun y => 0 < y.2.1 ∧ (∀ t, y.2.1 ≤ t → 0 < y.2.2.1 t) ∧ AntitoneOn y.2.2.1 (Ici y.2.1) ∧
            (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → y.2.2.1 t < ε) ∧
            (∀ t (ht : y.2.1 ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (y.2.2.2.2 t ht) (sourceSlice_CX5 y.2.2.2.1 t)) ∧
            (∀ t (ht : y.2.1 ≤ t),
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 y.2.2.2.1 t => y.2.2.2.2 t ht x)) ∧
            (∀ t, y.2.1 ≤ t → riemannianBallOf y.1.metric y.1.basepoint (2 * (y.2.2.1 t)⁻¹) ⊆ sourceSlice_CX5 y.2.2.2.1 t) ∧
            (∀ t (ht : y.2.1 ≤ t), ∀ k : ℕ, k ≤ max K ⌈(y.2.2.1 t)⁻¹⌉₊ →
              ∀ p ∈ riemannianBallOf y.1.metric y.1.basepoint (2 * (y.2.2.1 t)⁻¹),
                ckErr_O21 y.1 (postMetric F.observation t) t⁻¹ (y.2.2.2.2 t ht) k p < y.2.2.1 t) ∧
            (∀ t (_ht : y.2.1 ≤ t), ∀ x ∈ sourceSlice_CX5 y.2.2.2.1 t,
              Nonempty (PersistentModelPatch F y.1 y.2.1 y.2.2.1 (sourceSlice_CX5 y.2.2.2.1) y.2.2.2.2 t x)) ∧
            (∃ (β : ℝ → ℝ) (Ω' : TopologicalSpace.Opens (ℝ × (y.1).Carrier)),
      (∀ t, y.2.1 ≤ t → 0 < β t) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
      (∀ t (ht : y.2.1 ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (y.2.2.2.2 t ht) (sourceSlice_CX5 Ω' t)) ∧
      (∀ t (ht : y.2.1 ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω' t => y.2.2.2.2 t ht x)) ∧
      (∀ t, y.2.1 ≤ t → riemannianBallOf (y.1).metric (y.1).basepoint (2 * (β t)⁻¹) ⊆
        sourceSlice_CX5 Ω' t) ∧
      (∀ t (ht : y.2.1 ≤ t), ∀ k : ℕ, k ≤ max K ⌈(β t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (y.1).metric (y.1).basepoint (2 * (β t)⁻¹),
          ckErr_O21 (y.1) (postMetric F.observation t) t⁻¹ (y.2.2.2.2 t ht) k p < β t) ∧
      (∀ t, y.2.1 ≤ t → (sourceSlice_CX5 y.2.2.2.1 t : Set (y.1).Carrier) ⊆
        riemannianBallOf (y.1).metric (y.1).basepoint (2 * β t)⁻¹))
  let PD : Y → Y → Prop := fun y y' => ∃ Td : ℝ, ∀ t (h : y.2.1 ≤ t) (h' : y'.2.1 ≤ t), Td ≤ t →
    Disjoint (y.2.2.2.2 t h '' (sourceSlice_CX5 y.2.2.2.1 t : Set y.1.Carrier))
      (y'.2.2.2.2 t h' '' (sourceSlice_CX5 y'.2.2.2.1 t : Set y'.1.Carrier))
  let good : ∀ n : ℕ, (Fin n → Y) → Prop := fun n fam =>
    (∀ i, Single (fam i)) ∧ ∀ i j, i ≠ j → PD (fam i) (fam j)
  let Done : ∀ n : ℕ, (Fin n → Y) → Prop := fun n fam => ∀ w : ℝ, 0 < w →
    ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ¬ ∀ (i : Fin n) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : (fam i).2.1 ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          ((fam i).2.2.2.2 _ hj '' riemannianBallOf (fam i).1.metric (fam i).1.basepoint R)
  have disj : ∀ n (fam : Fin n → Y), good n fam → ∃ Td : ℝ, ∀ t (i j : Fin n)
      (hi : (fam i).2.1 ≤ t) (hj : (fam j).2.1 ≤ t), Td ≤ t → i ≠ j →
      Disjoint ((fam i).2.2.2.2 t hi '' (sourceSlice_CX5 (fam i).2.2.2.1 t : Set (fam i).1.Carrier))
        ((fam j).2.2.2.2 t hj '' (sourceSlice_CX5 (fam j).2.2.2.1 t : Set (fam j).1.Carrier)) := by
    intro n fam hg
    have hex : ∀ i j : Fin n, ∃ T : ℝ, i ≠ j → ∀ t (hi : (fam i).2.1 ≤ t) (hj : (fam j).2.1 ≤ t), T ≤ t →
        Disjoint ((fam i).2.2.2.2 t hi '' (sourceSlice_CX5 (fam i).2.2.2.1 t : Set (fam i).1.Carrier))
          ((fam j).2.2.2.2 t hj '' (sourceSlice_CX5 (fam j).2.2.2.1 t : Set (fam j).1.Carrier)) := by
      intro i j
      by_cases hij : i = j
      · exact ⟨0, fun h => absurd hij h⟩
      · obtain ⟨T, hT⟩ := hg.2 i j hij
        exact ⟨T, fun _ => hT⟩
    choose T hT using hex
    refine ⟨∑ i, ∑ j, |T i j|, fun t i j hi hj ht hij => hT i j hij t hi hj ?_⟩
    calc T i j ≤ |T i j| := le_abs_self _
      _ ≤ ∑ j', |T i j'| := Finset.single_le_sum (f := fun j' => |T i j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |T i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |T i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ t := ht
  have hstep' : ∀ n (fam : Fin n → Y), good n fam →
      Done n fam ∨ ∃ y : Y, good (n + 1) (Fin.snoc (α := fun _ => Y) fam y) := by
    intro n fam hg
    by_cases hD : Done n fam
    · exact Or.inl hD
    right
    obtain ⟨w, hw, S, hS, hesc⟩ : ∃ w : ℝ, 0 < w ∧ ∃ S : LatePointSequence_S13 F,
        IsWThickSequence_S13 S w ∧
        ∀ (i : Fin n) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : (fam i).2.1 ≤ (S.slices j).time,
          S.point j ∉ sliceCast_CX4 (S.slices j) ''
            ((fam i).2.2.2.2 _ hj '' riemannianBallOf (fam i).1.metric (fam i).1.basepoint R) := by
      by_contra hc
      exact hD fun w hw S hS he => hc ⟨w, hw, S, hS, he⟩
    obtain ⟨R0, hR0⟩ := hstep w hw n (fun i => (fam i).1) (fun i => (fam i).2.1) (fun i => (fam i).2.2.1)
      (fun i => (fam i).2.2.2.1) (fun i => (fam i).2.2.2.2) ⟨fun i => (hg.1 i).1, fun i => (hg.1 i).2.1, fun i => (hg.1 i).2.2.1, fun i => (hg.1 i).2.2.2.1, fun i => (hg.1 i).2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.2.1⟩
      (fun i => (hg.1 i).2.2.2.2.2.2.2.2.2) (disj n fam hg)
    obtain ⟨Rth, hRth⟩ := old_thin_O41 F K hHG03 w hw n (fun i => (fam i).1) (fun i => (fam i).2.1)
      (fun i => (fam i).2.2.1) (fun i => (fam i).2.2.2.1) (fun i => (fam i).2.2.2.2) ⟨fun i => (hg.1 i).1, fun i => (hg.1 i).2.1, fun i => (hg.1 i).2.2.1, fun i => (hg.1 i).2.2.2.1, fun i => (hg.1 i).2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.2.1⟩
    have hthin := hRth (fun i => max (R0 i) (Rth i)) (fun i => le_max_right _ _)
    obtain ⟨H, sH, hsH, αH, ΩH, mapH, c1, c2, c3, c4, c5, c6, c7, c8, c9, cesc⟩ :=
      exists_new_model_inst_O41 F K Hp hdec hneg hHG03 hextract w hw n (fun i => (fam i).1)
        (fun i => (fam i).2.1) (fun i => (fam i).2.2.2.2) (fun i => max (R0 i) (Rth i))
        (fun H S hW hPSC hESC hMIN => hone w hw n (fun i => (fam i).1) (fun i => (fam i).2.1)
          (fun i => (fam i).2.2.2.2) (fun i => max (R0 i) (Rth i)) H S hW hPSC hESC hMIN hthin
          (hDold w hw n (fun i => (fam i).1) (fun i => (fam i).2.1) (fun i => (fam i).2.2.1)
            (fun i => (fam i).2.2.2.1) (fun i => (fam i).2.2.2.2) ⟨fun i => (hg.1 i).1, fun i => (hg.1 i).2.1, fun i => (hg.1 i).2.2.1, fun i => (hg.1 i).2.2.2.1, fun i => (hg.1 i).2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.2.1⟩
            (fun i => max (R0 i) (Rth i)) H S hW))
        ⟨S, hS, hesc⟩
    obtain ⟨αn, Ωn, n1, n2, n3, n4, n5, n6, n7, n8, n9, Td, hTd⟩ :=
      hR0 H sH hsH αH ΩH mapH ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ (fun i => by
        obtain ⟨T', hT'⟩ := cesc i
        exact ⟨T', fun t hn hi hT hmem => hT' t hn hi hT
          (Set.image_mono (riemannianBallOf_mono _ _ (le_max_left _ _)) hmem)⟩)
    refine ⟨⟨H, sH, αn, Ωn, mapH⟩, fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact ⟨hsH, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩
      | cast j => rw [Fin.snoc_castSucc]; exact hg.1 j
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j =>
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact ⟨Td, fun t h h' hT => (hTd t j h' h hT).symm⟩
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact ⟨Td, fun t h h' hT => hTd t i h h' hT⟩
        | cast j =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hg.2 i j (fun h => hij (congrArg Fin.castSucc h))
  obtain ⟨n, fam, hg, hDn, -⟩ := hpi05_select_O21 good Done hv0 hV0
    (fun n fam hg => hvol n (fun i => (fam i).1) (fun i => (fam i).2.1) (fun i => (fam i).2.2.1)
      (fun i => (fam i).2.2.2.1) (fun i => (fam i).2.2.2.2) ⟨fun i => (hg.1 i).1, fun i => (hg.1 i).2.1, fun i => (hg.1 i).2.2.1, fun i => (hg.1 i).2.2.2.1, fun i => (hg.1 i).2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.2.1⟩ (disj n fam hg))
    ⟨fun i => i.elim0, fun i => i.elim0⟩ hstep'
  exact ⟨n, fun i => (fam i).1, fun i => (fam i).2.1, fun i => (fam i).2.2.1, fun i => (fam i).2.2.2.1,
    fun i => (fam i).2.2.2.2, fun i => (hg.1 i).1, fun i => (hg.1 i).2.1, fun i => (hg.1 i).2.2.1,
    fun i => (hg.1 i).2.2.2.1, fun i => (hg.1 i).2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.1,
    fun i => (hg.1 i).2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.1, fun i => (hg.1 i).2.2.2.2.2.2.2.2.1,
    disj n fam hg, hDn⟩

/-- `hfam_O44`: `hfam_O41` with `hstep` discharged by `hstep_O44` (inputs hHG03, HLOW). -/
theorem hfam_O44 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hone : ∀ wstar : ℝ, 0 < wstar →
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
    (∃ L : Fin old → ℝ, (∀ i', 0 < L i') ∧ ∃ Tb : ℝ,
      ∀ (i' : Fin old) (t : ℝ) (ht0 : 0 < t) (hi : sold i' ≤ t), Tb ≤ t →
        ∀ q ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i') \
            riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i'),
          ∀ r : ℝ, 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) (mold i' t hi q) =
              ENNReal.ofReal r →
            ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) (mold i' t hi q) r <
              ENNReal.ofReal (wstar * r ^ 3)) →
    (∀ (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id),
      ∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (ρ j) → E j (μ, p) = p) ∧
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
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
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
          ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin old) (r t : ℝ) (hr : T ≤ r) (ht : T ≤ t) (hri : sold i' ≤ r) (hti : sold i' ≤ t), r ≤ t → t ≤ 2 * r →
              smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint ∈
                mold i' t hti '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i') →
              smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint ∈
                mold i' r hri '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')) →
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
      (∀ t (ht : start ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht))
          (postMetric F.observation t)) (map t ht y) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (hstart.trans_le ht)) (postMetric F.observation t)) (map t ht y) r) ∧
      (∀ i : Fin old, ∃ T : ℝ, ∀ t (hn : start ≤ t) (hi : sold i ≤ t), T ≤ t →
        map t hn H.basepoint ∉
          mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (Rold i)))
    (hDold : ∀ wstar : ℝ, 0 < wstar →
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →
        ∀ (Rold : Fin count → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F),
          IsWThickSequence_S13 S wstar →
    (∀ (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id),
      ∀ (L : Fin count → ℝ), (∀ i', 0 < L i') → ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
        (∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (ρ j) → E j (μ, p) = p) ∧
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
        (∀ j (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
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
          ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin count) (r t : ℝ) (hr : T ≤ r) (ht : T ≤ t) (hri : start i' ≤ r) (hti : start i' ≤ t), r ≤ t → t ≤ 2 * r →
              smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint ∈
                map i' t hti '' riemannianBallOf (model i').metric (model i').basepoint (Rold i' - L i') →
              smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint ∈
                map i' r hri '' riemannianBallOf (model i').metric (model i').basepoint (Rold i')))
    (hextract : ∀ hneg : EventuallyNegativeScalar_S13 F, ∀ w : ℝ,
      ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w)
    (HLOW : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (sH : ℝ) (hsH : 0 < sH) (αH : ℝ → ℝ)
      (ΩH : TopologicalSpace.Opens (ℝ × H.Carrier))
      (mapH : (t : ℝ) → sH ≤ t → H.Carrier → (postStage F.observation t).Carrier),
      (∀ t, sH ≤ t → 0 < αH t) → (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε) →
      (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) →
      (∀ t (ht : sH ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 ΩH t => mapH t ht x)) →
      (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) →
      (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹),
          ckErr_O21 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αH t) →
      ∀ R : ℝ, ∃ w : ℝ, 0 < w ∧ ∃ T : ℝ, ∀ t (ht : sH ≤ t), T ≤ t →
        ∀ y ∈ riemannianBallOf H.metric H.basepoint R, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
            (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r)
    (hvolw : ∃ v V : ℝ, 0 < v ∧ 0 ≤ V ∧
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →       (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) →
        ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (A : Fin count → Set X),
          (∀ i, MeasurableSet (A i)) ∧ Pairwise (Disjoint on A) ∧
          (∀ i, ENNReal.ofReal (v / 2) ≤ μ (A i)) ∧ μ univ ≤ ENNReal.ofReal V) :
    EventuallyNegativeScalar_S13 F → ∃ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
      (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
      (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
      (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x)) ∧
      (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) ∧
      (∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t, T ≤ t → ∀ (ht0 : 0 < t) (w' : ℝ),
        w ≤ w' → w' ≤ w0 →
          ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
            curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
              ENNReal.ofReal r →
            ENNReal.ofReal (w' * r ^ 3) ≤
              ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
            ∃ (i : Fin count) (hi : start i ≤ t),
              p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹) :=
  hfam_O33 F K hHG03 (fun hneg => exists_disjoint_family_of_steps_O44 F K Hp hdec hneg hHG03 hone hDold
    (hextract hneg) (hstep_O44 F K hHG03 HLOW) hvolw) (cover_event_O33 F K)

end GC.LongTime.Ch12
