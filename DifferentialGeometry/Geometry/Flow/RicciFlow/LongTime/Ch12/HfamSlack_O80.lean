import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.R3AssemblyV3_O80

set_option autoImplicit false

/-! # CH12-O80 G2: `hfam_O80` = `hfam_S135` (text, `scratch/o80/gen_g2.py`) with `(Kth : ℝ) (hKth : 1 ≤ Kth)`, the slack hone
premise `IsWThickSequence_S13 S (Kth * wstar)`, proof through `exists_disjoint_family_of_steps_O80` ([FROZEN] CH12-O80 slack). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set MeasureTheory
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness Function
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12


/-- `hfam_O80` = `hfam_S135` (hone under hneg) with the slack hone premise `IsWThickSequence_S13 S (Kth * wstar)`. -/
theorem hfam_O80 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (Kth : ℝ) (hKth : 1 ≤ Kth)
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hone : EventuallyNegativeScalar_S13 F → ∀ wstar : ℝ, 0 < wstar →
    ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
      (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
      (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F),
      IsWThickSequence_S13 S (Kth * wstar) → PointedSmoothConverges_S13 S H → (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
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
      ∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
        ∀ θ : ℝ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) 1) → (∀ s, s ≤ 7 / 4 → θ s = 0) →
        (∀ s, 15 / 8 ≤ s → θ s = 1) →
        ∀ (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
                  ((∀ j, η j ≤ ε₀) ∧ (∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
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
      ∀ (L : Fin count → ℝ), (∀ i', 0 < L i') → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
        ∀ θ : ℝ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) 1) → (∀ s, s ≤ 7 / 4 → θ s = 0) →
        (∀ s, 15 / 8 ≤ s → θ s = 1) →
        ∀ (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
          H.Carrier → (postStage F.observation t).Carrier)
        (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ),
                  ((∀ j, η j ≤ ε₀) ∧ (∀ j, 0 ≤ η j) ∧ Filter.Tendsto η Filter.atTop (nhds 0) ∧ Monotone ρ ∧
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
  hfam_O33 F K hHG03 (fun hneg => exists_disjoint_family_of_steps_O80 F K Kth hKth Hp hdec hneg hHG03 (hone hneg) hDold
    (hextract hneg) (hstep_O44 F K hHG03 HLOW) hvolw) (cover_event_O33 F K)

end GC.LongTime.Ch12
