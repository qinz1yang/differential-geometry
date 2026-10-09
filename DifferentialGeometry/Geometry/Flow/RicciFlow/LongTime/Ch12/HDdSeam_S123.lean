import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HdistSeam_S123
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HDdFinal_S101

set_option autoImplicit false

/-! # CH12-S123 G1c: `hDd_S123 : HDd v4` := `hDd_v4_S101 … hold (hdist_S123 … hSW)` (the `hflow` binder of `hDd_S101`
is replaced by the same-window `hSW`; the conclusion is verbatim that of `hDd_S101`). -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem hDd_S123 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (wstar a : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
    (hold : ∀ i' : Fin old, ∃ (K : ℕ) (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × (Hold i').Carrier)),
      0 < sold i' ∧ (∀ t, sold i' ≤ t → 0 < α t) ∧ AntitoneOn α (Ici (sold i')) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : sold i' ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i' t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : sold i' ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold i' t ht x)) ∧
      (∀ t, sold i' ≤ t →
        riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : sold i' ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹),
          ckErr_S45 (Hold i') (postMetric F.observation t) t⁻¹ (mold i' t ht) k p < α t))
    (hSW :
      (∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1))
            (postMetric F.observation t)) (f j t ht (E j (μ, y))) = ENNReal.ofReal r ∧
          ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by positivity) ht.1)) (postMetric F.observation t))
            (f j t ht (E j (μ, y))) r)) →
          (∀ (h0 : 2 ^ 0 * T ∈ Icc (2 ^ 0 * T) (2 ^ (0 + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0), HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) →
          ∀ (i' : Fin old) (r t : ℝ) (hr : T ≤ r) (ht : T ≤ t) (hri : sold i' ≤ r) (hti : sold i' ≤ t), r ≤ t → t ≤ 2 * r →
              (∃ j : ℕ, r ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) ∧ t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) →
              ∀ q ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i'),
                ∀ δ : ℝ, 0 < δ →
                riemannianEDistOf (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT ht)) (postMetric F.observation t))
                  (mold i' t hti q) (smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint) < ENNReal.ofReal δ →
                riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT hr)) (postMetric F.observation r))
                  (mold i' r hri q) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint) <
                    ENNReal.ofReal (2 * δ + L i' / 8))
) :
      (∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
          ∀ y ∈ riemannianBallOf H.metric H.basepoint a, ∃ r : ℝ, 0 < r ∧
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
                mold i' r hri '' riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')) :=
  hDd_v4_S101 F wstar a old Hold sold mold Rold H S Φ hold
    (hdist_S123 F wstar a old Hold sold mold Rold H S Φ hSW)

end GC.LongTime.Ch12
