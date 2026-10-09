import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HDd4_S101

set_option autoImplicit false

/-! # CH12-S123 G1: `hdist_S123` (HDdist v4) from the SAME-WINDOW distance-flexible statement `hSW`

Ruling B (lead) : `hflow` is kept same-window; the seam time `u = 2^{j+1}T` is chained here.  `r` in window `j`
(`dyadicIndex_CX5 T r = j`), `t > u := 2^{j+1}T`: step 1 at `(u,t)` (both in closed window `j+1`) with `δ = L/64`,
step 2 at `(r,u)` (both in closed window `j`) with `δ = 2 (L/64) + L/8`; `dist_r < 2 δ₂ + L/8 = 7L/16 < L/2`.
The `δ`-flexible hypothesis avoids both `member_of_drift_S90` and an h_old path-lifting. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem hdist_S123 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (wstar a : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
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
              ∀ q ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i' - L i'),
                smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint = mold i' t hti q →
                riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT hr)) (postMetric F.observation r))
                  (mold i' r hri q) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint) < ENNReal.ofReal (L i' / 2)) := by
  intro L hL
  obtain ⟨ε₀, hε₀, J0, hJ0⟩ := hSW L hL
  refine ⟨ε₀, hε₀, J0, ?_⟩
  intro i hi T hTi hT θ hθ1 hθ2 hθ3 f E η ρ ν hS8 hanchor i' r t hr ht hri hti hrt htr q hq hxq
  have hSW' := hJ0 i hi T hTi hT θ hθ1 hθ2 hθ3 f E η ρ ν hS8 hanchor
  have hLi := hL i'
  have hr0 : 0 < r := lt_of_lt_of_le hT hr
  have hmem := dyadicIndex_mem_CX5 hT hr
  set j := dyadicIndex_CX5 T r with hjdef
  simp only [dyadicTime_CX5] at hmem
  obtain ⟨hj1, hj2⟩ := hmem
  have hzero : riemannianEDistOf (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT ht)) (postMetric F.observation t))
      (mold i' t hti q) (smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint) = 0 := by
    rw [hxq]; exact riemannianEDistOf_self _ _
  by_cases hcase : t ≤ 2 ^ (j + 1) * T
  · -- same window
    have h := hSW' i' r t hr ht hri hti hrt htr ⟨j, ⟨hj1, hj2.le⟩, ⟨hj1.trans hrt, hcase⟩⟩ q hq (L i' / 16)
      (by positivity) (by rw [hzero]; exact ENNReal.ofReal_pos.mpr (by positivity))
    refine lt_of_lt_of_le h ?_
    apply ENNReal.ofReal_le_ofReal
    linarith
  · -- seam at u = 2^(j+1) T
    rw [not_le] at hcase
    set u : ℝ := 2 ^ (j + 1) * T with hu
    have hru : r ≤ u := hj2.le
    have hTu : T ≤ u := hr.trans hru
    have hui : sold i' ≤ u := hri.trans hru
    have hu2r : u ≤ 2 * r := by
      have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [hu, this]; nlinarith
    have hu0 : 0 < u := lt_of_lt_of_le hT hTu
    have h2u : 2 ^ (j + 1 + 1) * T = 2 * u := by
      rw [hu]; ring
    have h1 := hSW' i' u t hTu ht hui hti hcase.le (htr.trans (by linarith))
      ⟨j + 1, ⟨le_rfl, by rw [h2u]; linarith⟩, ⟨hcase.le, by rw [h2u]; linarith⟩⟩ q hq (L i' / 64)
      (by positivity) (by rw [hzero]; exact ENNReal.ofReal_pos.mpr (by positivity))
    have h2 := hSW' i' r u hr hTu hri hui hru hu2r ⟨j, ⟨hj1, hj2.le⟩, ⟨hj1.trans hru, le_rfl⟩⟩ q hq
      (2 * (L i' / 64) + L i' / 8) (by positivity) h1
    refine lt_of_lt_of_le h2 ?_
    apply ENNReal.ofReal_le_ofReal
    linarith


end GC.LongTime.Ch12
