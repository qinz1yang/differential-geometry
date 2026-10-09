import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HDd4_S101
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PathDrift_S101

set_option autoImplicit false

/-! # CH12-S101 G3: `hdist_S101` (HDdist v4) from the flow-line identification `hflow`, and `hDd_S101 : HDd v4`

`hflow` (explicit input, producer = tower lift chain, NOT in S101): for the S8 data and `x t = mold i' t q`
there is a point `w` of the time-`r` stage (the backward flow image of the common point `x t`) which is joined
to the new track `x r` by an `h`-path of speed `≤ 3 (η_j + η_{j+1})` inside the chart ball `B(4 ρ_j)` of `f j r`
and to the old track `mold i' r q` by an `h_old`-path of speed `≤ L/8` inside `B(Rold)`.  Everything else
(near-isometry of both charts at time `r`, `η_j ≤ ε₀`, `α → 0`, triangle inequality) is proved here. -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem hdist_S101 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hflow :
      (∀ (L : Fin old → ℝ), (∀ i', 0 < L i') → ∃ J0 : ℕ, ∀ i : ℕ, J0 ≤ i → ∀ T : ℝ, T = (S.slices i).time → ∀ hT : 0 < T,
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
                ∃ w : (postStage F.observation r).Carrier,
                  (∃ (j : ℕ) (hmem : r ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (γ₁ γ₂ : ℝ → H.Carrier),
                    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₁ (Icc 0 1) ∧ ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₂ (Icc 0 1) ∧
                    f j r hmem (γ₁ 0) = smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint ∧
                    f j r hmem (γ₁ 1) = f j r hmem (γ₂ 0) ∧ f j r hmem (γ₂ 1) = w ∧
                    (∀ s ∈ Icc (0 : ℝ) 1, γ₁ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) ∧
                      γ₂ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
                    (∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ₁ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1)
                      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1) ≤ (3 * (η j + η (j + 1))) ^ 2 ∧
                      H.metric.inner (γ₂ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1)
                      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1) ≤ (3 * (η j + η (j + 1))) ^ 2)) ∧
                  (∃ γ₁ γ₂ : ℝ → (Hold i').Carrier, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₁ (Icc 0 1) ∧
                    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₂ (Icc 0 1) ∧ γ₁ 0 = q ∧ γ₁ 1 = γ₂ 0 ∧ mold i' r hri (γ₂ 1) = w ∧
                    (∀ s ∈ Icc (0 : ℝ) 1, γ₁ s ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i') ∧
                      γ₂ s ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i')) ∧
                    (∀ s ∈ Ioo (0 : ℝ) 1, (Hold i').metric.inner (γ₁ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1)
                      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1) ≤ (L i' / 20) ^ 2 ∧
                      (Hold i').metric.inner (γ₂ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1)
                      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1) ≤ (L i' / 20) ^ 2)))) :
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
  choose K α Ω hs hαpos hαanti hαlim hsm hemb hball hck using hold
  -- T0 i' : for r ≥ T0 i', α i' r < 1 / (|Rold i'| + 1) (so α ≤ 1 and Rold i' ≤ 2 / α)
  have hT0 : ∀ i', ∃ T0 : ℝ, ∀ r, T0 ≤ r → α i' r < 1 / (|Rold i'| + 1) := fun i' =>
    hαlim i' _ (by positivity)
  choose T0 hT0 using hT0
  obtain ⟨J1, hJ1⟩ := hflow L hL
  obtain ⟨J2, hJ2⟩ := Filter.eventually_atTop.mp
    (S.times_tendsto.eventually_ge_atTop (∑ i', |T0 i'|))
  refine ⟨(1 / (1 + ∑ i', 1 / L i')) / 100, by
    have : 0 ≤ ∑ i', 1 / L i' := Finset.sum_nonneg fun i' _ => (one_div_pos.mpr (hL i')).le
    positivity, max J1 J2, ?_⟩
  intro i hi T hTi hT θ hθ1 hθ2 hθ3 f E η ρ ν hS8 hanchor i' r t hr ht hri hti hrt htr q hq hxq
  obtain ⟨hεη, hS8'⟩ := hS8
  obtain ⟨w, ⟨j, hmem, γ₁, γ₂, hγ₁, hγ₂, hγ₁0, hγ₁1, hγ₂1, hγB, hγs⟩, ⟨γ'₁, γ'₂, hγ'₁, hγ'₂, hγ'₁0, hγ'₁γ₂, hγ'₂1, hγ'B, hγ's⟩⟩ :=
    hJ1 i ((le_max_left _ _).trans hi) T hTi hT θ hθ1 hθ2 hθ3 f E η ρ ν hS8' hanchor
      i' r t hr ht hri hti hrt htr q hq hxq
  set ε := (1 / (1 + ∑ i', 1 / L i')) with hεdef
  have hsum : 0 ≤ ∑ i', 1 / L i' := Finset.sum_nonneg fun i' _ => (one_div_pos.mpr (hL i')).le
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by linarith)]; linarith
  have hεL : ε ≤ L i' := by
    have h1 : 1 / L i' ≤ ∑ i', 1 / L i' :=
      Finset.single_le_sum (f := fun i' => 1 / L i') (fun i' _ => (one_div_pos.mpr (hL i')).le)
        (Finset.mem_univ i')
    rw [hεdef, div_le_iff₀ (by linarith)]
    have := hL i'
    have h2 : 1 ≤ L i' * (1 + ∑ i', 1 / L i') := by
      have : L i' * (1 / L i') = 1 := by field_simp
      nlinarith
    linarith
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- r ≥ T0 i'
  have hrT0 : T0 i' ≤ r := by
    have h1 : T0 i' ≤ ∑ j, |T0 j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |T0 j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i'))
    have h2 := hJ2 i ((le_max_right _ _).trans hi)
    rw [← hTi] at h2
    linarith
  have hαr := hT0 i' r hrT0
  have hα1 : α i' r ≤ 1 := by
    have : 1 / (|Rold i'| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [abs_nonneg (Rold i')]
    linarith
  have hr0 : 0 < r := lt_of_lt_of_le hT hr
  -- new track: x r to w (two paths)
  have hηj := hεη j
  have hηj1 := hεη (j + 1)
  obtain ⟨hη0, -, -, -, -, -, -, -, -, -, -, -, -, -, hacc, -⟩ := hS8'
  obtain ⟨hfs, -, hfck⟩ := hacc j r hmem
  have hσN : 0 ≤ 3 * (η j + η (j + 1)) := by have := hη0 j; have := hη0 (j + 1); positivity
  have hnewc := fun (γ : ℝ → H.Carrier) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1))
      (hB : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j))
      (hs : ∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) ≤ (3 * (η j + η (j + 1))) ^ 2) => edist_image_curve_S101 H (postMetric F.observation r) (inv_pos.mpr hr0)
    (f j r hmem) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) (isOpen_riemannianBallOf_S61 H _) hfs
    (δ := η j) (σ := 3 * (η j + η (j + 1))) (by linarith) hσN
    (fun p hp => hfck 0 (Nat.zero_le _) p hp) γ hγ hB hs
  have hn1 := hnewc γ₁ hγ₁ (fun s hs => (hγB s hs).1) (fun s hs => (hγs s hs).1)
  have hn2 := hnewc γ₂ hγ₂ (fun s hs => (hγB s hs).2) (fun s hs => (hγs s hs).2)
  rw [hγ₁0, hγ₁1] at hn1
  rw [hγ₂1] at hn2
  -- old track
  have hball' : riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i') ⊆
      riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α i' r)⁻¹) := by
    apply riemannianBallOf_mono
    have hap := hαpos i' r hri
    have : α i' r * (|Rold i'| + 1) < 1 := by
      have := mul_lt_mul_of_pos_right hαr (show 0 < |Rold i'| + 1 by positivity)
      rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
    rw [le_mul_inv_iff₀ hap]
    nlinarith [le_abs_self (Rold i'), abs_nonneg (Rold i')]
  have hLi := hL i'
  have holdc := fun (γ : ℝ → (Hold i').Carrier) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1))
      (hB : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i'))
      (hs : ∀ s ∈ Ioo (0 : ℝ) 1, (Hold i').metric.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) ≤ (L i' / 20) ^ 2) => edist_image_curve_S101 (Hold i') (postMetric F.observation r)
    (inv_pos.mpr hr0) (mold i' r hri) (riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α i' r)⁻¹))
    (isOpen_riemannianBallOf_S61 _ _) ((hsm i' r hri).mono (hball i' r hri)) (δ := α i' r) (σ := L i' / 20) hα1
    (by positivity) (fun p hp => hck i' r hri 0 (Nat.zero_le _) p hp) γ hγ (fun s hs => hball' (hB s hs)) hs
  have ho1 := holdc γ'₁ hγ'₁ (fun s hs => (hγ'B s hs).1) (fun s hs => (hγ's s hs).1)
  have ho2 := holdc γ'₂ hγ'₂ (fun s hs => (hγ'B s hs).2) (fun s hs => (hγ's s hs).2)
  rw [hγ'₁0, hγ'₁γ₂] at ho1
  rw [hγ'₂1] at ho2
  rw [riemannianEDistOf_comm] at hn1 hn2
  -- triangle
  have hsum2 : ENNReal.ofReal (2 * (L i' / 20)) + ENNReal.ofReal (2 * (L i' / 20)) +
      ENNReal.ofReal (2 * (3 * (η j + η (j + 1)))) + ENNReal.ofReal (2 * (3 * (η j + η (j + 1)))) <
      ENNReal.ofReal (L i' / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have : η j + η (j + 1) ≤ 2 * (ε / 100) := by linarith
    linarith [hεL, hLi]
  set d := riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr hr0) (postMetric F.observation r)) with hd
  have t1 := riemannianEDistOf_triangle (scaleMetric r⁻¹ (inv_pos.mpr hr0) (postMetric F.observation r))
    (mold i' r hri q) (mold i' r hri (γ'₂ 0)) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint)
  have t2 := riemannianEDistOf_triangle (scaleMetric r⁻¹ (inv_pos.mpr hr0) (postMetric F.observation r))
    (mold i' r hri (γ'₂ 0)) w (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint)
  have t3 := riemannianEDistOf_triangle (scaleMetric r⁻¹ (inv_pos.mpr hr0) (postMetric F.observation r))
    w (f j r hmem (γ₂ 0)) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint)
  calc d (mold i' r hri q) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint)
      ≤ d (mold i' r hri q) (mold i' r hri (γ'₂ 0)) + d (mold i' r hri (γ'₂ 0)) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint) := t1
    _ ≤ d (mold i' r hri q) (mold i' r hri (γ'₂ 0)) + (d (mold i' r hri (γ'₂ 0)) w +
          d w (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint)) := add_le_add le_rfl t2
    _ ≤ d (mold i' r hri q) (mold i' r hri (γ'₂ 0)) + (d (mold i' r hri (γ'₂ 0)) w +
          (d w (f j r hmem (γ₂ 0)) + d (f j r hmem (γ₂ 0)) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint))) :=
        add_le_add le_rfl (add_le_add le_rfl t3)
    _ ≤ ENNReal.ofReal (2 * (L i' / 20)) + (ENNReal.ofReal (2 * (L i' / 20)) +
          (ENNReal.ofReal (2 * (3 * (η j + η (j + 1)))) + ENNReal.ofReal (2 * (3 * (η j + η (j + 1)))))) := by
        exact add_le_add ho1 (add_le_add ho2 (add_le_add hn2 hn1))
    _ = ENNReal.ofReal (2 * (L i' / 20)) + ENNReal.ofReal (2 * (L i' / 20)) +
          ENNReal.ofReal (2 * (3 * (η j + η (j + 1)))) + ENNReal.ofReal (2 * (3 * (η j + η (j + 1)))) := by ring
    _ < _ := hsum2

end GC.LongTime.Ch12
