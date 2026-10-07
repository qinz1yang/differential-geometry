import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HdistSeam_S128
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OldReduce_S128
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NewSideEnd_S123
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PathDrift_S101

set_option autoImplicit false

/-! # CH12-S128 G2b: `hflow_S128 (hpatch) (hdrift) : hSW'` — assembly of the same-window distance statement

new half: `newside_closed_S123` (`w s := f j s p`, flow-line lifted at every `s` of the closed window `j`, `f j t p = x t`) +
`edist_image_curve_S101` along the `E_j`-segment (`d_r(x r, f j r p) ≤ 2 η_j ≤ L/16`);
old half: `OLD_of_drift_S128` (`hpatch` supplies the `hold` data; the single remaining input is `hdrift`, the model-drift
lemma along a flow-line).  `hSW'` = `hSW` of `hdist_S123` with the extra hypothesis `δ ≤ L i' / 4` (consumed by `hdist_S128`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem hflow_S128 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (wstar a : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (Rold : Fin old → ℝ) (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
    (hpatch : ∀ i' : Fin old, ∃ (K : ℕ) (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × (Hold i').Carrier)),
      0 < sold i' ∧ (∀ t, sold i' ≤ t → 0 < α t) ∧ AntitoneOn α (Ici (sold i')) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : sold i' ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i' t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : sold i' ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold i' t ht x)) ∧
      (∀ t, sold i' ≤ t →
        riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : sold i' ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹),
          ckErr_S45 (Hold i') (postMetric F.observation t) t⁻¹ (mold i' t ht) k p < α t) ∧
      (∀ t (_ht : sold i' ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
        Nonempty (PersistentModelPatch F (Hold i') (sold i') α (sourceSlice_CX5 Ω) (mold i') t x)))
    (hdrift : ∀ i' : Fin old, ∀ (hs : 0 < sold i') (K : ℕ) (α : ℝ → ℝ)
        (Ω : TopologicalSpace.Opens (ℝ × (Hold i').Carrier)),
      ((∀ t, sold i' ≤ t → 0 < α t) ∧ AntitoneOn α (Ici (sold i')) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : sold i' ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i' t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : sold i' ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold i' t ht x)) ∧
      (∀ t, sold i' ≤ t →
        riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : sold i' ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹),
          ckErr_S45 (Hold i') (postMetric F.observation t) t⁻¹ (mold i' t ht) k p < α t) ∧
      (∀ t (_ht : sold i' ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
        Nonempty (PersistentModelPatch F (Hold i') (sold i') α (sourceSlice_CX5 Ω) (mold i') t x))) →
      ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ (r t : ℝ) (hri : sold i' ≤ r) (hti : sold i' ≤ t),
        T0 ≤ r → ∀ (hrt : r ≤ t), t ≤ 2 * r →
        ∀ q' ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i'),
        ∀ (W : Set ℝ) (w : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) (hW : Icc r t ⊆ W),
        (∀ s ∈ Icc r t, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (w r hrW)) →
        w t (hW ⟨hrt, le_rfl⟩) = mold i' t hti q' →
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hs.trans_le hri)) (postMetric F.observation r))
          (mold i' r hri q') (w r (hW ⟨le_rfl, hrt⟩)) < ENNReal.ofReal ε) :
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
                ∀ δ : ℝ, 0 < δ → δ ≤ L i' / 4 →
                riemannianEDistOf (scaleMetric t⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT ht)) (postMetric F.observation t))
                  (mold i' t hti q) (smoothedPhysicalMap_CX5 H T hT θ f E t ht H.basepoint) < ENNReal.ofReal δ →
                riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT hr)) (postMetric F.observation r))
                  (mold i' r hri q) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint) <
                    ENNReal.ofReal (2 * δ + L i' / 8)) := by
  intro L hL
  choose K α Ω hconj using hpatch
  have hOLD := fun i' : Fin old => OLD_of_drift_S128 F (Hold i') (K i') (sold i') (hconj i').1 (mold i') (α i') (Ω i')
    (hconj i').2.1 (hconj i').2.2.2.1 (hconj i').2.2.2.2.1 (hconj i').2.2.2.2.2.1 (hconj i').2.2.2.2.2.2.1
    (hconj i').2.2.2.2.2.2.2.1 (Rold i')
    (hdrift i' (hconj i').1 (K i') (α i') (Ω i') (hconj i').2) (L i') (hL i')
  choose T0 hT0 using hOLD
  obtain ⟨ε₀, hε₀, hε₁, hεL⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ i', ε₀ ≤ L i' / 32 := by
    rcases isEmpty_or_nonempty (Fin old) with hE | hN
    · exact ⟨1, one_pos, le_rfl, fun i' => (hE.false i').elim⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i' => L i')
      refine ⟨min 1 (L i0 / 32), lt_min one_pos (by have := hL i0; positivity), min_le_left _ _,
        fun i' => ?_⟩
      exact (min_le_right _ _).trans (by have := hi0 i'; linarith)
  have hev : ∀ᶠ i in Filter.atTop, ∀ i', T0 i' ≤ (S.slices i).time :=
    Filter.eventually_all.2 fun i' => S.times_tendsto.eventually_ge_atTop (T0 i')
  obtain ⟨J0, hJ0⟩ := Filter.eventually_atTop.1 hev
  refine ⟨ε₀, hε₀, J0, ?_⟩
  intro i hi T hTi hT θ hθ1 hθ2 hθ3 f E η ρ ν hS8 hanchor i' r t hr ht hri hti hrt htr hwin q hq δ hδ hδL hd
  obtain ⟨hηε, hη0, -, -, -, hρ0, -, -, hE, hEb, hE0, hsupp, hispeed, -, hend, hf16, hlift, -⟩ := hS8
  obtain ⟨j, hrj, htj⟩ := hwin
  have hρj := hρ0 j
  have hxr := smoothedPhysicalMap_closed_S123 H hT θ hθ2 hθ3 f E ρ j hρj (hE0 (j + 1)) (hend j) r hr hrj
  have hxt := smoothedPhysicalMap_closed_S123 H hT θ hθ2 hθ3 f E ρ j hρj (hE0 (j + 1)) (hend j) t ht htj
  obtain ⟨p, γ₁, γ₂, hp, hγ₁, -, h10, -, h11, -, hB, hspd, hft, hlw⟩ :=
    newside_closed_S123 F H hT θ hθ1 f E η ρ j hρj (hE j) (fun μ => (hEb j μ).2) (hsupp j) (hispeed j)
      (hlift j) r t hrj htj hr ht hxr hxt
  have hrpos : 0 < r := lt_of_lt_of_le hT hr
  have hgm := hf16 j r hrj
  have hnew := edist_image_curve_S101 H (postMetric F.observation r) (inv_pos.mpr hrpos) (f j r hrj)
    (riemannianBallOf H.metric H.basepoint (4 * ρ j)) (isOpen_riemannianBallOf_S61 H _) hgm.1
    ((hηε j).trans hε₁) (hη0 j) (fun p hp => hgm.2.2 0 (Nat.zero_le _) p hp) γ₁ hγ₁
    (fun s hs => (hB s hs).1) (fun s hs => (hspd s hs).1)
  rw [h10, h11] at hnew
  have hWsub : Icc r t ⊆ Icc (2 ^ j * T) (2 ^ (j + 1) * T) := Icc_subset_Icc hrj.1 htj.2
  have hT0r : T0 i' ≤ r := by
    have := hJ0 i hi i'
    rw [← hTi] at this
    exact this.trans hr
  have hd' : riemannianEDistOf (scaleMetric t⁻¹ (inv_pos.mpr ((hconj i').1.trans_le hti))
      (postMetric F.observation t)) (mold i' t hti q)
      ((fun s (hs : s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) => f j s hs p) t (hWsub ⟨hrt, le_rfl⟩)) <
      ENNReal.ofReal δ := by
    change riemannianEDistOf _ (mold i' t hti q) (f j t _ p) < _
    rw [hft]
    exact hd
  have hold := hT0 i' r t hri hti hT0r hrt htr q hq δ hδ hδL (Icc (2 ^ j * T) (2 ^ (j + 1) * T))
    (fun s hs => f j s hs p) hWsub (fun s hs => hlw s (hWsub hs)) hd'
  have hη2 : 2 * η j ≤ L i' / 16 := by
    have := hεL i'
    have := hηε j
    linarith
  have hnew' : riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr hrpos) (postMetric F.observation r))
      (f j r hrj p) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint) ≤
      ENNReal.ofReal (L i' / 16) := by
    rw [riemannianEDistOf_comm]
    exact hnew.trans (ENNReal.ofReal_le_ofReal hη2)
  calc _ ≤ riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr hrpos) (postMetric F.observation r))
          (mold i' r hri q) (f j r hrj p) +
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr hrpos) (postMetric F.observation r))
          (f j r hrj p) (smoothedPhysicalMap_CX5 H T hT θ f E r hr H.basepoint) :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal (2 * δ + L i' / 16) + ENNReal.ofReal (L i' / 16) :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnew') hold hnew'
    _ = ENNReal.ofReal (2 * δ + L i' / 8) := by
        rw [← ENNReal.ofReal_add (by have := hL i'; positivity) (by have := hL i'; positivity)]
        congr 1; ring

end GC.LongTime.Ch12
