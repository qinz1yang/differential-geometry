import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoneFin_S72
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitBasic_CX6

set_option autoImplicit false

/-! CH12-O33 G1a — one greedy step of R3 ([FROZEN v2] CH12-O33 G1): if some `wstar`-thick
sequence escapes all old cores (¬Done), then a NEW model with S4 data and NEWESC-fin at the radii
`Rold` (fixed before the call) exists: `hextract` gives a converging subsequence (thickness and ESC
pass to subsequences), `Nat.find` picks the minimal truncation count among escaping thick limits,
and hone-fin is applied with that minimality. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- ESC passes to subsequences. -/
theorem esc_subsequence_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {old : ℕ} {Hold : Fin old → FiniteVolumeHyperbolicModel.{u}}
    {sold : Fin old → ℝ}
    {mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier}
    (S : LatePointSequence_S13 F) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hesc : ∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
      S.point j ∉ sliceCast_CX4 (S.slices j) ''
        (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) :
    ∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j →
      ∀ hj : sold i ≤ ((S.subsequence σ hσ).slices j).time,
        (S.subsequence σ hσ).point j ∉ sliceCast_CX4 ((S.subsequence σ hσ).slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R) := by
  intro i R
  obtain ⟨J, hJ⟩ := hesc i R
  exact ⟨J, fun j hj => hJ (σ j) (hj.trans (hσ.id_le j))⟩

/-- **G1a — one greedy step.** -/
theorem exists_new_model_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hone : ∀ wstar : ℝ, 0 < wstar →
      ∀ (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
        (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
        (Rold : Fin old → ℝ)
        (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F),
        IsWThickSequence_S13 S wstar → PointedSmoothConverges_S13 S H →
        -- ESC(S): the sequence escapes every old core image
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
          S.point j ∉ sliceCast_CX4 (S.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
        -- minimality of the truncation count among escaping w*-thick limits
        (∀ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
          IsWThickSequence_S13 S' wstar → PointedSmoothConverges_S13 S' H' →
          (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
            S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
              (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) →
          ∀ Tr' : HyperbolicTruncation H', ∃ Tr : HyperbolicTruncation H, Tr.count ≤ Tr'.count) →
        -- S4(H, wstar, a) (sheet S4 verbatim, ckErr_O15s := ckErr_S45, slice_O15s := sourceSlice_CX5)
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
          -- NEWESC-fin: finitely many old radii (lead ruling), see [FROZEN] CH12-S72 NEWESC-fin
          (∀ i : Fin old, ∃ T : ℝ, ∀ t (hn : start ≤ t) (hi : sold i ≤ t), T ≤ t →
            map t hn H.basepoint ∉
              mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (Rold i)))
    (hextract : ∀ w : ℝ, ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w)
    (wstar : ℝ) (hw : 0 < wstar) (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u})
    (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (Rold : Fin old → ℝ)
    (hnd : ∃ S : LatePointSequence_S13 F, IsWThickSequence_S13 S wstar ∧
      ∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) :
    ∃ H : FiniteVolumeHyperbolicModel.{u},
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
        -- NEWESC-fin: finitely many old radii (lead ruling), see [FROZEN] CH12-S72 NEWESC-fin
        (∀ i : Fin old, ∃ T : ℝ, ∀ t (hn : start ≤ t) (hi : sold i ≤ t), T ≤ t →
          map t hn H.basepoint ∉
            mold i t hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint (Rold i)) := by
  classical
  have hex : ∃ n : ℕ, ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
      IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
      (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
      ∃ Tr : HyperbolicTruncation H', Tr.count = n := by
    obtain ⟨S, hS, hesc⟩ := hnd
    obtain ⟨σ, hσ, M, hM⟩ := hextract wstar hw S hS
    obtain ⟨Tr⟩ := hHG03 M
    exact ⟨Tr.count, M, S.subsequence σ hσ, thick_subsequence_CX6 hS σ hσ, hM,
      esc_subsequence_O33 S σ hσ hesc, Tr, rfl⟩
  obtain ⟨H, S, hS, hconv, hesc, Tr0, hTr0⟩ := Nat.find_spec hex
  refine ⟨H, hone wstar hw old Hold sold mold Rold H S hS hconv hesc ?_⟩
  intro H' S' hS' hconv' hesc' Tr'
  exact ⟨Tr0, hTr0 ▸ Nat.find_min' hex ⟨H', S', hS', hconv', hesc', Tr', rfl⟩⟩

end GC.LongTime.Ch12
