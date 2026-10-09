import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepModelInst_O41

set_option autoImplicit false

/-! # CH12-O80 G2: level stabilisation + one greedy step with the slack premise ([FROZEN] CH12-O80 slack).

`exists_stable_level_O80` (hand) and `exists_new_model_inst_O80` (= `exists_new_model_inst_O41` text with the sequence at
`Kth * wstar`, the minimality premise of `honeD` and the output at `wstar`, new binder `hstab`; `scratch/o80/gen_g2.py`). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- Level stabilisation ([FROZEN] CH12-O80 slack): along the levels `w / Kth ^ j` the minimal count cannot strictly
decrease forever, so some level `wstar` has the same minimal count as the level `Kth * wstar`. -/
theorem exists_stable_level_O80 (Q : ℝ → ℕ → Prop) (hmono : ∀ a b n, b ≤ a → Q a n → Q b n)
    (Kth w : ℝ) (hKth : 1 ≤ Kth) (hw : 0 < w) (hne : ∃ n, Q w n) :
    ∃ wstar : ℝ, 0 < wstar ∧ Kth * wstar ≤ w ∧ ∀ n, Q wstar n → ∃ m ≤ n, Q (Kth * wstar) m := by
  classical
  have hK0 : 0 < Kth := lt_of_lt_of_le one_pos hKth
  have hlev : ∀ j : ℕ, w / Kth ^ j ≤ w := fun j => div_le_self hw.le (one_le_pow₀ hKth)
  have hex : ∀ j : ℕ, ∃ n, Q (w / Kth ^ j) n := fun j => by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, hmono _ _ _ (hlev j) hn⟩
  have hKK : ∀ j : ℕ, Kth * (w / Kth ^ (j + 1)) = w / Kth ^ j := by
    intro j
    rw [pow_succ]
    field_simp
  obtain ⟨j, hj⟩ : ∃ j, Nat.find (hex j) ≤ Nat.find (hex (j + 1)) := by
    by_contra h
    simp only [not_exists, not_le] at h
    have hd : ∀ j, Nat.find (hex j) + j ≤ Nat.find (hex 0) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => have := h j; omega
    have := hd (Nat.find (hex 0) + 1)
    omega
  refine ⟨w / Kth ^ (j + 1), div_pos hw (pow_pos hK0 _), (hKK j).le.trans (hlev j), fun n hn => ?_⟩
  refine ⟨Nat.find (hex j), hj.trans (Nat.find_min' (hex (j + 1)) hn), ?_⟩
  rw [hKK j]
  exact Nat.find_spec (hex j)

/-- `exists_new_model_inst_O41` with two levels: the sequence (honeD, hnd, extraction, `Nat.find`) at `Kth * wstar`, the
minimality premise of `honeD` and the output at `wstar`, bridged by `hstab` ([FROZEN] CH12-O80 slack). -/
theorem exists_new_model_inst_O80 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (hextract : ∀ w : ℝ, ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w)
    (Kth wstar : ℝ) (hKw : 0 < Kth * wstar) (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u})
    (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (Rold : Fin old → ℝ)
    (honeD : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F),
        IsWThickSequence_S13 S (Kth * wstar) → PointedSmoothConverges_S13 S H →
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
    (hnd : ∃ S : LatePointSequence_S13 F, IsWThickSequence_S13 S (Kth * wstar) ∧
      ∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R))
    (hstab : ∀ n : ℕ, (∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ Tr : HyperbolicTruncation H', Tr.count = n) →
      ∃ m ≤ n, ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' (Kth * wstar) ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ Tr : HyperbolicTruncation H', Tr.count = m) :
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
      IsWThickSequence_S13 S' (Kth * wstar) ∧ PointedSmoothConverges_S13 S' H' ∧
      (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
        S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
          (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
      ∃ Tr : HyperbolicTruncation H', Tr.count = n := by
    obtain ⟨S, hS, hesc⟩ := hnd
    obtain ⟨σ, hσ, M, hM⟩ := hextract (Kth * wstar) hKw S hS
    obtain ⟨Tr⟩ := hHG03 M
    exact ⟨Tr.count, M, S.subsequence σ hσ, thick_subsequence_CX6 hS σ hσ, hM,
      esc_subsequence_O33 S σ hσ hesc, Tr, rfl⟩
  obtain ⟨H, S, hS, hconv, hesc, Tr0, hTr0⟩ := Nat.find_spec hex
  refine ⟨H, honeD H S hS hconv hesc ?_⟩
  intro H' S' hS' hconv' hesc' Tr'
  obtain ⟨m, hm, hPm⟩ := hstab Tr'.count ⟨H', S', hS', hconv', hesc', Tr', rfl⟩
  exact ⟨Tr0, hTr0 ▸ (Nat.find_min' hex hPm).trans hm⟩

end GC.LongTime.Ch12
