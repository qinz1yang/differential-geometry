import DifferentialGeometry.Topology.Handle.Basic
import DifferentialGeometry.Topology.Handle.Duality
import DifferentialGeometry.Topology.Homotopy.ClosedCell
import DifferentialGeometry.Topology.Homotopy.Interval

namespace DifferentialGeometry.Topology.Handle

open DifferentialGeometry.Topology.Homotopy
open ContinuousMap
open unitInterval

private theorem radialStep_cellBoundary_norm (k : ℕ) (t : Set.Ico (0 : ℝ) 1)
    (u : CellBoundary k) :
    ‖(radialStep k (icoToI t) (cellBoundaryInclusion k u) : EuclideanSpace ℝ (Fin k))‖ =
      1 - (t : ℝ) := by
  rw [radialStep_norm]
  have hb : ‖(cellBoundaryInclusion k u : EuclideanSpace ℝ (Fin k))‖ = 1 := by
    simpa [cellBoundaryInclusion] using u.2
  simp [hb]

private theorem radialStep_cellBoundary_norm' (l : ℕ) (t : Set.Ico (0 : ℝ) 1)
    (v : CellBoundary l) :
    ‖(radialStep l (icoToI t) (cellBoundaryInclusion l v) : EuclideanSpace ℝ (Fin l))‖ =
      1 - (t : ℝ) := by
  rw [radialStep_norm]
  have hb : ‖(cellBoundaryInclusion l v : EuclideanSpace ℝ (Fin l))‖ = 1 := by
    simpa [cellBoundaryInclusion] using v.2
  simp [hb]

private theorem radialStep_cellBoundary_ne_zero (k : ℕ) (t : Set.Ico (0 : ℝ) 1)
    (u : CellBoundary k) :
    (radialStep k (icoToI t) (cellBoundaryInclusion k u) : EuclideanSpace ℝ (Fin k)) ≠ 0 := by
  intro hz
  have hnorm := radialStep_cellBoundary_norm k t u
  rw [hz, norm_zero] at hnorm
  have ht : (t : ℝ) < 1 := t.2.2
  linarith

private theorem radialStep_cellBoundary_ne_zero' (l : ℕ) (t : Set.Ico (0 : ℝ) 1)
    (v : CellBoundary l) :
    (radialStep l (icoToI t) (cellBoundaryInclusion l v) : EuclideanSpace ℝ (Fin l)) ≠ 0 := by
  intro hz
  have hnorm := radialStep_cellBoundary_norm' l t v
  rw [hz, norm_zero] at hnorm
  have ht : (t : ℝ) < 1 := t.2.2
  linarith

private theorem norm_smul_cellBoundary {k : ℕ} (t : Set.Ico (0 : ℝ) 1) (u : CellBoundary k) :
    ‖(1 - (t : ℝ)) • (u : EuclideanSpace ℝ (Fin k))‖ = 1 - (t : ℝ) := by
  have ht : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := le_of_lt t.2.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hb : ‖(u : EuclideanSpace ℝ (Fin k))‖ = 1 := u.2
  rw [hb]
  ring

theorem not_mem_cocore_of_ne_zero (k l : ℕ) {p : StandardHandle k l}
    (hne : (p.1 : EuclideanSpace ℝ (Fin k)) ≠ 0) :
    p ∉ cocoreDisk k l := by
  intro hp
  apply hne
  have hp' := congrArg (fun q : ClosedCell k => (q : EuclideanSpace ℝ (Fin k))) hp
  simpa [closedCellCenter] using hp'

theorem ne_zero_of_not_mem_cocore (k l : ℕ) {p : StandardHandle k l}
    (hp : p ∉ cocoreDisk k l) :
    (p.1 : EuclideanSpace ℝ (Fin k)) ≠ 0 := by
  intro hz
  exact hp (Subtype.ext (by simpa [closedCellCenter] using hz))

theorem not_mem_core_of_ne_zero (k l : ℕ) {p : StandardHandle k l}
    (hne : (p.2 : EuclideanSpace ℝ (Fin l)) ≠ 0) :
    p ∉ coreDisk k l := by
  intro hp
  apply hne
  have hp' := congrArg (fun q : ClosedCell l => (q : EuclideanSpace ℝ (Fin l))) hp
  simpa [closedCellCenter] using hp'

theorem ne_zero_of_not_mem_core (k l : ℕ) {p : StandardHandle k l}
    (hp : p ∉ coreDisk k l) :
    (p.2 : EuclideanSpace ℝ (Fin l)) ≠ 0 := by
  intro hz
  exact hp (Subtype.ext (by simpa [closedCellCenter] using hz))

private theorem radialStep_boundaryNormalize {k : ℕ} (x : EuclideanSpace ℝ (Fin k))
    (hx : x ≠ 0) (hle : ‖x‖ ≤ 1) :
    radialStep k (icoToI ⟨1 - ‖x‖, by
      constructor
      · linarith
      · have hlt : 0 < ‖x‖ := norm_pos_iff.mpr hx
        linarith⟩) (cellBoundaryInclusion k (boundaryNormalize x hx)) = ⟨x, hle⟩ := by
  apply Subtype.ext
  change (1 - (1 - ‖x‖)) • (‖x‖⁻¹ • x) = x
  have hsub : 1 - (1 - ‖x‖) = ‖x‖ := by ring
  rw [hsub]
  rw [smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)]
  simp

private theorem normalize_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

private noncomputable def attachingCollarInvFun (k l : ℕ) :
    {p : StandardHandle k l // p ∉ cocoreDisk k l} →
      AttachingRegion k l × Set.Ico (0 : ℝ) 1 :=
  fun p => ((boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
      (ne_zero_of_not_mem_cocore k l p.2), (p : StandardHandle k l).2),
    ⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
      one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2)⟩)

private theorem continuous_attachingCollarInvFun (k l : ℕ) :
    Continuous (attachingCollarInvFun k l) := by
  change Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
    ((boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
      (ne_zero_of_not_mem_cocore k l p.2), (p : StandardHandle k l).2),
      (⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2)⟩ : Set.Ico (0 : ℝ) 1)))
  have h₂ : Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have h₁ : Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖) :=
    continuous_norm.comp h₂
  have h₃ : Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      (p : StandardHandle k l).2) :=
    continuous_snd.comp continuous_subtype_val
  have hsmul : Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖⁻¹ •
        ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))) := by
    exact Continuous.smul
      (Continuous.inv₀ h₁ (fun p => norm_ne_zero_iff.mpr (ne_zero_of_not_mem_cocore k l p.2)))
      h₂
  have hJ : Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      (⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2)⟩ : Set.Ico (0 : ℝ) 1)) := by
    exact Continuous.subtype_mk (p := fun r : ℝ => r ∈ Set.Ico (0 : ℝ) 1)
      (continuous_const.sub h₁) (fun p => one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2))
  have hregion : Continuous (fun p : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      (boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
        (ne_zero_of_not_mem_cocore k l p.2), (p : StandardHandle k l).2)) := by
    exact (Continuous.subtype_mk (p := fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ = 1)
      hsmul (fun p => by
        exact normalize_norm ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
          (ne_zero_of_not_mem_cocore k l p.2))).prodMk h₃
  exact hregion.prodMk hJ

noncomputable def attachingCollar (k l : ℕ) :
    (AttachingRegion k l × Set.Ico (0 : ℝ) 1) ≃ₜ
      {p : StandardHandle k l // p ∉ cocoreDisk k l} where
  toFun := fun z => ⟨(radialStep k (icoToI z.2) (cellBoundaryInclusion k z.1.1), z.1.2), by
    exact not_mem_cocore_of_ne_zero k l (radialStep_cellBoundary_ne_zero k z.2 z.1.1)⟩
  invFun := attachingCollarInvFun k l
  left_inv := by
    intro z
    rcases z with ⟨⟨u, y⟩, t⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        have hx : (radialStep k (icoToI t) (cellBoundaryInclusion k u) :
            EuclideanSpace ℝ (Fin k)) = (1 - (t : ℝ)) • (u : EuclideanSpace ℝ (Fin k)) := by
          simp [radialStep, icoToI, cellBoundaryInclusion]
        dsimp [attachingCollarInvFun]
        dsimp [boundaryNormalize]
        rw [hx]
        rw [norm_smul_cellBoundary t u]
        rw [smul_smul]
        have h : (1 : ℝ) - (t : ℝ) ≠ 0 := by
          have ht : (t : ℝ) < 1 := t.2.2
          linarith
        rw [inv_mul_cancel₀ h]
        simp
      · rfl
    · apply Subtype.ext
      change 1 - ‖(radialStep k (icoToI t) (cellBoundaryInclusion k u) :
        EuclideanSpace ℝ (Fin k))‖ = (t : ℝ)
      rw [radialStep_cellBoundary_norm]
      ring
  right_inv := by
    intro p
    rcases p with ⟨q, hq⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : ClosedCell k => (z : EuclideanSpace ℝ (Fin k)))
        (radialStep_boundaryNormalize (q.1 : EuclideanSpace ℝ (Fin k))
          (ne_zero_of_not_mem_cocore k l hq) q.1.2)
    · rfl
  continuous_toFun := by
    have h₁ : Continuous (fun z : AttachingRegion k l × Set.Ico (0 : ℝ) 1 =>
        radialStep k (icoToI z.2) (cellBoundaryInclusion k z.1.1)) := by
      exact (continuous_radialStep k).comp
        ((continuous_icoToI.comp continuous_snd).prodMk
          ((continuous_cellBoundaryInclusion k).comp (continuous_fst.comp continuous_fst)))
    have h₂ : Continuous (fun z : AttachingRegion k l × Set.Ico (0 : ℝ) 1 => z.1.2) :=
      continuous_snd.comp continuous_fst
    exact Continuous.subtype_mk
      (h₁.prodMk h₂)
      (by
        intro z
        exact not_mem_cocore_of_ne_zero k l (radialStep_cellBoundary_ne_zero k z.2 z.1.1))
  continuous_invFun := continuous_attachingCollarInvFun k l

private noncomputable def beltCollarInvFun (k l : ℕ) :
    {p : StandardHandle k l // p ∉ coreDisk k l} →
      BeltRegion k l × Set.Ico (0 : ℝ) 1 :=
  fun p => (((p : StandardHandle k l).1,
    boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
      (ne_zero_of_not_mem_core k l p.2)),
    ⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
      one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2)⟩)

private theorem continuous_beltCollarInvFun (k l : ℕ) :
    Continuous (beltCollarInvFun k l) := by
  change Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
    (((p : StandardHandle k l).1,
      boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
        (ne_zero_of_not_mem_core k l p.2)),
      (⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2)⟩ : Set.Ico (0 : ℝ) 1)))
  have h₂ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have h₁ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖) :=
    continuous_norm.comp h₂
  have h₃ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      (p : StandardHandle k l).1) :=
    continuous_fst.comp continuous_subtype_val
  have hsmul : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖⁻¹ •
        ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))) := by
    exact Continuous.smul
      (Continuous.inv₀ h₁ (fun p => norm_ne_zero_iff.mpr (ne_zero_of_not_mem_core k l p.2)))
      h₂
  have hJ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      (⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2)⟩ : Set.Ico (0 : ℝ) 1)) := by
    exact Continuous.subtype_mk (p := fun r : ℝ => r ∈ Set.Ico (0 : ℝ) 1)
      (continuous_const.sub h₁) (fun p => one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2))
  have hregion : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      ((p : StandardHandle k l).1,
        boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l p.2))) := by
    exact h₃.prodMk (Continuous.subtype_mk (p := fun z : EuclideanSpace ℝ (Fin l) => ‖z‖ = 1)
      hsmul (fun p => by
        exact normalize_norm ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l p.2)))
  exact hregion.prodMk hJ

noncomputable def beltCollar (k l : ℕ) :
    (BeltRegion k l × Set.Ico (0 : ℝ) 1) ≃ₜ
      {p : StandardHandle k l // p ∉ coreDisk k l} where
  toFun := fun z => ⟨(z.1.1, radialStep l (icoToI z.2) (cellBoundaryInclusion l z.1.2)), by
    exact not_mem_core_of_ne_zero k l (radialStep_cellBoundary_ne_zero' l z.2 z.1.2)⟩
  invFun := beltCollarInvFun k l
  left_inv := by
    intro z
    rcases z with ⟨⟨x, v⟩, t⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        have hx : (radialStep l (icoToI t) (cellBoundaryInclusion l v) :
            EuclideanSpace ℝ (Fin l)) = (1 - (t : ℝ)) • (v : EuclideanSpace ℝ (Fin l)) := by
          simp [radialStep, icoToI, cellBoundaryInclusion]
        dsimp [beltCollarInvFun]
        dsimp [boundaryNormalize]
        rw [hx]
        rw [norm_smul_cellBoundary t v]
        rw [smul_smul]
        have h : (1 : ℝ) - (t : ℝ) ≠ 0 := by
          have ht : (t : ℝ) < 1 := t.2.2
          linarith
        rw [inv_mul_cancel₀ h]
        simp
    · apply Subtype.ext
      change 1 - ‖(radialStep l (icoToI t) (cellBoundaryInclusion l v) :
        EuclideanSpace ℝ (Fin l))‖ = (t : ℝ)
      rw [radialStep_cellBoundary_norm']
      ring
  right_inv := by
    intro p
    rcases p with ⟨q, hq⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact congrArg (fun z : ClosedCell l => (z : EuclideanSpace ℝ (Fin l)))
        (radialStep_boundaryNormalize (q.2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l hq) q.2.2)
  continuous_toFun := by
    have h₁ : Continuous (fun z : BeltRegion k l × Set.Ico (0 : ℝ) 1 =>
        radialStep l (icoToI z.2) (cellBoundaryInclusion l z.1.2)) := by
      exact (continuous_radialStep l).comp
        ((continuous_icoToI.comp continuous_snd).prodMk
          ((continuous_cellBoundaryInclusion l).comp (continuous_snd.comp continuous_fst)))
    have h₂ : Continuous (fun z : BeltRegion k l × Set.Ico (0 : ℝ) 1 => z.1.1) :=
      continuous_fst.comp continuous_fst
    exact Continuous.subtype_mk
      (h₂.prodMk h₁)
      (by
        intro z
        exact not_mem_core_of_ne_zero k l (radialStep_cellBoundary_ne_zero' l z.2 z.1.2))
  continuous_invFun := continuous_beltCollarInvFun k l

private noncomputable def bicollarInvFun (k l : ℕ) :
    {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} →
      Corner k l × Set.Ico (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1 :=
  fun p => ((boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
      (ne_zero_of_not_mem_cocore k l p.2.2),
    boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
      (ne_zero_of_not_mem_core k l p.2.1)),
    (⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2.2)⟩,
      ⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2.1)⟩))

private theorem continuous_bicollarInvFun (k l : ℕ) :
    Continuous (bicollarInvFun k l) := by
  change Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
    ((boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
        (ne_zero_of_not_mem_cocore k l p.2.2),
      boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
        (ne_zero_of_not_mem_core k l p.2.1)),
      ((⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
          one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2.2)⟩ : Set.Ico (0 : ℝ) 1),
        (⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
          one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2.1)⟩ : Set.Ico (0 : ℝ) 1))))
  have h₁c : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have h₂c : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hn₁ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖) :=
    continuous_norm.comp h₁c
  have hn₂ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖) :=
    continuous_norm.comp h₂c
  have hsmul₁ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖⁻¹ •
        ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))) := by
    exact Continuous.smul
      (Continuous.inv₀ hn₁ (fun p => norm_ne_zero_iff.mpr (ne_zero_of_not_mem_cocore k l p.2.2)))
      h₁c
  have hsmul₂ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖⁻¹ •
        ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))) := by
    exact Continuous.smul
      (Continuous.inv₀ hn₂ (fun p => norm_ne_zero_iff.mpr (ne_zero_of_not_mem_core k l p.2.1)))
      h₂c
  have hJ₁ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      (⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2.2)⟩ : Set.Ico (0 : ℝ) 1)) := by
    exact Continuous.subtype_mk (p := fun r : ℝ => r ∈ Set.Ico (0 : ℝ) 1)
      (continuous_const.sub hn₁) (fun p => one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2.2))
  have hJ₂ : Continuous (fun p : {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =>
      (⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
        one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2.1)⟩ : Set.Ico (0 : ℝ) 1)) := by
    exact Continuous.subtype_mk (p := fun r : ℝ => r ∈ Set.Ico (0 : ℝ) 1)
      (continuous_const.sub hn₂) (fun p => one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2.1))
  exact ((Continuous.subtype_mk (p := fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ = 1)
      hsmul₁ (fun p => by
        exact normalize_norm ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
          (ne_zero_of_not_mem_cocore k l p.2.2))).prodMk
    (Continuous.subtype_mk (p := fun z : EuclideanSpace ℝ (Fin l) => ‖z‖ = 1)
      hsmul₂ (fun p => by
        exact normalize_norm ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l p.2.1)))).prodMk
    (hJ₁.prodMk hJ₂)

noncomputable def bicollar (k l : ℕ) :
    (Corner k l × Set.Ico (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1) ≃ₜ
      {p : StandardHandle k l // p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} where
  toFun := fun z => ⟨(radialStep k (icoToI z.2.1) (cellBoundaryInclusion k z.1.1),
    radialStep l (icoToI z.2.2) (cellBoundaryInclusion l z.1.2)), by
    constructor
    · exact not_mem_core_of_ne_zero k l (radialStep_cellBoundary_ne_zero' l z.2.2 z.1.2)
    · exact not_mem_cocore_of_ne_zero k l (radialStep_cellBoundary_ne_zero k z.2.1 z.1.1)⟩
  invFun := bicollarInvFun k l
  left_inv := by
    intro z
    rcases z with ⟨⟨u, v⟩, ⟨t₁, t₂⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        have hx₁ : (radialStep k (icoToI t₁) (cellBoundaryInclusion k u) :
            EuclideanSpace ℝ (Fin k)) = (1 - (t₁ : ℝ)) • (u : EuclideanSpace ℝ (Fin k)) := by
          simp [radialStep, icoToI, cellBoundaryInclusion]
        dsimp [bicollarInvFun]
        dsimp [boundaryNormalize]
        rw [hx₁]
        rw [norm_smul_cellBoundary t₁ u]
        rw [smul_smul]
        have h₁ : (1 : ℝ) - (t₁ : ℝ) ≠ 0 := by
          have ht : (t₁ : ℝ) < 1 := t₁.2.2
          linarith
        rw [inv_mul_cancel₀ h₁]
        simp
      · apply Subtype.ext
        have hx₂ : (radialStep l (icoToI t₂) (cellBoundaryInclusion l v) :
            EuclideanSpace ℝ (Fin l)) = (1 - (t₂ : ℝ)) • (v : EuclideanSpace ℝ (Fin l)) := by
          simp [radialStep, icoToI, cellBoundaryInclusion]
        dsimp [bicollarInvFun]
        dsimp [boundaryNormalize]
        rw [hx₂]
        rw [norm_smul_cellBoundary t₂ v]
        rw [smul_smul]
        have h₂ : (1 : ℝ) - (t₂ : ℝ) ≠ 0 := by
          have ht : (t₂ : ℝ) < 1 := t₂.2.2
          linarith
        rw [inv_mul_cancel₀ h₂]
        simp
    · apply Prod.ext
      · apply Subtype.ext
        change 1 - ‖(radialStep k (icoToI t₁) (cellBoundaryInclusion k u) :
          EuclideanSpace ℝ (Fin k))‖ = (t₁ : ℝ)
        rw [radialStep_cellBoundary_norm]
        ring
      · apply Subtype.ext
        change 1 - ‖(radialStep l (icoToI t₂) (cellBoundaryInclusion l v) :
          EuclideanSpace ℝ (Fin l))‖ = (t₂ : ℝ)
        rw [radialStep_cellBoundary_norm']
        ring
  right_inv := by
    intro p
    rcases p with ⟨q, hq⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : ClosedCell k => (z : EuclideanSpace ℝ (Fin k)))
        (radialStep_boundaryNormalize (q.1 : EuclideanSpace ℝ (Fin k))
          (ne_zero_of_not_mem_cocore k l hq.2) q.1.2)
    · apply Subtype.ext
      exact congrArg (fun z : ClosedCell l => (z : EuclideanSpace ℝ (Fin l)))
        (radialStep_boundaryNormalize (q.2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l hq.1) q.2.2)
  continuous_toFun := by
    have h₁ : Continuous (fun z : Corner k l × Set.Ico (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1 =>
        radialStep k (icoToI z.2.1) (cellBoundaryInclusion k z.1.1)) := by
      exact (continuous_radialStep k).comp
        ((continuous_icoToI.comp (continuous_fst.comp continuous_snd)).prodMk
          ((continuous_cellBoundaryInclusion k).comp (continuous_fst.comp continuous_fst)))
    have h₂ : Continuous (fun z : Corner k l × Set.Ico (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1 =>
        radialStep l (icoToI z.2.2) (cellBoundaryInclusion l z.1.2)) := by
      exact (continuous_radialStep l).comp
        ((continuous_icoToI.comp (continuous_snd.comp continuous_snd)).prodMk
          ((continuous_cellBoundaryInclusion l).comp (continuous_snd.comp continuous_fst)))
    exact Continuous.subtype_mk
      (h₁.prodMk h₂)
      (by
        intro z
        constructor
        · exact not_mem_core_of_ne_zero k l (radialStep_cellBoundary_ne_zero' l z.2.2 z.1.2)
        · exact not_mem_cocore_of_ne_zero k l (radialStep_cellBoundary_ne_zero k z.2.1 z.1.1))
  continuous_invFun := continuous_bicollarInvFun k l

theorem attachingCollar_zero (k l : ℕ) (a : AttachingRegion k l) :
    ((attachingCollar k l) (a, ⟨0, by norm_num⟩) : StandardHandle k l) =
      attachingInclusion k l a := by
  rcases a with ⟨u, y⟩
  simp [attachingCollar, attachingInclusion, icoToI]

theorem beltCollar_zero (k l : ℕ) (a : BeltRegion k l) :
    ((beltCollar k l) (a, ⟨0, by norm_num⟩) : StandardHandle k l) =
      beltInclusion k l a := by
  rcases a with ⟨x, v⟩
  simp [beltCollar, beltInclusion, icoToI]

theorem bicollar_zero (k l : ℕ) (c : Corner k l) :
    ((bicollar k l) (c, (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)) : StandardHandle k l) =
      cornerInclusion k l c := by
  rcases c with ⟨u, v⟩
  simp [bicollar, cornerInclusion, icoToI]

theorem attachingCollar_apply (k l : ℕ) (a : AttachingRegion k l) (t : Set.Ico (0 : ℝ) 1) :
    ((attachingCollar k l) (a, t) : StandardHandle k l) =
      (radialStep k (icoToI t) (cellBoundaryInclusion k a.1), a.2) := by
  rcases a with ⟨u, y⟩
  rfl

theorem beltCollar_apply (k l : ℕ) (a : BeltRegion k l) (t : Set.Ico (0 : ℝ) 1) :
    ((beltCollar k l) (a, t) : StandardHandle k l) =
      (a.1, radialStep l (icoToI t) (cellBoundaryInclusion l a.2)) := by
  rcases a with ⟨x, v⟩
  rfl

theorem bicollar_apply (k l : ℕ) (c : Corner k l) (t₁ t₂ : Set.Ico (0 : ℝ) 1) :
    ((bicollar k l) (c, (t₁, t₂)) : StandardHandle k l) =
      (radialStep k (icoToI t₁) (cellBoundaryInclusion k c.1),
        radialStep l (icoToI t₂) (cellBoundaryInclusion l c.2)) := by
  rcases c with ⟨u, v⟩
  rfl

theorem attachingCollar_symm_apply (k l : ℕ) (p : {p : StandardHandle k l // p ∉ cocoreDisk k l}) :
    (attachingCollar k l).symm p =
      ((boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
          (ne_zero_of_not_mem_cocore k l p.2), (p : StandardHandle k l).2),
        ⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
          one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2)⟩) := by
  rfl

theorem beltCollar_symm_apply (k l : ℕ) (p : {p : StandardHandle k l // p ∉ coreDisk k l}) :
    (beltCollar k l).symm p =
      (((p : StandardHandle k l).1,
        boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l p.2)),
        ⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
          one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2)⟩) := by
  rfl

theorem bicollar_symm_apply (k l : ℕ) (p : {p : StandardHandle k l //
      p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l}) :
    (bicollar k l).symm p =
      ((boundaryNormalize ((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))
          (ne_zero_of_not_mem_cocore k l p.2.2),
        boundaryNormalize ((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))
          (ne_zero_of_not_mem_core k l p.2.1)),
        (⟨1 - ‖((p : StandardHandle k l).1 : EuclideanSpace ℝ (Fin k))‖,
            one_minus_norm_mem_Ico (ne_zero_of_not_mem_cocore k l p.2.2)⟩,
          ⟨1 - ‖((p : StandardHandle k l).2 : EuclideanSpace ℝ (Fin l))‖,
            one_minus_norm_mem_Ico (ne_zero_of_not_mem_core k l p.2.1)⟩)) := by
  rfl

theorem swap_attachingCollar (k l : ℕ) (a : AttachingRegion k l) (t : Set.Ico (0 : ℝ) 1) :
    (swap k l ((attachingCollar k l) (a, t)) : StandardHandle l k) =
      (beltCollar l k (Prod.swap a, t) : StandardHandle l k) := by
  rcases a with ⟨u, y⟩
  simp [attachingCollar_apply, beltCollar_apply]

theorem swap_beltCollar (k l : ℕ) (a : BeltRegion k l) (t : Set.Ico (0 : ℝ) 1) :
    (swap k l ((beltCollar k l) (a, t)) : StandardHandle l k) =
      (attachingCollar l k (Prod.swap a, t) : StandardHandle l k) := by
  rcases a with ⟨x, v⟩
  simp [beltCollar_apply, attachingCollar_apply]

theorem swap_bicollar (k l : ℕ) (c : Corner k l) (t₁ t₂ : Set.Ico (0 : ℝ) 1) :
    (swap k l ((bicollar k l) (c, (t₁, t₂))) : StandardHandle l k) =
      (bicollar l k (Prod.swap c, (t₂, t₁)) : StandardHandle l k) := by
  rcases c with ⟨u, v⟩
  simp [bicollar_apply]

theorem bicollar_eq_attaching_belt (k l : ℕ) (c : Corner k l) (t₁ t₂ : Set.Ico (0 : ℝ) 1) :
    ((bicollar k l (c, (t₁, t₂))) : StandardHandle k l) =
      ((attachingCollar k l
        ((c.1, radialStep l (icoToI t₂) (cellBoundaryInclusion l c.2)), t₁)) :
        StandardHandle k l) := by
  rcases c with ⟨u, v⟩
  simp [bicollar_apply, attachingCollar_apply]

theorem bicollar_eq_belt_attaching (k l : ℕ) (c : Corner k l) (t₁ t₂ : Set.Ico (0 : ℝ) 1) :
    ((bicollar k l (c, (t₁, t₂))) : StandardHandle k l) =
      ((beltCollar k l
        ((radialStep k (icoToI t₁) (cellBoundaryInclusion k c.1), c.2), t₂)) :
        StandardHandle k l) := by
  rcases c with ⟨u, v⟩
  simp [bicollar_apply, beltCollar_apply]

theorem swap_attachingCollar_symm (k l : ℕ) (p : {p : StandardHandle k l // p ∉ cocoreDisk k l}) :
    (attachingCollar k l).symm p =
      (Prod.map (Prod.swap : BeltRegion l k → AttachingRegion k l)
        (id : Set.Ico (0 : ℝ) 1 → Set.Ico (0 : ℝ) 1))
        ((beltCollar l k).symm (swapCocoreComplement k l p)) := by
  rw [attachingCollar_symm_apply, beltCollar_symm_apply]
  simp

theorem swap_beltCollar_symm (k l : ℕ) (p : {p : StandardHandle k l // p ∉ coreDisk k l}) :
    (beltCollar k l).symm p =
      (Prod.map (Prod.swap : AttachingRegion l k → BeltRegion k l)
        (id : Set.Ico (0 : ℝ) 1 → Set.Ico (0 : ℝ) 1))
        ((attachingCollar l k).symm (swapCoreComplement k l p)) := by
  rw [beltCollar_symm_apply, attachingCollar_symm_apply]
  simp

theorem swap_bicollar_symm (k l : ℕ) (p : {p : StandardHandle k l //
      p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l}) :
    (bicollar k l).symm p =
      (Prod.map (Prod.swap : Corner l k → Corner k l)
        (fun r : Set.Ico (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1 => (r.2, r.1)))
        ((bicollar l k).symm (swapCoreCocoreComplement k l p)) := by
  rw [bicollar_symm_apply, bicollar_symm_apply]
  simp

theorem attachingCollar_range (k l : ℕ) :
    ((fun z : AttachingRegion k l × Set.Ico (0 : ℝ) 1 =>
      ((attachingCollar k l) z : StandardHandle k l)) '' Set.univ) =
      {p : StandardHandle k l | p ∉ cocoreDisk k l} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (attachingCollar k l z).2
  · intro hp
    refine ⟨(attachingCollar k l).symm ⟨p, hp⟩, trivial, ?_⟩
    exact congrArg (fun q : {p : StandardHandle k l // p ∉ cocoreDisk k l} =>
      (q : StandardHandle k l)) ((attachingCollar k l).right_inv ⟨p, hp⟩)

theorem beltCollar_range (k l : ℕ) :
    ((fun z : BeltRegion k l × Set.Ico (0 : ℝ) 1 =>
      ((beltCollar k l) z : StandardHandle k l)) '' Set.univ) =
      {p : StandardHandle k l | p ∉ coreDisk k l} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (beltCollar k l z).2
  · intro hp
    refine ⟨(beltCollar k l).symm ⟨p, hp⟩, trivial, ?_⟩
    exact congrArg (fun q : {p : StandardHandle k l // p ∉ coreDisk k l} =>
      (q : StandardHandle k l)) ((beltCollar k l).right_inv ⟨p, hp⟩)

theorem bicollar_range (k l : ℕ) :
    ((fun z : Corner k l × Set.Ico (0 : ℝ) 1 × Set.Ico (0 : ℝ) 1 =>
      ((bicollar k l) z : StandardHandle k l)) '' Set.univ) =
      {p : StandardHandle k l | p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (bicollar k l z).2
  · intro hp
    refine ⟨(bicollar k l).symm ⟨p, hp⟩, trivial, ?_⟩
    exact congrArg (fun q : {p : StandardHandle k l //
      p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} => (q : StandardHandle k l))
      ((bicollar k l).right_inv ⟨p, hp⟩)

theorem isClosed_cocoreDisk (k l : ℕ) : IsClosed (cocoreDisk k l) := by
  have h : cocoreDisk k l = (fun p : StandardHandle k l =>
      ((p.1 : ClosedCell k) : EuclideanSpace ℝ (Fin k))) ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin k))) := by
    ext p
    constructor
    · intro hp
      have hp' : p.1 = closedCellCenter k := by simpa [cocoreDisk] using hp
      have hval := congrArg (fun q : ClosedCell k => (q : EuclideanSpace ℝ (Fin k))) hp'
      simpa [closedCellCenter] using hval
    · intro hp
      simpa [cocoreDisk] using (Subtype.ext (by simpa [closedCellCenter] using hp))
  rw [h]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_fst)

theorem isClosed_coreDisk (k l : ℕ) : IsClosed (coreDisk k l) := by
  have h : coreDisk k l = (fun p : StandardHandle k l =>
      ((p.2 : ClosedCell l) : EuclideanSpace ℝ (Fin l))) ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin l))) := by
    ext p
    constructor
    · intro hp
      have hp' : p.2 = closedCellCenter l := by simpa [coreDisk] using hp
      have hval := congrArg (fun q : ClosedCell l => (q : EuclideanSpace ℝ (Fin l))) hp'
      simpa [closedCellCenter] using hval
    · intro hp
      simpa [coreDisk] using (Subtype.ext (by simpa [closedCellCenter] using hp))
  rw [h]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_snd)

theorem isOpen_attachingCollarSet (k l : ℕ) :
    IsOpen {p : StandardHandle k l | p ∉ cocoreDisk k l} := by
  rw [show {p : StandardHandle k l | p ∉ cocoreDisk k l} = (cocoreDisk k l)ᶜ by rfl]
  exact (isClosed_cocoreDisk k l).isOpen_compl

theorem isOpen_beltCollarSet (k l : ℕ) :
    IsOpen {p : StandardHandle k l | p ∉ coreDisk k l} := by
  rw [show {p : StandardHandle k l | p ∉ coreDisk k l} = (coreDisk k l)ᶜ by rfl]
  exact (isClosed_coreDisk k l).isOpen_compl

theorem isOpen_bicollarSet (k l : ℕ) :
    IsOpen {p : StandardHandle k l | p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} := by
  rw [show {p : StandardHandle k l | p ∉ coreDisk k l ∧ p ∉ cocoreDisk k l} =
      (coreDisk k l)ᶜ ∩ (cocoreDisk k l)ᶜ by
    ext p
    simp]
  exact (isClosed_coreDisk k l).isOpen_compl.inter (isClosed_cocoreDisk k l).isOpen_compl

end DifferentialGeometry.Topology.Handle
