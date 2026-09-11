import DifferentialGeometry.Topology.Attachment.Union
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev Retained (B : ℝ) := S2 × Ico (0 : ℝ) B
private abbrev Ball (L B : ℝ) := {x : E3 // ‖x‖ < L + B}
private abbrev Shell (L B : ℝ) := {x : Ball L B // L ≤ ‖x.val‖}

def radialCapBoundary {L : ℝ} (hL : 0 < L) : S2 → Cap L :=
  fun y => ⟨L • (y : E3), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL,
      mem_sphere_zero_iff_norm.mp y.property, mul_one]⟩

def retainedBoundary {B : ℝ} (hB : 0 < B) : S2 → Retained B :=
  fun y => (y, ⟨0, ⟨le_rfl, hB⟩⟩)

private def retainedRadial {L B : ℝ} (q : Retained B) : E3 :=
  (L + q.2.val) • (q.1 : E3)

private theorem retainedRadial_norm {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    ‖retainedRadial (L := L) q‖ = L + q.2.val := by
  change ‖(L + q.2.val) • (q.1 : E3)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
    mem_sphere_zero_iff_norm.mp q.1.property, mul_one]

private def retainedToShell {L B : ℝ} (hL : 0 < L) (q : Retained B) : Shell L B :=
  ⟨⟨retainedRadial (L := L) q, by
    rw [retainedRadial_norm hL]
    linarith [q.2.property.2]⟩, by
    rw [retainedRadial_norm hL]
    exact le_add_of_nonneg_right q.2.property.1⟩

private def shellPunctured {L B : ℝ} (hL : 0 < L) (x : Shell L B) : ({0}ᶜ : Set E3) :=
  ⟨x.val.val, by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      norm_pos_iff.mp (hL.trans_le x.property)⟩

private def shellToRetained {L B : ℝ} (hL : 0 < L) (x : Shell L B) : Retained B :=
  ((homeomorphUnitSphereProd E3 (shellPunctured hL x)).1,
    ⟨‖x.val.val‖ - L, ⟨sub_nonneg.mpr x.property, by linarith [x.val.property]⟩⟩)

def retainedCylinderHomeomorphShell {L B : ℝ} (hL : 0 < L) :
    Retained B ≃ₜ Shell L B where
  toFun := retainedToShell hL
  invFun := shellToRetained hL
  left_inv q := by
    apply Prod.ext
    · change (homeomorphUnitSphereProd E3
        ((homeomorphUnitSphereProd E3).symm
          (q.1, ⟨L + q.2.val, add_pos_of_pos_of_nonneg hL q.2.property.1⟩))).1 = q.1
      rw [Homeomorph.apply_symm_apply]
    · apply Subtype.ext
      change ‖retainedRadial (L := L) q‖ - L = q.2.val
      rw [retainedRadial_norm hL]
      ring
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (L + (‖x.val.val‖ - L)) •
      ((homeomorphUnitSphereProd E3 (shellPunctured hL x)).1 : E3) = x.val.val
    rw [show L + (‖x.val.val‖ - L) = ‖x.val.val‖ by ring]
    have h := congrArg (fun y : ({0}ᶜ : Set E3) => y.val)
      ((homeomorphUnitSphereProd E3).symm_apply_apply
        (shellPunctured hL x))
    simpa only [homeomorphUnitSphereProd_symm_apply_coe,
      homeomorphUnitSphereProd_apply_snd_coe, shellPunctured] using h
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const.add (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp ((homeomorphUnitSphereProd E3).continuous.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
    · exact ((continuous_norm.comp
        (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const).subtype_mk _

theorem retainedCylinderHomeomorphShell_apply {L B : ℝ} (hL : 0 < L)
    (q : Retained B) :
    ((retainedCylinderHomeomorphShell hL q).val : E3) =
      (L + q.2.val) • (q.1 : E3) := rfl

theorem retainedCylinderHomeomorphShell_symm_snd {L B : ℝ} (hL : 0 < L)
    (x : Shell L B) :
    ((retainedCylinderHomeomorphShell hL).symm x).2.val = ‖x.val.val‖ - L := rfl

private def capInclusion {L B : ℝ} (hB : 0 < B) : Cap L → Ball L B :=
  fun x => ⟨x.val, by linarith [x.property]⟩

private theorem capInclusion_injective {L B : ℝ} (hB : 0 < B) :
    Injective (capInclusion (L := L) hB) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Ball L B => z.val) h)

private theorem capInclusion_continuous {L B : ℝ} (hB : 0 < B) :
    Continuous (capInclusion (L := L) hB) :=
  continuous_subtype_val.subtype_mk _

private theorem shell_isClosed (L B : ℝ) :
    IsClosed {x : Ball L B | L ≤ ‖x.val‖} :=
  isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)

private theorem cap_isCompact (L : ℝ) : IsCompact {x : E3 | ‖x‖ ≤ L} := by
  have he : {x : E3 | ‖x‖ ≤ L} = Metric.closedBall (0 : E3) L := by
    ext x
    simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact isCompact_closedBall 0 L

private theorem capInclusion_boundary {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Cap L) (hx : L ≤ ‖(capInclusion hB x).val‖) :
    x ∈ range (radialCapBoundary hL) := by
  have hxnorm : ‖x.val‖ = L := le_antisymm x.property hx
  let p : ({0}ᶜ : Set E3) :=
    ⟨x.val, by simpa only [mem_compl_iff, mem_singleton_iff] using
      norm_pos_iff.mp (by rw [hxnorm]; exact hL)⟩
  refine ⟨(homeomorphUnitSphereProd E3 p).1, ?_⟩
  apply Subtype.ext
  change L • ((homeomorphUnitSphereProd E3 p).1 : E3) = x.val
  have h := congrArg (fun y : ({0}ᶜ : Set E3) => y.val)
    ((homeomorphUnitSphereProd E3).symm_apply_apply p)
  simpa only [homeomorphUnitSphereProd_symm_apply_coe,
    homeomorphUnitSphereProd_apply_snd_coe, p, hxnorm] using h

private theorem shell_union_range_capInclusion {L B : ℝ} (hB : 0 < B) :
    {x : Ball L B | L ≤ ‖x.val‖} ∪ range (capInclusion (L := L) hB) = univ := by
  ext x
  constructor
  · intro _
    exact mem_univ x
  · intro _
    by_cases hx : L ≤ ‖x.val‖
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x.val, (lt_of_not_ge hx).le⟩, Subtype.ext rfl⟩

private theorem retainedBoundary_capInclusion {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (y : S2) :
    (retainedCylinderHomeomorphShell hL (retainedBoundary hB y)).val =
      capInclusion hB (radialCapBoundary hL y) := by
  apply Subtype.ext
  change (L + 0) • (y : E3) = L • (y : E3)
  rw [add_zero]

def radialCapAttachmentHomeomorph {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB) ≃ₜ
      {x : E3 // ‖x‖ < L + B} := by
  letI : CompactSpace (Cap L) := isCompact_iff_compactSpace.mp (cap_isCompact L)
  let H := retainedCylinderHomeomorphShell (B := B) hL
  let i := radialCapBoundary hL
  let φ := retainedBoundary hB
  let c := capInclusion (L := L) hB
  let Q := adjunctionHomeomorphUnionImage i (H ∘ φ) c
    (retainedBoundary_capInclusion hL hB)
    (capInclusion_injective hB) (capInclusion_continuous hB)
    (capInclusion_boundary hL hB) (shell_isClosed L B)
  exact ((adjunctionHomeoOfLowerEquiv i φ H).symm.trans Q).trans
    ((Homeomorph.setCongr (shell_union_range_capInclusion (L := L) hB)).trans
      (Homeomorph.Set.univ (Ball L B)))

theorem radialCapAttachmentHomeomorph_cap {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Cap L) :
    (radialCapAttachmentHomeomorph hL hB
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x) : E3) = x.val := rfl

theorem radialCapAttachmentHomeomorph_retained {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (q : Retained B) :
    (radialCapAttachmentHomeomorph hL hB
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) q) : E3) =
      (L + q.2.val) • (q.1 : E3) := rfl

end DifferentialGeometry.Topology.Manifold.Attachment
