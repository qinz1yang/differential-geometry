import DifferentialGeometry.Topology.Manifold.Attachment.RadialManifold

set_option autoImplicit false
noncomputable section
open Set Function Manifold IsManifold TopologicalSpace
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev Retained (B : ℝ) := S2 × Ico (0 : ℝ) B
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

abbrev retainedFace (B : ℝ) := {q : Retained B // q.2.val = 0}

def retainedFaceHomeomorph {B : ℝ} (hB : 0 < B) : S2 ≃ₜ retainedFace B where
  toFun y := ⟨retainedBoundary hB y, rfl⟩
  invFun q := q.val.1
  left_inv _ := rfl
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact q.property.symm
  continuous_toFun := Continuous.subtype_mk (continuous_id.prodMk continuous_const) _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

@[reducible] def retainedFaceChartedSpace {B : ℝ} (hB : 0 < B) :
    ChartedSpace E2 (retainedFace B) :=
  chartedSpaceOfHomeomorph (M := S2) (retainedFaceHomeomorph hB).symm

theorem retainedFace_isManifold {B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    IsManifold (𝓡 2) ∞ (retainedFace B) := by
  let := retainedFaceChartedSpace hB
  exact @isManifoldOfHomeomorph ℝ _ E2 E2 _ _ _ (𝓡 2) S2 _
    inferInstance ∞ (retainedFace B) _ (retainedFaceHomeomorph hB).symm inferInstance

def retainedFaceDiffeomorph {B : ℝ} (hB : 0 < B) :
    letI := retainedFaceChartedSpace hB
    S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ retainedFace B := by
  let := retainedFaceChartedSpace hB
  let e := retainedFaceHomeomorph hB
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e.symm (𝓡 2) ∞
      contMDiff_invFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e.symm (𝓡 2) ∞ }

def radialCapGluingDiffeomorph {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    letI := retainedFaceChartedSpace hB
    BoundaryManifold (𝓡∂ 3) (Cap L) ≃ₘ⟮𝓡 2, 𝓡 2⟯ retainedFace B := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let := retainedFaceChartedSpace hB
  exact (closedBallBoundaryDiffeomorph hL).trans (retainedFaceDiffeomorph hB)

theorem radialCapGluingDiffeomorph_coherence {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    letI := retainedFaceChartedSpace hB
    ∀ b : BoundaryManifold (𝓡∂ 3) (Cap L),
      adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) b.val =
        adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)
          (radialCapGluingDiffeomorph hL hB b).val := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let := retainedFaceChartedSpace hB
  intro b
  have hb : radialCapBoundary hL (closedBallBoundaryDiffeomorph hL b) = b.val := by
    apply Subtype.ext
    change L • (L⁻¹ • b.val.val) = b.val.val
    simp [smul_smul, hL.ne']
  have h := adjunction_coherence (radialCapBoundary hL) (retainedBoundary hB)
    (closedBallBoundaryDiffeomorph hL b)
  rw [hb] at h
  exact h

theorem radialCapAttachment_inclusions_cover {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    range (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB)) ∪
      range (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  induction p using Quot.inductionOn with
  | h q =>
    rcases q with x | y
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨y, rfl⟩

theorem radialCapAttachment_cap_eq_retained_iff {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Cap L) (q : Retained B) :
    adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x =
      adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) q ↔
      x = radialCapBoundary hL q.1 ∧ q.2.val = 0 := by
  constructor
  · intro he
    have hr := congrArg (fun p => (radialCapAttachmentHomeomorph hL hB p : E3)) he
    change x.val = (L + q.2.val) • q.1.val at hr
    have hn := x.property
    rw [hr, norm_smul, Real.norm_eq_abs,
      abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one] at hn
    have hzero : q.2.val = 0 := le_antisymm (by linarith) q.2.property.1
    refine ⟨?_, hzero⟩
    apply Subtype.ext
    change x.val = L • q.1.val
    simpa only [hzero, add_zero] using hr
  · rintro ⟨hx, hq⟩
    have he : retainedBoundary hB q.1 = q := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact hq.symm
    rw [hx, ← he]
    exact adjunction_coherence (radialCapBoundary hL) (retainedBoundary hB) q.1

theorem radialCapAttachment_inclusions_inter {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    range (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB)) ∩
        range (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) =
      range (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) ∘ radialCapBoundary hL) := by
  ext p
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨q, hq⟩⟩
    have he := (radialCapAttachment_cap_eq_retained_iff hL hB x q).mp (hx.trans hq.symm)
    exact ⟨q.1, by change adjunctionCell _ _ (radialCapBoundary hL q.1) = p; rw [← he.1]; exact hx⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨radialCapBoundary hL y, rfl⟩,
      ⟨retainedBoundary hB y, (adjunction_coherence (radialCapBoundary hL) (retainedBoundary hB) y).symm⟩⟩

theorem radialCapAttachment_tip_interior {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    let x : Cap L := ⟨0, by simpa using hL.le⟩
    x ∉ (𝓡∂ 3).boundary (Cap L) ∧
      adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x ∉
        range (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) := by
  let := closedBallChartedSpace hL
  let x : Cap L := ⟨0, by simpa using hL.le⟩
  constructor
  · rw [closedBall_boundary_eq_sphere hL]
    change ¬ ‖(0 : E3)‖ = L
    simpa only [norm_zero] using ne_of_lt hL
  · rintro ⟨q, hq⟩
    have he := (radialCapAttachment_cap_eq_retained_iff hL hB x q).mp hq.symm
    have hn := congrArg (fun y : Cap L => ‖y.val‖) he.1
    change ‖(0 : E3)‖ = ‖L • q.1.val‖ at hn
    rw [norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hL,
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one] at hn
    exact hL.ne' hn.symm

end DifferentialGeometry.Topology.Manifold.Attachment
