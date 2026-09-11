import DifferentialGeometry.Topology.Manifold.Attachment.RadialManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev Retained (B : ℝ) := S2 × Ico (0 : ℝ) B
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem insertionBuffer_pos {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    0 < B := (mul_pos (by norm_num : (0 : ℝ) < 2) hA).trans hAB

abbrev InsertionQuotient {B : ℝ} (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)

private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

def insertedQuotientMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    let hB : 0 < B := insertionBuffer_pos hA hAB
    letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
    SmoothRiemannianMetric (𝓡 3) (InsertionQuotient hB) := by
  let hB : 0 < B := insertionBuffer_pos hA hAB
  exact Diffeomorph.pullbackMetric (insertedMetric hA hAB hη h)
    (radialCapAttachmentDiffeomorph transitionEnd_pos hB)

theorem insertedQuotientMetric_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : InsertionQuotient (insertionBuffer_pos hA hAB)) (v w : TangentSpace (𝓡 3) x) :
    (insertedQuotientMetric hA hAB hη h).inner x v w =
      (insertedMetric hA hAB hη h).inner
        (radialCapAttachmentDiffeomorph transitionEnd_pos (insertionBuffer_pos hA hAB) x)
        (mfderiv (𝓡 3) (𝓡 3)
          (radialCapAttachmentDiffeomorph transitionEnd_pos (insertionBuffer_pos hA hAB)) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (radialCapAttachmentDiffeomorph transitionEnd_pos (insertionBuffer_pos hA hAB)) x w) :=
  Diffeomorph.pullbackMetric_inner _ _ _ _ _

private def retainedInterpolation {A B : ℝ} (hA : 0 < A) : Retained B → insertionCylinder A B :=
  fun q => ⟨(q.1, q.2.val), ⟨by linarith [q.2.property.1], q.2.property.2⟩⟩
private theorem retainedInterpolation_smooth {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    ContMDiff IR IC ∞ (retainedInterpolation (B := B) hA) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  intro q
  exact codRestr_contMDiffAt (I := IR) (J := IC) (V := insertionCylinder A B)
    (fun p => (retainedInterpolation (B := B) hA p).property)
    (contMDiff_fst.prodMk
      ((isSmoothEmbedding_halfClosedInterval_inclusion hB).contMDiff.comp contMDiff_snd)).contMDiffAt

theorem insertedQuotientMetric_retained {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    let hB : 0 < B := insertionBuffer_pos hA hAB
    letI := halfClosedIntervalChartedSpace hB
    ∀ (q : Retained B) (v w : TangentSpace IR q),
      (insertedQuotientMetric hA hAB hη h).inner
        (adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB) q)
        (mfderiv IR (𝓡 3)
          (adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) q v)
        (mfderiv IR (𝓡 3)
          (adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) q w) =
      h.inner ⟨(q.1, q.2.val), ⟨by linarith [q.2.property.1], q.2.property.2⟩⟩
        (mfderiv IR IC (fun p : Retained B => (p.1, p.2.val)) q v)
        (mfderiv IR IC (fun p : Retained B => (p.1, p.2.val)) q w) := by
  let hB : 0 < B := insertionBuffer_pos hA hAB
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  dsimp only
  intro q v w
  let d := radialCapAttachmentDiffeomorph transitionEnd_pos hB
  let j := adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
  let ρ := retainedInterpolation (B := B) hA
  have hj : ContMDiff IR (𝓡 3) ∞ j :=
    (isSmoothEmbedding_radialCapAttachment_retained transitionEnd_pos hB).contMDiff
  have hρ : ContMDiff IR IC ∞ ρ := retainedInterpolation_smooth hA hB
  have heq : (d ∘ j : Retained B → insertionBall B) = insertionMap hA hAB ∘ ρ := by
    funext p
    apply Subtype.ext
    change (transitionEnd + p.2.val) • p.1.val = conformalRadius p.2.val • p.1.val
    rw [conformalRadius_cylindrical p.2.property.1]
  have hpoint : d (j q) = insertionMap hA hAB (ρ q) := congrFun heq q
  have hdiff (u : TangentSpace IR q) :
      mfderiv (𝓡 3) (𝓡 3) d (j q) (mfderiv IR (𝓡 3) j q u) =
        mfderiv IC (𝓡 3) (insertionMap hA hAB) (ρ q) (mfderiv IR IC ρ q u) := by
    have hh := congrArg (β := TangentSpace IR q →L[ℝ] E3)
      (fun f : Retained B → insertionBall B => mfderiv IR (𝓡 3) f q) heq
    erw [mfderiv_comp q (d.contMDiff.mdifferentiableAt (by decide))
        (hj.mdifferentiableAt (by decide)),
      mfderiv_comp q ((contMDiff_insertionMap hA hAB).mdifferentiableAt (by decide))
        (hρ.mdifferentiableAt (by decide))] at hh
    exact congrArg (fun D => D u) hh
  have hcoord (u : TangentSpace IR q) :
      mfderiv IR IC ρ q u =
        mfderiv IR IC (fun p : Retained B => (p.1, p.2.val)) q u := by
    have hh := mfderiv_comp q
      ((contMDiff_subtype_val (I := IC) (U := insertionCylinder A B) (n := ∞)).mdifferentiableAt (by decide))
      (hρ.mdifferentiableAt (by decide))
    rw [mfderiv_subtype_val] at hh
    exact (congrArg (fun D => D u) hh).symm
  rw [insertedQuotientMetric_inner]
  change (insertedMetric hA hAB hη h).inner (d (j q))
    (mfderiv (𝓡 3) (𝓡 3) d (j q) (mfderiv IR (𝓡 3) j q v))
    (mfderiv (𝓡 3) (𝓡 3) d (j q) (mfderiv IR (𝓡 3) j q w)) = _
  rw [hdiff, hdiff]
  erw [hpoint]
  rw [insertedMetric_retained hA hAB hη h (ρ q) q.2.property.1, hcoord, hcoord]
  rfl

theorem insertedQuotientMetric_cap {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    let hB : 0 < B := insertionBuffer_pos hA hAB
    letI := closedBallChartedSpace transitionEnd_pos
    ∀ (x : Cap) (v w : TangentSpace (𝓡∂ 3) x),
      (insertedQuotientMetric hA hAB hη h).inner
        (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x)
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x w) =
      (insertedMetric hA hAB hη h).inner
        ⟨x.val, by change ‖x.val‖ < transitionEnd + B; linarith [x.property]⟩
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x w) := by
  let hB : 0 < B := insertionBuffer_pos hA hAB
  let := closedBallChartedSpace transitionEnd_pos
  let := closedBall_isManifold transitionEnd_pos
  dsimp only
  intro x v w
  let d := radialCapAttachmentDiffeomorph transitionEnd_pos hB
  let j := adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
  have hj : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ j :=
    (isSmoothEmbedding_radialCapAttachment_cap transitionEnd_pos hB).contMDiff
  have hdj : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (d ∘ j : Cap → insertionBall B) :=
    d.contMDiff.comp hj
  have hdiff (u : TangentSpace (𝓡∂ 3) x) :
      mfderiv (𝓡 3) (𝓡 3) d (j x) (mfderiv (𝓡∂ 3) (𝓡 3) j x u) =
        mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x u := by
    have h1 := mfderiv_comp x
      ((contMDiff_subtype_val (I := 𝓡 3) (U := insertionBall B) (n := ∞)).mdifferentiableAt (by decide))
      (hdj.mdifferentiableAt (by decide))
    have h2 := mfderiv_comp x (d.contMDiff.mdifferentiableAt (by decide))
      (hj.mdifferentiableAt (by decide))
    rw [mfderiv_subtype_val] at h1
    have h1u := congrArg (fun D => D u) h1
    have h2u := congrArg (fun D => D u) h2
    exact h2u.symm.trans h1u.symm
  rw [insertedQuotientMetric_inner]
  change (insertedMetric hA hAB hη h).inner (d (j x))
    (mfderiv (𝓡 3) (𝓡 3) d (j x) (mfderiv (𝓡∂ 3) (𝓡 3) j x v))
    (mfderiv (𝓡 3) (𝓡 3) d (j x) (mfderiv (𝓡∂ 3) (𝓡 3) j x w)) = _
  rw [hdiff, hdiff]
  rfl

theorem insertedQuotientMetric_cap_of_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    let hB : 0 < B := insertionBuffer_pos hA hAB
    letI := closedBallChartedSpace transitionEnd_pos
    ∀ (x : Cap), ‖x.val‖ < conformalRadius (-7 * A / 4) →
      ∀ (v w : TangentSpace (𝓡∂ 3) x),
      (insertedQuotientMetric hA hAB hη h).inner
        (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x)
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x w) =
      η * metric.inner x.val
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x w) := by
  let := closedBallChartedSpace transitionEnd_pos
  dsimp only
  intro x hx v w
  let p : insertionBall B := ⟨x.val, by
    change ‖x.val‖ < transitionEnd + B
    have hB := insertionBuffer_pos hA hAB
    linarith [x.property]⟩
  have hcap := insertedQuotientMetric_cap hA hAB hη h x v w
  have hinner := insertedMetric_inner_of_inner hA hAB hη h p hx
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x v)
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Cap → E3) x w)
  exact hcap.trans hinner

end DifferentialGeometry.PDE.RicciFlow.StandardCap
