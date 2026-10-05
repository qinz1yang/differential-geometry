import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcTraceManifold
import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalOrCircle
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# FC39 GROUP G arcs (A4): the components of a trace are embedded arcs and circles

Lane FC39-G-ARC (external draft 58 §四 A4, disposition D58-5). The weakest classification the arc
layer needs, for the compact one-manifold `R.traceSet_GARC i` (`FC39GArcTraceManifold.lean`), with
no surface classification and no FC40:

* `CircleRegion.trace_component_val_isSmoothEmbedding_GARC` — a component, included in the base,
  is a smooth embedding (composition with the open inclusion);
* `CircleRegion.exists_trace_arcs_loops_GARC` — **the trace is the disjoint union of finitely
  many embedded arcs `[0, 1] → Base` and embedded circles `Circle → Base`**, with intrinsic
  boundary: a point of an arc is a second zero exactly at the two ends, a circle has none.

The components are those of the trace (`OneManifold.finite_connectedComponents_and_Icc_or_circle`);
boundary points are transported by the diffeomorphisms (`Diffeomorph.preimage_boundary`,
`ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val`, `boundary_Icc`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold.OneManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

variable {W : CompactCarrier.{u}} (R : CircleRegion W) (i : Fin R.definingCount)

/-- A component of the trace, included in the base. -/
def CircleRegion.traceComponentVal_GARC (x : R.traceSet_GARC i) :
    componentOpens x → R.Base :=
  fun y => y.1.1

/-- **A component of the trace is smoothly embedded in the base.** -/
theorem CircleRegion.trace_component_val_isSmoothEmbedding_GARC (x : R.traceSet_GARC i) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (R.traceComponentVal_GARC i x) :=
  (R.trace_val_isSmoothEmbedding_GARC i).comp_of_smoothBoundary
    (IsSmoothEmbedding.of_opens (componentOpens x))

/-- The range of a component in the base. -/
theorem CircleRegion.range_traceComponentVal_GARC (x : R.traceSet_GARC i) :
    range (R.traceComponentVal_GARC i x) = Subtype.val '' connectedComponent x := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- An end point of `[0, 1]` (in the certificate convention `iccEnd`) is a boundary point, and
conversely. -/
theorem icc_isBoundaryPoint_iff_GARC {t : Icc (0 : ℝ) 1} :
    (𝓡∂ 1).IsBoundaryPoint t ↔ (t = iccEnd false ∨ t = iccEnd true) := by
  have h := congrArg (t ∈ ·) (boundary_Icc (x := (0 : ℝ)) (y := 1))
  simp only [eq_iff_iff] at h
  change (𝓡∂ 1).IsBoundaryPoint t ↔ _ at h
  rw [h]
  have h0 : (⊥ : Icc (0 : ℝ) 1) = iccEnd false := rfl
  have h1 : (⊤ : Icc (0 : ℝ) 1) = iccEnd true := rfl
  simp [h0, h1]

/-- A point of an arc component (the image of `t` under the inverse of a diffeomorphism onto
`[0, 1]`) is a second zero exactly at the end points. -/
theorem CircleRegion.traceBd_arc_iff_GARC (x : R.traceSet_GARC i)
    (e : componentOpens x ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) {t : Icc (0 : ℝ) 1} :
    R.traceBd_GARC i (R.traceComponentVal_GARC i x (e.symm t)) ↔
      (t = iccEnd false ∨ t = iccEnd true) := by
  rw [← icc_isBoundaryPoint_iff_GARC]
  change R.traceBd_GARC i (e.symm t).1.1 ↔ _
  rw [← CircleRegion.trace_isBoundaryPoint_iff_GARC,
    ← ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val]
  have hb := congrArg (t ∈ ·) (e.symm.preimage_boundary (by simp))
  simp only [eq_iff_iff] at hb
  exact hb

/-- A circle component has no second zero. -/
theorem CircleRegion.not_traceBd_loop_GARC (x : R.traceSet_GARC i)
    (e : Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens x) (z : Circle) :
    ¬ R.traceBd_GARC i (R.traceComponentVal_GARC i x (e z)) := by
  change ¬ R.traceBd_GARC i (e z).1.1
  rw [← CircleRegion.trace_isBoundaryPoint_iff_GARC,
    ← ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val]
  intro hz
  have hb := congrArg (z ∈ ·) (e.preimage_boundary (by simp))
  simp only [eq_iff_iff] at hb
  have hz' : z ∈ (𝓡 1).boundary Circle := hb.mp hz
  rw [ModelWithCorners.Boundaryless.boundary_eq_empty] at hz'
  exact hz'

/-- An arc component, parametrized by `[0, 1]`, is a smooth embedding. -/
theorem CircleRegion.arc_isSmoothEmbedding_GARC (x : R.traceSet_GARC i)
    (e : componentOpens x ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (R.traceComponentVal_GARC i x ∘ e.symm) :=
  (R.trace_component_val_isSmoothEmbedding_GARC i x).comp_diffeomorph e.symm

/-- A circle component, parametrized by the circle, is a smooth embedding. -/
theorem CircleRegion.loop_isSmoothEmbedding_GARC (x : R.traceSet_GARC i)
    (e : Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens x) :
    IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (R.traceComponentVal_GARC i x ∘ e) := by
  have hg := R.trace_component_val_isSmoothEmbedding_GARC i x
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
    (hg.contMDiff.comp e.contMDiff) fun z => ?_, hg.isEmbedding.comp e.toHomeomorph.isEmbedding⟩
  have hgd : MDifferentiableAt (𝓡∂ 1) (𝓡 2) (R.traceComponentVal_GARC i x) (e z) :=
    (hg.contMDiff (e z)).mdifferentiableAt (by simp)
  have hed : MDifferentiableAt (𝓡 1) (𝓡∂ 1) e z :=
    (e.contMDiff z).mdifferentiableAt (by simp)
  rw [mfderiv_comp z hgd hed]
  refine (hg.isImmersion.mfderiv_injective (by simp) (e z)).comp ?_
  rw [← e.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (e.mfderivToContinuousLinearEquiv (by simp) z).injective

/-- Distinct connected components of the trace have disjoint images in the base. -/
theorem CircleRegion.disjoint_component_image_GARC {x y : R.traceSet_GARC i}
    (h : (ConnectedComponents.mk x : ConnectedComponents (R.traceSet_GARC i)) ≠
      ConnectedComponents.mk y) :
    Disjoint (Subtype.val '' connectedComponent x) (Subtype.val '' connectedComponent y) := by
  rw [disjoint_image_iff Subtype.val_injective]
  refine connectedComponent_disjoint fun hc => h ?_
  exact ConnectedComponents.coe_eq_coe.mpr hc

/-- **The trace is a finite disjoint union of embedded arcs and embedded circles**, with intrinsic
boundary: a point of an arc is a second zero exactly at `t = 0, 1`; a circle has no second zero. -/
theorem CircleRegion.exists_trace_arcs_loops_GARC :
    ∃ (na nl : ℕ) (arc : Fin na → Icc (0 : ℝ) 1 → R.Base) (loop : Fin nl → Circle → R.Base),
      (∀ a, IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (arc a)) ∧
      (∀ a, IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (loop a)) ∧
      (Pairwise fun a a' => Disjoint (range (arc a)) (range (arc a'))) ∧
      (Pairwise fun a a' => Disjoint (range (loop a)) (range (loop a'))) ∧
      (∀ a a', Disjoint (range (arc a)) (range (loop a'))) ∧
      (⋃ a, range (arc a)) ∪ (⋃ a, range (loop a)) = R.traceSet_GARC i ∧
      (∀ a t, R.traceBd_GARC i (arc a t) ↔ (t = iccEnd false ∨ t = iccEnd true)) ∧
      ∀ a z, ¬ R.traceBd_GARC i (loop a z) := by
  classical
  obtain ⟨hfin, hclass⟩ := finite_connectedComponents_and_Icc_or_circle (M := R.traceSet_GARC i)
  let rep : ConnectedComponents (R.traceSet_GARC i) → R.traceSet_GARC i := fun κ => κ.out
  have hrep : ∀ κ, ConnectedComponents.mk (rep κ) = κ := fun κ => Quotient.out_eq κ
  let IsArc : ConnectedComponents (R.traceSet_GARC i) → Prop := fun κ =>
    Nonempty (componentOpens (rep κ) ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1)
  let Ka := {κ // IsArc κ}
  let Kl := {κ // ¬ IsArc κ}
  have eKl : ∀ κ : Kl, Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens (rep κ.1)) :=
    fun κ => (hclass (rep κ.1)).resolve_left κ.2
  let fa := Finite.equivFin Ka
  let fl := Finite.equivFin Kl
  let ea : ∀ a, componentOpens (rep (fa.symm a).1) ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1 :=
    fun a => (fa.symm a).2.some
  let el : ∀ a, Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens (rep (fl.symm a).1) :=
    fun a => (eKl (fl.symm a)).some
  let arc : Fin (Nat.card Ka) → Icc (0 : ℝ) 1 → R.Base := fun a =>
    R.traceComponentVal_GARC i (rep (fa.symm a).1) ∘ (ea a).symm
  let loop : Fin (Nat.card Kl) → Circle → R.Base := fun a =>
    R.traceComponentVal_GARC i (rep (fl.symm a).1) ∘ el a
  have harc : ∀ a, range (arc a) = Subtype.val '' connectedComponent (rep (fa.symm a).1) :=
    fun a => ((ea a).symm.surjective.range_comp _).trans (R.range_traceComponentVal_GARC i _)
  have hloop : ∀ a, range (loop a) = Subtype.val '' connectedComponent (rep (fl.symm a).1) :=
    fun a => ((el a).surjective.range_comp _).trans (R.range_traceComponentVal_GARC i _)
  have hdisj : ∀ κ κ' : ConnectedComponents (R.traceSet_GARC i), κ ≠ κ' →
      Disjoint (Subtype.val '' connectedComponent (rep κ))
        (Subtype.val '' connectedComponent (rep κ')) := fun κ κ' h =>
    R.disjoint_component_image_GARC i (by rw [hrep, hrep]; exact h)
  refine ⟨Nat.card Ka, Nat.card Kl, arc, loop, fun a => R.arc_isSmoothEmbedding_GARC i _ (ea a),
    fun a => R.loop_isSmoothEmbedding_GARC i _ (el a), ?_, ?_, ?_, ?_,
    fun a _ => R.traceBd_arc_iff_GARC i _ (ea a), fun a z => R.not_traceBd_loop_GARC i _ (el a) z⟩
  · intro a a' h
    rw [harc, harc]
    refine hdisj _ _ fun hκ => h (fa.symm.injective (Subtype.ext hκ))
  · intro a a' h
    rw [hloop, hloop]
    refine hdisj _ _ fun hκ => h (fl.symm.injective (Subtype.ext hκ))
  · intro a a'
    rw [harc, hloop]
    refine hdisj _ _ fun hκ => (fl.symm a').2 ?_
    rw [← hκ]
    exact (fa.symm a).2
  · apply Subset.antisymm
    · refine union_subset (iUnion_subset fun a => ?_) (iUnion_subset fun a => ?_)
      · rw [harc]
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      · rw [hloop]
        rintro _ ⟨y, -, rfl⟩
        exact y.2
    · intro c hc
      let y : R.traceSet_GARC i := ⟨c, hc⟩
      let κ : ConnectedComponents (R.traceSet_GARC i) := ConnectedComponents.mk y
      have hy : y ∈ connectedComponent (rep κ) := by
        have : connectedComponent (rep κ) = connectedComponent y :=
          ConnectedComponents.coe_eq_coe.mp (hrep κ)
        rw [this]
        exact mem_connectedComponent
      by_cases hk : IsArc κ
      · left
        refine mem_iUnion.mpr ⟨fa ⟨κ, hk⟩, ?_⟩
        rw [harc, Equiv.symm_apply_apply]
        exact ⟨y, hy, rfl⟩
      · right
        refine mem_iUnion.mpr ⟨fl ⟨κ, hk⟩, ?_⟩
        rw [hloop, Equiv.symm_apply_apply]
        exact ⟨y, hy, rfl⟩

end GC.GraphManifold.Assembly
