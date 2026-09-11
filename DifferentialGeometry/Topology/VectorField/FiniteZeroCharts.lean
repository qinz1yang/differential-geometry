import DifferentialGeometry.Topology.Manifold.FiniteInteriorCharts
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]
  (V : ∀ x : M, TangentSpace I x)

theorem exists_pairwise_disjoint_zero_charts (hfinite : {x | V x = 0}.Finite)
    (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x) :
    ∃ (c : {x | V x = 0} → PartialDiffeomorph I 𝓘(ℝ,E) M E ∞)
      (r R : {x | V x = 0} → ℝ),
      (∀ p, p.val ∈ (c p).source) ∧
      (∀ p, 0 < r p ∧ r p < R p) ∧
      (∀ p, closedBall (c p p.val) (R p) ⊆ (c p).target) ∧
      Pairwise (fun p q => Disjoint
        ((c p).symm '' closedBall (c p p.val) (R p))
        ((c q).symm '' closedBall (c q q.val) (R q))) ∧
      ∀ p,
        IsCompact ((c p).symm '' closedBall (c p p.val) (R p)) ∧
        p.val ∈ (c p).symm '' ball (c p p.val) (r p) ∧
        (∀ x ∈ (c p).symm '' closedBall (c p p.val) (R p), V x = 0 ↔ x = p.val) ∧
        (∀ y ∈ closedBall (c p p.val) (R p),
          _root_.VectorField.mpullback 𝓘(ℝ,E) I (c p).symm V y = 0 ↔ y = c p p.val) ∧
        (∀ y ∈ closedBall (c p p.val) (R p), r p ≤ dist y (c p p.val) →
          V ((c p).symm y) ≠ 0 ∧
            _root_.VectorField.mpullback 𝓘(ℝ,E) I (c p).symm V y ≠ 0) ∧
        (∀ y ∈ sphere (c p p.val) (R p),
          V ((c p).symm y) ≠ 0 ∧
            _root_.VectorField.mpullback 𝓘(ℝ,E) I (c p).symm V y ≠ 0) := by
  obtain ⟨R,hR,hRt,hdis,hone⟩ :=
    DifferentialGeometry.Manifold.exists_pairwise_disjoint_interiorChart_closedBalls I hfinite hinterior
  let c : {x | V x = 0} → PartialDiffeomorph I 𝓘(ℝ,E) M E ∞ :=
    fun p => DifferentialGeometry.Manifold.interiorChart I ∞ p.val
  have hsource (p : {x | V x = 0}) : p.val ∈ (c p).source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ p.val).mpr (hinterior p p.property)
  have hr (p : {x | V x = 0}) : 0 < R p / 2 ∧ R p / 2 < R p :=
    ⟨half_pos (hR p),half_lt_self (hR p)⟩
  have hzero (p : {x | V x = 0}) (x : M)
      (hx : x ∈ (c p).symm '' closedBall (c p p.val) (R p)) : V x = 0 ↔ x = p.val := by
    constructor
    · intro hz
      exact mem_singleton_iff.mp ((hone p) ▸ (show x ∈
        ((c p).symm '' closedBall (c p p.val) (R p)) ∩ {x | V x = 0} from ⟨hx,hz⟩))
    · rintro rfl
      exact p.property
  have hcoordinate (p : {x | V x = 0}) (y : E) (hy : y ∈ closedBall (c p p.val) (R p)) :
      V ((c p).symm y) = 0 ↔ y = c p p.val := by
    rw [hzero p _ ⟨y,hy,rfl⟩]
    constructor
    · intro he
      have hh := congrArg (fun x : M => c p x) he
      exact ((c p).right_inv (hRt p hy)).symm.trans hh
    · intro he
      exact he ▸ (c p).left_inv (hsource p)
  have hpullback (p : {x | V x = 0}) (y : E) (hy : y ∈ closedBall (c p p.val) (R p)) :
      _root_.VectorField.mpullback 𝓘(ℝ,E) I (c p).symm V y = 0 ↔ y = c p p.val :=
    (mpullback_partialDiffeomorph_eq_zero_iff (c p).symm (by simp) V (hRt p hy)).trans
      (hcoordinate p y hy)
  have hannulus (p : {x | V x = 0}) (y : E) (hy : y ∈ closedBall (c p p.val) (R p))
      (hyr : R p / 2 ≤ dist y (c p p.val)) :
      V ((c p).symm y) ≠ 0 ∧ _root_.VectorField.mpullback 𝓘(ℝ,E) I (c p).symm V y ≠ 0 := by
    have hne : y ≠ c p p.val := by
      intro he
      have h := hyr
      rw [he,dist_self] at h
      exact (not_le_of_gt (hr p).1) h
    exact ⟨fun hz => hne ((hcoordinate p y hy).mp hz),
      fun hz => hne ((hpullback p y hy).mp hz)⟩
  refine ⟨c,fun p => R p / 2,R,hsource,hr,hRt,hdis,fun p => ?_⟩
  refine ⟨(isCompact_closedBall (c p p.val) (R p)).image_of_continuousOn
    ((c p).symm.toOpenPartialHomeomorph.continuousOn.mono (hRt p)),
    ⟨c p p.val,mem_ball_self (hr p).1,(c p).left_inv (hsource p)⟩,
    hzero p,hpullback p,hannulus p,?_⟩
  intro y hy
  apply hannulus p y (sphere_subset_closedBall hy)
  exact (hr p).2.le.trans_eq (mem_sphere.mp hy).symm

end DifferentialGeometry.VectorField
