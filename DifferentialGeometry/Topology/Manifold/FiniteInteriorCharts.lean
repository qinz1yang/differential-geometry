import DifferentialGeometry.Topology.Manifold.InteriorChart
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

theorem exists_interiorChart_closedBall_subset {x : M} (hx : I.IsInteriorPoint x)
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ R : ℝ, 0 < R ∧
      closedBall (interiorChart I ∞ x x) R ⊆ (interiorChart I ∞ x).target ∧
      (interiorChart I ∞ x).symm '' closedBall (interiorChart I ∞ x x) R ⊆ U := by
  let c := interiorChart I ∞ x
  have hxs : x ∈ c.source := (mem_interiorChart_source_iff I ∞ x).mpr hx
  have hxt : c x ∈ c.target := c.map_source hxs
  have hU' : U ∈ 𝓝 (c.symm (c x)) := (c.left_inv hxs).symm ▸ hU
  have hpre : c.symm ⁻¹' U ∈ 𝓝 (c x) :=
    (c.symm.toOpenPartialHomeomorph.continuousAt hxt).preimage_mem_nhds hU'
  obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (c.open_target.mem_nhds hxt) hpre)
  refine ⟨R,hR,fun y hy => (hball hy).1,?_⟩
  rintro y ⟨z,hz,rfl⟩
  exact (hball hz).2

variable [T2Space M]

theorem exists_pairwise_disjoint_interiorChart_closedBalls {A : Set M}
    (hA : A.Finite) (hAI : ∀ x ∈ A, I.IsInteriorPoint x) :
    ∃ R : A → ℝ,
      (∀ p, 0 < R p) ∧
      (∀ p, closedBall (interiorChart I ∞ p.val p.val) (R p) ⊆
        (interiorChart I ∞ p.val).target) ∧
      Pairwise (fun p q : A => Disjoint
        ((interiorChart I ∞ p.val).symm '' closedBall (interiorChart I ∞ p.val p.val) (R p))
        ((interiorChart I ∞ q.val).symm '' closedBall (interiorChart I ∞ q.val q.val) (R q))) ∧
      (∀ p : A, ((interiorChart I ∞ p.val).symm ''
        closedBall (interiorChart I ∞ p.val p.val) (R p)) ∩ A = {p.val}) := by
  obtain ⟨U,hU,hdis⟩ := hA.t2_separation
  choose R hR htarget hsub using fun p : A =>
    exists_interiorChart_closedBall_subset I (hAI p p.property) ((hU p).2.mem_nhds (hU p).1)
  refine ⟨R,hR,htarget,?_,?_⟩
  · intro p q hpq
    have hpq' : p.val ≠ q.val := fun he => hpq (Subtype.ext he)
    exact (hdis p.property q.property hpq').mono (hsub p) (hsub q)
  · intro p
    ext x
    constructor
    · rintro ⟨hx,hxA⟩
      apply mem_singleton_iff.mpr
      by_contra hxp
      exact Set.disjoint_left.mp (hdis p.property hxA (fun he => hxp he.symm))
        (hsub p hx) (hU x).1
    · intro hx
      have he : x = p.val := hx
      subst x
      refine ⟨⟨interiorChart I ∞ p.val p.val,mem_closedBall_self (hR p).le,?_⟩,p.property⟩
      exact (interiorChart I ∞ p.val).left_inv
        ((mem_interiorChart_source_iff I ∞ p.val).mpr (hAI p p.property))

end Poincare.Manifold
