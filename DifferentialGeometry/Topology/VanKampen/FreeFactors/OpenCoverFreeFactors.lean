import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor
import DifferentialGeometry.Topology.VanKampen.FreeFactors.StarCoverGroups
import DifferentialGeometry.Topology.VanKampen.FreeProduct
set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VanKampen
namespace GC.Topology
universe u

theorem isFreeFactor_connected_overlap {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace ↥(U ∩ V)]
    (x : U) : GC.Group.IsFreeFactor (FundamentalGroup U x) (FundamentalGroup X x.val) := by
  let z : ↥(U ∩ V) := Classical.choice inferInstance
  let e := fundamentalGroupEquivFreeProduct U V hU hV hcover z.val z.property
  have h := GC.Group.isFreeFactor_coprodI (fundamentalGroupFactor U V z.val z.property) false
  have h' : GC.Group.IsFreeFactor (FundamentalGroup U (leftBasepoint U z.val z.property.1))
      (FundamentalGroup X z.val) := h.congr (MulEquiv.refl _) e
  let p : Path (leftBasepoint U z.val z.property.1) x := PathConnectedSpace.somePath _ _
  exact h'.congr (FundamentalGroup.fundamentalGroupMulEquivOfPath p)
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map continuous_subtype_val))

theorem isFreeFactor_separated_bridge {X : Type u} [TopologicalSpace X]
    (A B V : Set X) (hA : IsOpen A) (hB : IsOpen B) (hV : IsOpen V)
    (hdisj : Disjoint A B) (hcover : (A ∪ B) ∪ V = univ)
    [PathConnectedSpace A] [PathConnectedSpace B] [SimplyConnectedSpace V]
    [SimplyConnectedSpace ↥(A ∩ V)] [SimplyConnectedSpace ↥(B ∩ V)]
    (x : A) : GC.Group.IsFreeFactor (FundamentalGroup A x) (FundamentalGroup X x.val) := by
  let a : ↥(A ∩ V) := Classical.choice inferInstance
  let b : ↥(B ∩ V) := Classical.choice inferInstance
  let : PathConnectedSpace ↥(A ∪ V) := pathConnectedSpace_union A V ⟨a.val, a.property⟩
  let : PathConnectedSpace ↥(B ∪ V) := pathConnectedSpace_union B V ⟨b.val, b.property⟩
  have hinter : (A ∪ V) ∩ (B ∪ V) = V := by
    ext y
    constructor
    · rintro ⟨hyA | hyV, hyB | hyV⟩
      · exact (disjoint_left.mp hdisj hyA hyB).elim
      all_goals exact hyV
    · intro hyV; exact ⟨Or.inr hyV, Or.inr hyV⟩
  let : SimplyConnectedSpace ↥((A ∪ V) ∩ (B ∪ V)) := by rw [hinter]; infer_instance
  have hc : (A ∪ V) ∪ (B ∪ V) = univ := by
    rw [← hcover]; ext y; simp only [mem_union]; tauto
  let y : ↥(A ∪ V) := ⟨x.val, Or.inl x.property⟩
  have hf := isFreeFactor_connected_overlap (A ∪ V) (B ∪ V) (hA.union hV) (hB.union hV) hc y
  obtain ⟨e⟩ := union_fundamentalGroup_equiv A V hA hV x y
  exact hf.congr e (MulEquiv.refl _)

end GC.Topology
