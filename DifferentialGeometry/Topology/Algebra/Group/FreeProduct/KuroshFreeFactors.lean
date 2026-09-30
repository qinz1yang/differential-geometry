import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.LargeFreeFactor
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteKurosh
import Mathlib.GroupTheory.GroupAction.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace GC.Group
open GraphCoveringTheory.Kurosh

theorem treeVertexStabilizer_isFreeFactor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) : IsFreeFactor (treeVertexStabilizer G H a) H := by
  apply isFreeFactor_of_indexed_equiv (TreeKuroshComponent G H)
    (kuroshBassSerreEquiv G H) (Sum.inl a)
  exact MulEquiv.ulift

theorem rawVertexStabilizer_isFreeFactor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (x : RawBassSerreVertex G) :
    IsFreeFactor (MulAction.stabilizer H x) H := by
  let a := actionOrbitMk H (RawBassSerreVertex G) x
  have he : actionOrbitMk H (RawBassSerreVertex G) (rawTreeRepresentative G H a) =
      actionOrbitMk H (RawBassSerreVertex G) x := rawTreeRepresentative_orbit G H a
  obtain ⟨h, hh⟩ := (actionOrbitMk_eq_iff H (RawBassSerreVertex G) _ _).mp he
  exact (treeVertexStabilizer_isFreeFactor G H a).congr
    (MulAction.stabilizerEquivStabilizer hh.symm) (MulEquiv.refl H)

theorem intersectionFactorInH_isFreeFactor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι) (g : FreeProduct G) :
    IsFreeFactor (intersectionFactorInH H i g) H := by
  let x := RawBassSerreVertex.factor i (factorCosetMk G i g)
  have hs : MulAction.stabilizer H x = intersectionFactorInH H i g := by
    ext h
    exact rawBassSerre_factor_fixed_iff G H i g h
  exact (rawVertexStabilizer_isFreeFactor G H x).congr
    (MulEquiv.subgroupCongr hs) (MulEquiv.refl H)

theorem factor_isFreeFactor_of_range_le {ι : Type} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (h : MonoidHom.range (factorInclusion G i) ≤ H) : IsFreeFactor (G i) H := by
  let f : G i →* intersectionFactorInH H i (1 : FreeProduct G) :=
    { toFun := fun a => ⟨⟨factorInclusion G i a, h ⟨a,rfl⟩⟩,
        ⟨h ⟨a,rfl⟩, (mem_conjugateSubgroup_iff _ _ _).mpr (by simp)⟩⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
      map_mul' := by intro a b; apply Subtype.ext; apply Subtype.ext; exact map_mul _ a b }
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      exact factorInclusion_injective G i (congrArg (fun x => x.val.val) he)
    · intro x
      have hx : x.val.val ∈ MonoidHom.range (factorInclusion G i) := by
        simpa using (mem_conjugateSubgroup_iff _ _ _).mp x.property.2
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩
  exact (intersectionFactorInH_isFreeFactor G H i 1).congr
    (MulEquiv.ofBijective f hf).symm (MulEquiv.refl H)

end GC.Group
