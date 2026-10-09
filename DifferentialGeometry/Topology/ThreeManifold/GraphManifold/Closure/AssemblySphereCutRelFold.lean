import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringComponent
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Collapse.CutPieceBalls

/-!
# Chapter-14 assembly, relative COMPARE G1: the fold off the caps

Lane ASM-L2e, group G1. For the cut-and-capped data `X : SphereCutCapped W S E` of a sphere seam,
the fold of the cut carrier read through the inverse of the core embedding is a partial
diffeomorphism of the capped carrier, defined off the caps, onto `W` off the seam sphere
(`SphereCutCapped.exists_capComplementFold`). Every relative piece of the comparison (drilled
components, placed plug, torus seams) is mapped into `W` through it.

* `SphereCutCapped.capFold`: `fold ∘ invFun core`, a map on the whole capped carrier;
  `capFold_core`: it is the fold on the core.
* `isLocalDiffeomorphAt_capFold`: off the caps it is a local diffeomorphism — at the core image of
  an interior point (fold and core have bijective differentials) and at the core image of a boundary
  point, which lies on a torus collar, where it is `E.collar ∘ retained.collar⁻¹`.
* `capFold_injOn`, `capFold_image`: it is injective off the caps (the fold identifies only the two
  cut spheres, which the core sends into the caps) with image `W` off the seam sphere.
* `SphereCutCapped.capComplementFold`, `exists_capComplementFold`: the partial diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- A point of the cut carrier (on the first cut sphere). -/
theorem cutCarrier_nonempty : Nonempty X.C.Carrier :=
  ⟨X.B.sphere (Fin.cast X.h2.symm 0)
    (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, halfZero)⟩

/-- A point of the capped carrier. -/
theorem cappedCarrier_nonempty : Nonempty X.Q.Carrier :=
  let := X.cutCarrier_nonempty
  ⟨X.capping.core (Classical.arbitrary _)⟩

/-- The fold read through the inverse of the core, on the whole capped carrier. -/
def capFold (x : X.Q.Carrier) : W.Carrier :=
  let := X.cutCarrier_nonempty
  X.fold (Function.invFun X.capping.core x)

theorem core_injective' : Injective X.capping.core :=
  X.capping.core_embedding.isEmbedding.injective

theorem capFold_core (y : X.C.Carrier) : X.capFold (X.capping.core y) = X.fold y := by
  let := X.cutCarrier_nonempty
  change X.fold (Function.invFun X.capping.core (X.capping.core y)) = X.fold y
  rw [Function.leftInverse_invFun X.core_injective' y]

theorem capFold_comp_core : X.capFold ∘ X.capping.core = X.fold :=
  funext X.capFold_core

/-- The set of the capped carrier off the caps. -/
def capComplement : Set X.Q.Carrier := (⋃ j, range (X.capping.cap j))ᶜ

theorem isOpen_capComplement : IsOpen X.capComplement := by
  exact isOpen_compl_iff.mpr
    (isClosed_iUnion_of_finite fun j => (isCompact_range (X.capping.cap j).continuous).isClosed)

/-- The differential of the fold is bijective everywhere (orientation field). -/
theorem fold_mfderiv_bijective (x : X.C.Carrier) :
    Bijective (mfderiv X.C.model W.model X.fold x) := by
  obtain ⟨L, hL, -⟩ := X.oriented x
  have he : ⇑(mfderiv X.C.model W.model X.fold x) = ⇑L := funext fun v => (hL v).symm
  rw [he]
  exact L.bijective

/-- A cut point whose core image is off the caps is not on a cut sphere. -/
theorem not_mem_sphere_of_core_mem {y : X.C.Carrier}
    (hy : X.capping.core y ∈ X.capComplement) (j : Fin X.B.sphereCount) (z : ClosureSphere.{u}) :
    y ≠ X.B.sphere j (z, halfZero) := by
  rintro rfl
  apply hy
  refine mem_iUnion.mpr ⟨j, ?_⟩
  have hmem : X.capping.core (X.B.sphere j (z, halfZero)) ∈
      range fun z' => X.capping.core (X.B.sphere j (z', halfZero)) := ⟨z, rfl⟩
  rw [← X.capping.core_cap_intersection j] at hmem
  exact hmem.2

/-- Every point off the caps is a core point. -/
theorem exists_core_eq {x : X.Q.Carrier} (hx : x ∈ X.capComplement) :
    ∃ y, X.capping.core y = x := by
  rcases X.capping.every_point x with h | ⟨j, y, rfl⟩
  · exact h
  · exact (hx (mem_iUnion.mpr ⟨j, y, rfl⟩)).elim

/-- **Local diffeomorphism off the caps.** -/
theorem isLocalDiffeomorphAt_capFold {x : X.Q.Carrier} (hx : x ∈ X.capComplement) :
    IsLocalDiffeomorphAt X.Q.model W.model ∞ X.capFold x := by
  obtain ⟨y, rfl⟩ := X.exists_core_eq hx
  rcases X.C.model.isInteriorPoint_or_isBoundaryPoint y with hi | hb
  · have hfold : IsLocalDiffeomorphAt X.C.model W.model ∞ (X.capFold ∘ X.capping.core) y := by
      rw [X.capFold_comp_core]
      exact isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective X.smooth hi
        (X.fold_mfderiv_bijective y)
    have hcore : IsLocalDiffeomorphAt X.C.model X.Q.model ∞ X.capping.core y :=
      isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective X.capping.core_embedding.contMDiff hi
        (X.capping.core_positive y hi).1
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hfold hcore
  · have hb' : y ∈ X.C.model.boundary X.C.Carrier := hb
    rw [X.B.boundary_eq] at hb'
    rcases hb' with ht | hs
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.mp ht
      have hsrc : (t, halfZero) ∈ (X.capping.retained.collar i).source := by
        rw [X.capping.retained.source_eq]
        exact zero_mem_halfCollarSource t
      have hsrcE : (t, halfZero) ∈ (E.collar (Fin.cast X.hn i)).source := by
        rw [E.source_eq]
        exact zero_mem_halfCollarSource t
      have h := GC.Seifert.Wiring.isLocalDiffeomorphAt_of_comp_eq X.capFold
        (X.capping.retained.collar i) (E.collar (Fin.cast X.hn i)) hsrc hsrcE (by
          rintro q ⟨hq, -⟩
          rw [X.capping.retained.source_eq] at hq
          rw [X.capping.retained_collar i q hq, X.capFold_core]
          have hi : i = Fin.cast X.hn.symm (Fin.cast X.hn i) := by
            ext
            rfl
          conv_lhs => rw [hi]
          exact X.tori (Fin.cast X.hn i) q hq)
      rwa [X.capping.retained_collar i _ (zero_mem_halfCollarSource t)] at h
    · obtain ⟨j, z, rfl⟩ := mem_iUnion.mp hs
      exact (X.not_mem_sphere_of_core_mem hx j z rfl).elim

/-- **Injectivity off the caps.** -/
theorem capFold_injOn : InjOn X.capFold X.capComplement := by
  intro x hx x' hx' he
  obtain ⟨y, rfl⟩ := X.exists_core_eq hx
  obtain ⟨y', rfl⟩ := X.exists_core_eq hx'
  rw [X.capFold_core, X.capFold_core] at he
  rcases X.fold_eq he with h | ⟨z, ⟨h, -⟩ | ⟨h, -⟩⟩
  · rw [h]
  · exact (X.not_mem_sphere_of_core_mem hx _ z h).elim
  · exact (X.not_mem_sphere_of_core_mem hx _ z h).elim

/-- The fold of a point of a cut sphere lies on the seam sphere. -/
theorem fold_sphere_zero (j : Fin X.B.sphereCount) (z : ClosureSphere.{u}) :
    X.fold (X.B.sphere j (z, halfZero)) = S.collar (z, 0) := by
  have hj : j = Fin.cast X.h2.symm (Fin.cast X.h2 j) := by
    ext
    rfl
  rw [hj, show halfZero = halfPoint 0 le_rfl from rfl,
    X.spheres (Fin.cast X.h2 j) z 0 le_rfl zero_lt_one]
  simp

/-- **The image off the caps** is `W` off the seam sphere. -/
theorem capFold_image :
    X.capFold '' X.capComplement = (range fun z => S.collar (z, 0))ᶜ := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := X.exists_core_eq hx
    change S.collar (z, 0) = X.capFold (X.capping.core y) at hz
    rw [X.capFold_core, ← X.fold_sphere_zero (Fin.cast X.h2.symm 0) z] at hz
    rcases X.fold_eq hz with h | ⟨z', ⟨-, h⟩ | ⟨-, h⟩⟩
    · exact X.not_mem_sphere_of_core_mem hx _ z h.symm
    · exact X.not_mem_sphere_of_core_mem hx _ z' h
    · exact X.not_mem_sphere_of_core_mem hx _ z' h
  · intro hw
    obtain ⟨y, rfl⟩ := X.surjective w
    refine ⟨X.capping.core y, ?_, X.capFold_core y⟩
    intro hcap
    obtain ⟨j, hj⟩ := mem_iUnion.mp hcap
    have hmem : X.capping.core y ∈ range X.capping.core ∩ range (X.capping.cap j) := ⟨⟨y, rfl⟩, hj⟩
    rw [X.capping.core_cap_intersection j] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hy := X.core_injective' hz
    exact hw ⟨z, by rw [← hy, X.fold_sphere_zero]⟩

/-- The open set off the caps. -/
def capComplementOpens : TopologicalSpace.Opens X.Q.Carrier :=
  ⟨X.capComplement, X.isOpen_capComplement⟩

/-- **The fold off the caps, as a partial diffeomorphism.** -/
def capComplementFold : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞ :=
  let := X.cappedCarrier_nonempty
  DifferentialGeometry.Geometry.Collapse.partialDiffeomorphOfInjOn X.capFold X.capComplementOpens
    (fun _ hx => (X.isLocalDiffeomorphAt_capFold hx).contMDiffAt.contMDiffWithinAt)
    (DifferentialGeometry.isLocalDiffeomorph_restrict_open X.capComplementOpens
      fun x => X.isLocalDiffeomorphAt_capFold x.property)
    X.capFold_injOn

theorem capComplementFold_apply (x : X.Q.Carrier) : X.capComplementFold x = X.capFold x := rfl

theorem capComplementFold_source :
    X.capComplementFold.source = (⋃ j, range (X.capping.cap j))ᶜ := rfl

theorem capComplementFold_target :
    X.capComplementFold.target = (range fun z => S.collar (z, 0))ᶜ :=
  X.capFold_image

theorem capComplementFold_core (y : X.C.Carrier) :
    X.capComplementFold (X.capping.core y) = X.fold y :=
  X.capFold_core y

end SphereCutCapped

/-- **G1 (ASM-L2e).** The fold of the cut carrier, read through the core, is a partial
diffeomorphism from the capped carrier off the caps onto `W` off the seam sphere. -/
theorem SphereCutCapped.exists_capComplementFold {W : CompactCarrier.{u}} {S : SphereSeam W}
    {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E) :
    ∃ F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞,
      F.source = (⋃ j, range (X.capping.cap j))ᶜ ∧
      F.target = (range fun z => S.collar (z, 0))ᶜ ∧
      ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y :=
  ⟨X.capComplementFold, X.capComplementFold_source, X.capComplementFold_target,
    fun y _ => X.capComplementFold_core y⟩

end GC.GraphManifold.Assembly
