import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

/-!
Actual spherical and toroidal boundary collars on compact carriers.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem closureSphere_dimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] closureSphere_dimension

abbrev ClosureSphere : Type u := ULift.{u} SphereTwo

instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ClosureSphere.{u} :=
  uliftChartedSpace _ _

instance : IsManifold (𝓡 2) ∞ ClosureSphere.{u} := isManifold_ulift _ _

abbrev sphereHalfCollarModel := (𝓡 2).prod (𝓡∂ 1)

abbrev sphereSignedCollarModel := (𝓡 2).prod 𝓘(ℝ)

def sphereHalfCollarSource : Set (ClosureSphere.{u} × EuclideanHalfSpace 1) :=
  {p | p.2.val 0 < 1}

def sphereSignedCollarSource : Set (ClosureSphere.{u} × ℝ) :=
  univ ×ˢ Ioo (-1 : ℝ) 1

structure MixedBoundaryCertificate (C : CompactCarrier.{u}) where
  torusCount : ℕ
  tori : BoundaryTori C torusCount
  sphereCount : ℕ
  sphere : Fin sphereCount → PartialDiffeomorph sphereHalfCollarModel C.model
    (ClosureSphere.{u} × EuclideanHalfSpace 1) C.Carrier ∞
  sphere_source : ∀ i, (sphere i).source = sphereHalfCollarSource
  sphere_disjoint : Pairwise fun i j => Disjoint (sphere i).target (sphere j).target
  sphere_zero_boundary : ∀ i z, C.model.IsBoundaryPoint (sphere i (z, halfZero))
  cross_disjoint : ∀ i j, Disjoint (tori.collar i).target (sphere j).target
  exhausted : C.model.boundary C.Carrier = tori.image ∪
    ⋃ i, range fun z => sphere i (z, halfZero)

namespace MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

def sphereMap (i : Fin B.sphereCount) : C(ClosureSphere.{u}, C.Carrier) :=
  ⟨fun z => B.sphere i (z, halfZero), by
    apply ((B.sphere i).contMDiffOn.continuousOn).comp_continuous
      (continuous_id.prodMk continuous_const)
    intro z
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    norm_num⟩

def sphereImage : Set C.Carrier := ⋃ i, range (B.sphereMap i)

theorem boundary_eq : C.model.boundary C.Carrier = B.tori.image ∪ B.sphereImage :=
  B.exhausted

theorem sphereMap_injective (i : Fin B.sphereCount) : Function.Injective (B.sphereMap i) := by
  intro z w h
  have hz : (z, halfZero) ∈ (B.sphere i).source := by
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  have hw : (w, halfZero) ∈ (B.sphere i).source := by
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  exact congrArg Prod.fst ((B.sphere i).injOn hz hw h)

theorem boundary_eq_tori_of_sphereCount_zero (h : B.sphereCount = 0) :
    C.model.boundary C.Carrier = B.tori.image := by
  rw [B.boundary_eq]
  have hempty : B.sphereImage = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Fin.elim0 (h ▸ i)
  rw [hempty, union_empty]

def ofTori {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) : MixedBoundaryCertificate C where
  torusCount := n
  tori := E
  sphereCount := 0
  sphere i := i.elim0
  sphere_source i := i.elim0
  sphere_disjoint i := i.elim0
  sphere_zero_boundary i := i.elim0
  cross_disjoint i j := j.elim0
  exhausted := by
    simpa only [iUnion_of_empty, union_empty] using hb

theorem ofTori_collar {n : ℕ} (E : BoundaryTori C n)
    (hb : C.model.boundary C.Carrier = E.image) (i : Fin n)
    (p : Torus × EuclideanHalfSpace 1) : (ofTori E hb).tori.collar i p = E.collar i p := rfl

end MixedBoundaryCertificate

end GC.GraphManifold
