import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapQuotient

/-!
Actual open quotient patches off spherical attachments, including all retained torus collars.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

theorem sphereImage_closed : IsClosed B.sphereImage :=
  isClosed_iUnion_of_finite fun i => (isCompact_range (B.sphereMap i).continuous).isClosed

def sphereCapCoreOpen : Opens C.Carrier := ⟨B.sphereImageᶜ, B.sphereImage_closed.isOpen_compl⟩

def sphereCapBallOpen : Opens (ClosedCell 3) :=
  ⟨{x | ‖x.val‖ < 1}, isOpen_lt continuous_subtype_val.norm continuous_const⟩

private theorem quotient_open_image {O : Set (SphereCapCut B)} (hO : IsOpen O)
    (hblock : ∀ x ∈ O, ∀ i, x ∉ B.sphereCapGluing.block i) :
    IsOpen (B.sphereCapQuotientMap '' O) := by
  apply isOpen_quotient_mk_image_of_saturated ?_ hO
  intro x y hxy
  constructor
  · intro hx
    have he := B.sphereCapGluing.eq_of_rel_of_notMem (hblock x hx) hxy
    exact he ▸ hx
  · intro hy
    have he := B.sphereCapGluing.eq_of_rel_of_notMem (hblock y hy)
      (B.sphereCapGluing.isEquivalence_rel.symm hxy)
    exact he ▸ hy

private theorem core_not_in_block {x : C.Carrier} (hx : x ∈ B.sphereCapCoreOpen)
    (i : Fin B.sphereCount) : Sum.inl x ∉ B.sphereCapGluing.block i := by
  rintro (⟨z, hz⟩ | ⟨z, hz⟩)
  · apply hx
    exact mem_iUnion.mpr ⟨i, z, Sum.inl_injective hz⟩
  · dsimp [sphereCapRight] at hz
    cases hz

private theorem ball_not_in_block (i : Fin B.sphereCount) {x : ClosedCell 3}
    (hx : x ∈ sphereCapBallOpen) (j : Fin B.sphereCount) :
    Sum.inr (i, x) ∉ B.sphereCapGluing.block j := by
  rintro (⟨z, hz⟩ | ⟨z, hz⟩)
  · dsimp [sphereCapLeft] at hz
    cases hz
  · have he : closureSphereToBall z = x := congrArg Prod.snd (Sum.inr_injective hz)
    have hn : ‖x.val‖ = 1 := by
      rw [← he]
      exact norm_eq_of_mem_sphere z.down
    exact (ne_of_lt hx) hn

theorem sphereCapCore_openEmbedding :
    Topology.IsOpenEmbedding (fun x : B.sphereCapCoreOpen => B.sphereCapCore x.val) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact B.sphereCapCore.continuous.comp continuous_subtype_val
  · exact B.sphereCapCore_injective.comp Subtype.val_injective
  · intro A hA
    have hO : IsOpen (Sum.inl '' (Subtype.val '' A) : Set (SphereCapCut B)) :=
      isOpenMap_inl _ (B.sphereCapCoreOpen.isOpen.isOpenMap_subtype_val A hA)
    have hq := B.quotient_open_image hO ?_
    · change IsOpen ((fun x : B.sphereCapCoreOpen =>
        B.sphereCapQuotientMap (Sum.inl x.val)) '' A)
      simpa only [Set.image_image, Function.comp_def] using hq
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩ i
      exact B.core_not_in_block z.property i

theorem sphereCapBall_openEmbedding (i : Fin B.sphereCount) :
    Topology.IsOpenEmbedding (fun x : sphereCapBallOpen => B.sphereCapBall i x.val) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (B.sphereCapBall i).continuous.comp continuous_subtype_val
  · exact (B.sphereCapBall_injective i).comp Subtype.val_injective
  · intro A hA
    have htag : IsOpen ({i} : Set (Fin B.sphereCount)) := isOpen_discrete _
    have hprod : IsOpen ({i} ×ˢ (Subtype.val '' A : Set (ClosedCell 3))) :=
      htag.prod (sphereCapBallOpen.isOpen.isOpenMap_subtype_val A hA)
    have hq := B.quotient_open_image (isOpenMap_inr _ hprod) ?_
    · convert hq using 1
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Sum.inr (i, x.val), ⟨(i, x.val), ⟨rfl, x, hx, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨p, ⟨hi, z, hz, hzp⟩, rfl⟩, rfl⟩
        have hip : p.1 = i := hi
        have he : p = (i, z.val) := Prod.ext hip hzp.symm
        exact ⟨z, hz, by rw [he]; rfl⟩
    · rintro x ⟨p, ⟨hi, z, hz, hzp⟩, rfl⟩ j
      have hip : p.1 = i := hi
      have he : p = (i, z.val) := Prod.ext hip hzp.symm
      rw [he]
      exact B.ball_not_in_block i z.property j

theorem torus_collar_mem_sphereCapCoreOpen (i : Fin B.torusCount)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    B.tori.collar i p ∈ B.sphereCapCoreOpen := by
  intro h
  obtain ⟨j, hj⟩ := mem_iUnion.mp h
  obtain ⟨z, hz⟩ := hj
  have hzero : (z, halfZero) ∈ (B.sphere j).source := by
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  have ht : B.tori.collar i p ∈ (B.tori.collar i).target :=
    (B.tori.collar i).map_source' (by rw [B.tori.source_eq]; exact hp)
  have hs : B.tori.collar i p ∈ (B.sphere j).target := hz ▸ (B.sphere j).map_source' hzero
  exact (B.cross_disjoint i j).le_bot ⟨ht, hs⟩

end GC.GraphManifold.MixedBoundaryCertificate
