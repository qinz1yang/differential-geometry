import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecPorts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyInverseSmooth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyHalfCollar

/-!
# FC42 sphere recursion, packet S2 (first half): the transport map and the side lifts

Lane ASM-SPH (review 40 §2.4 "first layer", dispositions packet S2). For the cut-and-capped data
`X : SphereCutCapped W S E` of a sphere seam `S`:

* `SphereSeam.zeroSphere`: the seam sphere `Σ = S.collar (·, 0)` (compact, inside the collar target).
* `SphereCutCapped.fold_preimage_zeroSphere`: the fold sends exactly the two cut spheres onto `Σ`;
  `mfderiv_fold_bijective` (from the pointwise orientation field `oriented`).
* `cutInverse` (a section of the surjective fold) is the inverse of the fold off the cut spheres;
  it is continuous on `Σᶜ` (the fold is a closed map) and smooth there
  (`contMDiffOn_of_leftInverse_of_bijective_mfderiv`, boundary points of the cut carrier allowed).
* `coreInverse`: the inverse of the core embedding on the complement of the caps, smooth there.
* **`transport`**: THE transport map, the partial diffeomorphism `W \ Σ ≅ Q \ caps`,
  `x ↦ core (fold⁻¹ x)`; it carries the external ports of `W` onto the retained ports of `Q` on the
  whole collar (`transport_externalCollar`) and interior points to interior points.
* `sideLift j`: the lift across the seam on side `j` (copy `j` of the cut sphere on `Σ`, `cutInverse`
  elsewhere), with `fold ∘ sideLift j = id` and the collar formula `sideLift_collar`;
  `contMDiff_sideLift_comp`: a smooth map into `W` that stays on side `j` of the seam (in the
  collar, signed height `≥ 0`) lifts smoothly into the cut carrier — smoothness at the cut boundary
  comes from the whole-collar equalities `spheres` and `contMDiffOn_halfPoint_max`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- A one-sided inverse of a closed map is continuous on the set where it is a two-sided inverse. -/
theorem continuousOn_of_isClosedMap_of_leftInverse {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} {g : β → α} {s : Set β} (hf : IsClosedMap f)
    (hfg : ∀ x ∈ s, f (g x) = x) (hgf : ∀ y, f y ∈ s → g (f y) = y) : ContinuousOn g s := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨f '' t, hf t ht, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image]
  constructor
  · rintro ⟨hx, hxs⟩
    exact ⟨⟨g x, hx, hfg x hxs⟩, hxs⟩
  · rintro ⟨⟨y, hy, rfl⟩, hxs⟩
    refine ⟨?_, hxs⟩
    rw [hgf y hxs]
    exact hy

/-! ## The seam sphere -/

namespace SphereSeam

variable {W : CompactCarrier.{u}} (S : SphereSeam W)

theorem mem_source_iff {p : ClosureSphere.{u} × ℝ} :
    p ∈ S.collar.source ↔ -1 < p.2 ∧ p.2 < 1 := by
  rw [S.source_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem zero_mem_source (z : ClosureSphere.{u}) : (z, (0 : ℝ)) ∈ S.collar.source :=
  S.mem_source_iff.mpr ⟨by norm_num, zero_lt_one⟩

/-- The seam sphere `Σ = S.collar (·, 0)`. -/
def zeroSphere : Set W.Carrier :=
  range fun z => S.collar (z, 0)

theorem continuous_zeroSection : Continuous fun z : ClosureSphere.{u} => S.collar (z, 0) :=
  S.collar.contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
    S.zero_mem_source

theorem isCompact_zeroSphere : IsCompact S.zeroSphere :=
  isCompact_range S.continuous_zeroSection

theorem isClosed_zeroSphere : IsClosed S.zeroSphere :=
  S.isCompact_zeroSphere.isClosed

theorem zeroSphere_subset_target : S.zeroSphere ⊆ S.collar.target := by
  rintro _ ⟨z, rfl⟩
  exact S.collar.map_source (S.zero_mem_source z)

theorem collar_symm_collar {p : ClosureSphere.{u} × ℝ} (hp : p ∈ S.collar.source) :
    S.collar.symm (S.collar p) = p :=
  S.collar.toPartialEquiv.left_inv hp

theorem collar_collar_symm {x : W.Carrier} (hx : x ∈ S.collar.target) :
    S.collar (S.collar.symm x) = x :=
  S.collar.toPartialEquiv.right_inv hx

/-- A collar point lies on the seam sphere exactly at height zero. -/
theorem collar_mem_zeroSphere_iff {p : ClosureSphere.{u} × ℝ} (hp : p ∈ S.collar.source) :
    S.collar p ∈ S.zeroSphere ↔ p.2 = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have h := S.collar.toPartialEquiv.injOn (S.zero_mem_source z) hp hz
    rw [← h]
  · intro h
    refine ⟨p.1, ?_⟩
    change S.collar (p.1, 0) = S.collar p
    rw [← h]

end SphereSeam

/-- The sign of side `j`: copy `0` of the cut sphere is the side `s ≥ 0` of the collar, copy `1`
the side `s ≤ 0`. -/
def cutSideSign (j : Fin 2) : ℝ :=
  if j.val = 0 then 1 else -1

theorem cutSideSign_mul (j : Fin 2) (s : ℝ) :
    cutSideSign j * s = if j.val = 0 then s else -s := by
  unfold cutSideSign
  split_ifs <;> ring

theorem cutSideSign_mul_self (j : Fin 2) : cutSideSign j * cutSideSign j = 1 := by
  unfold cutSideSign
  split_ifs <;> norm_num

theorem abs_cutSideSign_mul (j : Fin 2) (s : ℝ) : |cutSideSign j * s| = |s| := by
  unfold cutSideSign
  split_ifs <;> simp

/-! ## The fold, its inverse off the cut spheres, the core inverse, the transport -/

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The point `z` of copy `j` of the cut sphere. -/
def cutSphere (j : Fin 2) (z : ClosureSphere.{u}) : X.C.Carrier :=
  X.B.sphere (Fin.cast X.h2.symm j) (z, halfZero)

theorem fold_cutSphere (j : Fin 2) (z : ClosureSphere.{u}) :
    X.fold (X.cutSphere j z) = S.collar (z, 0) := by
  unfold cutSphere
  rw [show halfZero = halfPoint 0 le_rfl from rfl, X.spheres j z 0 le_rfl zero_lt_one]
  split_ifs <;> simp

/-- The two cut spheres of the cut carrier. -/
def cutSpheres : Set X.C.Carrier :=
  ⋃ j, range (X.B.sphereMap j)

variable {X} in
theorem mem_cutSpheres_iff {y : X.C.Carrier} :
    y ∈ X.cutSpheres ↔ ∃ (j : Fin 2) (z : ClosureSphere.{u}), y = X.cutSphere j z := by
  constructor
  · intro hy
    obtain ⟨j, z, rfl⟩ := mem_iUnion.mp hy
    exact ⟨Fin.cast X.h2 j, z, rfl⟩
  · rintro ⟨j, z, rfl⟩
    exact mem_iUnion.mpr ⟨Fin.cast X.h2.symm j, z, rfl⟩

theorem cutSphere_mem_cutSpheres (j : Fin 2) (z : ClosureSphere.{u}) :
    X.cutSphere j z ∈ X.cutSpheres :=
  X.mem_cutSpheres_iff.mpr ⟨j, z, rfl⟩

/-- The fold sends exactly the two cut spheres onto the seam sphere. -/
theorem fold_preimage_zeroSphere : X.fold ⁻¹' S.zeroSphere = X.cutSpheres := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    change S.collar (z, 0) = X.fold y at hz
    rw [← X.fold_cutSphere 0 z] at hz
    rcases X.fold_eq hz with h | ⟨z', ⟨-, h2⟩ | ⟨-, h2⟩⟩
    · rw [← h]
      exact X.cutSphere_mem_cutSpheres 0 z
    · exact X.mem_cutSpheres_iff.mpr ⟨1, z', h2⟩
    · exact X.mem_cutSpheres_iff.mpr ⟨0, z', h2⟩
  · intro hy
    obtain ⟨j, z, rfl⟩ := X.mem_cutSpheres_iff.mp hy
    exact ⟨z, (X.fold_cutSphere j z).symm⟩

theorem isClosed_cutSpheres : IsClosed X.cutSpheres := by
  rw [← X.fold_preimage_zeroSphere]
  exact S.isClosed_zeroSphere.preimage X.smooth.continuous

variable {X} in
theorem fold_mem_zeroSphere_iff {y : X.C.Carrier} : X.fold y ∈ S.zeroSphere ↔ y ∈ X.cutSpheres := by
  rw [← X.fold_preimage_zeroSphere]
  rfl

/-- The differential of the fold is bijective everywhere (field `oriented`). -/
theorem mfderiv_fold_bijective (x : X.C.Carrier) :
    Bijective (mfderiv X.C.model W.model X.fold x) := by
  obtain ⟨L, hL, -⟩ := X.oriented x
  have hfun : (mfderiv X.C.model W.model X.fold x :
      TangentSpace X.C.model x → TangentSpace W.model (X.fold x)) = L :=
    funext fun v => (hL v).symm
  rw [hfun]
  exact L.bijective

/-- A section of the fold: the inverse of the fold off the cut spheres. -/
def cutInverse : W.Carrier → X.C.Carrier :=
  Function.surjInv X.surjective

theorem fold_cutInverse (x : W.Carrier) : X.fold (X.cutInverse x) = x :=
  Function.surjInv_eq X.surjective x

theorem cutInverse_fold {y : X.C.Carrier} (hy : y ∉ X.cutSpheres) :
    X.cutInverse (X.fold y) = y := by
  rcases X.fold_eq (X.fold_cutInverse (X.fold y)) with h | ⟨z, ⟨-, h⟩ | ⟨-, h⟩⟩
  · exact h
  · exact (hy (h ▸ X.cutSphere_mem_cutSpheres 1 z)).elim
  · exact (hy (h ▸ X.cutSphere_mem_cutSpheres 0 z)).elim

theorem cutInverse_notMem_cutSpheres {x : W.Carrier} (hx : x ∉ S.zeroSphere) :
    X.cutInverse x ∉ X.cutSpheres := by
  rw [← X.fold_mem_zeroSphere_iff, X.fold_cutInverse]
  exact hx

theorem continuousOn_cutInverse : ContinuousOn X.cutInverse S.zeroSphereᶜ :=
  continuousOn_of_isClosedMap_of_leftInverse X.smooth.continuous.isClosedMap
    (fun x _ => X.fold_cutInverse x)
    (fun _ hy => X.cutInverse_fold fun h => hy (X.fold_mem_zeroSphere_iff.mpr h))

/-- **The inverse of the fold is smooth off the seam sphere.** -/
theorem contMDiffOn_cutInverse :
    ContMDiffOn W.model X.C.model ∞ X.cutInverse S.zeroSphereᶜ :=
  contMDiffOn_of_leftInverse_of_bijective_mfderiv (A := X.cutSpheresᶜ)
    X.isClosed_cutSpheres.isOpen_compl S.isClosed_zeroSphere.isOpen_compl
    X.smooth.contMDiffOn (fun _ hy h => hy (X.fold_mem_zeroSphere_iff.mp h))
    (fun _ hx => X.cutInverse_notMem_cutSpheres hx) (fun x _ => X.fold_cutInverse x)
    (fun _ hy => X.cutInverse_fold hy) X.continuousOn_cutInverse
    (fun x _ => X.mfderiv_fold_bijective x)

/-- The cut carrier has a point (a point of a cut sphere). -/
theorem nonempty_C : Nonempty X.C.Carrier :=
  ⟨X.cutSphere 0 (@Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace))⟩

/-- The caps of the capped carrier. -/
def capSet : Set X.Q.Carrier :=
  ⋃ j, range (X.capping.cap j)

theorem isClosed_capSet : IsClosed X.capSet :=
  isClosed_iUnion_of_finite fun j => (isCompact_range (X.capping.cap j).continuous).isClosed

theorem core_injective : Injective X.capping.core :=
  X.capping.core_embedding.isEmbedding.injective

theorem core_cutSphere (j : Fin 2) (z : ClosureSphere.{u}) :
    X.capping.core (X.cutSphere j z) ∈ X.capSet := by
  refine mem_iUnion.mpr ⟨Fin.cast X.h2.symm j,
    (X.capping.attaching (Fin.cast X.h2.symm j)).symm z |> closureSphereToBall, ?_⟩
  rw [X.capping.boundary_eq, Diffeomorph.apply_symm_apply]
  rfl

variable {X} in
/-- The core is a bijection from the complement of the cut spheres onto the complement of the
caps. -/
theorem core_mem_capSet_iff {y : X.C.Carrier} : X.capping.core y ∈ X.capSet ↔ y ∈ X.cutSpheres := by
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    have hmem : X.capping.core y ∈ range X.capping.core ∩ range (X.capping.cap j) :=
      ⟨⟨y, rfl⟩, hj⟩
    rw [X.capping.core_cap_intersection] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [← X.core_injective hz]
    exact mem_iUnion.mpr ⟨j, z, rfl⟩
  · intro hy
    obtain ⟨j, z, rfl⟩ := X.mem_cutSpheres_iff.mp hy
    exact X.core_cutSphere j z

theorem compl_capSet_subset_range : X.capSetᶜ ⊆ range X.capping.core := by
  intro x hx
  rcases X.capping.every_point x with ⟨y, rfl⟩ | ⟨j, y, rfl⟩
  · exact ⟨y, rfl⟩
  · exact (hx (mem_iUnion.mpr ⟨j, y, rfl⟩)).elim

/-- The inverse of the core embedding (on its range). -/
def coreInverse : X.Q.Carrier → X.C.Carrier :=
  @Function.invFun _ _ X.nonempty_C X.capping.core

theorem coreInverse_core (y : X.C.Carrier) : X.coreInverse (X.capping.core y) = y :=
  @Function.leftInverse_invFun _ _ X.nonempty_C _ X.core_injective y

theorem core_coreInverse {x : X.Q.Carrier} (hx : x ∈ range X.capping.core) :
    X.capping.core (X.coreInverse x) = x :=
  @Function.invFun_eq _ _ X.nonempty_C _ _ hx

theorem coreInverse_notMem_cutSpheres {x : X.Q.Carrier} (hx : x ∉ X.capSet) :
    X.coreInverse x ∉ X.cutSpheres := by
  rw [← X.core_mem_capSet_iff, X.core_coreInverse (X.compl_capSet_subset_range hx)]
  exact hx

theorem mfderiv_core_bijective (y : X.C.Carrier) :
    Bijective (mfderiv X.C.model X.Q.model X.capping.core y) := by
  have hinj : Injective (mfderiv X.C.model X.Q.model X.capping.core y) :=
    X.capping.core_embedding.isImmersion.mfderiv_injective (by simp) y
  let f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv X.C.model X.Q.model X.capping.core y).toLinearMap
  have hinj' : Injective f := hinj
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj'⟩

theorem contMDiffOn_coreInverse :
    ContMDiffOn X.Q.model X.C.model ∞ X.coreInverse X.capSetᶜ :=
  contMDiffOn_of_leftInverse_of_bijective_mfderiv (A := X.cutSpheresᶜ)
    X.isClosed_cutSpheres.isOpen_compl X.isClosed_capSet.isOpen_compl
    X.capping.core_embedding.contMDiff.contMDiffOn
    (fun _ hy h => hy (X.core_mem_capSet_iff.mp h))
    (fun _ hx => X.coreInverse_notMem_cutSpheres hx)
    (fun _ hx => X.core_coreInverse (X.compl_capSet_subset_range hx))
    (fun y _ => X.coreInverse_core y)
    (continuousOn_of_isClosedMap_of_leftInverse X.capping.core.continuous.isClosedMap
      (fun _ hx => X.core_coreInverse (X.compl_capSet_subset_range hx))
      (fun y _ => X.coreInverse_core y))
    (fun y _ => X.mfderiv_core_bijective y)

/-- **S2, THE transport map**: the partial diffeomorphism `W \ Σ ≅ Q \ caps`,
`x ↦ core (fold⁻¹ x)`, inverse `y ↦ fold (core⁻¹ y)`. -/
def transport : PartialDiffeomorph W.model X.Q.model W.Carrier X.Q.Carrier ∞ where
  toFun x := X.capping.core (X.cutInverse x)
  invFun y := X.fold (X.coreInverse y)
  source := S.zeroSphereᶜ
  target := X.capSetᶜ
  map_source' x hx := fun h => X.cutInverse_notMem_cutSpheres hx (X.core_mem_capSet_iff.mp h)
  map_target' y hy := fun h => X.coreInverse_notMem_cutSpheres hy (X.fold_mem_zeroSphere_iff.mp h)
  left_inv' x _ := by
    rw [X.coreInverse_core, X.fold_cutInverse]
  right_inv' y hy := by
    rw [X.cutInverse_fold (X.coreInverse_notMem_cutSpheres hy),
      X.core_coreInverse (X.compl_capSet_subset_range hy)]
  open_source := S.isClosed_zeroSphere.isOpen_compl
  open_target := X.isClosed_capSet.isOpen_compl
  contMDiffOn_toFun := X.capping.core_embedding.contMDiff.comp_contMDiffOn X.contMDiffOn_cutInverse
  contMDiffOn_invFun := X.smooth.comp_contMDiffOn X.contMDiffOn_coreInverse

theorem transport_source : X.transport.source = S.zeroSphereᶜ :=
  rfl

theorem transport_target : X.transport.target = X.capSetᶜ :=
  rfl

theorem transport_apply (x : W.Carrier) : X.transport x = X.capping.core (X.cutInverse x) :=
  rfl

theorem transport_symm_apply (y : X.Q.Carrier) : X.transport.symm y = X.fold (X.coreInverse y) :=
  rfl

/-- The transport of a fold image off the cut spheres. -/
theorem transport_fold {y : X.C.Carrier} (hy : y ∉ X.cutSpheres) :
    X.transport (X.fold y) = X.capping.core y := by
  rw [transport_apply, X.cutInverse_fold hy]

theorem mfderiv_transport_bijective {x : W.Carrier} (hx : x ∉ S.zeroSphere) :
    Bijective (mfderiv W.model X.Q.model X.transport x) :=
  ((PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ X.transport hx).mfderivToContinuousLinearEquiv
    (by simp)).bijective

/-- A tori-collar point of the cut carrier is not on the cut spheres. -/
theorem toriCollar_notMem_cutSpheres (i : Fin X.B.torusCount) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : X.B.tori.collar i p ∉ X.cutSpheres := by
  intro h
  obtain ⟨j, z, hz⟩ := mem_iUnion.mp h
  have h1 : X.B.tori.collar i p ∈ (X.B.tori.collar i).target :=
    (X.B.tori.collar i).map_source ((X.B.tori.source_eq i).symm ▸ hp)
  have h2 : X.B.sphereMap j z ∈ (X.B.sphere j).target := by
    apply (X.B.sphere j).map_source
    rw [X.B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  exact Set.disjoint_left.mp (X.B.cross_disjoint i j) h1 (hz ▸ h2)

include X in
/-- The external collars of `W` avoid the seam sphere. -/
theorem externalCollar_notMem_zeroSphere (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : E.collar i p ∉ S.zeroSphere := by
  rw [← X.tori i p hp, X.fold_mem_zeroSphere_iff]
  exact X.toriCollar_notMem_cutSpheres _ hp

/-- **The external ports are carried to the retained ports, on the whole collar.** -/
theorem transport_externalCollar (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    X.transport (E.collar i p) = X.capping.retained.collar (Fin.cast X.hn.symm i) p := by
  rw [← X.tori i p hp, X.transport_fold (X.toriCollar_notMem_cutSpheres _ hp),
    X.capping.retained_collar _ p hp]

/-- Interior points off the seam sphere go to interior points. -/
theorem transport_mem_interior {x : W.Carrier} (hxi : x ∈ W.interior) :
    X.transport x ∈ X.Q.interior := by
  change X.Q.model.IsInteriorPoint (X.transport x)
  by_contra hb
  have hbd : X.transport x ∈ X.Q.model.boundary X.Q.Carrier :=
    (X.Q.model.isBoundaryPoint_iff_not_isInteriorPoint _).mpr hb
  rw [X.capping.boundary_exhausted] at hbd
  obtain ⟨k, t, ht⟩ := mem_iUnion.mp hbd
  rw [X.capping.retained_zero, transport_apply] at ht
  have hy : X.B.tori.torusMap k t = X.cutInverse x := X.core_injective ht
  have hfx : X.fold (X.B.tori.torusMap k t) = x := by rw [hy, X.fold_cutInverse]
  have hE : X.fold (X.B.tori.torusMap k t) = E.collar (Fin.cast X.hn k) (t, halfZero) := by
    have h := X.tori (Fin.cast X.hn k) (t, halfZero) (zero_mem_halfCollarSource t)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h
    exact h
  have hbW : W.model.IsBoundaryPoint x := by
    rw [← hfx, hE]
    exact E.boundary_zero _ t
  exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hxi hbW

/-! ## The side lifts across the seam -/

/-- **S2.** The lift across the seam on side `j`: copy `j` of the cut sphere on `Σ`, the inverse
of the fold elsewhere. -/
def sideLift (j : Fin 2) (x : W.Carrier) : X.C.Carrier :=
  @ite _ (x ∈ S.zeroSphere) (Classical.propDecidable _)
    (X.cutSphere j (S.collar.symm x).1) (X.cutInverse x)

theorem sideLift_of_mem (j : Fin 2) (z : ClosureSphere.{u}) :
    X.sideLift j (S.collar (z, 0)) = X.cutSphere j z := by
  unfold sideLift
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨z, rfl⟩), S.collar_symm_collar (S.zero_mem_source z)]

theorem sideLift_of_notMem (j : Fin 2) {x : W.Carrier} (hx : x ∉ S.zeroSphere) :
    X.sideLift j x = X.cutInverse x := by
  unfold sideLift
  exact ite_eq_right_of_eq_false _ _ (eq_false hx)

theorem fold_sideLift (j : Fin 2) (x : W.Carrier) : X.fold (X.sideLift j x) = x := by
  by_cases hx : x ∈ S.zeroSphere
  · obtain ⟨z, rfl⟩ := hx
    rw [X.sideLift_of_mem, X.fold_cutSphere]
  · rw [X.sideLift_of_notMem j hx, X.fold_cutInverse]

theorem sideLift_injective (j : Fin 2) : Injective (X.sideLift j) :=
  fun x y h => by rw [← X.fold_sideLift j x, ← X.fold_sideLift j y, h]

/-- **The collar formula of the side lift**, on the whole closed side `0 ≤ s < 1`. -/
theorem sideLift_collar (j : Fin 2) (z : ClosureSphere.{u}) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    X.sideLift j (S.collar (z, cutSideSign j * s)) =
      X.B.sphere (Fin.cast X.h2.symm j) (z, halfPoint s hs0) := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    rw [mul_zero, X.sideLift_of_mem]
    rfl
  · have hsrc : (z, cutSideSign j * s) ∈ S.collar.source := by
      refine S.mem_source_iff.mpr ?_
      have habs : |cutSideSign j * s| < 1 := by rw [abs_cutSideSign_mul, abs_of_pos hpos]; exact hs1
      exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2⟩
    have hnot : S.collar (z, cutSideSign j * s) ∉ S.zeroSphere := by
      rw [S.collar_mem_zeroSphere_iff hsrc]
      intro h
      unfold cutSideSign at h
      split_ifs at h <;> linarith
    have hfold : X.fold (X.B.sphere (Fin.cast X.h2.symm j) (z, halfPoint s hs0)) =
        S.collar (z, cutSideSign j * s) := by
      rw [X.spheres j z s hs0 hs1, cutSideSign_mul]
    rw [X.sideLift_of_notMem j hnot, ← hfold, X.cutInverse_fold]
    rw [← X.fold_mem_zeroSphere_iff, hfold]
    exact hnot

section SideSmooth

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- **S2, smoothness at the cut boundary.** A smooth map into `W` that stays on side `j` of the
seam (signed collar height `≥ 0` wherever it meets the collar) lifts smoothly into the cut
carrier. -/
theorem contMDiff_sideLift_comp (j : Fin 2) {m : M → W.Carrier} (hm : ContMDiff IM W.model ∞ m)
    (hside : ∀ q p, p ∈ S.collar.source → m q = S.collar p → 0 ≤ cutSideSign j * p.2) :
    ContMDiff IM X.C.model ∞ (X.sideLift j ∘ m) := by
  intro q
  by_cases hq : m q ∈ S.zeroSphere
  · let U : Set M := m ⁻¹' S.collar.target
    have hU : IsOpen U := S.collar.open_target.preimage hm.continuous
    have hqU : q ∈ U := S.zeroSphere_subset_target hq
    let h : M → ClosureSphere.{u} × ℝ := fun q' => S.collar.symm (m q')
    have hh : ContMDiffOn IM ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ h U :=
      S.collar.symm.contMDiffOn.comp hm.contMDiffOn fun _ hq' => hq'
    have hhsrc : ∀ q' ∈ U, h q' ∈ S.collar.source := fun _ hq' => S.collar.map_target hq'
    let σ : M → ℝ := fun q' => cutSideSign j * (h q').2
    have hσ : ContMDiffOn IM 𝓘(ℝ, ℝ) ∞ σ U :=
      contMDiffOn_const.mul (contMDiff_snd.comp_contMDiffOn hh)
    have hσpos : ∀ q' ∈ U, 0 ≤ σ q' := fun q' hq' =>
      hside q' (h q') (hhsrc q' hq') (S.collar_collar_symm hq').symm
    have hσlt : ∀ q' ∈ U, σ q' < 1 := fun q' hq' => by
      have h1 := (S.mem_source_iff.mp (hhsrc q' hq'))
      have habs : |σ q'| < 1 := by
        change |cutSideSign j * (h q').2| < 1
        rw [abs_cutSideSign_mul]
        exact abs_lt.mpr h1
      exact (abs_lt.mp habs).2
    let F : M → ClosureSphere.{u} × EuclideanHalfSpace 1 := fun q' =>
      ((h q').1, halfPoint (max (σ q') 0) (le_max_right _ _))
    have hF : ContMDiffOn IM ((𝓡 2).prod (𝓡∂ 1)) ∞ F U :=
      (contMDiff_fst.comp_contMDiffOn hh).prodMk (contMDiffOn_halfPoint_max hσ hσpos)
    have hFsrc : ∀ q' ∈ U, F q' ∈ (X.B.sphere (Fin.cast X.h2.symm j)).source := by
      intro q' hq'
      rw [X.B.sphere_source]
      change max (σ q') 0 < 1
      exact max_lt (hσlt q' hq') one_pos
    have hG : ContMDiffOn IM X.C.model ∞ (fun q' => X.B.sphere (Fin.cast X.h2.symm j) (F q')) U :=
      (X.B.sphere (Fin.cast X.h2.symm j)).contMDiffOn.comp hF hFsrc
    have heq : ∀ q' ∈ U, X.sideLift j (m q') = X.B.sphere (Fin.cast X.h2.symm j) (F q') := by
      intro q' hq'
      have hm' : m q' = S.collar ((h q').1, cutSideSign j * σ q') := by
        have hsq : cutSideSign j * σ q' = (h q').2 := by
          change cutSideSign j * (cutSideSign j * (h q').2) = (h q').2
          rw [← mul_assoc, cutSideSign_mul_self, one_mul]
        rw [hsq, Prod.mk.eta, S.collar_collar_symm hq']
      rw [hm', X.sideLift_collar j _ (hσpos q' hq') (hσlt q' hq')]
      simp only [F, max_eq_left (hσpos q' hq')]
    exact ((hG q hqU).contMDiffAt (hU.mem_nhds hqU)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hqU) heq)
  · have hV : IsOpen (m ⁻¹' S.zeroSphereᶜ) :=
      S.isClosed_zeroSphere.isOpen_compl.preimage hm.continuous
    have hcomp : ContMDiffOn IM X.C.model ∞ (X.cutInverse ∘ m) (m ⁻¹' S.zeroSphereᶜ) :=
      X.contMDiffOn_cutInverse.comp hm.contMDiffOn fun _ h => h
    exact ((hcomp q hq).contMDiffAt (hV.mem_nhds hq)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hV.mem_nhds hq) fun q' hq' => X.sideLift_of_notMem j hq')

end SideSmooth

end SphereCutCapped

end GC.GraphManifold.Assembly
