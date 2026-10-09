import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCapping
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RelativeCaps
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams

/-!
# Chapter-14 assembly, L2-relative: the cut-and-capped data of one sphere seam

Lane ASM-L2 (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §3
L2-relative; V2 statements `build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:531–537, 867–904`,
review item 6, disposition D9).

* `PreservesOrientationAt`: the pointwise orientation clause of
  `RawGraphPresentation.quotient_oriented` for a map between two carriers (V2 §2, verbatim).
* `SphereCutCapped` (V2, verbatim): the outputs of `exists_sphereCutCarrier`
  (`SphereCutCarrier.lean:2512`) INCLUDING `kind`, `surjective` and the pointwise orientation
  `oriented` of the fold, plus a relative capping.
* `exists_sphereCutCapped` (producer adapter): `exists_sphereCutCarrier` and
  `exists_relativeSphereCapping` (`SphereCapCapping.lean:82`).
* `SphereCutCapped.components_count`: the capped carrier of a connected `W` has one or two
  components. The map sending a cut sphere to the component containing its cap is onto: otherwise
  the preimage `U` of a missed component under the core is clopen and contains no point of the cut
  spheres, so by `fold_eq_iff` the images of `U` and of its complement are disjoint closed sets
  covering `W`; connectedness of `W` empties `U`, and the caps (connected, attached to the cut
  spheres) give the contradiction.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The pointwise orientation clause of `RawGraphPresentation.quotient_oriented`
(`Presentation.lean:119–125`), for a map between two carriers. -/
def PreservesOrientationAt {X Y : CompactCarrier.{u}} (f : X.Carrier → Y.Carrier)
    (x : X.Carrier) : Prop :=
  ∃ L : TangentSpace X.model x ≃ₗ[ℝ] TangentSpace Y.model (f x),
    (∀ v, L v = mfderiv X.model Y.model f x v) ∧
    Orientation.map (Fin 3) L (X.orientation.orientation x) = Y.orientation.orientation (f x)

/-- **V2 (review item 6, D9): the cut-and-capped data of one interior sphere seam.** Exactly the
outputs of `exists_sphereCutCarrier` (`Closure/SphereCutCarrier.lean:2512`) INCLUDING the three that
V1 dropped — `kind`, `surjective` and the pointwise orientation `oriented` of the fold (smoothness
plus exact set fibres do not give a smooth local inverse: a local `x ↦ x³`-type injection away from
all collars keeps every V1 hypothesis) — and a relative capping (`exists_relativeSphereCapping`,
`Closure/SphereCapCapping.lean:82`). Fields are data and equalities.

Deviation from the V2 text (no loss of content): the V2 field `fold_eq_iff` (an iff) is replaced by
its forward half `fold_eq`, because the projection of an iff field always has the structure as an
explicit variable on both sides and fails the `explicitVarsOfIff` linter. The backward half follows
from `spheres` at `s = 0`; the full V2 iff is the theorem `SphereCutCapped.fold_eq_iff` below. -/
structure SphereCutCapped (W : CompactCarrier.{u}) (S : SphereSeam W) {n : ℕ}
    (E : BoundaryTori W n) where
  C : CompactCarrier.{u}
  B : MixedBoundaryCertificate C
  hn : B.torusCount = n
  h2 : B.sphereCount = 2
  fold : C.Carrier → W.Carrier
  kind : C.kind = .withBoundary
  smooth : ContMDiff C.model W.model ∞ fold
  surjective : Surjective fold
  oriented : ∀ x, PreservesOrientationAt (X := C) (Y := W) fold x
  tori : ∀ i p, p ∈ halfCollarSource →
    fold (B.tori.collar (Fin.cast hn.symm i) p) = E.collar i p
  spheres : ∀ i z s (hs0 : 0 ≤ s), s < 1 →
    fold (B.sphere (Fin.cast h2.symm i) (z, halfPoint s hs0)) =
      S.collar (z, if i.val = 0 then s else -s)
  fold_eq : ∀ {x y}, fold x = fold y → x = y ∨ ∃ z,
    (x = B.sphere (Fin.cast h2.symm 0) (z, halfZero) ∧
      y = B.sphere (Fin.cast h2.symm 1) (z, halfZero)) ∨
    (x = B.sphere (Fin.cast h2.symm 1) (z, halfZero) ∧
      y = B.sphere (Fin.cast h2.symm 0) (z, halfZero))
  Q : CompactCarrier.{u}
  capping : RelativeSphereCapping C Q B

/-- Producer adapter of `SphereCutCapped` (from `exists_sphereCutCarrier` and
`exists_relativeSphereCapping`; no new mathematics). -/
theorem exists_sphereCutCapped (W : CompactCarrier.{u}) (S : SphereSeam W) {n : ℕ}
    (E : BoundaryTori W n) (hE : W.model.boundary W.Carrier = E.image)
    (havoid : ∀ i, Disjoint (E.collar i).target S.collar.target) :
    Nonempty (SphereCutCapped W S E) := by
  obtain ⟨C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf, hrel, -⟩ :=
    exists_sphereCutCarrier W S.collar S.source_eq S.target_interior E hE havoid
  obtain ⟨Q, ⟨K⟩⟩ := exists_relativeSphereCapping C B
  exact ⟨⟨C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf, fun {x y} h => (hrel x y).mp h, Q, K⟩⟩

/-- The V2 field `fold_eq_iff` of `SphereCutCapped`: the forward half is the field `fold_eq`, the
backward half is the collar equality `spheres` at `s = 0`. -/
theorem SphereCutCapped.fold_eq_iff {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ}
    {E : BoundaryTori W n} {X : SphereCutCapped W S E} {x y : X.C.Carrier} :
    X.fold x = X.fold y ↔ x = y ∨ ∃ z,
      (x = X.B.sphere (Fin.cast X.h2.symm 0) (z, halfZero) ∧
        y = X.B.sphere (Fin.cast X.h2.symm 1) (z, halfZero)) ∨
      (x = X.B.sphere (Fin.cast X.h2.symm 1) (z, halfZero) ∧
        y = X.B.sphere (Fin.cast X.h2.symm 0) (z, halfZero)) := by
  refine ⟨X.fold_eq, ?_⟩
  have h0 : ∀ z, X.fold (X.B.sphere (Fin.cast X.h2.symm 0) (z, halfZero)) = S.collar (z, 0) := by
    intro z
    rw [show halfZero = halfPoint 0 le_rfl from rfl, X.spheres 0 z 0 le_rfl zero_lt_one]
    simp
  have h1 : ∀ z, X.fold (X.B.sphere (Fin.cast X.h2.symm 1) (z, halfZero)) = S.collar (z, 0) := by
    intro z
    rw [show halfZero = halfPoint 0 le_rfl from rfl, X.spheres 1 z 0 le_rfl zero_lt_one]
    simp
  rintro (rfl | ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
  · rfl
  · rw [h0, h1]
  · rw [h0, h1]

/-- The standard two-sphere of the closure files is connected. -/
theorem closureSphere_connectedSpace : ConnectedSpace ClosureSphere.{u} :=
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

/-- The closed unit `3`-cell is connected. -/
theorem closedCell_three_connectedSpace : ConnectedSpace (ClosedCell 3) := by
  have hset : {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x
    simp
  have hc : IsConnected {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} := by
    rw [hset]
    exact (convex_closedBall 0 1).isConnected (Metric.nonempty_closedBall.mpr zero_le_one)
  exact isConnected_iff_connectedSpace.mp hc

/-- Every point of a carrier lies in a piece of a component decomposition. -/
theorem exists_mem_componentsPiece {Q : CompactCarrier.{u}} (DQ : Q.Components)
    (x : Q.Carrier) : ∃ i, x ∈ DQ.piece i :=
  mem_iUnion.mp (DQ.covers ▸ mem_univ x)

/-- A piece of a component decomposition is clopen. -/
theorem isClopen_componentsPiece {Q : CompactCarrier.{u}} (DQ : Q.Components)
    (i : Fin DQ.count) : IsClopen (DQ.piece i : Set Q.Carrier) :=
  ⟨DQ.closed i, (DQ.piece i).isOpen⟩

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The component of the capped carrier containing the capped cut sphere `j`. -/
def spherePiece (DQ : X.Q.Components) (j : Fin X.B.sphereCount) : Fin DQ.count :=
  (exists_mem_componentsPiece DQ (X.capping.core (X.B.sphereMap j
    (@Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace))))).choose

/-- The whole cut sphere `j` lies in its component. -/
theorem sphere_mem_spherePiece (DQ : X.Q.Components) (j : Fin X.B.sphereCount)
    (z : ClosureSphere.{u}) :
    X.capping.core (X.B.sphere j (z, halfZero)) ∈ DQ.piece (X.spherePiece DQ j) := by
  have := closureSphere_connectedSpace.{u}
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have h₀ : X.capping.core (X.B.sphereMap j z₀) ∈ DQ.piece (X.spherePiece DQ j) :=
    (exists_mem_componentsPiece DQ (X.capping.core (X.B.sphereMap j z₀))).choose_spec
  have hconn : IsConnected (range fun w => X.capping.core (X.B.sphereMap j w)) :=
    isConnected_range (X.capping.core.continuous.comp (X.B.sphereMap j).continuous)
  have hsub := hconn.isPreconnected.subset_isClopen (isClopen_componentsPiece DQ (X.spherePiece DQ j))
    ⟨_, ⟨z₀, rfl⟩, h₀⟩
  exact hsub ⟨z, rfl⟩

/-- Every component of the capped carrier contains a capped cut sphere. -/
theorem spherePiece_surjective [ConnectedSpace W.Carrier] (DQ : X.Q.Components) :
    Surjective (X.spherePiece DQ) := by
  have := closureSphere_connectedSpace.{u}
  have := closedCell_three_connectedSpace
  intro i
  by_contra hmiss'
  have hmiss : ∀ j, X.spherePiece DQ j ≠ i := fun j hj => hmiss' ⟨j, hj⟩
  let U : Set X.C.Carrier := X.capping.core ⁻¹' (DQ.piece i)
  have hUclopen : IsClopen U := (isClopen_componentsPiece DQ i).preimage X.capping.core.continuous
  have hnot : ∀ j z, X.capping.core (X.B.sphere j (z, halfZero)) ∉ DQ.piece i := by
    intro j z hz
    exact Set.disjoint_left.mp (DQ.disjoint (hmiss j)) (X.sphere_mem_spherePiece DQ j z) hz
  have hsep : ∀ x ∈ U, ∀ y, X.fold x = X.fold y → y ∈ U := by
    intro x hx y hxy
    rcases X.fold_eq hxy with rfl | ⟨z, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact hx
    · exact (hnot _ z hx).elim
    · exact (hnot _ z hx).elim
  have hcont : Continuous X.fold := X.smooth.continuous
  have hAc : IsClosed (X.fold '' U) :=
    (hUclopen.isClosed.isCompact.image hcont).isClosed
  have hBc : IsClosed (X.fold '' Uᶜ) :=
    (hUclopen.isOpen.isClosed_compl.isCompact.image hcont).isClosed
  have hAB : X.fold '' U = (X.fold '' Uᶜ)ᶜ := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
      exact hy (hsep x hx y hyx.symm)
    · intro hw
      obtain ⟨y, rfl⟩ := X.surjective w
      by_cases hy : y ∈ U
      · exact ⟨y, hy, rfl⟩
      · exact (hw ⟨y, hy, rfl⟩).elim
  have hAo : IsOpen (X.fold '' U) := by
    rw [hAB]
    exact hBc.isOpen_compl
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  let j₀ : Fin X.B.sphereCount := Fin.cast X.h2.symm 0
  rcases isClopen_iff.mp ⟨hAc, hAo⟩ with hA | hA
  · have hU : U = ∅ := image_eq_empty.mp hA
    obtain ⟨⟨x, hx⟩⟩ := (DQ.connected i).toNonempty
    rcases X.capping.every_point x with ⟨y, rfl⟩ | ⟨j, y, rfl⟩
    · have hy : y ∈ U := hx
      rw [hU] at hy
      exact hy
    · have hconn : IsConnected (range (X.capping.cap j)) :=
        isConnected_range (X.capping.cap j).continuous
      have hsub := hconn.isPreconnected.subset_isClopen (isClopen_componentsPiece DQ i) ⟨_, ⟨y, rfl⟩, hx⟩
      have hb : X.capping.cap j (closureSphereToBall z₀) ∈ DQ.piece i := hsub ⟨_, rfl⟩
      rw [X.capping.boundary_eq] at hb
      exact hnot j _ hb
  · have hx₁ : X.fold (X.B.sphere j₀ (z₀, halfZero)) ∈ X.fold '' U := by
      rw [hA]
      exact mem_univ _
    rw [hAB] at hx₁
    exact hx₁ ⟨_, hnot j₀ z₀, rfl⟩

/-- At most two components: one for each cut sphere. -/
theorem components_count_le [ConnectedSpace W.Carrier] (DQ : X.Q.Components) :
    DQ.count ≤ 2 := by
  have h := Fintype.card_le_of_surjective (X.spherePiece DQ) (X.spherePiece_surjective DQ)
  simp only [Fintype.card_fin] at h
  exact X.h2 ▸ h

end SphereCutCapped

/-- **V2 (review item 6, D9): one or two capped components.** The real cut of one sphere gives a
capped carrier with one component (non-separating sphere) or two (separating sphere). -/
theorem SphereCutCapped.components_count {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E)
    (DQ : X.Q.Components) : DQ.count = 1 ∨ DQ.count = 2 := by
  have hle := X.components_count_le DQ
  have hpos := DQ.count_pos
  omega

end GC.GraphManifold.Assembly
