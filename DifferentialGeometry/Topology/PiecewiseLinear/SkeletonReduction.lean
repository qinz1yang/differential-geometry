/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh

/-!
# The one-skeleton reduction of Moise 35.2 to Moise 35.1

Moise derives Theorem 2 of §35 (printed p. 251), rendered here by `Moise352`, from Theorem 1 of
§35 (printed p. 248), rendered here by `Moise351`.  His proof is two paragraphs long.

The first paragraph performs three reductions.  `K` is moved into `Int K` by a piecewise linear
homeomorphism which is as close to the identity as one pleases; this replaces the hypothesis
that `h` and `φ` are defined on `K` alone by the hypothesis that they are defined on an open set
containing the moved copy.  Then `U` is chosen so that `K` is closed relative to `U`, and then
the statement is reduced to `K` closed in `M₁` with `φ` strongly positive on all of `M₁`.

The second paragraph subdivides `K` so that `diam h(|St σ|) < inf φ | |St σ|` for every simplex
`σ`, takes a regular neighbourhood `N` of the one-skeleton `K¹`, produces from Theorem 35.1 a
piecewise linear homeomorphism of `N` onto a neighbourhood of `h(K¹)` which approximates `h|N`
within any prescribed tolerance, and then extends it over the 2- and 3-simplexes one at a time.
Moise's closing sentence is that this last step is the same as the passage from Theorem 33.1 to
Theorem 34.1 carried out in §34 (printed pp. 239--246), where the simplexes of `K` are treated
essentially one at a time.

There is no tower of stages, no sequence of tolerances and no agreement clause between
consecutive stages anywhere in this proof.

## What is proved here and what is assumed

* `exists_isSubdivision_diam_image_closedStars_lt` is the subdivision condition of the second
  paragraph, for a finite complex: the stars of the subdivision have images of diameter smaller
  than the value of `φ` at every point of the star.  It is proved.
* `Moise352InwardPush` is the inward push of the first paragraph.  It is **assumed**: the tree
  has an inward push for a compact combinatorial 3-manifold with boundary
  (`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward`) but that push carries
  no bound on how far it moves points, and no controlled push exists anywhere in the tree.
* `Moise352SkeletonExtension` is the §34 transition.  It is **assumed** and is the sole
  remaining mathematical obligation of this route.
* `moise352_of_inwardPush_of_skeletonExtension` derives `Moise352 3` from `Moise351`,
  `Moise352InwardPush 3` and `Moise352SkeletonExtension 3`.

The two further reductions of Moise's first paragraph are not available in the form he states
them, and are not used.  `Moise352` is stated for a set carried by a `LocallyFinitePieceTower`,
and every open set is such a set (`isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen`), so
`K` need not be closed in `M₁` and cannot be made so without changing the statement.  The
passage to a strongly positive function on all of `M₁` is not needed either, because `Moise351`
already accepts a continuous positive `φ` on the ambient open set.

## The transport along the push

The approximation produced by the §34 argument lives on the pushed copy of `K` and has to be
carried back along the push.  That transport is left inside `Moise352SkeletonExtension`, which
therefore receives the push as one of its hypotheses, because `IsPLWithinAt` is not monotone in
its set — its witnessing polytopes are required to lie inside the set — so a piecewise linear
map on an open set is not piecewise linear on an arbitrary subset, and the tree has no
composition lemma for `IsPLOn` between two manifolds.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-- A topological embedding of a subspace restricts to a topological embedding of any smaller
subspace. -/
private theorem isEmbedding_domRestrict_of_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {K U : Set X}
    (hf : Topology.IsEmbedding (K.domRestrict f)) (hUK : U ⊆ K) :
    Topology.IsEmbedding (U.domRestrict f) :=
  hf.comp (Topology.IsEmbedding.inclusion hUK)

/-- The identity is piecewise linear on an open set.

Openness is what makes this available: the polytopes witnessing `IsPiecewiseAffineWithinAt` must
lie inside the set, so `IsPLOn` does not restrict to arbitrary subsets, but it does restrict to
a set which is a neighbourhood of each of its points. -/
private theorem isPLOn_id_of_isOpen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [HasGroupoid M (plGroupoid n)] {s : Set M}
    (hs : IsOpen s) : IsPLOn n n (id : M → M) s := by
  intro x hx
  have hnb : s ∈ 𝓝[(univ : Set M)] x := by
    rw [nhdsWithin_univ]
    exact hs.mem_nhds hx
  have h₂ : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty n n) (id : M → M)
      (univ ∩ s) x :=
    (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mpr (isPL_id x)
  rwa [univ_inter] at h₂

/-- **Moise's subdivision condition**, printed p. 251, for a finite complex.

Moise asks for a subdivision of `K` in which every simplex `σ` satisfies
`diam h(|St σ|) < inf φ | |St σ|`, where `St σ` collects the simplexes meeting `σ` together with
their faces.  In the vocabulary of this tree the carrier of `St σ` is the union of the closed
stars of the vertices of `σ`, and the infimum of `φ` over a set is rendered pointwise.

The proof is uniform continuity of `g` on the compact carrier against a positive lower bound for
`φ`, fed into `exists_isSubdivision_closedStars_subset_cover` through the cover by balls of
radius half the modulus of continuity.  Only the compact case is available: every mesh theorem
in the tree needs a finite complex, and a locally finite polyhedral manifold with boundary is
presented by a tower of finite pieces with no compatible global subdivision. -/
theorem exists_isSubdivision_diam_image_closedStars_lt {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace Z] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {g : E → Z} (hg : ContinuousOn g K.space) {φ : E → ℝ} (hφ : ContinuousOn φ K.space)
    (hpos : ∀ x ∈ K.space, 0 < φ x) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s ∈ R.faces, ∀ x ∈ ⋃ v ∈ s, closedStar R v,
        Metric.diam (g '' ⋃ v ∈ s, closedStar R v) < φ x := by
  have hKc : IsCompact K.space :=
    DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K
  obtain ⟨c, hc, hcle⟩ := exists_pos_forall_le_of_continuousOn hKc hφ hpos
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hg) (c / 2) (by positivity)
  obtain ⟨R, hR, hRfin, hstar⟩ :=
    exists_isSubdivision_closedStars_subset_cover K
      (fun z : K.space => Metric.ball (z : E) (δ / 2))
      (fun _ => Metric.isOpen_ball.preimage continuous_subtype_val)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (half_pos hδ)⟩)
  refine ⟨R, hR, hRfin, fun s hs x hx => ?_⟩
  obtain ⟨z, hz⟩ := hstar s hs
  have hsub : (⋃ v ∈ s, closedStar R v) ⊆ K.space :=
    iUnion₂_subset fun v _ => (closedStar_subset_space R v).trans hR.space_eq.subset
  have hdiam : Metric.diam (g '' ⋃ v ∈ s, closedStar R v) ≤ c / 2 := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    refine le_of_lt (hclose y (hsub hy) y' (hsub hy') ?_)
    have h₁ : dist y (z : E) < δ / 2 := Metric.mem_ball.mp (hz hy)
    have h₂ : dist y' (z : E) < δ / 2 := Metric.mem_ball.mp (hz hy')
    calc dist y y' ≤ dist y (z : E) + dist (z : E) y' := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (z : E) y']; linarith
  exact hdiam.trans_lt (lt_of_lt_of_le (by linarith) (hcle x (hsub hx)))

/-- **The inward push**, the first sentence of Moise's proof of Theorem 35.2, printed p. 251:
`K` can be moved into `Int K` by a piecewise linear homeomorphism which is as close to the
identity as we please.  Moise refers back to the same move at the head of the proof of Theorem
34.1, printed p. 239.

Three points about the rendering.  `Int K` is the ambient interior `interior K`; for a
polyhedral manifold with boundary this is `K` less its frontier, by
`frontier_eq_polyhedralBoundary`.  Closeness to the identity is measured after the embedding
`h`, because `M₁` carries no metric in `Moise352`; since `h` is an embedding this is exactly the
uniform statement that the push moves points slightly.  The inverse `q` is asked for on an open
set `W` containing the moved copy rather than on the moved copy alone, which is what the collar
formula supplies — the push raises the collar coordinate by an affine reparametrisation whose
inverse is defined on a slightly larger collar — and is what lets a piecewise linear map built
on `W` be carried back to `K`.

This is **not proved anywhere in the tree**.  The tree has an exact inward push for a compact
combinatorial 3-manifold with boundary,
`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward`, built from
`collarInwardMap`, but the push height there is an unbounded inf of inverse collar heights and
no statement in the tree carries both an interior clause and a closeness clause. -/
def Moise352InwardPush (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x

/-- The conclusion of the inward push holds whenever `K` is open, with the identity as both the
push and its inverse.

This is the consistency witness for `Moise352InwardPush`: its conclusion is satisfiable, at
nondegenerate data, by every nonempty open subset of a piecewise linear manifold.  The witness
is boundaryless, `interior K = K`, so it does not exercise the content of the statement, which
is the case `frontier K ≠ ∅`. -/
theorem exists_isPLOn_injOn_leftInvOn_of_isOpen {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [HasGroupoid M₁ (plGroupoid n)] {K : Set M₁} (hK : IsOpen K) (h : M₁ → M₂) {ψ : M₁ → ℝ}
    (hψ : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x :=
  ⟨id, id, K, hK, hK.interior_eq.ge, mapsTo_id K, isPLOn_id_of_isOpen hK, injOn_id K,
    isPLOn_id_of_isOpen hK, mapsTo_id K, fun _ _ => rfl, fun x hx => by simpa using hψ x hx⟩

/-- **The §34 transition**, the sole remaining obligation of Moise's route to Theorem 35.2.

The hypotheses are exactly what Moise has available at the end of the first paragraph of the
proof on printed p. 251, and the conclusion is Theorem 35.2 itself.

The first hypothesis is the inward push, at every tolerance: Moise's "as close to the identity
as we please".  The second is Theorem 35.1, printed p. 248, applied to a locally finite
polyhedral graph inside an open subset of `K`; the graph is the one-skeleton `K¹` of whatever
subdivision the argument chooses, the open set is the one produced by the push, and the
tolerance `ψ` is free, which is Moise's "for every `φ' ≫ 0` on `M₁` we can make `f` a
`φ'`-approximation of `h|N`".  The regular neighbourhood `N` of the graph and the piecewise
linear homeomorphism carrying it onto a neighbourhood of `h(K¹)` are the output of 35.1.

What remains is the argument of §34, printed pp. 239--246: subdivide so that the stars have
small image, which is `exists_isSubdivision_diam_image_closedStars_lt` in the compact case and
needs a compatible subdivision of the whole tower in general; split the regular neighbourhood of
the one-skeleton into dual cells at the edge midpoints; extend the homeomorphism over the 2- and
3-simplexes one at a time, using solid tori, spines and general position; and carry the result
back along the push.  Moise's closing sentence is that this is the same passage as from Theorem
33.1 to Theorem 34.1. -/
def Moise352SkeletonExtension (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ φ : M₁ → ℝ, ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    (∀ ψ : M₁ → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
      ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
        IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
        ∀ x ∈ K, dist (h (p x)) (h x) < ψ x) →
    (∀ {U : Set M₁}, IsOpen U → U ⊆ K → ∀ {G : Set M₁}, G ⊆ U →
      IsClosed (((↑) : U → M₁) ⁻¹' G) → IsLocallyFinitePolyhedralGraph (n := n) G →
      ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
        ∃ N : Set M₁, IsLocallyFiniteRegularNeighborhoodOf (n := n) N G U ∧
          ∃ f : M₁ → M₂, IsPLHomeomorphInto n f N ∧ f '' N ∈ nhdsSet (h '' G) ∧
            ∀ x ∈ N, dist (f x) (h x) < ψ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x

/-- **Moise 35.2 from Moise 35.1**, along the route of printed p. 251.

The inward push supplies the first hypothesis of the §34 transition verbatim.  Theorem 35.1
supplies the second: its ambient open set is any open subset `U` of `K`, on which `h` is still
an embedding, and its remaining hypotheses — `G` contained in `U`, closed relative to `U`, and a
locally finite polyhedral graph — are carried by the transition itself, since the choice of the
one-skeleton belongs to the §34 argument. -/
theorem moise352_of_inwardPush_of_skeletonExtension (hpush : Moise352InwardPush.{u} 3)
    (h351 : Moise351.{u}) (hext : Moise352SkeletonExtension.{u} 3) : Moise352.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  refine hext hK hh φ hφ hpos (fun ψ hψ hψpos => hpush hK hh ψ hψ hψpos) ?_
  intro U hU hUK G hGU hGclosed hGgraph ψ hψ hψpos
  exact h351 hU hGU hGclosed hGgraph (isEmbedding_domRestrict_of_subset hh hUK) ψ hψ hψpos

/-- Every hypothesis of `Moise352SkeletonExtension` is dischargeable at nondegenerate data: an
open subset of a piecewise linear 3-manifold, with the inward push witnessed by the identity and
Theorem 35.1 supplying the regular neighbourhoods.

This is the non-vacuity evidence for `Moise352SkeletonExtension`.  The hypotheses of an
obligation of this shape can be met, so the obligation is not vacuously true. -/
theorem exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen (h351 : Moise351.{u})
    (hext : Moise352SkeletonExtension.{u} 3) {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
    [SecondCountableTopology M₁] [Nonempty M₁] [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {K : Set M₁}
    (hK : IsOpen K) {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (φ : M₁ → ℝ)
    (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x := by
  refine hext (isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) hK) hh φ hφ hpos
    (fun _ _ hψpos => exists_isPLOn_injOn_leftInvOn_of_isOpen hK h hψpos) ?_
  intro U hU hUK G hGU hGclosed hGgraph ψ hψ hψpos
  exact h351 hU hGU hGclosed hGgraph (isEmbedding_domRestrict_of_subset hh hUK) ψ hψ hψpos

/-- The conclusion shared by `Moise352` and `Moise352SkeletonExtension` is satisfiable at
nondegenerate data: on an open set the identity is a piecewise linear embedding approximating
itself within any positive error.

Together with `exists_isPLHomeomorphInto_dist_lt_of_skeletonExtension_of_isOpen` this shows that
neither the hypotheses nor the conclusion of the obligation is empty. -/
theorem exists_isPLHomeomorphInto_dist_lt_id_of_isOpen {n : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [HasGroupoid M (plGroupoid n)] {K : Set M}
    (hK : IsOpen K) {φ : M → ℝ} (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ f : M → M, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (id x) < φ x := by
  refine ⟨id, ⟨isPLOn_id_of_isOpen hK, injOn_id K, ?_⟩, fun x hx => by simpa using hpos x hx⟩
  intro y hy
  rw [Set.image_id] at hy
  exact ⟨id, by rw [Set.image_id]; exact isPLOn_id_of_isOpen hK y hy, fun _ _ => rfl⟩

/-- A concrete nondegenerate instance of the data both obligations quantify over: the whole of
`EuclideanSpace ℝ (Fin 3)`, which is nonempty, is a locally finite polyhedral manifold with
boundary, and carries a piecewise linear embedding approximating the identity within `1`.

This rules out the failure mode in which a contract is satisfied only by degenerate data: the
carrier here is nonempty and the approximation is a genuine piecewise linear homeomorphism onto
its image.  The polyhedral boundary is empty, which is the part of `Moise352InwardPush` that no
witness in this file exercises. -/
theorem isLocallyFinitePolyhedralManifoldWithBoundary_univ_three :
    (univ : Set (EuclideanSpace ℝ (Fin 3))).Nonempty ∧
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3
        (univ : Set (EuclideanSpace ℝ (Fin 3))) ∧
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphInto 3 f univ ∧
          ∀ x ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))), dist (f x) (id x) < 1 :=
  ⟨univ_nonempty, isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) isOpen_univ,
    exists_isPLHomeomorphInto_dist_lt_id_of_isOpen isOpen_univ fun _ _ => one_pos⟩

end DifferentialGeometry.Topology.PiecewiseLinear
