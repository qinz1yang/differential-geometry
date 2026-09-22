/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierSupportLocallyFinite
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellLocallyFiniteCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Statements
import DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldOfLocallyFinitePLPieceIn
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsLocallyFinitePLPieceInOfIsOpen
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSubordinateToCover

/-!
# Sorry-first skeleton of P0, the controlled source triangulation and its carriers

The assembly `section34Control` proves the endpoint `Section34ControlStatement` for real from the
two leaves of this file and three proved modules; every `sorry` is a leaf and none sits
inside an assembly.

P0 is the **producer** of the two hypotheses that the controlled form of Moise 35.1 takes as
given: a locally finite triangulation `𝒦` of the open set `U` with
`IsCombinatorialManifold 3 𝒦.complex`, and a carrier system `H` with
`Section34CarrierControl U 𝒦 h η H`.  The realisation ambient is existential,
`EuclideanSpace ℝ (Fin N)` with `N` produced together with `𝒦`, exactly as in
`exists_section34NormalFamily`: `LocallyFinitePLPieceIn Ea 3 M₁ U` realises **all** of `U` inside
`Ea` by its `bijOn` field, so a fixed `Ea = EuclideanSpace ℝ (Fin 3)` would ask that `U` embed in
`ℝ³` and would exclude `U = M₁ = S³`.  A fixed finite `N` keeps `Ea` in `Type 0`, which is what
`Section34CarrierControl` and the consumer's `∀ (Ea : Type)` binder require.

How the endpoint feeds the controlled 35.1 skeleton.  `ControlledGraphNeighborhoodStatement`
binds, after `hU` and `hh`, exactly
`∀ (Ea : Type) [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]`
`(𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U), IsCombinatorialManifold 3 𝒦.complex →`
`∀ (η : M₁ → ℝ) (H : Finset Ea → Set M₂), Section34CarrierControl U 𝒦 h η H → …`.
Instantiating `Ea := EuclideanSpace ℝ (Fin N)` with the `N`, `𝒦`, `H` of this endpoint and the
same `U, h, η` discharges both of those hypotheses verbatim; the `M₁ M₂` instance list, `hU` and
`hh` are the same in the two statements, and the consumer leaves `η` free, so the continuity and
positivity this endpoint assumes are not needed there.  Skeletons cannot import each other, so the
match is by textual comparison of those binders and not by a shared `def`.  The consumer has no
`[Nonempty M₁]` in its instance list and needs none: it takes `𝒦` as a hypothesis, and a
`LocallyFinitePLPieceIn Ea 3 M₁ U` has a total field `map : Ea → M₁`, so `𝒦.map 0` inhabits `M₁`
there.  Only a *producer* of such a `𝒦`, like this endpoint, has to assume it; a caller that does
not yet hold a `𝒦` splits on `IsEmpty M₁` first, as the terminal skeleton's assembly does.

What the carrier clauses do and do not control.  `Section34CarrierControl` prescribes no
*shape* for the carrier `H t` relative to the image `h '' S_t` of the support
`S_t = Section34CarrierSupport 𝒦 t`; in particular `H t` is not asked to be a regular
neighbourhood of it.  It does control distances.  Its six clauses are
`h '' S_t ⊆ interior (H t)`, `H t ⊆ h '' U`, local finiteness of `H` in the subspace `h '' U`,
`dist y z < η x` for `x ∈ S_t` and `y, z ∈ H t`, `IsPLCellOn 3 (H t) (frontier (H t))`, and one
piecewise linear chart of `M₂` containing `H t`.  The first and the fourth already give
`x ∈ S_t → H t ⊆ Metric.ball (h x) (η x)`, because `h x ∈ H t` and every other point of `H t` is
at distance less than `η x` from it; so `H t` lies in the `η`-neighbourhood of `h '' S_t` and no
separate proximity clause is owed, and a smaller scale is obtained by shrinking the input `η`
rather than by adding a clause.  A closed piecewise linear `3`-cell read inside
one chart of `M₂`, small enough for `η` and contained in the open set `h '' U`, meets all six as
soon as `h '' S_t` lands in its interior.  The carriers are therefore taken from a locally finite
cover of `h '' U` by such cells, and the subdivision is taken subordinate to the `h`-preimages of
their open cores, which is what puts each `h '' S_t` inside one interior.  Version 1 of this file
instead demanded a cell hugging the possibly wild topological `3`-cell `h '' S_t`, whose leaf
`exists_isPLCellOn_image_of_isPLCellOn` needs a Bing-type approximation of a bicollared sphere
together with Schoenflies; that leaf and the swelling leaf `exists_isOpen_locallyFinite_superset`
that fed it are removed, and with them the cell clause of leaf (b).  No clause of
`Section34CarrierControl` is weakened, and the endpoint is unchanged.

The leaves, with content and review state.  Review AF read all five.  Four came back OK and are
now **frozen**: `exists_isPLCellOn_locallyFinite_cover_of_isOpen`,
`isCombinatorialManifold_of_locallyFinitePLPieceIn`, `locallyFinite_section34CarrierSupport` and
`exists_isSubdivision_section34CarrierSupport_subset`.  The fifth,
`exists_locallyFinitePLPieceIn_of_isOpen`, came back **false** for a missing `[Nonempty M₁]`; the
repair is the reviewer's own, was checked against the Lean text, and the leaf is frozen in the
repaired form.

`exists_locallyFinitePLPieceIn_of_isOpen` (a1): one locally finite complex in a *fixed* finite
dimensional ambient realising an arbitrary open subset of a piecewise linear `3`-manifold.  The
tree proves `exists_locallyFinitePieceTower_of_isOpen`, a tower of *compact* pieces whose ambient
dimension `(T.piece i).ambientDim` grows with `i`, glued by `IsGlueIso` maps; assembling one
locally finite complex in a single `ℝ^N` out of it is the recorded open foundational brick, not a
short consequence of the tower API, so it is a leaf.  General position embeds a locally finite
`3`-complex in `ℝ⁷`; the telescoping realisation with heights is the alternative, and the leaf
fixes neither, because `N` is existential.  The reviewer's warning is that the difficulty is
exactly this: the leaf must deliver **one** realisation in a fixed finite dimension whose
realising complex is *topologically* locally finite, and general position gives injectivity of a
map on an infinite complex without giving that local finiteness, so an appeal to general position
alone does not prove (a1).  Its `[Nonempty M₁]` is necessary and not a convenience: the structure
`LocallyFinitePLPieceIn E 3 M₁ U` carries a total field `map : E → M₁`, and
`E = EuclideanSpace ℝ (Fin N)` is nonempty for every `N`, `N = 0` included, so for `M₁ = ∅` no
such structure exists while every other hypothesis of the leaf still holds.

`isCombinatorialManifold_of_locallyFinitePLPieceIn` (a2): **proved**, imported from
`IsCombinatorialManifoldOfLocallyFinitePLPieceIn`. The real producer omits the redundant
`HasGroupoid` instance: the realization already carries both directions of the PL chart
certificates. The frozen statement is checked as a corollary, not claimed byte-identical
to the stronger public signature. The complex of *any* locally finite
piecewise linear realisation of an *open* subset of a piecewise linear `3`-manifold is a
combinatorial `3`-manifold.  Stated for every such realisation, which is the full conclusion of
(a1), so the composition needs no equation pinning the object to its producer.  It is the
classical fact that a triangulated `3`-manifold is combinatorial; openness of `U` is essential.

`locallyFinite_section34CarrierSupport` (a3): **proved**, imported from
`Section34CarrierSupportLocallyFinite` (2026-09-21, statement byte-identical with the frozen
leaf).  Each `Section34CarrierSupport 𝒦 t` lies
in `U`, and the family, indexed by the *faces*, is locally finite at every point of `U`.  The face
restriction is not cosmetic: for a `t` that is not a face but contains a vertex `w` of `𝒦` the
support still contains the closed star of `w`, and there are infinitely many such `t`.

`exists_isSubdivision_section34CarrierSupport_subset` (b): for an arbitrary open cover of `U` a
subdivision `𝒦₁` with the same realisation map, still a combinatorial `3`-manifold, each of whose
carrier supports lies in one member of the cover.  The cover is arbitrary, so the subdivision is
allowed to be finer and finer towards the ends of `U`; a uniform mesh would not do.  In a
simplicial complex two closed simplices meet in a common face, so `Section34CarrierSupport 𝒦₁ t`
is the simplicial neighbourhood of `|t|`, and shrinking every simplicial neighbourhood below a
prescribed open cover is the standard effect of iterated subdivision on each compact piece.  The
version 1 clause making that support a closed piecewise linear cell is gone: no clause of
`Section34CarrierControl` looks at the shape of a support.

`exists_isPLCellOn_locallyFinite_cover_of_isOpen` (c): **proved**, imported from
`PLCellLocallyFiniteCover` (2026-09-21, statement byte-identical with the frozen leaf).  It
is: an open set `Y` of a piecewise linear `3`-manifold, with a neighbourhood `N y` prescribed
at every `y ∈ Y`, carries a locally finite
family of closed piecewise linear `3`-cells `C i ⊆ Y`, each inside one `N y` and inside one
piecewise linear chart, whose open cores `G i ⊆ interior (C i)` still cover `Y`.  Elementary and
general: a compact exhaustion `K n ⊆ interior (K (n + 1))` of the locally compact, σ-compact `Y`,
each compact shell `K n \ interior (K (n - 1))` covered by finitely many cores of chart cubes
lying in `interior (K (n + 1)) \ K (n - 2)`; local finiteness at a point of `K m` holds because
`interior (K (m + 1))` misses every cell of every shell `n ≥ m + 3`.  For `Y = ∅` the empty index
type answers, and cells are nonempty, so no index is junk.

Proved here, not leaves.  `finite_inter_nonempty_of_isCompact_of_locallyFinite`: a family that is
locally finite on an ambient set meets a compact subset of it in finitely many members.
`nonempty_section34CarrierSupport`: the support of a face is nonempty, a face being a nonempty
finite set whose body lies in its own support.  `exists_section34ControlNeighborhood`: the
assignment `y ↦ N y`, where for `y = h x₀` the set `N y` is the ball of radius `η x₀ / 8` about
`y` intersected with the image of `{x ∈ U | η x₀ / 2 < η x}`, so that any two of its points are at
distance less than `η x` for every `x ∈ U` with `h x ∈ N y`; both margins are needed, the ball for
the diameter and the image for comparing `η x` with `η x₀`.
`exists_section34CarrierControl_of_cellCover`: it sets `H t := C (idx t)` and proves all six
clauses.  Local finiteness of the carriers is **proved** and is not an output demanded of a leaf:
near `y ∈ h '' U` only finitely many `C i` meet a neighbourhood; for each such `i` the set
`U ∩ h ⁻¹' C i` is compact, because `h` restricted to `U` is an embedding with range `h '' U` and
`C i` is a compact subset of that range; and a compact subset of `U` meets only finitely many of
the nonempty supports, by (a3).  Also proved: the openness of `h '' V` for every open `V ⊆ U`,
which is invariance of domain and is what makes `h '' U` an open set at all.

Vacuity.  `U = ∅` is allowed and stays allowed: it forces `𝒦.complex.space = ∅`, so there are no
faces, all six clauses of `Section34CarrierControl` and `IsCombinatorialManifold` are vacuous, the
cell cover of the empty `h '' U` is empty, and any `N` will do.  `M₁ = ∅` is **excluded**, by the
instance `[Nonempty M₁]` on the endpoint and on leaf (a1).  The reason is not vacuity but the
total field `map : E → M₁` of `LocallyFinitePLPieceIn E 3 M₁ U`: with `M₁ = ∅` and `U = ∅` every
other hypothesis holds, yet `E = EuclideanSpace ℝ (Fin N)` is nonempty for every `N`, so there is
no such structure and the unrepaired statement was false.  The hypothesis is `[Nonempty M₁]` and
never `U.Nonempty`: an empty open subset of a nonempty manifold must keep being allowed, and the
already proved tower producer assumes exactly `[Nonempty X]`.  `U = M₁ = S³` is compact and
needs `N ≥ 4`; nothing in the endpoint fixes `N = 3`.  A disconnected `U` is untouched, the
neighbourhood assignment being pointwise.  When `η` tends to `0` at an end of `U` the cells shrink
there, which is why (b) is stated for an arbitrary cover and (c) for an arbitrary neighbourhood
assignment.  A non piecewise linear `h` enters only through images of the supports and through
`IsOpen (h '' V)`; no clause asks `h` to be piecewise linear anywhere, and the carriers are
piecewise linear in `M₂` by construction and not by transport along `h`.  No carrier is
degenerate: `IsPLCellOn 3 (H t) (frontier (H t))` forces a nonempty `3`-cell whose ambient
frontier is its intrinsic boundary, and `h '' S_t ⊆ interior (H t)` with a nonempty `S_t` forces a
nonempty interior.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit): `exists_locallyFinitePLPieceIn_of_isOpen` (the proved piece tower with all
vertices on the moment curve in `ℝ⁷`, local finiteness proved in `ℝ⁷`; brick
`LocallyFinitePieceTower.toLocallyFinitePLPieceIn`) and
`exists_isSubdivision_section34CarrierSupport_subset` (the `relDerived` subdivision iterated to
region-dependent depths from local Lebesgue numbers; the real module states it without the unused
`[SecondCountableTopology M₁]` and `[HasGroupoid M₁ (plGroupoid 3)]`, a proved generalisation of
which the frozen leaf is the special case). With these the file has no `sorry` left:
`section34Control` is a real proof of `Section34ControlStatement`, and the module is ready to be
promoted out of `Skeleton/`.

Promoted out of `Skeleton/` on 2026-09-22: every former leaf is proved in an imported real module
(`PLCellLocallyFiniteCover`, `Section34CarrierSupportLocallyFinite` from the owner's lane;
`IsCombinatorialManifoldOfLocallyFinitePLPieceIn` from lane F;
`ExistsLocallyFinitePLPieceInOfIsOpen` and `SubdivisionSubordinateToCover` from an Opus 5.5
worker), so `section34Control` below is an unconditional proof of `Section34ControlStatement`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}

end Leaves

theorem finite_inter_nonempty_of_isCompact_of_locallyFinite {Λ : Type*} {M : Type*}
    [TopologicalSpace M] (sc : Λ → Set M) (Y K : Set M) (hK : IsCompact K) (hKY : K ⊆ Y)
    (hLF : ∀ x ∈ Y, ∃ V ∈ 𝓝 x, {l | (sc l ∩ V).Nonempty}.Finite) :
    {l | (sc l ∩ K).Nonempty}.Finite := by
  classical
  have key : ∀ x : M, ∃ V : Set M, x ∈ K → V ∈ 𝓝 x ∧ {l | (sc l ∩ V).Nonempty}.Finite := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨V, hV, hfin⟩ := hLF x (hKY hx)
      exact ⟨V, fun _ => ⟨hV, hfin⟩⟩
    · exact ⟨univ, fun hx' => absurd hx' hx⟩
  choose V hV using key
  obtain ⟨s, hsK, hs⟩ := hK.elim_nhds_subcover V fun x hx => (hV x hx).1
  refine (s.finite_toSet.biUnion fun x hx =>
    (hV x (hsK x (Finset.mem_coe.mp hx))).2).subset ?_
  rintro l ⟨y, hy, hyK⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hs hyK)
  exact mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, ⟨y, hy, hyx⟩⟩

theorem nonempty_section34CarrierSupport {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}
    (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    (Section34CarrierSupport 𝒦 t).Nonempty := by
  obtain ⟨w, hw⟩ := 𝒦.complex.nonempty_of_mem_faces ht
  exact ⟨𝒦.map w, Set.mem_biUnion (Finset.mem_coe.mpr hw)
    (Set.mem_biUnion (show t ∈ {s : Finset Ea | s ∈ 𝒦.complex.faces ∧ w ∈ s} from ⟨ht, hw⟩)
      (Set.mem_image_of_mem 𝒦.map (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))))⟩

theorem exists_section34ControlNeighborhood {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [MetricSpace M₂] {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hinj : InjOn h U)
    (himOpen : ∀ V : Set M₁, V ⊆ U → IsOpen V → IsOpen (h '' V)) (η : M₁ → ℝ)
    (hηc : ContinuousOn η U) (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ N : M₂ → Set M₂, ∀ y ∈ h '' U, N y ∈ 𝓝 y ∧
      ∀ w ∈ N y, ∀ z ∈ N y, ∀ x ∈ U, h x ∈ N y → dist w z < η x := by
  classical
  have key : ∀ y : M₂, ∃ Ny : Set M₂, y ∈ h '' U → Ny ∈ 𝓝 y ∧
      ∀ w ∈ Ny, ∀ z ∈ Ny, ∀ x ∈ U, h x ∈ Ny → dist w z < η x := by
    intro y
    by_cases hy : y ∈ h '' U
    · obtain ⟨x₀, hx₀, rfl⟩ := hy
      have hpos : 0 < η x₀ := hηpos x₀ hx₀
      refine ⟨Metric.ball (h x₀) (η x₀ / 8) ∩ h '' (U ∩ η ⁻¹' Set.Ioi (η x₀ / 2)),
        fun _ => ⟨?_, ?_⟩⟩
      · exact (Metric.isOpen_ball.inter (himOpen _ inter_subset_left
          (hηc.isOpen_inter_preimage hU isOpen_Ioi))).mem_nhds
          ⟨Metric.mem_ball_self (by linarith),
            ⟨x₀, ⟨hx₀, show η x₀ / 2 < η x₀ by linarith⟩, rfl⟩⟩
      · intro w hw z hz x hx hhx
        have hwd : dist w (h x₀) < η x₀ / 8 := Metric.mem_ball.mp hw.1
        have hzd : dist (h x₀) z < η x₀ / 8 := by
          rw [dist_comm]
          exact Metric.mem_ball.mp hz.1
        have htri := dist_triangle w (h x₀) z
        obtain ⟨x', hx', hx'eq⟩ := hhx.2
        have hxx : x' = x := hinj hx'.1 hx hx'eq
        have hηx : η x₀ / 2 < η x := by
          rw [← hxx]
          exact hx'.2
        linarith
    · exact ⟨univ, fun hy' => absurd hy' hy⟩
  choose N hN using key
  exact ⟨N, fun y hy => hN y hy⟩

theorem exists_section34CarrierControl_of_cellCover {Ea : Type} [NormedAddCommGroup Ea]
    [NormedSpace ℝ Ea] {M₁ M₂ : Type u} [TopologicalSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
    (hh : Topology.IsEmbedding (U.domRestrict h)) {η : M₁ → ℝ}
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) {ι : Type*} (C G : ι → Set M₂)
    (hCcell : ∀ i, IsPLCellOn 3 (C i) (frontier (C i))) (hGC : ∀ i, G i ⊆ interior (C i))
    (hCU : ∀ i, C i ⊆ h '' U)
    (hCchart : ∀ i, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, C i ⊆ c.source)
    (hClf : ∀ y ∈ h '' U, ∃ V ∈ 𝓝 y, {i | (C i ∩ V).Nonempty}.Finite)
    (hCdiam : ∀ i : ι, ∀ x ∈ U, h x ∈ C i → ∀ y ∈ C i, ∀ z ∈ C i, dist y z < η x)
    (hSsub : ∀ t ∈ 𝒦.complex.faces, ∃ i, Section34CarrierSupport 𝒦 t ⊆ U ∩ h ⁻¹' G i)
    (hSlf : ∀ x ∈ U, ∃ V ∈ 𝓝 x, {t : Finset Ea | t ∈ 𝒦.complex.faces ∧
      (Section34CarrierSupport 𝒦 t ∩ V).Nonempty}.Finite) :
    ∃ H : Finset Ea → Set M₂, Section34CarrierControl U 𝒦 h η H := by
  classical
  choose idx hidx using fun τ : 𝒦.complex.faces => hSsub (τ : Finset Ea) τ.2
  have hpre : ∀ S : Set M₂, Subtype.val '' (U.domRestrict h ⁻¹' S) = U ∩ h ⁻¹' S := by
    intro S
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨x, hx⟩, hxS, rfl⟩
      exact ⟨hx, hxS⟩
    · rintro x ⟨hx, hxS⟩
      exact ⟨⟨x, hx⟩, hxS, rfl⟩
  have hrange : Set.range (U.domRestrict h) = h '' U := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hKcpt : ∀ i, IsCompact (U ∩ h ⁻¹' C i) := by
    intro i
    rw [← hpre]
    exact (hh.isInducing.isCompact_preimage' (hCcell i).isCompact
      (hrange ▸ hCU i)).image continuous_subtype_val
  have hfib : ∀ i : ι, {τ : 𝒦.complex.faces | idx τ = i}.Finite := by
    intro i
    refine (finite_inter_nonempty_of_isCompact_of_locallyFinite
      (fun τ : 𝒦.complex.faces => Section34CarrierSupport 𝒦 (τ : Finset Ea)) U
      (U ∩ h ⁻¹' C i) (hKcpt i) inter_subset_left (fun x hx => ?_)).subset ?_
    · obtain ⟨V, hV, hfin⟩ := hSlf x hx
      exact ⟨V, hV, (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset
        fun τ hτ => ⟨τ.2, hτ⟩⟩
    · intro τ hτ
      obtain ⟨x₁, hx₁⟩ := nonempty_section34CarrierSupport 𝒦 τ.2
      have hsub := hidx τ
      rw [hτ] at hsub
      have hmem : h x₁ ∈ C i := interior_subset (hGC i (hsub hx₁).2)
      exact ⟨x₁, hx₁, (hsub hx₁).1, hmem⟩
  have hcarrier : ∀ t : Finset Ea, ∃ Ht : Set M₂,
      ∀ ht : t ∈ 𝒦.complex.faces, Ht = C (idx ⟨t, ht⟩) := by
    intro t
    by_cases ht : t ∈ 𝒦.complex.faces
    · exact ⟨C (idx ⟨t, ht⟩), fun _ => rfl⟩
    · exact ⟨∅, fun ht' => absurd ht' ht⟩
  choose Hfam hHfam using hcarrier
  refine ⟨Hfam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hHfam t ht]
    rintro _ ⟨x, hx, rfl⟩
    exact hGC _ (hidx ⟨t, ht⟩ hx).2
  · intro t ht
    rw [hHfam t ht]
    exact hCU _
  · intro y hy
    obtain ⟨V, hV, hfin⟩ := hClf y hy
    refine ⟨V, mem_nhdsWithin_of_mem_nhds hV,
      ((hfin.biUnion fun i _ => hfib i).image Subtype.val).subset ?_⟩
    rintro t ⟨ht, hne⟩
    rw [hHfam t ht] at hne
    exact ⟨⟨t, ht⟩, mem_iUnion₂.mpr ⟨idx ⟨t, ht⟩, hne, rfl⟩, rfl⟩
  · intro t ht x hx y hy z hz
    rw [hHfam t ht] at hy hz
    exact hCdiam _ x (hidx ⟨t, ht⟩ hx).1
      (interior_subset (hGC _ (hidx ⟨t, ht⟩ hx).2)) y hy z hz
  · intro t ht
    rw [hHfam t ht]
    exact hCcell _
  · intro t ht
    rw [hHfam t ht]
    exact hCchart _

theorem section34Control : Section34ControlStatement.{u} := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  have hcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  have himOpen : ∀ V : Set M₁, V ⊆ U → IsOpen V → IsOpen (h '' V) := fun V hVU hV =>
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hV (hcont.mono hVU)
      (hinj.mono hVU)
  obtain ⟨Nb, hNb⟩ := exists_section34ControlNeighborhood hU hinj himOpen η hηc hηpos
  obtain ⟨ι, C, G, hCcell, hGopen, hGC, hCU, hCN, hCchart, hcover, hClf⟩ :=
    exists_isPLCellOn_locallyFinite_cover_of_isOpen (himOpen U subset_rfl hU) Nb
      fun y hy => (hNb y hy).1
  obtain ⟨n, ⟨𝒦₀⟩⟩ := exists_locallyFinitePLPieceIn_of_isOpen (M₁ := M₁) hU
  obtain ⟨𝒦, -, -, h𝒦, hSsub⟩ :=
    exists_isSubdivision_section34CarrierSupport_subset hU 𝒦₀
      (isCombinatorialManifold_of_locallyFinitePLPieceIn hU 𝒦₀) (fun i => U ∩ h ⁻¹' G i)
      (fun i => hcont.isOpen_inter_preimage hU (hGopen i))
      (fun x hx => by
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
        exact mem_iUnion.mpr ⟨i, hx, hi⟩)
  obtain ⟨-, hSlf⟩ := locallyFinite_section34CarrierSupport 𝒦
  have hCdiam : ∀ i : ι, ∀ x ∈ U, h x ∈ C i → ∀ y ∈ C i, ∀ z ∈ C i, dist y z < η x := by
    intro i x hx hxC y hy z hz
    obtain ⟨y₀, hy₀, hsub⟩ := hCN i
    exact (hNb y₀ hy₀).2 y (hsub hy) z (hsub hz) x hx (hsub hxC)
  obtain ⟨H, hH⟩ := exists_section34CarrierControl_of_cellCover hh (η := η) 𝒦 C G hCcell hGC
    hCU hCchart hClf hCdiam hSsub hSlf
  exact ⟨n, 𝒦, H, h𝒦, hH⟩

end DifferentialGeometry.Topology.PiecewiseLinear
