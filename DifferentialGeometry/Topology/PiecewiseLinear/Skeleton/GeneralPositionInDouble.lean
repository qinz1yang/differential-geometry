/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoBuffered

/-!
# Sorry-first skeleton of general position in the double

The assembly `generalPositionInDoubleBuffered` below is proved for real from the fourteen leaves
of this file, from the proved cover theorem `exists_finiteAdaptedCover_of_compactSpace`, from the
proved bridge `eq_regionGluedMap_of_eqOn`, from
`SingularTwoCell.nonempty_normalSingularCellData_of_fields`, from
`doublePointSet_subset_of_preimage_singleton_eq_off` and from
`exists_boundary_loop_of_buffered_homotopy`; every `sorry` is a leaf, none is inside the
assembly.  The chain is: adapted half-space charts at every point of the double, a finite cover
of the whole double by regions `closure (W j) ⊆ V j` with `closure (V j)` inside one adapted
chart, one fixed common wall system, then a chart-by-chart induction on wall-adapted blocks.

The wall system is now a certificate, not a family of unrelated sets.  `IsCommonWallSystem Q ρ
Cf Bf BdM C ec ℓ Eb Eb'` records a finite simplicial complex `Q` of dimension at most three in a
realisation ambient `Ea` which is a type parameter, never a fixed `ℝ³`, together with the
realisation coordinate `ρ : M → Ea`, a continuous injection with `Set.range ρ = Q.space`; the
design's homeomorphism `|Q| ≅ M` is its inverse.  The three cells, their open cores, the walls
and the one-skeleton are then *defined* from `Q` and `ρ`: `wallSystemCells Q` are the faces with
four vertices, `wallSystemWalls Q` those with three, `wallSystemCell ρ s = ρ ⁻¹' convexHull s`,
`wallSystemCellInt ρ s = ρ ⁻¹' openSimplex s`, and `wallSystemSkeleton Q ρ` is the union of the
cells of the faces with at most two vertices.  Hence `wallSystemCellInt_subset_wallSystemCell`,
`isClosed_wallSystemCell`, `isClosed_wallSystemSkeleton`, `iUnion_wallSystemCell_eq_univ`,
`disjoint_wallSystemCellInt_wallSystemCell`, `wallSystemCell_sdiff_subset_iUnion_wall`,
`wallSystemCell_inter_subset_wallSystemSkeleton`, `isOpen_wallSystemCellInt` and the star
incidence lemmas `wallSystemStar_inter_wall_subset`,
`wallSystemStar_subset_union_wallSystemCell` are proved theorems, not recorded hypotheses.
`C` and `BdM` are the unions of the cells of designated subcomplexes `Cf`, `Bf`, so that
`subset_iUnion_wallSystemCell_of_eq_boundary` proves that the physical boundary is covered by
walls.  Since `M` is the closed double, `wallSides` asks of *every* wall that it have exactly
two three cells, and `boundarySides` asks of a wall of `Bf` only that exactly one of them lie
in `Cf`: uniqueness among all cells would be unsatisfiable, because a wall of `BdM` is a face
of one cell of `C` and of its mirror copy.  `wallIncidence_simplexBoundary` and
`exists_wallIncidence_of_fourSimplexBoundary` inhabit the combinatorial fields
(`finiteFaces`, `dimLe`, `memCell`, `wallSides`, and a non-empty wall set) with the boundary
complex of a four simplex, a genuine triangulated closed three manifold; they also exhibit the
two distinct three cells of a wall, which is what makes uniqueness inside `Cf` the only
satisfiable form.  `wallSystemCell_subset_layer` derives `wall w ⊆ Eb' i` from the star clause.
The
certificate also carries the two compact layers, the adaptedness of every chart of the finite
family to the pair `(C, BdM)`, and the affineness of every such chart on the `ρ`-preimages of
the simplices lying in its compact layer: `ec i = A ∘ ρ` there.

A `WallProductBlock` is an `IsStableCrossingBlock` with all its clauses, disjoint from
`wallSystemSkeleton Q ρ`, together with a support type: inside one open three cell, or
straddling exactly one wall `w` whose two cells `cm ≠ cp` both contain `w` and are the two sides
of `{t = 0}` for the block's own parameter `t`, or a physical boundary half block with
`t = ℓ ∘ ec`.  `HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η` asks for finitely many such
blocks, each in its own chart of the fixed finite family and inside the `Eb` of that chart,
whose inner blocks cover the double points over an *open* set containing `Z`.  With
`Z k = ⋃ j < k, closure (W j)` the induction invariant is the global cell data together with
`HasWallProductBlocks (⇑cell) cell.domain … Q ρ (Z k) ηk` for the one fixed `Q`, `ρ`.
Normality over an open neighbourhood of `Z k` is the proved corollary
`exists_normalCrossing_of_hasWallProductBlocks`, which feeds the blocks to the frozen leaf
`hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock`.

The key computation (*).  A transition that is affine on both sides of a wall and agrees on it
is, in affine coordinates matching on the wall, `H (u, v, t) = (u + α t, v + β t, c t)` with
`c > 0` on each side, since an affine map fixing the plane `t = 0` pointwise has exactly this
shape.  With `s = t' / c` the transported graph is `a' (v', t') = a (v' - β s, s) + α s`, for
each fixed `t'` a translation, so `La`, `Lb` and the margin `η` are unchanged and only the box
shape and the full preimage clause have to be restored by shrinking the outer block.  That the
two affine branches of the transition agree on the whole wall plane, and not merely on the
piece the block sees, is the proved lemma `eqOn_wallPlane_of_eqOn_transition`; its hypothesis
`hspan` — the affine span of `⇑ec '' (cell cm ∩ cell cp)` contains the wall plane — is part of
the proof obligation of `wallProductBlock_transport`, which has to obtain it from the relative
openness of `chartBlock ∩ wall w` inside that plane, and is deliberately not a hypothesis of
the leaf.  The transport leaf also has to invert the affine map of `chartAffine` along the cell
in order to read the transition as an affine map of the chart target.

Why the old per-chart margin failed.  Consult W exhibits two flat sheets with a strict graph
margin in two charts which, after a translation tapered to zero on a fixed subdivision, have
their double line lying *inside* a wall of the later chart, where the four rays become the bent
model with `La * Lb ≥ 1`; so "old later margin plus current margin plus one frozen sheet" does
not give the later margin of the new map.  In a block the two graph equations `u = a (v, t)`,
`v = b (u, t)` with `La * Lb ≤ 1 - η` have at most one solution for each value of `t`
(`eq_of_snd_eq_of_isStableCrossingBlock`, `eq_of_mem_wall_of_isStableCrossingBlock`), so an old
double line inside a wall is not a wall product block.

Vacuity, clause by clause.  `IsStableCrossingBlock` is not satisfiable by degenerate data over
a set carrying double points: over a double point of a block the two graph projections force
two *different* sheets (`sheets_nonempty_of_isStableCrossingBlock`), and
`exists_sheets_of_hasWallProductBlocks` lifts this to the family; `0 < η` is a field of both
predicates.  `hasWallProductBlocks_empty` gives the base case `Z 0 = ∅` and nothing more.  The
counterexamples of review AB are excluded as follows.

* Fake cells `cell * = ∅`, `cellInt * = M`, no walls, `skel1 = ∅` (against the wall system, the
  transport leaf and the per-chart corollary): impossible, because `cellInt` and `cell` are now
  the same construction on the same face, `wallSystemCellInt_subset_wallSystemCell`, and
  `iUnion_wallSystemCell_eq_univ` forbids empty cells covering `M`.
* `skel1 = M` (against the generic producer): impossible, because
  `disjoint_wallSystemCellInt_wallSystemSkeleton` and `wallSystemCellInt_nonempty` give
  `wallSystemSkeleton_ne_univ`.
* The bump of review AB §2 — interpolated sheets `y = 0`, `y = x` inside the wall `x = 0`,
  the old second sheet `y = x + a q (x, t)` with a PL bump `q` vanishing at all coarse vertices
  (against the stability leaf): excluded by the new hypothesis `hlinear`, the frozen seed's
  facewise affineness of `ec ∘ D` on `R`, which the assembly no longer discards; with it
  `simplicialMap R (ec ∘ ⇑D) = ec ∘ ⇑D` on `Rc.space`, so the old double set is the
  interpolated one and the bump is not admissible data.
* Two free boundary edges `(-1,0,0)–(1,0,0)`, `(0,-1,0)–(0,1,0)` crossing on the physical
  boundary (against the generic producer and the recognition leaf): the premise of `hgenfold`
  is now `IsFreeDoubleGerm`, which contains `y ∉ BdM`, so a boundary double point is no longer
  forbidden to meet a wall; the physical boundary only has to avoid `wallSystemSkeleton Q ρ`.
* Three free triangles whose planes cross at one point of an open three cell (against the
  recognition leaf): excluded by the new hypothesis `hgfiber`, the two-point fibres of the
  *new* map `regionGluedMap …`, supplied in the assembly from `hcard'` through the proved
  bridge `eq_regionGluedMap_of_eqOn`; `hgcont` supplies the continuity across the gluing seam
  that compactness of the new double point set needs.

Two graphs with a margin are not two source sheets.  Review R refuted the claim that the
recognition of the complete source sheets at a margin-stable block was done.  Take
`γ : [0, 6] → ℝ²` linear through `(2, 0), (0, 0), (0, 2), (-2, 2), (-2, 0), (0, 0), (0, -2)`,
`S = [0, 6] × [-2, 2]`, `D (s, t) = (γ s, 4 + t)`, `ec = id`, `ℓ = z₃`,
`A (x, y, z) = (x, y, z - 4)`, `r = 1`, `tlo = -1`: collecting the two vertical half-sheets in
`SA` and the two horizontal ones in `SB` satisfies the full preimage equation, both graph
equations with `a = b = 0` and makes both graph projections bijective, yet the two genuine
sheets are two bent `L`s whose four rays occur in the cyclic order `AABB`.
`IsStableCrossingBlock` therefore carries, for each sheet, that its graph projection is a PL
homeomorphism onto its image and that at every sheet point over the *inner* block the sheet is a
neighbourhood of that point in `S` and its projection a neighbourhood of the projected point in
`blockHalfPlane tlo`; the outer block carries a compact buffer inside `ec.source`.
`isStableCrossingBlock_of_eqOn_sheets` transports a block along any map agreeing with the old
one on `SA ∪ SB` with the same full preimage, and is the common core of the two retention
lemmas `isStableCrossingBlock_of_eqOn_compl` and `isStableCrossingBlock_of_preimage_singleton_eq`.

Free means free in the source, and that is a neighbourhood condition.  Review V refuted the
predicate used until the seventh iteration with an unmoved rectangle outside `R` whose double
points have their second preimage outside `R`, where the universal quantifier over the simplices
of `R` containing it is empty.  `FreeSourceGerm R Ac g S y` now asks, of every fibre point, both
`R.space ∈ 𝓝[S] x` and that no simplex of `R` containing `x` has a frozen vertex;
`mem_space_of_freeSourceGerm` records that a free source germ has its whole fibre in `R.space`.
`IsFreeDoubleGerm` is that together with `y ∉ BdM`, `IsFreeBoundaryDoubleGerm` together with
`y ∈ BdM`, and `IsFreeInteriorDoubleGerm` adds that every fibre point is interior to a triangle.
Every double point of the glued map over `closure (W k)` is a free source germ, by the proved
theorem `freeSourceGerm_of_mem_closure`; that is why general position is asked for free germs
only, and why `exists_wallGenericVertexMap` carries no condition at a frozen or mixed germ.

Two scales, not one.  The third external review refuted the claim that a single `ε` can both
keep the perturbed chart image inside `⇑ec '' V` and measure the ambient error; preparation
returns an ambient `δ` and a chart `ε` with the conversion
`dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ`.  Admissibility is the
`Prop`-valued `AdmissibleVertexMap`: vertex error `< τ`, equality with `ec ∘ ⇑D` at vertices of
the frozen collar, height zero exactly at the physical boundary vertices `Bv`, positive height
at all other vertices; it is inhabited for every `τ > 0` by the unperturbed vertex map
(`exists_admissibleVertexMap_of_adaptedChart`) and monotone in `τ` (`AdmissibleVertexMap.mono`),
which is how the generic leaf's `τ` is fed back into the frozen leaf's `τ₀`.

The leaves, with owner and review state.  The eight leaves marked frozen are byte-identical with
the reviewed snapshot.  The six leaves of design Y passed the tenth review (digest AG): five as
they stood, `exists_wallGenericVertexMap` after the one interface repair it prescribed; all
fourteen leaves are now frozen.

`exists_adaptedHalfSpaceChart_in_double` (lane H, reviewed 2026-09-21, frozen): every point of
the double of a combinatorial three manifold with boundary has arbitrarily small charts of the
maximal `plGroupoid 3` atlas adapted to the actual pair.

`SingularTwoCell.exists_cutOutPiece_of_closure_subset` (lane H, reviewed 2026-09-21, frozen): the
cut-out source piece with boundary, its frozen collar `Ac` and the seam data `Ω`, `Nb`.

`exists_gluedCell_of_vertexMap_in_adaptedChart` (lane H, reviewed 2026-09-21, frozen): the
literal gluing, with equality on the whole complement.

`exists_globalInvariants_of_gluedCell` (lane H, reviewed 2026-09-21, frozen): the invariants of
the glued cell on the whole disk, with the buffered boundary homotopy.

`exists_normalizationPreparation_on_prescribedRegion` (lane H, reviewed 2026-09-21, frozen):
the control complex `T`, the scales `κ`, `δ`, `ε` and the three buffers, all before the
perturbation.

`exists_transitionSubdivisionOnOverlap` (lane H, reviewed 2026-09-21, frozen): on a compact
overlap of two adapted charts, a finite complex in the first chart's target covering a whole
neighbourhood of the overlap, on whose faces the transition is affine.  **No longer on the
assembly path**: the pairwise overlap complexes are superseded by the one common wall system of
`exists_commonWallComplex`, of which this leaf is the local input.  The statement is retained
unchanged because a proof of the common system will consume it.

`hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` (lane H, reviewed 2026-09-21, frozen): a
margin-stable block is a PL normal double crossing at each double point of its *inner* block.

`exists_protectedSubdivision_in_adaptedChart` (lane H, reviewed 2026-09-21, frozen): the seed.
It fixes `R`, `τ₀` and the compact `Kt` before any vertex map and asserts, for every admissible
`φ`, the control clauses.  The assembly uses `R`, `τ₀`, `Kt`, the facewise affineness of
`ec ∘ ⇑D` on `R` and the control clauses.  **Two parts of its conclusion are not on the
assembly path**: `hprot`, because all normality now comes from the blocks, and `hpersist`, the
current-chart blocks with margin `η / 2`, because those blocks carry no support type.

`exists_commonWallComplex` (design Y, reviewed OK, frozen): stated for the
double itself, so that the realisation is the given one: from the finite chart family and its
adaptedness to the pair, a *subdivision* `Q` of the
double complex `double 3 K`, with `ρ` the subtype coercion, forming a common wall system with
the two compact layers and the star clause.  `C` and `BdM` are subcomplexes of `double 3 K`
already, so no cover of the double is assumed: the cover belongs to the global assembly, the
chart readings `0 ≤ ℓ`, `ℓ = 0` supply `chartC`, `chartBd`, and `chartAtlas` supplies the piecewise
linear compatibility; the proof subdivides so that every chart becomes affine on the cells of
its compact layer, which is where `exists_transitionSubdivisionOnOverlap` enters.  `wallSides`
has to come from the face incidence of a closed three manifold, `double 3 K` being one by
`isCombinatorialManifold_double_succ_succ`, preserved under subdivision; it does not follow
from `dimLe` and `memCell` alone.  A wall of `BdM` still has two cells, exactly one of them in
`Cf`, which is what `boundarySides` says.

`wallProductBlock_transport` (design Y, reviewed OK, frozen): the computation
(*) from the certificate's `chartAffine`, transporting a wall product block of one chart to a
wall product block of another chart *for the same certificate*, on a smaller outer block centred
at a prescribed inner point and localised into a prescribed open set, with the same `La`, `Lb`,
`η`.  Its two proof obligations follow from the fields: a *nonempty* relatively open piece of a
wall contains three affinely independent points and so spans the wall plane; and the affine map
of `chartAffine` is inverted only after restriction to `affineSpan ℝ ↑c` of a three cell, where
it is injective and both sides have dimension three, never on the whole ambient `Ea`.

`hasStableCrossingBlocks_of_wallProductBlocks` (design Y, reviewed OK, frozen):
over a compact `Z'` inside `interior (Eb i₀)` the wall product blocks transport to margin-stable
blocks in the chart `i₀`.  Its proof is the single-block transport plus a finite subcover of the
compact set `doublePointSet f S ∩ Z'`, which lies in `C` by `hmapC`; `Z' ⊆ C` is *not*
assumed.  It is the only supplier of the frozen seed's `hstable`.

`wallProductBlocks_stable_on_fixedSubdivision` (design Y, reviewed OK as stated, frozen):
on the final `R` of the frozen seed, and with its facewise affineness `hlinear`, there is
`0 < τ ≤ τ₀` such that every admissible `φ` with error `< τ` keeps a wall-adapted certificate
over `Z` with margin `η / 2` *for the same `Q`, `ρ`*.  No subdivision is made after `τ`.  "The
same `Q`, `ρ`" is not "the same wall label block by block": the conclusion quantifies the new
block family afresh and promises no correspondence with the old one.  The present consumer
needs only existence; a consumer that used the old type (ii) wall would need named witnesses
and a refinement relation with equal wall labels.

`exists_wallGenericVertexMap` (design Y, repaired as review ten prescribed, frozen): relative
density of the finite wall conditions, for free germs only — the four-point guard, free germs avoid
`wallSystemSkeleton Q ρ`, a double point on the image of a source edge of an *interior* free
germ avoids every wall, and at a free interior germ on a wall the double point set accumulates
in both adjacent open three cells.  It receives `hlinear`, and `hVE : closure V ⊆ interior (Eb i₀)`:
`hVec` alone puts the active region in the chart, where `chartAffine` says nothing unless whole
cells lie in the layer `Eb' i₀`; with `hVE`, the finite mesh and `hlinear` let the perturbation be
shrunk until the interpolated image stays in the layer, and `starLayer` then reaches `chartAffine`.

`wallProductBlocks_of_wallGenericity` (design Y, reviewed OK, frozen):
recognition of the four free models — three cell interior triangle-triangle, source fold edge,
interior wall, physical boundary — giving the whole certificate over `closure (W k)`.  It
receives the continuity `hgcont` and the two-point fibres `hgfiber` of the *new* map.

The leaf most likely still wrong is `wallProductBlocks_stable_on_fixedSubdivision`: it is the
one that has to convert "the old wall blocks survive" into "the new blocks are again
wall-adapted for the same fixed wall system", and it is *not* asked in Lean to keep the same
wall for the centre region of a type (ii) block — that is recorded here as a proof obligation
and as a question for the reviewer, not as a clause of the statement.  The digest proves the
margin part only modulo
the seam estimate `Lip ((p_φ − p₀) ∘ q⁻¹) ≤ C ‖φ − φ₀‖_∞`; that the new type (ii) block keeps
the *same* wall as the old one is what its proof has to arrange by keeping the wall and its
normal coordinate and re-choosing only the source sheets and the small box.

Fixture.  In a double cube, the product `γ × [-1, 1]` with `γ` the broken line through
`(-2, -1)`, `(1, 1)`, `(-1, 1)`, `(2, -1)`, a genuine common subdivision of the double complex
whose walls contain the crossing points of `γ`, a frozen outer collar and a non-zero small
perturbation of the free vertices satisfy every hypothesis of every new leaf, with a non-empty
double point set, a non-empty block family, free interior germs along the interior of the
crossing arc and free boundary germs where that arc meets `BdM`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_adaptedHalfSpaceChart_in_double {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (y : (double 3 K).space) (U : Set (double 3 K).space), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧
          y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ Bd ↔ ℓ (ec x) = 0) := by
  sorry

def UniformInjectivityScale {α : Type*} [PseudoMetricSpace α] {β : Type*} (S : Set α)
    (f : α → β) (η : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dist x y < η → f x = f y → x = y

theorem uniformInjectivityScale_of_injOn {α : Type*} [PseudoMetricSpace α] {β : Type*}
    {S : Set α} {f : α → β} (h : InjOn f S) (η : ℝ) : UniformInjectivityScale S f η :=
  fun _ hx _ hy _ hxy => h hx hy hxy

open Classical in
def StarInj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    (T : Geometry.SimplicialComplex ℝ E) (g : E → β) : Prop :=
  ∀ v ∈ T.vertices, InjOn g (starComplex T v).space

open Classical in
theorem starInj_of_injOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    {T : Geometry.SimplicialComplex ℝ E} {g : E → β} (h : InjOn g T.space) : StarInj T g := by
  intro v _
  exact Set.InjOn.mono (space_mono_of_faces_subset (starComplex_faces_subset T v)) h

theorem preimage_singleton_eq_of_eqOn_compl_of_image_subset {α β : Type*} {f f' : α → β}
    {R : Set α} {P : Set β} (hoff : EqOn f' f Rᶜ) (hf : f '' R ⊆ P) (hf' : f' '' R ⊆ P)
    {y : β} (hy : y ∉ P) : f' ⁻¹' {y} = f ⁻¹' {y} := by
  ext x
  by_cases hx : x ∈ R
  · simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      exact absurd (h ▸ hf' (mem_image_of_mem f' hx)) hy
    · intro h
      exact absurd (h ▸ hf (mem_image_of_mem f hx)) hy
  · simp only [mem_preimage, mem_singleton_iff, hoff hx]

def blockBox (r tlo : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1| ≤ r ∧ |p.2.1| ≤ r ∧ p.2.2 ∈ Icc tlo r}

def blockHalfPlane (tlo : ℝ) : Set (ℝ × ℝ) :=
  {p | tlo = 0 → 0 ≤ p.2}

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem exists_finiteAdaptedCover_of_compactSpace [T2Space M] [CompactSpace M] (BdM C : Set M)
    (hchart : ∀ (y : M) (U : Set M), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)) :
    ∃ (n : ℕ) (W V : ℕ → Set M),
      (∀ j, IsOpen (W j)) ∧ (∀ j, IsOpen (V j)) ∧ (∀ j, closure (W j) ⊆ V j) ∧
        (∀ j, n ≤ j → W j = ∅) ∧ (⋃ j, W j) = univ ∧
        ∀ j < n, ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
          (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
          ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ closure (V j) ⊆ ec.source ∧
            (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
            (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M
  have key : ∀ y : M, ∃ (Wy Vy : Set M)
      (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      IsOpen Wy ∧ y ∈ Wy ∧ IsOpen Vy ∧ closure Wy ⊆ Vy ∧ closure Vy ⊆ ec.source ∧
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧
        (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
        (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
    intro y
    obtain ⟨ec, ℓ, hec, hℓ, hy, -, hC, hBd⟩ := hchart y univ Filter.univ_mem
    obtain ⟨s, hs, hsub, hcomp⟩ := local_compact_nhds (ec.open_source.mem_nhds hy)
    have hVopen : IsOpen (interior s) := isOpen_interior
    have hyV : y ∈ interior s := mem_interior_iff_mem_nhds.2 hs
    have hclV : closure (interior s) ⊆ ec.source :=
      (closure_mono interior_subset).trans (hcomp.isClosed.closure_eq.subset.trans hsub)
    obtain ⟨s', hs', hsub', hcomp'⟩ := local_compact_nhds (hVopen.mem_nhds hyV)
    exact ⟨interior s', interior s, ec, ℓ, isOpen_interior,
      mem_interior_iff_mem_nhds.2 hs', hVopen,
      (closure_mono interior_subset).trans (hcomp'.isClosed.closure_eq.subset.trans hsub'),
      hclV, hec, hℓ, hC, hBd⟩
  choose Wy Vy ecy ℓy hWopen hymem hVyopen hWVy hVycl hecm hℓne hCm hBdm using key
  obtain ⟨t, -, hcover⟩ :=
    isCompact_univ.elim_nhds_subcover Wy fun y _ => (hWopen y).mem_nhds (hymem y)
  let p : ∀ j : ℕ, j < t.card → M := fun j h => ((t.equivFin.symm ⟨j, h⟩ : {x // x ∈ t}) : M)
  refine ⟨t.card, fun j => if h : j < t.card then Wy (p j h) else ∅,
    fun j => if h : j < t.card then Vy (p j h) else ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hVyopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWVy _
    · simp only [dif_neg h, closure_empty]
      exact Subset.rfl
  · intro j hj
    exact dif_neg (not_lt.2 hj)
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    refine mem_iUnion.2 ⟨((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ), ?_⟩
    rw [dif_pos (t.equivFin ⟨y, hy⟩).isLt]
    have hval : p ((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ) (t.equivFin ⟨y, hy⟩).isLt = y :=
      congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨y, hy⟩)
    rw [hval]
    exact hxy
  · intro j hj
    refine ⟨ecy (p j hj), ℓy (p j hj), hecm _, hℓne _, ?_, hCm _, hBdm _⟩
    simp only [dif_pos hj]
    exact hVycl _

theorem SingularTwoCell.exists_cutOutPiece_of_closure_subset [T2Space M] (D : SingularTwoCell M)
    {V₀ V : Set M} (hV : IsOpen V) (hV₀ : closure V₀ ⊆ V) :
    ∃ (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Ω Nb : Set (EuclideanSpace ℝ (Fin 2))),
      Rc.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 Rc ∧
        Lc.faces ⊆ Rc.faces ∧ Ac.faces ⊆ Rc.faces ∧
        Rc.space ⊆ D.domain ∧ Rc.space ⊆ ⇑D ⁻¹' V ∧
        Lc.space = Rc.space ∩ frontier D.domain ∧
        IsOpen Ω ∧ D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω ∧ D.domain ∩ Ω ⊆ Rc.space ∧
        IsOpen Nb ∧ Rc.space \ Ω ⊆ Nb ∧ Rc.space ∩ Nb ⊆ Ac.space ∧
        Disjoint Ac.space (⇑D ⁻¹' closure V₀) := by
  sorry

theorem exists_gluedCell_of_vertexMap_in_adaptedChart [T2Space M] (D : SingularTwoCell M)
    {V : Set M} (hVopen : IsOpen V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpl : IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space)
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V)) :
    ∃ D' : SingularTwoCell M, D'.domain = D.domain ∧
      EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space ∧
      EqOn (⇑D') (⇑D) Rc.spaceᶜ := by
  sorry

def chartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' blockBox r tlo)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem chartBlock_mono_of_half (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) {r tlo : ℝ} (hr : 0 ≤ r) (ht : tlo ≤ 0) :
    chartBlock ec A (r / 2) (tlo / 2) ⊆ chartBlock ec A r tlo := by
  intro x hx
  obtain ⟨hxs, hxb⟩ := hx
  refine ⟨hxs, ?_⟩
  simp only [mem_preimage, blockBox, mem_ofPred_eq, mem_Icc] at hxb ⊢
  exact ⟨hxb.1.trans (by linarith), hxb.2.1.trans (by linarith),
    by linarith [hxb.2.2.1], by linarith [hxb.2.2.2]⟩

def innerChartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  chartBlock ec A (r / 2) (tlo / 2)

noncomputable def blockSheetProjA (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).2.1, (A (ec (f x))).2.2)

noncomputable def blockSheetProjB (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).1, (A (ec (f x))).2.2)

def FreeSourceGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (y : M) : Prop :=
  ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x ∧ ∀ σ ∈ R.faces,
    x ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) → ∀ v ∈ σ, v ∉ Ac.space

def IsFreeDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∉ BdM ∧ FreeSourceGerm R Ac g S y

def IsFreeBoundaryDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∈ BdM ∧ FreeSourceGerm R Ac g S y

def IsFreeInteriorDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  IsFreeDoubleGerm R Ac g S BdM y ∧
    ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem mem_space_of_freeSourceGerm
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {y : M}
    (h : FreeSourceGerm R Ac g S y) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ S ∩ g ⁻¹' {y}) : x ∈ R.space :=
  mem_of_mem_nhdsWithin hx.1 (h x hx).1

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem freeSourceGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {y : M}
    (hAc : Ac.space = ∅) (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    FreeSourceGerm R Ac g S y := by
  refine fun x hx => ⟨hnhds x hx, fun _ _ _ v _ => ?_⟩
  rw [hAc]
  exact notMem_empty v

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∉ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    IsFreeDoubleGerm R Ac g S BdM y :=
  ⟨hy, freeSourceGerm_of_frozenSpace_eq_empty hAc hnhds⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeBoundaryDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∈ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    IsFreeBoundaryDoubleGerm R Ac g S BdM y :=
  ⟨hy, freeSourceGerm_of_frozenSpace_eq_empty hAc hnhds⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeInteriorDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∉ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x)
    (hint : ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))) :
    IsFreeInteriorDoubleGerm R Ac g S BdM y :=
  ⟨isFreeDoubleGerm_of_frozenSpace_eq_empty hAc hy hnhds, hint⟩

def IsStableCrossingBlock (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM : Set M)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  0 < r ∧ 0 < η ∧ 0 ≤ La ∧ 0 ≤ Lb ∧ La * Lb ≤ 1 - η ∧
    IsCompact (closure (chartBlock ec A r tlo)) ∧
    closure (chartBlock ec A r tlo) ⊆ ec.source ∧
    ((tlo = -r ∧ Disjoint (chartBlock ec A r tlo) BdM) ∨
        (tlo = 0 ∧ (∀ z, (A z).2.2 = ℓ z) ∧
          ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))) ∧
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB ∧ Disjoint SA SB ∧
    (∀ x ∈ SA, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) ∧
    (∀ x ∈ SB, (A (ec (f x))).2.1 = b ((A (ec (f x))).1, (A (ec (f x))).2.2)) ∧
    IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA) ∧
    IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB) ∧
    (∀ x ∈ SA, f x ∈ innerChartBlock ec A r tlo → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjA ec A f x)) ∧
    (∀ x ∈ SB, f x ∈ innerChartBlock ec A r tlo → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjB ec A f x)) ∧
    (∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|) ∧
    (∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|) ∧
    IsPiecewiseAffineOn a univ ∧ IsPiecewiseAffineOn b univ

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.margin_pos {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) : 0 < η :=
  h.2.1

def HasStableCrossingBlocks (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM Q : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (m : ℕ) (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ))
      (r tlo : Fin m → ℝ) (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2)))
      (a b : Fin m → ℝ × ℝ → ℝ) (La Lb : Fin m → ℝ),
      doublePointSet f S ∩ Q ⊆ ⋃ i, innerChartBlock ec (A i) (r i) (tlo i) ∧
        ∀ i, IsStableCrossingBlock f S ec ℓ BdM (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i)
          (La i) (Lb i) η

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.mono {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q Q' : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η) (hQ : Q' ⊆ Q) :
    HasStableCrossingBlocks f S ec ℓ BdM Q' η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb,
    (inter_subset_inter Subset.rfl hQ).trans hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.mono_margin {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η η' : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hη' : 0 < η') (hle : η' ≤ η) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η' :=
  ⟨h.1, hη', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans (by linarith), h.2.2.2.2.2⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.mono_doublePointSet {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q Q' : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η)
    (hQ : doublePointSet f S ∩ Q' ⊆ doublePointSet f S ∩ Q) :
    HasStableCrossingBlocks f S ec ℓ BdM Q' η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hQ.trans hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.union {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q₁ Q₂ : Set M} {η₁ η₂ : ℝ}
    (h₁ : HasStableCrossingBlocks f S ec ℓ BdM Q₁ η₁)
    (h₂ : HasStableCrossingBlocks f S ec ℓ BdM Q₂ η₂) :
    HasStableCrossingBlocks f S ec ℓ BdM (Q₁ ∪ Q₂) (min η₁ η₂) := by
  obtain ⟨hη₁, m₁, A₁, r₁, t₁, SA₁, SB₁, a₁, b₁, La₁, Lb₁, hcov₁, hblk₁⟩ := h₁
  obtain ⟨hη₂, m₂, A₂, r₂, t₂, SA₂, SB₂, a₂, b₂, La₂, Lb₂, hcov₂, hblk₂⟩ := h₂
  refine ⟨lt_min hη₁ hη₂, m₁ + m₂, Fin.addCases A₁ A₂, Fin.addCases r₁ r₂,
    Fin.addCases t₁ t₂, Fin.addCases SA₁ SA₂, Fin.addCases SB₁ SB₂, Fin.addCases a₁ a₂,
    Fin.addCases b₁ b₂, Fin.addCases La₁ La₂, Fin.addCases Lb₁ Lb₂, ?_, ?_⟩
  · rintro y ⟨hy, hQ | hQ⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₁ ⟨hy, hQ⟩)
      refine mem_iUnion.2 ⟨Fin.castAdd m₂ i, ?_⟩
      simpa only [Fin.addCases_left] using hi
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₂ ⟨hy, hQ⟩)
      refine mem_iUnion.2 ⟨Fin.natAdd m₁ i, ?_⟩
      simpa only [Fin.addCases_right] using hi
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using
        (hblk₁ i).mono_margin (lt_min hη₁ hη₂) (min_le_left _ _)
    · simpa only [Fin.addCases_right] using
        (hblk₂ i).mono_margin (lt_min hη₁ hη₂) (min_le_right _ _)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ}
    (hQ : doublePointSet f S ∩ Q = ∅) (hη : 0 < η) :
    HasStableCrossingBlocks f S ec ℓ BdM Q η := by
  refine ⟨hη, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    Fin.elim0, Fin.elim0, ?_, fun i => i.elim0⟩
  rw [hQ]
  exact empty_subset _

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem sheets_nonempty_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) :
    (SA ∩ f ⁻¹' {y}).Nonempty ∧ (SB ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, hplA, hplB, -, -, -, -, -, -⟩ := h
  obtain ⟨x, hxS, z, hzS, hxz, hxy, hzy⟩ := hy
  have hfeq : f x = f z := by rw [hxy, hzy]
  have hxmem : x ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hxS, by simp only [mem_preimage, hxy]; exact hyB⟩
  have hzmem : z ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hzS, by simp only [mem_preimage, hzy]; exact hyB⟩
  have hnotA : ¬(x ∈ SA ∧ z ∈ SA) := by
    rintro ⟨hxA, hzA⟩
    exact hxz (hplA.bijOn.injOn hxA hzA (by simp only [blockSheetProjA, hfeq]))
  have hnotB : ¬(x ∈ SB ∧ z ∈ SB) := by
    rintro ⟨hxB, hzB⟩
    exact hxz (hplB.bijOn.injOn hxB hzB (by simp only [blockSheetProjB, hfeq]))
  rcases hxmem with hxA | hxB
  · rcases hzmem with hzA | hzB
    · exact absurd ⟨hxA, hzA⟩ hnotA
    · exact ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  · rcases hzmem with hzA | hzB
    · exact ⟨⟨z, hzA, hzy⟩, ⟨x, hxB, hxy⟩⟩
    · exact absurd ⟨hxB, hzB⟩ hnotB

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_sheets_of_hasStableCrossingBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Q) :
    ∃ SA' SB' : Set (EuclideanSpace ℝ (Fin 2)),
      Disjoint SA' SB' ∧ (SA' ∩ f ⁻¹' {y}).Nonempty ∧ (SB' ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hy)
  obtain ⟨hr0, -, -, -, -, -, -, hside, -, hdisj, -, -, -, -, -, -, -, -, -, -⟩ := hblk i
  have ht : tlo i ≤ 0 := by
    rcases hside with ⟨h1, -⟩ | ⟨h1, -, -⟩
    · rw [h1]; linarith
    · exact le_of_eq h1
  obtain ⟨hA, hB⟩ := sheets_nonempty_of_isStableCrossingBlock (hblk i) hy.1
    (chartBlock_mono_of_half ec (A i) (le_of_lt hr0) ht hi)
  exact ⟨SA i, SB i, hdisj, hA, hB⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_flatSheets {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x)) :
    IsStableCrossingBlock f S ec ℓ BdM A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, hcpt, hsrc, Or.inl ⟨rfl, hBd⟩, hpre, hdisj,
    hA, hB, hplA, hplB, hnA, hnB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_flatSheets_boundary {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r 0)))
    (hsrc : closure (chartBlock ec A r 0) ⊆ ec.source)
    (hheight : ∀ z, (A z).2.2 = ℓ z)
    (hfront : ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))
    (hpre : S ∩ f ⁻¹' chartBlock ec A r 0 = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r 0 → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane 0] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r 0 → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane 0] (blockSheetProjB ec A f x)) :
    IsStableCrossingBlock f S ec ℓ BdM A r 0 SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, hcpt, hsrc,
    Or.inr ⟨rfl, hheight, hfront⟩, hpre, hdisj, hA, hB, hplA, hplB, hnA, hnB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_eqOn_sheets {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hgeq : EqOn g f (SA ∪ SB))
    (hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  obtain ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, hside, -, hdisj, hgA, hgB, hplA, hplB,
    hnA, hnB, hLipa, hLipb, hpa, hpb⟩ := h
  have hprojA : EqOn (blockSheetProjA ec A g) (blockSheetProjA ec A f) SA := by
    intro x hx
    simp only [blockSheetProjA, hgeq (Or.inl hx)]
  have hprojB : EqOn (blockSheetProjB ec A g) (blockSheetProjB ec A f) SB := by
    intro x hx
    simp only [blockSheetProjB, hgeq (Or.inr hx)]
  have himA : blockSheetProjA ec A g '' SA = blockSheetProjA ec A f '' SA := image_congr hprojA
  have himB : blockSheetProjB ec A g '' SB = blockSheetProjB ec A f '' SB := image_congr hprojB
  refine ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, ?_, hpre', hdisj, ?_, ?_, ?_, ?_, ?_, ?_,
    hLipa, hLipb, hpa, hpb⟩
  · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr ⟨h1, h2, fun x hx => ?_⟩
      rw [hgeq hx]
      exact h3 x hx
  · intro x hx
    rw [hgeq (Or.inl hx)]
    exact hgA x hx
  · intro x hx
    rw [hgeq (Or.inr hx)]
    exact hgB x hx
  · rw [himA]
    exact hplA.congr hprojA
  · rw [himB]
    exact hplB.congr hprojB
  · intro x hx hxb
    rw [hgeq (Or.inl hx)] at hxb
    rw [himA, hprojA hx]
    exact hnA x hx hxb
  · intro x hx hxb
    rw [hgeq (Or.inr hx)] at hxb
    rw [himB, hprojB hx]
    exact hnB x hx hxb

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem preimage_chartBlock_eq_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) :
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact hpre

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_preimage_singleton_eq {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM N : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hN : chartBlock ec A r tlo ⊆ N)
    (hfib : ∀ z ∈ N, S ∩ g ⁻¹' {z} = S ∩ f ⁻¹' {z}) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  have hpre := preimage_chartBlock_eq_of_isStableCrossingBlock h
  have hgeq : EqOn g f (SA ∪ SB) := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    have hmem : x ∈ S ∩ g ⁻¹' {f x} := by
      rw [hfib (f x) (hN hxpre.2)]
      exact ⟨hxpre.1, rfl⟩
    exact hmem.2
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hmem : x ∈ S ∩ f ⁻¹' {g x} := by
        rw [← hfib (g x) (hN hx.2)]
        exact ⟨hx.1, rfl⟩
      have hfx : f x = g x := hmem.2
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, hfx]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq hx]; exact hxpre.2⟩
  exact isStableCrossingBlock_of_eqOn_sheets h hgeq hpre'

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_eqOn_compl {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S Rgn : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hoff : EqOn g f Rgnᶜ) (hfree : Disjoint Rgn (S ∩ f ⁻¹' chartBlock ec A r tlo))
    (hfree' : Disjoint Rgn (S ∩ g ⁻¹' chartBlock ec A r tlo)) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  have hpre := preimage_chartBlock_eq_of_isStableCrossingBlock h
  have hgeq : EqOn g f (SA ∪ SB) := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    exact hoff fun hxR => (disjoint_left.mp hfree hxR) hxpre
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hxR : x ∉ Rgn := fun hxR => (disjoint_left.mp hfree' hxR) hx
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, ← hoff hxR]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq hx]; exact hxpre.2⟩
  exact isStableCrossingBlock_of_eqOn_sheets h hgeq hpre'

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eq_of_snd_eq_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y z : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo)
    (hz : z ∈ doublePointSet f S) (hzB : z ∈ chartBlock ec A r tlo)
    (ht : (A (ec y)).2.2 = (A (ec z)).2.2) : y = z := by
  have hgraph : ∀ p : M, p ∈ doublePointSet f S → p ∈ chartBlock ec A r tlo →
      (A (ec p)).1 = a ((A (ec p)).2.1, (A (ec p)).2.2) ∧
        (A (ec p)).2.1 = b ((A (ec p)).1, (A (ec p)).2.2) := by
    intro p hp hpB
    obtain ⟨⟨x, hxA, hxp⟩, ⟨x', hx'B, hx'p⟩⟩ :=
      sheets_nonempty_of_isStableCrossingBlock h hp hpB
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hgA, hgB, -, -, -, -, -, -, -, -⟩ := h
    have hfx : f x = p := hxp
    have hfx' : f x' = p := hx'p
    exact ⟨by simpa only [hfx] using hgA x hxA, by simpa only [hfx'] using hgB x' hx'B⟩
  obtain ⟨hay, hby⟩ := hgraph y hy hyB
  obtain ⟨haz, hbz⟩ := hgraph z hz hzB
  obtain ⟨-, hη, hLa, hLb, hmar, -, -, -, -, -, -, -, -, -, -, -, hLipa, hLipb, -, -⟩ := h
  have hP : (0 : ℝ) ≤ |(A (ec y)).1 - (A (ec z)).1| := abs_nonneg _
  have hQ : (0 : ℝ) ≤ |(A (ec y)).2.1 - (A (ec z)).2.1| := abs_nonneg _
  have h1 : |(A (ec y)).1 - (A (ec z)).1| ≤ La * |(A (ec y)).2.1 - (A (ec z)).2.1| := by
    rw [hay, haz, ht]
    exact hLipa _ _ _
  have h2 : |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ Lb * |(A (ec y)).1 - (A (ec z)).1| := by
    rw [hby, hbz, ht]
    exact hLipb _ _ _
  have h3 : La * |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ La * (Lb * |(A (ec y)).1 - (A (ec z)).1|) :=
    mul_le_mul_of_nonneg_left h2 hLa
  have h5 : La * Lb * |(A (ec y)).1 - (A (ec z)).1| ≤ (1 - η) * |(A (ec y)).1 - (A (ec z)).1| :=
    mul_le_mul_of_nonneg_right hmar hP
  have hu : (A (ec y)).1 = (A (ec z)).1 := by
    have hzero : |(A (ec y)).1 - (A (ec z)).1| = 0 := by
      by_contra hne
      have hpos : 0 < |(A (ec y)).1 - (A (ec z)).1| := lt_of_le_of_ne hP (Ne.symm hne)
      nlinarith [h1, h3, h5, hpos, hη]
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hv : (A (ec y)).2.1 = (A (ec z)).2.1 := by
    have hzero : |(A (ec y)).2.1 - (A (ec z)).2.1| = 0 := by
      have : |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ 0 := by
        have hu0 : |(A (ec y)).1 - (A (ec z)).1| = 0 := by
          rw [hu, sub_self, abs_zero]
        nlinarith [h2, hu0]
      exact le_antisymm this hQ
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hAeq : A (ec y) = A (ec z) := Prod.ext_iff.2 ⟨hu, Prod.ext_iff.2 ⟨hv, ht⟩⟩
  have hecyz : ec y = ec z := by
    have := congrArg (⇑A.symm) hAeq
    simpa only [AffineEquiv.symm_apply_apply] using this
  exact ec.injOn hyB.1 hzB.1 hecyz

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eq_of_mem_wall_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Wl : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hwall : ∀ x ∈ chartBlock ec A r tlo, x ∈ Wl ↔ (A (ec x)).2.2 = 0) {y z : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) (hyW : y ∈ Wl)
    (hz : z ∈ doublePointSet f S) (hzB : z ∈ chartBlock ec A r tlo) (hzW : z ∈ Wl) : y = z :=
  eq_of_snd_eq_of_isStableCrossingBlock h hy hyB hz hzB
    (((hwall y hyB).1 hyW).trans ((hwall z hzB).1 hzW).symm)

def wallSystemCells (Q : Geometry.SimplicialComplex ℝ Ea) : Set (Finset Ea) :=
  {s | s ∈ Q.faces ∧ s.card = 4}

def wallSystemWalls (Q : Geometry.SimplicialComplex ℝ Ea) : Set (Finset Ea) :=
  {s | s ∈ Q.faces ∧ s.card = 3}

def wallSystemCell (ρ : M → Ea) (s : Finset Ea) : Set M :=
  ρ ⁻¹' convexHull ℝ (s : Set Ea)

def wallSystemCellInt (ρ : M → Ea) (s : Finset Ea) : Set M :=
  ρ ⁻¹' openSimplex s

def wallSystemSkeleton (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea) : Set M :=
  ⋃ s ∈ {s : Finset Ea | s ∈ Q.faces ∧ s.card ≤ 2}, wallSystemCell ρ s

def wallSystemStar (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea) (s : Finset Ea) :
    Set M :=
  ρ ⁻¹' (⋃ t ∈ {t : Finset Ea | t ∈ Q.faces ∧ ¬s ⊆ t}, convexHull ℝ (t : Set Ea))ᶜ

structure IsCommonWallSystem (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea)
    (Cf Bf : Set (Finset Ea)) (BdM C : Set M) {ι : Type}
    (ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M) : Prop where
  finiteFaces : Q.faces.Finite
  dimLe : ∀ s ∈ Q.faces, s.card ≤ 4
  memCell : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c
  continuous : Continuous ρ
  injective : Function.Injective ρ
  rangeEq : Set.range ρ = Q.space
  facesC : Cf ⊆ wallSystemCells Q
  facesBd : Bf ⊆ wallSystemWalls Q
  eqC : C = ⋃ c ∈ Cf, wallSystemCell ρ c
  eqBd : BdM = ⋃ w ∈ Bf, wallSystemCell ρ w
  wallSides : ∀ w ∈ wallSystemWalls Q, ∃ cm ∈ wallSystemCells Q,
    ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
      ∀ c ∈ wallSystemCells Q, w ⊆ c → c = cm ∨ c = cp
  boundarySides : ∀ w ∈ Bf, ∃ c ∈ Cf, w ⊆ c ∧ ∀ c' ∈ Cf, w ⊆ c' → c' = c
  starLayer : ∀ i, ∀ c ∈ wallSystemCells Q, (wallSystemCell ρ c ∩ Eb i).Nonempty →
    wallSystemCell ρ c ⊆ Eb' i
  layerSubset : ∀ i, Eb i ⊆ Eb' i
  layerCompact : ∀ i, IsCompact (Eb' i)
  layerSource : ∀ i, Eb' i ⊆ (ec i).source
  chartAtlas : ∀ i, ec i ∈ (plGroupoid 3).maximalAtlas M
  normalNe : ∀ i, ℓ i ≠ 0
  chartC : ∀ i, ∀ x ∈ (ec i).source, x ∈ C ↔ 0 ≤ ℓ i (ec i x)
  chartBd : ∀ i, ∀ x ∈ (ec i).source, x ∈ BdM ↔ ℓ i (ec i x) = 0
  chartAffine : ∀ i, ∀ s ∈ Q.faces, wallSystemCell ρ s ⊆ Eb' i →
    ∃ A : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3), ∀ x ∈ wallSystemCell ρ s, ec i x = A (ρ x)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_subset_wallSystemCell (ρ : M → Ea) (s : Finset Ea) :
    wallSystemCellInt ρ s ⊆ wallSystemCell ρ s :=
  fun _ hx => openSimplex_subset_convexHull s hx

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isClosed_wallSystemCell {ρ : M → Ea} (hcont : Continuous ρ) (s : Finset Ea) :
    IsClosed (wallSystemCell ρ s) :=
  (s.finite_toSet.isClosed_convexHull ℝ).preimage hcont

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_subset_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {s : Finset Ea} (hs : s ∈ Q.faces) (hcard : s.card ≤ 2) :
    wallSystemCell ρ s ⊆ wallSystemSkeleton Q ρ :=
  fun _ hx => mem_iUnion₂.2 ⟨s, ⟨hs, hcard⟩, hx⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isClosed_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hfin : Q.faces.Finite) (hcont : Continuous ρ) : IsClosed (wallSystemSkeleton Q ρ) :=
  Set.Finite.isClosed_biUnion (hfin.subset fun _ ht => ht.1)
    fun t _ => isClosed_wallSystemCell hcont t

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem disjoint_wallSystemCellInt_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    Disjoint (wallSystemCellInt ρ c) (wallSystemSkeleton Q ρ) := by
  refine Set.disjoint_left.2 fun x hx hskel => ?_
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hskel
  have hsub : c ⊆ t :=
    face_subset_of_mem_openSimplex_of_mem_convexHull Q hc.1 ht.1 hx hxt
  have hle := Finset.card_le_card hsub
  have hc4 : c.card = 4 := hc.2
  have ht2 : t.card ≤ 2 := ht.2
  omega

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_nonempty {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hrange : Set.range ρ = Q.space) {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    (wallSystemCellInt ρ c).Nonempty := by
  have hne : c.Nonempty := Finset.card_pos.mp (by rw [hc.2]; norm_num)
  have hmem : c.centroid ℝ id ∈ Q.space :=
    Q.convexHull_subset_space hc.1 (openSimplex_subset_convexHull c
      (centroid_mem_openSimplex hne))
  rw [← hrange] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, by simpa only [wallSystemCellInt, mem_preimage, hx] using
    centroid_mem_openSimplex hne⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemSkeleton_ne_univ {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hrange : Set.range ρ = Q.space) {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    wallSystemSkeleton Q ρ ≠ univ := by
  intro huniv
  obtain ⟨x, hx⟩ := wallSystemCellInt_nonempty (ρ := ρ) hrange hc
  have hx' : x ∈ wallSystemSkeleton Q ρ := by rw [huniv]; exact mem_univ x
  exact Set.disjoint_left.1 (disjoint_wallSystemCellInt_wallSystemSkeleton hc) hx hx'

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem iUnion_wallSystemCell_eq_univ {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hrange : Set.range ρ = Q.space)
    (hmem : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) :
    (⋃ c ∈ wallSystemCells Q, wallSystemCell ρ c) = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : ρ x ∈ Q.space := by rw [← hrange]; exact mem_range_self x
  obtain ⟨s, hs, hxs⟩ := Q.mem_space_iff.mp hx
  obtain ⟨c, hc, hsc⟩ := hmem s hs
  exact mem_iUnion₂.2 ⟨c, hc, convexHull_mono (Finset.coe_subset.2 hsc) hxs⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem disjoint_wallSystemCellInt_wallSystemCell {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {c c' : Finset Ea} (hc : c ∈ wallSystemCells Q)
    (hc' : c' ∈ wallSystemCells Q) (hne : c ≠ c') :
    Disjoint (wallSystemCellInt ρ c) (wallSystemCell ρ c') := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  refine hne (Finset.eq_of_subset_of_card_le
    (face_subset_of_mem_openSimplex_of_mem_convexHull Q hc.1 hc'.1 hx hx') ?_)
  have hc4 : c.card = 4 := hc.2
  have hc4' : c'.card = 4 := hc'.2
  omega

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_sdiff_subset_iUnion_wall {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    wallSystemCell ρ c \ wallSystemCellInt ρ c ⊆
      ⋃ w ∈ wallSystemWalls Q, wallSystemCell ρ w := by
  rintro x ⟨hx, hxi⟩
  obtain ⟨t, htc, htne, hxt⟩ := exists_openSimplex_of_mem_convexHull hx
  have hc4 : c.card = 4 := hc.2
  have hle : t.card ≤ c.card := Finset.card_le_card htc
  have hcard : t.card ≤ 3 := by
    by_contra hlt
    have heq : t = c := Finset.eq_of_subset_of_card_le htc (by omega)
    exact hxi (by rw [wallSystemCellInt, mem_preimage, ← heq]; exact hxt)
  obtain ⟨w, htw, hwc, hwcard⟩ := Finset.exists_subsuperset_card_eq htc hcard (by omega)
  refine mem_iUnion₂.2 ⟨w, ⟨Q.down_closed hc.1 hwc (Finset.card_pos.mp (by omega)),
    hwcard⟩, ?_⟩
  exact convexHull_mono (Finset.coe_subset.2 htw) (openSimplex_subset_convexHull t hxt)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_sdiff_subset_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {w : Finset Ea} (hw : w ∈ wallSystemWalls Q) :
    wallSystemCell ρ w \ wallSystemCellInt ρ w ⊆ wallSystemSkeleton Q ρ := by
  rintro x ⟨hx, hxi⟩
  obtain ⟨t, htw, htne, hxt⟩ := exists_openSimplex_of_mem_convexHull hx
  have hw3 : w.card = 3 := hw.2
  have hle : t.card ≤ w.card := Finset.card_le_card htw
  have hcard : t.card ≤ 2 := by
    by_contra hlt
    have heq : t = w := Finset.eq_of_subset_of_card_le htw (by omega)
    exact hxi (by rw [wallSystemCellInt, mem_preimage, ← heq]; exact hxt)
  exact mem_iUnion₂.2 ⟨t, ⟨Q.down_closed hw.1 htw htne, hcard⟩,
    openSimplex_subset_convexHull t hxt⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_inter_subset_wallSystemSkeleton {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {w w' : Finset Ea} (hw : w ∈ wallSystemWalls Q)
    (hw' : w' ∈ wallSystemWalls Q) (hne : w ≠ w') :
    wallSystemCell ρ w ∩ wallSystemCell ρ w' ⊆ wallSystemSkeleton Q ρ := by
  classical
  rintro x ⟨hx, hx'⟩
  have hw3 : w.card = 3 := hw.2
  have hw3' : w'.card = 3 := hw'.2
  have hmem : ρ x ∈ convexHull ℝ ((w ∩ w' : Finset Ea) : Set Ea) := by
    rw [Finset.coe_inter]
    exact Q.inter_subset_convexHull hw.1 hw'.1 ⟨hx, hx'⟩
  have hnonempty : (w ∩ w').Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hmem
    simp at hmem
  have hle : (w ∩ w').card ≤ w.card := Finset.card_le_card Finset.inter_subset_left
  have hcard : (w ∩ w').card ≤ 2 := by
    by_contra hlt
    have hww : w ∩ w' = w :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : w ⊆ w' := hww ▸ Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  exact mem_iUnion₂.2 ⟨w ∩ w',
    ⟨Q.down_closed hw.1 Finset.inter_subset_left hnonempty, hcard⟩, hmem⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isOpen_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hfin : Q.faces.Finite) (hcont : Continuous ρ) (s : Finset Ea) :
    IsOpen (wallSystemStar Q ρ s) := by
  refine IsOpen.preimage hcont (isOpen_compl_iff.mpr ?_)
  exact Set.Finite.isClosed_biUnion (hfin.subset fun _ ht => ht.1)
    fun t _ => t.finite_toSet.isClosed_convexHull ℝ

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_subset_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {s : Finset Ea} (hs : s ∈ Q.faces) :
    wallSystemCellInt ρ s ⊆ wallSystemStar Q ρ s := by
  intro x hx hbad
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hbad
  exact ht.2 (face_subset_of_mem_openSimplex_of_mem_convexHull Q hs ht.1 hx hxt)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_face_of_mem_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space) {s : Finset Ea} {x : M}
    (hx : x ∈ wallSystemStar Q ρ s) :
    ∃ t ∈ Q.faces, s ⊆ t ∧ x ∈ wallSystemCellInt ρ t := by
  have hxQ : ρ x ∈ Q.space := by rw [← hrange]; exact mem_range_self x
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex Q hxQ
  refine ⟨t, ht, ?_, hxt⟩
  by_contra hst
  exact hx (mem_iUnion₂.2 ⟨t, ⟨ht, hst⟩, openSimplex_subset_convexHull t hxt⟩)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCellInt_eq_wallSystemStar {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space) (hdim : ∀ t ∈ Q.faces, t.card ≤ 4)
    {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    wallSystemCellInt ρ c = wallSystemStar Q ρ c := by
  refine Subset.antisymm (wallSystemCellInt_subset_wallSystemStar hc.1) fun x hx => ?_
  obtain ⟨t, ht, hct, hxt⟩ := exists_face_of_mem_wallSystemStar hrange hx
  have hc4 : c.card = 4 := hc.2
  have hdt := hdim t ht
  rw [Finset.eq_of_subset_of_card_le hct (by omega)]
  exact hxt

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isOpen_wallSystemCellInt {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    (hfin : Q.faces.Finite) (hcont : Continuous ρ) (hrange : Set.range ρ = Q.space)
    (hdim : ∀ t ∈ Q.faces, t.card ≤ 4) {c : Finset Ea} (hc : c ∈ wallSystemCells Q) :
    IsOpen (wallSystemCellInt ρ c) := by
  rw [wallSystemCellInt_eq_wallSystemStar hrange hdim hc]
  exact isOpen_wallSystemStar hfin hcont c

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemStar_inter_wall_subset {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space) {w w' : Finset Ea}
    (hw : w ∈ wallSystemWalls Q) (hw' : w' ∈ wallSystemWalls Q) :
    wallSystemStar Q ρ w ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w := by
  rintro x ⟨hxs, hx'⟩
  obtain ⟨t, ht, hwt, hxt⟩ := exists_face_of_mem_wallSystemStar hrange hxs
  have htw' : t ⊆ w' :=
    face_subset_of_mem_openSimplex_of_mem_convexHull Q ht hw'.1 hxt hx'
  have hw3 : w.card = 3 := hw.2
  have hw3' : w'.card = 3 := hw'.2
  rw [Finset.eq_of_subset_of_card_le (hwt.trans htw') (by omega)]
  exact hx'

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemStar_subset_union_wallSystemCell {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} (hrange : Set.range ρ = Q.space)
    (hmem : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) {w cm cp : Finset Ea}
    (hsides : ∀ c ∈ wallSystemCells Q, w ⊆ c → c = cm ∨ c = cp) :
    wallSystemStar Q ρ w ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp := by
  intro x hx
  obtain ⟨t, ht, hwt, hxt⟩ := exists_face_of_mem_wallSystemStar hrange hx
  obtain ⟨c, hc, htc⟩ := hmem t ht
  have hxc : x ∈ wallSystemCell ρ c :=
    convexHull_mono (Finset.coe_subset.2 htc) (openSimplex_subset_convexHull t hxt)
  rcases hsides c hc (hwt.trans htc) with rfl | rfl
  · exact Or.inl hxc
  · exact Or.inr hxc

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallSystemCell_subset_layer {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {ι : Type} {Eb Eb' : ι → Set M} (i : ι)
    (hstar : ∀ c ∈ wallSystemCells Q, (wallSystemCell ρ c ∩ Eb i).Nonempty →
      wallSystemCell ρ c ⊆ Eb' i)
    (hmem : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) {s : Finset Ea}
    (hs : s ∈ Q.faces) (hne : (wallSystemCell ρ s ∩ Eb i).Nonempty) :
    wallSystemCell ρ s ⊆ Eb' i := by
  obtain ⟨c, hc, hsc⟩ := hmem s hs
  have hsub : wallSystemCell ρ s ⊆ wallSystemCell ρ c :=
    fun _ hx => convexHull_mono (Finset.coe_subset.2 hsc) hx
  obtain ⟨z, hzs, hzE⟩ := hne
  exact hsub.trans (hstar c hc ⟨z, hsub hzs, hzE⟩)

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem subset_iUnion_wallSystemCell_of_eq_boundary {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Bf : Set (Finset Ea)} {BdM : Set M} (hfaces : Bf ⊆ wallSystemWalls Q)
    (heq : BdM = ⋃ w ∈ Bf, wallSystemCell ρ w) :
    BdM ⊆ ⋃ w ∈ wallSystemWalls Q, wallSystemCell ρ w := by
  rw [heq]
  exact iUnion₂_subset fun w hw x hx => mem_iUnion₂.2 ⟨w, hfaces hw, hx⟩

theorem wallIncidence_simplexBoundary {T : Finset Ea}
    (hT : AffineIndependent ℝ ((↑) : T → Ea)) (hcard : T.card = 5) :
    (simplexBoundary T hT).faces.Finite ∧
      (∀ s ∈ (simplexBoundary T hT).faces, s.card ≤ 4) ∧
      (∀ s ∈ (simplexBoundary T hT).faces,
        ∃ c ∈ wallSystemCells (simplexBoundary T hT), s ⊆ c) ∧
      (wallSystemWalls (simplexBoundary T hT)).Nonempty ∧
      ∀ w ∈ wallSystemWalls (simplexBoundary T hT),
        ∃ cm ∈ wallSystemCells (simplexBoundary T hT),
          ∃ cp ∈ wallSystemCells (simplexBoundary T hT), cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
            ∀ c ∈ wallSystemCells (simplexBoundary T hT), w ⊆ c → c = cm ∨ c = cp := by
  classical
  have hface : ∀ s : Finset Ea,
      s ∈ (simplexBoundary T hT).faces ↔ s ⊆ T ∧ s.Nonempty ∧ s ≠ T :=
    fun _ => mem_simplexBoundary_faces_iff
  have hcardle : ∀ s ∈ (simplexBoundary T hT).faces, s.card ≤ 4 := by
    intro s hs
    obtain ⟨hsT, -, hne⟩ := (hface s).1 hs
    have hle := Finset.card_le_card hsT
    by_contra hlt
    exact hne (Finset.eq_of_subset_of_card_le hsT (by omega))
  have hcell : ∀ z ∈ T, ∀ w : Finset Ea, w ⊆ T → w.card = 3 → z ∉ w →
      insert z w ∈ wallSystemCells (simplexBoundary T hT) := by
    intro z hzT w hwT hw3 hzw
    have hins : (insert z w).card = 4 := by
      rw [Finset.card_insert_of_notMem hzw, hw3]
    refine ⟨(hface _).2 ⟨Finset.insert_subset hzT hwT, Finset.insert_nonempty z w, ?_⟩, hins⟩
    intro hEq
    rw [hEq, hcard] at hins
    omega
  refine ⟨simplexBoundary_faces_finite T hT, hcardle, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsT, hsne, -⟩ := (hface s).1 hs
    obtain ⟨c, hsc, hcT, hc4⟩ :=
      Finset.exists_subsuperset_card_eq hsT (hcardle s hs) (by omega)
    refine ⟨c, ⟨(hface c).2 ⟨hcT, Finset.card_pos.mp (by omega), ?_⟩, hc4⟩, hsc⟩
    intro hEq
    rw [hEq, hcard] at hc4
    omega
  · obtain ⟨w, hwT, hw3⟩ := Finset.exists_subset_card_eq (s := T) (n := 3) (by omega)
    refine ⟨w, (hface w).2 ⟨hwT, Finset.card_pos.mp (by omega), ?_⟩, hw3⟩
    intro hEq
    rw [hEq, hcard] at hw3
    omega
  · rintro w ⟨hwf, hw3⟩
    obtain ⟨hwT, -, -⟩ := (hface w).1 hwf
    have hsd : (T \ w).card = 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hwT, hcard, hw3]
    obtain ⟨u, v, huv, huvT⟩ := Finset.card_eq_two.mp hsd
    have huTw : u ∈ T \ w := by rw [huvT]; exact Finset.mem_insert_self u {v}
    have hvTw : v ∈ T \ w := by
      rw [huvT]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    refine ⟨insert u w, hcell u (Finset.mem_sdiff.mp huTw).1 w hwT hw3
        (Finset.mem_sdiff.mp huTw).2, insert v w,
      hcell v (Finset.mem_sdiff.mp hvTw).1 w hwT hw3 (Finset.mem_sdiff.mp hvTw).2, ?_,
      Finset.subset_insert u w, Finset.subset_insert v w, ?_⟩
    · intro hEq
      have hv : v ∈ insert u w := by rw [hEq]; exact Finset.mem_insert_self v w
      rcases Finset.mem_insert.mp hv with h1 | h1
      · exact huv h1.symm
      · exact (Finset.mem_sdiff.mp hvTw).2 h1
    · rintro c ⟨hcf, hc4⟩ hwc
      obtain ⟨hcT, -, -⟩ := (hface c).1 hcf
      have hcw : (c \ w).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hwc, hc4, hw3]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcw
      have hzc : z ∈ c \ w := by rw [hz]; exact Finset.mem_singleton_self z
      have hzmem : z ∈ T \ w :=
        Finset.mem_sdiff.mpr ⟨hcT (Finset.mem_sdiff.mp hzc).1, (Finset.mem_sdiff.mp hzc).2⟩
      have hcz : c = insert z w := by
        have h1 : w ∪ c \ w = c := Finset.union_sdiff_of_subset hwc
        rw [hz] at h1
        rw [← h1]
        ext a
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        tauto
      rw [huvT] at hzmem
      rcases Finset.mem_insert.mp hzmem with rfl | hzv
      · exact Or.inl hcz
      · rw [Finset.mem_singleton.mp hzv] at hcz
        exact Or.inr hcz

theorem exists_wallIncidence_of_fourSimplexBoundary :
    ∃ Q : Geometry.SimplicialComplex ℝ (Fin (3 + 2) → ℝ), Q.faces.Finite ∧
      (∀ s ∈ Q.faces, s.card ≤ 4) ∧ (∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) ∧
      (wallSystemWalls Q).Nonempty ∧
      ∀ w ∈ wallSystemWalls Q, ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q,
        cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
          ∀ c ∈ wallSystemCells Q, w ⊆ c → c = cm ∨ c = cp :=
  ⟨simplexBoundary (stdVertices 3) (stdVertices_affineIndependent 3),
    wallIncidence_simplexBoundary (stdVertices_affineIndependent 3) (card_stdVertices 3)⟩


omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eqOn_wallPlane_of_eqOn_transition
    {ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {Km Kp : Set M}
    {A₁ A₂ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {ψ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] ℝ}
    (h₁ : EqOn (fun z => ec' (ec.symm z)) A₁ (⇑ec '' Km))
    (h₂ : EqOn (fun z => ec' (ec.symm z)) A₂ (⇑ec '' Kp))
    (hspan : {z | ψ z = 0} ⊆
      (affineSpan ℝ (⇑ec '' (Km ∩ Kp)) : Set (EuclideanSpace ℝ (Fin 3)))) :
    EqOn A₁ A₂ {z | ψ z = 0} := by
  refine fun z hz => AffineMap.eqOn_affineSpan (fun u hu => ?_) (hspan hz)
  obtain ⟨x, hx, rfl⟩ := hu
  rw [← h₁ ⟨x, hx.1, rfl⟩, ← h₂ ⟨x, hx.2, rfl⟩]

def WallProductBlock (f : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM C : Set M)
    (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η ∧
    Disjoint (chartBlock ec A r tlo) (wallSystemSkeleton Q ρ) ∧
    ((∃ c ∈ wallSystemCells Q, tlo = -r ∧
        chartBlock ec A r tlo ⊆ wallSystemCellInt ρ c) ∨
      (∃ w ∈ wallSystemWalls Q, ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q,
        tlo = -r ∧ cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
          chartBlock ec A r tlo ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp ∧
          (chartBlock ec A r tlo ∩ wallSystemCellInt ρ cm).Nonempty ∧
          (chartBlock ec A r tlo ∩ wallSystemCellInt ρ cp).Nonempty ∧
          (∀ w' ∈ wallSystemWalls Q,
            chartBlock ec A r tlo ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w) ∧
          (∀ x ∈ chartBlock ec A r tlo, x ∈ wallSystemCell ρ w ↔ (A (ec x)).2.2 = 0) ∧
          (∀ x ∈ chartBlock ec A r tlo ∩ wallSystemCell ρ cm, (A (ec x)).2.2 ≤ 0) ∧
          ∀ x ∈ chartBlock ec A r tlo ∩ wallSystemCell ρ cp, 0 ≤ (A (ec x)).2.2) ∨
      (∃ c ∈ wallSystemCells Q, ∃ w ∈ wallSystemWalls Q, tlo = 0 ∧ w ⊆ c ∧
        (∀ z, (A z).2.2 = ℓ z) ∧ chartBlock ec A r tlo ∩ C ⊆ wallSystemCell ρ c ∧
          (chartBlock ec A r tlo ∩ wallSystemCellInt ρ c).Nonempty ∧
          chartBlock ec A r tlo ∩ BdM ⊆ wallSystemCell ρ w ∧
          ∀ w' ∈ wallSystemWalls Q,
            chartBlock ec A r tlo ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w))

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem WallProductBlock.toIsStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : WallProductBlock f S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb η) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η := h.1

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem WallProductBlock.mono_margin {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η η' : ℝ}
    (h : WallProductBlock f S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hη' : 0 < η') (hle : η' ≤ η) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb η' :=
  ⟨h.1.mono_margin hη' hle, h.2.1, h.2.2⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallProductBlock_of_flatSheets_interior {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {c : Finset Ea} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x))
    (hc : c ∈ wallSystemCells Q)
    (hcell : chartBlock ec A r (-r) ⊆ wallSystemCellInt ρ c) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 :=
  ⟨isStableCrossingBlock_of_flatSheets hr hcpt hsrc hBd hpre hdisj hA hB hplA hplB hnA hnB,
    Set.disjoint_of_subset_left hcell (disjoint_wallSystemCellInt_wallSystemSkeleton hc),
    Or.inl ⟨c, hc, rfl, hcell⟩⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallProductBlock_of_flatSheets_wall {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {w cm cp : Finset Ea} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x))
    (hskel : Disjoint (chartBlock ec A r (-r)) (wallSystemSkeleton Q ρ))
    (hw : w ∈ wallSystemWalls Q) (hcm : cm ∈ wallSystemCells Q)
    (hcp : cp ∈ wallSystemCells Q) (hne : cm ≠ cp) (hwm : w ⊆ cm) (hwp : w ⊆ cp)
    (hcov : chartBlock ec A r (-r) ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp)
    (hmne : (chartBlock ec A r (-r) ∩ wallSystemCellInt ρ cm).Nonempty)
    (hpne : (chartBlock ec A r (-r) ∩ wallSystemCellInt ρ cp).Nonempty)
    (hone : ∀ w' ∈ wallSystemWalls Q,
      chartBlock ec A r (-r) ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w)
    (hzero : ∀ x ∈ chartBlock ec A r (-r), x ∈ wallSystemCell ρ w ↔ (A (ec x)).2.2 = 0)
    (hsm : ∀ x ∈ chartBlock ec A r (-r) ∩ wallSystemCell ρ cm, (A (ec x)).2.2 ≤ 0)
    (hsp : ∀ x ∈ chartBlock ec A r (-r) ∩ wallSystemCell ρ cp, 0 ≤ (A (ec x)).2.2) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 :=
  ⟨isStableCrossingBlock_of_flatSheets hr hcpt hsrc hBd hpre hdisj hA hB hplA hplB hnA hnB,
    hskel, Or.inr (Or.inl ⟨w, hw, cm, hcm, cp, hcp, rfl, hne, hwm, hwp, hcov, hmne, hpne,
      hone, hzero, hsm, hsp⟩)⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallProductBlock_of_flatSheets_physicalBoundary {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {c w : Finset Ea} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r 0)))
    (hsrc : closure (chartBlock ec A r 0) ⊆ ec.source)
    (hheight : ∀ z, (A z).2.2 = ℓ z)
    (hfront : ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))
    (hpre : S ∩ f ⁻¹' chartBlock ec A r 0 = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r 0 → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane 0] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r 0 → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane 0] (blockSheetProjB ec A f x))
    (hskel : Disjoint (chartBlock ec A r 0) (wallSystemSkeleton Q ρ))
    (hc : c ∈ wallSystemCells Q) (hw : w ∈ wallSystemWalls Q) (hwc : w ⊆ c)
    (hcovC : chartBlock ec A r 0 ∩ C ⊆ wallSystemCell ρ c)
    (hcne : (chartBlock ec A r 0 ∩ wallSystemCellInt ρ c).Nonempty)
    (hcovB : chartBlock ec A r 0 ∩ BdM ⊆ wallSystemCell ρ w)
    (hone : ∀ w' ∈ wallSystemWalls Q,
      chartBlock ec A r 0 ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r 0 SA SB (fun _ => 0) (fun _ => 0) 0 0 1 :=
  ⟨isStableCrossingBlock_of_flatSheets_boundary hr hcpt hsrc hheight hfront hpre hdisj
      hA hB hplA hplB hnA hnB,
    hskel, Or.inr (Or.inr ⟨c, hc, w, hw, rfl, hwc, hheight, hcovC, hcne, hcovB, hone⟩)⟩

def HasWallProductBlocks (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2))) {ι : Type}
    (ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb : ι → Set M) (BdM C : Set M)
    (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea) (Z : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (N : Set M) (m : ℕ) (j : Fin m → ι)
      (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ)) (r tlo : Fin m → ℝ)
      (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2))) (a b : Fin m → ℝ × ℝ → ℝ)
      (La Lb : Fin m → ℝ),
      IsOpen N ∧ Z ⊆ N ∧
        doublePointSet f S ∩ N ⊆ ⋃ i, innerChartBlock (ec (j i)) (A i) (r i) (tlo i) ∧
        (∀ i, chartBlock (ec (j i)) (A i) (r i) (tlo i) ⊆ Eb (j i)) ∧
        ∀ i, WallProductBlock f S (ec (j i)) (ℓ (j i)) BdM C Q ρ
          (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i) (La i) (Lb i) η

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasWallProductBlocks_empty {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ} (hη : 0 < η) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ ∅ η := by
  refine ⟨hη, ∅, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, isOpen_empty, Subset.rfl, ?_,
    fun i => i.elim0, fun i => i.elim0⟩
  rw [inter_empty]
  exact empty_subset _

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasWallProductBlocks_of_wallProductBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C N Z : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {i₀ : ι}
    (h : WallProductBlock f S (ec i₀) (ℓ i₀) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hN : IsOpen N) (hZN : Z ⊆ N)
    (hcov : doublePointSet f S ∩ N ⊆ innerChartBlock (ec i₀) A r tlo)
    (hE : chartBlock (ec i₀) A r tlo ⊆ Eb i₀) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η := by
  refine ⟨h.1.margin_pos, N, 1, fun _ => i₀, fun _ => A, fun _ => r, fun _ => tlo,
    fun _ => SA, fun _ => SB, fun _ => a, fun _ => b, fun _ => La, fun _ => Lb, hN, hZN,
    ?_, fun _ => hE, fun _ => h⟩
  exact hcov.trans (subset_iUnion (fun _ : Fin 1 => innerChartBlock (ec i₀) A r tlo) 0)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasWallProductBlocks.mono {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Z Z' : Set M} {η : ℝ}
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η) (hZ : Z' ⊆ Z) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z' η := by
  obtain ⟨hη, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hN, hZN, hcov, hE, hblk⟩ := h
  exact ⟨hη, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hN, hZ.trans hZN, hcov, hE, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasWallProductBlocks.union {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Z₁ Z₂ : Set M} {η₁ η₂ : ℝ}
    (h₁ : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z₁ η₁)
    (h₂ : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z₂ η₂) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ (Z₁ ∪ Z₂) (min η₁ η₂) := by
  obtain ⟨hη₁, N₁, m₁, j₁, A₁, r₁, t₁, SA₁, SB₁, a₁, b₁, La₁, Lb₁, hN₁, hQ₁, hc₁, hE₁,
    hb₁⟩ := h₁
  obtain ⟨hη₂, N₂, m₂, j₂, A₂, r₂, t₂, SA₂, SB₂, a₂, b₂, La₂, Lb₂, hN₂, hQ₂, hc₂, hE₂,
    hb₂⟩ := h₂
  refine ⟨lt_min hη₁ hη₂, N₁ ∪ N₂, m₁ + m₂, Fin.addCases j₁ j₂, Fin.addCases A₁ A₂,
    Fin.addCases r₁ r₂, Fin.addCases t₁ t₂, Fin.addCases SA₁ SA₂, Fin.addCases SB₁ SB₂,
    Fin.addCases a₁ a₂, Fin.addCases b₁ b₂, Fin.addCases La₁ La₂, Fin.addCases Lb₁ Lb₂,
    hN₁.union hN₂, union_subset_union hQ₁ hQ₂, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hNy | hNy⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hc₁ ⟨hy, hNy⟩)
      refine mem_iUnion.2 ⟨Fin.castAdd m₂ i, ?_⟩
      simpa only [Fin.addCases_left] using hi
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hc₂ ⟨hy, hNy⟩)
      refine mem_iUnion.2 ⟨Fin.natAdd m₁ i, ?_⟩
      simpa only [Fin.addCases_right] using hi
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using hE₁ i
    · simpa only [Fin.addCases_right] using hE₂ i
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using
        (hb₁ i).mono_margin (lt_min hη₁ hη₂) (min_le_left _ _)
    · simpa only [Fin.addCases_right] using
        (hb₂ i).mono_margin (lt_min hη₁ hη₂) (min_le_right _ _)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_isStableCrossingBlock_of_hasWallProductBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C Z : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ}
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Z) :
    ∃ (i : ι) (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
      (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb : ℝ),
      IsStableCrossingBlock f S (ec i) (ℓ i) BdM A r tlo SA SB a b La Lb η ∧
        y ∈ innerChartBlock (ec i) A r tlo := by
  obtain ⟨-, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, -, hZN, hcov, -, hblk⟩ := h
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov ⟨hy.1, hZN hy.2⟩)
  exact ⟨j i, A i, r i, tlo i, SA i, SB i, a i, b i, La i, Lb i, (hblk i).1, hi⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_sheets_of_hasWallProductBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C Z : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ}
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Z) :
    ∃ SA' SB' : Set (EuclideanSpace ℝ (Fin 2)),
      Disjoint SA' SB' ∧ (SA' ∩ f ⁻¹' {y}).Nonempty ∧ (SB' ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨i, A, r, tlo, SA, SB, a, b, La, Lb, hblk, hi⟩ :=
    exists_isStableCrossingBlock_of_hasWallProductBlocks h hy
  obtain ⟨hr0, -, -, -, -, -, -, hside, -, hdisj, -, -, -, -, -, -, -, -, -, -⟩ := id hblk
  have ht : tlo ≤ 0 := by
    rcases hside with ⟨h1, -⟩ | ⟨h1, -, -⟩
    · rw [h1]; linarith
    · exact le_of_eq h1
  obtain ⟨hA, hB⟩ := sheets_nonempty_of_isStableCrossingBlock hblk hy.1
    (chartBlock_mono_of_half (ec i) A (le_of_lt hr0) ht hi)
  exact ⟨SA, SB, hdisj, hA, hB⟩

theorem exists_transitionSubdivisionOnOverlap
    (ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hec' : ec' ∈ (plGroupoid 3).maximalAtlas M)
    (N : Set M) (hN : IsCompact N) (hNec : N ⊆ ec.source) (hNec' : N ⊆ ec'.source) :
    ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      Q.faces.Finite ∧ ⇑ec '' N ⊆ interior Q.space ∧
        Q.space ⊆ ⇑ec '' (ec.source ∩ ec'.source) ∧
        ∀ s ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun z => ec' (ec.symm z)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) := by
  sorry

theorem hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock (D : SingularTwoCell M)
    {BdM : Set M} (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock (⇑D) D.domain ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet (⇑D) D.domain)
    (hyB : y ∈ innerChartBlock ec A r tlo) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e.source)
        (⇑e '' (e.source ∩ BdM)) (e y) := by
  sorry

theorem exists_normalCrossing_of_hasWallProductBlocks (D : SingularTwoCell M)
    {BdM C Z : Set M} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ}
    (hec : ∀ i, ec i ∈ (plGroupoid 3).maximalAtlas M) (hℓ : ∀ i, ℓ i ≠ 0)
    (hBdchart : ∀ i, ∀ x ∈ (ec i).source, x ∈ BdM ↔ ℓ i (ec i x) = 0)
    (h : HasWallProductBlocks (⇑D) D.domain ec ℓ Eb BdM C Q ρ Z η) :
    ∃ O : Set M, IsOpen O ∧ Z ⊆ O ∧
      ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e.source)
            (⇑e '' (e.source ∩ BdM)) (e y) := by
  obtain ⟨-, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hN, hZN, hcov, -, hblk⟩ := h
  refine ⟨N, hN, hZN, fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hy)
  exact hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock D (ec (j i)) (ℓ (j i))
    (hec (j i)) (hℓ (j i)) (hBdchart (j i)) (hblk i).1 hy.1 hi

open Classical in
theorem exists_commonWallComplex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (n : ℕ) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (V : Fin n → Set (double 3 K).space)
      (ec : Fin n → OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
      (ℓ : Fin n → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)),
      (∀ i, ec i ∈ (plGroupoid 3).maximalAtlas (double 3 K).space) → (∀ i, ℓ i ≠ 0) →
        (∀ i, ∀ x ∈ (ec i).source, x ∈ C ↔ 0 ≤ ℓ i (ec i x)) →
        (∀ i, ∀ x ∈ (ec i).source, x ∈ Bd ↔ ℓ i (ec i x) = 0) →
        (∀ i, closure (V i) ⊆ (ec i).source) →
        ∃ (Q : Geometry.SimplicialComplex ℝ (E × E × ℝ))
          (Cf Bf : Set (Finset (E × E × ℝ))) (Eb Eb' : Fin n → Set (double 3 K).space),
          IsSubdivision Q (double 3 K) ∧ (∀ i, closure (V i) ⊆ interior (Eb i)) ∧
            IsCommonWallSystem Q ((↑) : (double 3 K).space → E × E × ℝ) Cf Bf Bd C
              ec ℓ Eb Eb' := by
  sorry

theorem wallProductBlock_transport [T2Space M] {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M} {BdM C N : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {y : M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') (i i' : ι)
    (h : WallProductBlock f S (ec i) (ℓ i) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hmapC : MapsTo f S C) (hblkE : chartBlock (ec i) A r tlo ⊆ Eb i)
    (hy : y ∈ innerChartBlock (ec i) A r tlo) (hy' : y ∈ Eb i')
    (hN : IsOpen N) (hyN : y ∈ N) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ)
      (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ),
      WallProductBlock f S (ec i') (ℓ i') BdM C Q ρ A' r' tlo' SA' SB' a' b' La Lb η ∧
        A' (ec i' y) = 0 ∧ y ∈ innerChartBlock (ec i') A' r' tlo' ∧
        chartBlock (ec i') A' r' tlo' ⊆ N ∩ chartBlock (ec i) A r tlo := by
  sorry

theorem hasStableCrossingBlocks_of_wallProductBlocks [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M}
    {BdM C Z Z' : Set M} {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {Cf Bf : Set (Finset Ea)} {η κ : ℝ}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb')
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η)
    (hScpt : IsCompact S) (hcont : ContinuousOn f S) (hmapC : MapsTo f S C)
    (hκ : 0 < κ) (hinj : UniformInjectivityScale S f κ)
    (i₀ : ι) (hZ'cpt : IsCompact Z') (hZ'Z : Z' ⊆ Z) (hZ'E : Z' ⊆ interior (Eb i₀)) :
    HasStableCrossingBlocks f S (ec i₀) (ℓ i₀) BdM Z' η := by
  sorry

def AdmissibleVertexMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (τ : ℝ) : Prop :=
  (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices ∧
    (∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space) ∧
    (∀ v ∈ R.vertices, dist (φ v) (ec (D v)) < τ) ∧
    (∀ v ∈ R.vertices, v ∈ Ac.space → φ v = ec (D v)) ∧
    (∀ v ∈ R.vertices, v ∈ Bv → ℓ (φ v) = 0) ∧
    ∀ v ∈ R.vertices, v ∉ Bv → 0 < ℓ (φ v)

theorem AdmissibleVertexMap.mono {D : SingularTwoCell M}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ}
    {Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {τ τ' : ℝ}
    (h : AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ) (hle : τ ≤ τ') :
    AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ' :=
  ⟨h.1, h.2.1, fun v hv => lt_of_lt_of_le (h.2.2.1 v hv) hle, h.2.2.2⟩

open Classical in
theorem exists_admissibleVertexMap_of_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRsfin : R.faces.Finite) (hsub : IsSubdivision R Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Bv : Finset (EuclideanSpace ℝ (Fin 2)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv (fun v => ec (D v)) τ := by
  classical
  have hvfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hRsfin
  have hvR : ∀ v ∈ R.vertices, v ∈ Rc.space := by
    intro v hv
    rw [← hsub.space_eq]
    exact Geometry.SimplicialComplex.vertices_subset_space hv
  have hsrc : ∀ v ∈ R.vertices, D v ∈ ec.source := fun v hv => hVec (hRV (hvR v hv))
  have hmemBv : ∀ v, v ∈ hvfin.toFinset.filter (fun w => w ∈ Lc.space) ↔
      v ∈ R.vertices ∧ v ∈ Lc.space := by
    intro v
    simp [Finset.mem_filter, hvfin.mem_toFinset]
  refine ⟨hvfin.toFinset.filter fun w => w ∈ Lc.space, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ((hmemBv v).1 (Finset.mem_coe.mp hv)).1
  · exact fun v hv => ⟨fun h => ((hmemBv v).1 h).2, fun h => (hmemBv v).2 ⟨hv, h⟩⟩
  · intro v _
    simpa using hτ
  · exact fun _ _ _ => rfl
  · intro v hv hvB
    have hvL : v ∈ Lc.space := ((hmemBv v).1 hvB).2
    rw [hLspace] at hvL
    have hmem : v ∈ D.domain ∩ ⇑D ⁻¹' BdM := by
      rw [hproper]
      exact hvL.2
    exact (hBdchart (D v) (hsrc v hv)).1 hmem.2
  · intro v hv hvB
    have hvRc : v ∈ Rc.space := hvR v hv
    have hvL : v ∉ Lc.space := fun h => hvB ((hmemBv v).2 ⟨hv, h⟩)
    have hne : ℓ (ec (D v)) ≠ 0 := by
      intro h
      have hBd : D v ∈ BdM := (hBdchart (D v) (hsrc v hv)).2 h
      have hfr : v ∈ frontier D.domain := by
        rw [← hproper]
        exact ⟨hRdom hvRc, hBd⟩
      exact hvL (by rw [hLspace]; exact ⟨hvRc, hfr⟩)
    exact lt_of_le_of_ne ((hCchart (D v) (hsrc v hv)).1 (hmapC (hRdom hvRc))) (Ne.symm hne)

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

open Classical in
noncomputable def regionGluedMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) → M :=
  fun x => if x ∈ Rc.space then ec.symm (simplicialMap Rs φ x) else D x

theorem eq_regionGluedMap_of_eqOn {D D' : SingularTwoCell M}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {Rs Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    ⇑D' = regionGluedMap D ec Rs φ Rc := by
  classical
  funext x
  by_cases hx : x ∈ Rc.space
  · simp only [regionGluedMap, if_pos hx]
    exact hglue hx
  · simp only [regionGluedMap, if_neg hx]
    exact hglueoff hx

theorem exists_normalizationPreparation_on_prescribedRegion [CompactSpace M]
    (D : SingularTwoCell M) {BdM B W V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hVopen : IsOpen V) (hWV : closure W ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W)) :
    ∃ (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (κ δ ε : ℝ),
      0 < κ ∧ 0 < δ ∧ 0 < ε ∧ T.faces.Finite ∧ T.space = D.domain ∧ StarInj T (⇑D) ∧
        (∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
          StarInj T g → UniformInjectivityScale D.domain g κ ∧
            ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space) ∧
        ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z) := by
  sorry

open Classical in
theorem exists_protectedSubdivision_in_adaptedChart [CompactSpace M]
    (D : SingularTwoCell M) {BdM C Z O W V : Set M} {η κ δ ε : ℝ}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hZclosed : IsClosed Z) (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVopen : IsOpen V) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hWV : closure W ⊆ V) (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W))
    (hstable : HasStableCrossingBlocks (⇑D) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hTfin : T.faces.Finite)
    (hTspace : T.space = D.domain) (hTstar : StarInj T (⇑D))
    (hκ : 0 < κ) (hδ : 0 < δ) (hε : 0 < ε)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hconv : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) :
    ∃ (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (τ : ℝ) (K : Set M),
      0 < τ ∧ IsSubdivision R Rc ∧ R.faces.Finite ∧
        (∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun x => ec (D x)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))) ∧
        IsCompact K ∧ K ⊆ V ∧ ⇑D '' Rc.space ⊆ interior K ∧
        ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
          (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
          AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
          IsPiecewiseAffineOn (simplicialMap R φ) Rc.space ∧
            (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < ε) ∧
            EqOn (simplicialMap R φ) (fun x => ec (D x)) Ac.space ∧
            (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
            (∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space) ∧
            (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
              Disjoint
                (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
                (⇑ec '' closure W)) ∧
            MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) ∧
            regionGluedMap D ec R φ Rc '' Rc.space ⊆ K ∧
            StarInj T (regionGluedMap D ec R φ Rc) ∧
            (∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Z ∩ K,
              (∃ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
                  (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' {y} ∩
                    convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
                ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
                  HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec R φ Rc)
                    (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' e₁.source)
                    (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
            HasStableCrossingBlocks (regionGluedMap D ec R φ Rc) D.domain ec ℓ BdM
              (Z ∩ closure (V \ closure W)) (η / 2) := by
  sorry

theorem exists_globalInvariants_of_gluedCell (D D' : SingularTwoCell M)
    {BdM B C V : Set M} {ε δ κ : ℝ}
    {T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) (hκ : 0 < κ)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hclose : ∀ x ∈ D.domain, dist (D' x) (D x) < δ) (hstar : StarInj T (⇑D'))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVopen : IsOpen V) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V)
    (hbdbuf : ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z))
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    MapsTo (⇑D') D'.domain C ∧ (∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z}) ∧
      (∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U) ∧
      (∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2) ∧
      D'.domain ∩ ⇑D' ⁻¹' BdM = frontier D'.domain ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) M,
        (∀ x : frontier D.domain, H (0, x) = D x) ∧
        (∀ x : frontier D.domain, H (1, x) = D' x) ∧
        ∀ (t : unitInterval) (x : frontier D.domain),
          H (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (H (t, x)) := by
  sorry

open Classical in
theorem freeSourceGerm_of_mem_closure (D : SingularTwoCell M) {W V : Set M} {ε : ℝ}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rc Ac Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hsub : IsSubdivision Rs Rc) (hVec : V ⊆ ec.source) (hΩ : IsOpen Ω)
    (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hsep : ∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
      Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
        (⇑ec '' closure W))
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))
    {y : M} (hy : y ∈ closure W) :
    FreeSourceGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain y := by
  classical
  intro x hx
  have hxdom : x ∈ D.domain := hx.1
  have hxy : regionGluedMap D ec Rs φ Rc x = y := hx.2
  have hxR : x ∈ Rc.space := by
    by_contra hxR
    have hDx : D x = y := by
      rw [← hxy]
      simp only [regionGluedMap, if_neg hxR]
    exact hxR (hΩR ⟨hxdom, hΩcover ⟨hxdom, by simp only [mem_preimage, hDx]; exact hy⟩⟩)
  have hgx : ec.symm (simplicialMap Rs φ x) = y := by
    rw [← hxy]
    simp only [regionGluedMap, if_pos hxR]
  have hxA : x ∈ Rc.space \ Ac.space :=
    hactive x hxR _ (hsmall x hxR) (by rw [hgx]; exact hy)
  have hxΩ : x ∈ Ω := by
    by_contra hxo
    exact hxA.2 (hNbA ⟨hxR, hNbfr ⟨hxR, hxo⟩⟩)
  refine ⟨?_, ?_⟩
  · rw [hsub.space_eq]
    exact mem_nhdsWithin.2 ⟨Ω, hΩ, hxΩ, fun z hz => hΩR ⟨hz.2, hz.1⟩⟩
  · intro σ hσ hxσ v hv hvA
    obtain ⟨w, hwV, hw⟩ := hmaps hxR
    have hecy : ec y = simplicialMap Rs φ x := by
      rw [← hgx, ← hw, ec.left_inv (hVec hwV)]
    exact Set.disjoint_left.mp (hsep σ hσ ⟨v, hv, hvA⟩) ⟨x, hxσ, rfl⟩ ⟨y, hy, hecy⟩

open Classical in
theorem wallProductBlocks_stable_on_fixedSubdivision [CompactSpace M] (D : SingularTwoCell M)
    {BdM C Z W V Kt : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {η κ δ ε τ₀ : ℝ} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hZclosed : IsClosed Z)
    (hVopen : IsOpen V) (hVec : closure V ⊆ (ecf i₀).source) (hWV : closure W ⊆ V)
    (hVE : closure V ⊆ interior (Eb i₀))
    (Rc Lc Ac R T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω)
    (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb) (hNbfr : Rc.space \ Ω ⊆ Nb)
    (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite)
    (hκ : 0 < κ) (hδ : 0 < δ) (hε : 0 < ε) (hτ₀ : 0 < τ₀)
    (hlinear : ∀ s ∈ R.faces,
      ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun x => ecf i₀ (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hconv : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ecf i₀ (D x)) < ε → z ∈ ⇑(ecf i₀) '' V ∧ dist ((ecf i₀).symm z) (D x) < δ)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ecf i₀ (D x)) < ε → (ecf i₀).symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hKcpt : IsCompact Kt) (hKV : Kt ⊆ V) (hDKt : ⇑D '' Rc.space ⊆ interior Kt)
    (hwp : HasWallProductBlocks (⇑D) D.domain ecf ℓf Eb BdM C Q ρ Z η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧
      ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
        (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
        AdmissibleVertexMap D (ecf i₀) (ℓf i₀) Lc Ac R Bv φ τ →
        IsPiecewiseAffineOn (simplicialMap R φ) Rc.space →
        (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ecf i₀ (D x)) < ε) →
        EqOn (simplicialMap R φ) (fun x => ecf i₀ (D x)) Ac.space →
        (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
          Disjoint (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
            (⇑(ecf i₀) '' closure W)) →
        MapsTo (simplicialMap R φ) Rc.space (⇑(ecf i₀) '' V) →
        regionGluedMap D (ecf i₀) R φ Rc '' Rc.space ⊆ Kt →
        StarInj T (regionGluedMap D (ecf i₀) R φ Rc) →
        HasWallProductBlocks (regionGluedMap D (ecf i₀) R φ Rc) D.domain ecf ℓf Eb BdM C
          Q ρ Z (η / 2) := by
  sorry

open Classical in
theorem exists_wallGenericVertexMap (D : SingularTwoCell M) {BdM C V : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hVec : V ⊆ (ecf i₀).source)
    (hVE : closure V ⊆ interior (Eb i₀))
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite)
    (hlinear : ∀ s ∈ R.faces,
      ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun x => ecf i₀ (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D (ecf i₀) (ℓf i₀) Lc Ac R Bv φ τ ∧
        (∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker (ℓf i₀)) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2)))) ∧
        (∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
          FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y →
            y ∉ wallSystemSkeleton Q ρ) ∧
        (∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
          IsFreeDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
            ∀ σ ∈ R.faces, σ.card ≤ 2 →
              y ∈ regionGluedMap D (ecf i₀) R φ Rc ''
                  (Rc.space ∩ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
                ∀ w ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w) ∧
        ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
          IsFreeInteriorDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
            ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
              ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧
                y ∈ wallSystemCell ρ cm ∧ y ∈ wallSystemCell ρ cp ∧
                ∀ U ∈ 𝓝 y,
                  (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                    wallSystemCellInt ρ cm).Nonempty ∧
                  (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                    wallSystemCellInt ρ cp).Nonempty := by
  sorry

open Classical in
theorem wallProductBlocks_of_wallGenericity (D : SingularTwoCell M) {BdM C W V Kt : Set M}
    {ι : Type} (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    {ε κ : ℝ} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hκ : 0 < κ)
    (hVopen : IsOpen V) (hVec : closure V ⊆ (ecf i₀).source) (hWV : closure W ⊆ V)
    (hWE : closure W ⊆ interior (Eb i₀))
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hRfin : Rc.faces.Finite) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite) (hε : 0 < ε)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ecf i₀ (D x)) < ε)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓf i₀ (simplicialMap R φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓf i₀ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    (hfrozen : EqOn (simplicialMap R φ) (fun x => ecf i₀ (D x)) Ac.space)
    (hmaps : MapsTo (simplicialMap R φ) Rc.space (⇑(ecf i₀) '' V))
    (hD'K : regionGluedMap D (ecf i₀) R φ Rc '' Rc.space ⊆ Kt) (hKV : Kt ⊆ V)
    (hinj' : UniformInjectivityScale D.domain (regionGluedMap D (ecf i₀) R φ Rc) κ)
    (hgcont : ContinuousOn (regionGluedMap D (ecf i₀) R φ Rc) D.domain)
    (hgfiber : ∀ y,
      (D.domain ∩ regionGluedMap D (ecf i₀) R φ Rc ⁻¹' {y}).encard ≤ 2)
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker (ℓf i₀)) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hfree : ∀ y ∈ closure W,
      FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y)
    (hgenskel : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y →
        y ∉ wallSystemSkeleton Q ρ)
    (hgenfold : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      IsFreeDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
        ∀ σ ∈ R.faces, σ.card ≤ 2 →
          y ∈ regionGluedMap D (ecf i₀) R φ Rc ''
              (Rc.space ∩ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
            ∀ w ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w)
    (hgencross : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      IsFreeInteriorDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
        ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
          ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧
            y ∈ wallSystemCell ρ cm ∧ y ∈ wallSystemCell ρ cp ∧
            ∀ U ∈ 𝓝 y,
              (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                wallSystemCellInt ρ cm).Nonempty ∧
              (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                wallSystemCellInt ρ cp).Nonempty) :
    ∃ η' : ℝ, 0 < η' ∧
      HasWallProductBlocks (regionGluedMap D (ecf i₀) R φ Rc) D.domain ecf ℓf Eb BdM C
        Q ρ (closure W) η' := by
  sorry

end MetricAmbient

open Classical in
theorem generalPositionInDoubleBuffered : GeneralPositionInDoubleBufferedStatement := by
  classical
  intro E _ _ _ S K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let _ : CompactSpace (double 3 K).space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space (double 3 K)).isCompact
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  intro ι C Bd B G β γ hloc hfiber _ hbuffer _ hmapC hproper hsurj hparam havoid
  have hBspace : S.boundaryNeighborhood.space ⊆ K.space := fun x hx =>
    PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex hx)
  obtain ⟨n, W, V, hWopen, hVopen, hWV, hWn, huniv, hcharts⟩ :=
    exists_finiteAdaptedCover_of_compactSpace Bd C
      fun y U hU => exists_adaptedHalfSpaceChart_in_double K S.isManifold y U hU
  choose ecf ℓf hecf hℓf hVclf hCf hBdf using hcharts
  obtain ⟨Qc, Cf, Bf, Eb, Eb', hQsub, hVEint, hsys⟩ :=
    exists_commonWallComplex K S.isManifold n (fun i : Fin n => V i.1)
      (fun i : Fin n => ecf i.1 i.isLt) (fun i : Fin n => ℓf i.1 i.isLt)
      (fun i : Fin n => hecf i.1 i.isLt) (fun i : Fin n => hℓf i.1 i.isLt)
      (fun i : Fin n => hCf i.1 i.isLt) (fun i : Fin n => hBdf i.1 i.isLt)
      (fun i : Fin n => hVclf i.1 i.isLt)
  have hVW : ∀ j, V j ⊆ ⋃ i, W i := by
    intro j
    rw [huniv]
    exact subset_univ _
  have hdpG : doublePointSet (⇑G) G.domain ⊆ ⋃ j, W j := by
    rw [huniv]
    exact subset_univ _
  have hUW : ⋃ j, W j ⊆ ⋃ j, ⋃ (_ : j < n), closure (W j) := by
    refine iUnion_subset fun j => ?_
    by_cases hj : j < n
    · exact fun x hx => mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, subset_closure hx⟩⟩
    · rw [hWn j (not_lt.mp hj)]
      exact empty_subset _
  have key : ∀ k : ℕ, ∃ (cl : SingularTwoCell (double 3 K).space)
      (bdry : ContinuousMap loopCircle (frontier cl.domain))
      (gl : freeLoop S.boundaryNeighborhoodSpace) (ηk : ℝ),
      cl.domain = G.domain ∧ MapsTo (⇑cl) cl.domain C ∧
        (∀ x ∈ cl.domain, ∃ U ∈ 𝓝[cl.domain] x, InjOn (⇑cl) U) ∧
        (∀ y, (cl.domain ∩ ⇑cl ⁻¹' {y}).encard ≤ 2) ∧
        cl.domain ∩ ⇑cl ⁻¹' Bd = frontier cl.domain ∧
        (∀ z ∈ Set.range cl.boundary, B ∈ 𝓝[Bd] z) ∧
        doublePointSet (⇑cl) cl.domain ⊆ ⋃ j, W j ∧ 0 < ηk ∧
        HasWallProductBlocks (⇑cl) cl.domain (fun i : Fin n => ecf i.1 i.isLt)
          (fun i : Fin n => ℓf i.1 i.isLt) Eb Bd C Qc
          ((↑) : (double 3 K).space → E × E × ℝ)
          (⋃ j, ⋃ (_ : j < k), closure (W j)) ηk ∧
        Function.Surjective bdry ∧
        (∀ θ, ((cl (bdry θ) : (double 3 K).space) : E × E × ℝ) = ι (gl θ)) ∧
        ¬loopClassMeets gl S.basepoint S.normalSubgroup := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, β, γ, 1, rfl, hmapC, hloc, hfiber, hproper, hbuffer, hdpG, one_pos, ?_,
          hsurj, hparam, havoid⟩
        refine HasWallProductBlocks.mono (hasWallProductBlocks_empty one_pos) ?_
        exact iUnion_subset fun j => iUnion_subset fun hj => absurd hj (Nat.not_lt_zero j)
    | succ k ih =>
        obtain ⟨cl, bdry, gl, ηk, hdom, hclC, hclloc, hclfib, hclpr, hclbuf, hcldp, hηk,
          hwp, hbsurj, hbparam, hbavoid⟩ := ih
        have hZsucc : (⋃ j, ⋃ (_ : j < k + 1), closure (W j)) ⊆
            (⋃ j, ⋃ (_ : j < k), closure (W j)) ∪ closure (W k) := by
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
          · exact fun x hx => mem_union_left _ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hlt, hx⟩⟩)
          · subst heq
            exact fun x hx => mem_union_right _ hx
        by_cases hk : k < n
        · have hZclosed : IsClosed (⋃ j, ⋃ (_ : j < k), closure (W j)) :=
            Set.Finite.isClosed_biUnion (Set.finite_lt_nat k) fun j _ => isClosed_closure
          have hVcl : closure (V k) ⊆ (ecf k hk).source := hVclf k hk
          have hVec : V k ⊆ (ecf k hk).source := subset_closure.trans hVcl
          obtain ⟨Rc, Lc, Ac, Ω, Nb, hRfin, hRman, hLR, hAR, hRdom, hRV, hLspace, hΩ,
            hΩcover, hΩR, hNb, hNbfr, hNbA, hAfree⟩ :=
            cl.exists_cutOutPiece_of_closure_subset (V₀ := W k) (hVopen k) (hWV k)
          obtain ⟨Ok, hOkopen, hOkZ, hOkcross⟩ :=
            exists_normalCrossing_of_hasWallProductBlocks cl
              (fun i : Fin n => hecf i.1 i.isLt) (fun i : Fin n => hℓf i.1 i.isLt)
              (fun i : Fin n => hBdf i.1 i.isLt) hwp
          obtain ⟨T, κ, δ, ε, hκ, hδ, hε, hTfin, hTspace, hTstar, hcert, hconv, hactive,
            hbdbuf⟩ :=
            exists_normalizationPreparation_on_prescribedRegion cl hclloc hclfib hclbuf
              (hVopen k) (hWV k) (ecf k hk) hVec Rc Ac hRfin hAR hRdom hRV hAfree
          have hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
              dist z (ecf k hk (cl x)) < ε → z ∈ ⇑(ecf k hk) '' V k :=
            fun x hx z hz => (hconv x hx z hz).1
          have hinjD : UniformInjectivityScale cl.domain (⇑cl) κ :=
            (hcert (⇑cl) (fun x _ => by rw [dist_self]; exact hδ) hTstar).1
          have hstk : HasStableCrossingBlocks (⇑cl) cl.domain (ecf k hk) (ℓf k hk) Bd
              ((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩ closure (V k \ closure (W k))) ηk :=
            hasStableCrossingBlocks_of_wallProductBlocks hsys hwp
              cl.isPLBall_domain.isPolyhedron.isCompact cl.continuousOn hclC hκ hinjD
              ⟨k, hk⟩ ((hZclosed.inter isClosed_closure).isCompact) inter_subset_left
              fun x hx => hVEint ⟨k, hk⟩ (closure_mono Set.sdiff_subset hx.2)
          obtain ⟨R, τ₀, Kt, hτ₀, hsub, hRsfin, hlinear, hKcpt, hKV, hDKint, hcontrol⟩ :=
            exists_protectedSubdivision_in_adaptedChart cl hclloc hclfib hclpr hclC
              hOkcross hZclosed hOkopen hOkZ (ecf k hk) (ℓf k hk) (hecf k hk) (hℓf k hk)
              (hVopen k) hVcl (hCf k hk) (hBdf k hk) Rc Lc Ac hRfin hRman hLR hAR hRdom
              hRV hLspace hΩ hΩR hNb hNbfr hNbA (hWV k) hAfree hstk T hTfin hTspace hTstar
              hκ hδ hε hcert hconv
          obtain ⟨τ, hτ, hτle, hstab⟩ :=
            wallProductBlocks_stable_on_fixedSubdivision cl
              (fun i : Fin n => ecf i.1 i.isLt) (fun i : Fin n => ℓf i.1 i.isLt) Eb Eb'
              ⟨k, hk⟩ hsys hclloc hclfib hclpr hclC hZclosed (hVopen k) hVcl
              (hWV k) (hVEint ⟨k, hk⟩) Rc Lc Ac R T hRfin hRdom hRV hLspace hΩ hΩcover
              hΩR hNb hNbfr hNbA hsub hRsfin hκ hδ hε hτ₀ hlinear hcert hconv hactive
              hKcpt hKV hDKint hwp
          obtain ⟨Bv, φ, hadm, hguard, hgenskel, hgenfold, hgencross⟩ :=
            exists_wallGenericVertexMap cl (fun i : Fin n => ecf i.1 i.isLt)
              (fun i : Fin n => ℓf i.1 i.isLt) Eb Eb' ⟨k, hk⟩ hsys hclpr hclC hVec
              (hVEint ⟨k, hk⟩) Rc Lc Ac hLR hAR hRdom hRV hLspace R hsub hRsfin hlinear hτ
          obtain ⟨hpl, hsmall, hfrozen, hpnonneg, hpzero, hsep, hmaps, hgK, hstarG, -, -⟩ :=
            hcontrol Bv φ (hadm.mono hτle)
          obtain ⟨cl', hdom', hglue, hglueoff⟩ :=
            exists_gluedCell_of_vertexMap_in_adaptedChart cl (hVopen k) (ecf k hk)
              (hecf k hk) hVec Rc Ac hRfin hRman hAR hRdom hRV hΩ hΩR hNb hNbfr hNbA R φ
              hsub hRsfin hfrozen hpl hmaps
          have hbridge : ⇑cl' = regionGluedMap cl (ecf k hk) R φ Rc :=
            eq_regionGluedMap_of_eqOn hglue hglueoff
          have hclose : ∀ x ∈ cl.domain, dist (cl' x) (cl x) < δ := by
            intro x _
            by_cases hxR : x ∈ Rc.space
            · rw [hglue hxR]
              exact (hconv x hxR _ (hsmall x hxR)).2
            · rw [hglueoff hxR, dist_self]
              exact hδ
          have hstarcl : StarInj T (⇑cl') := by
            rw [hbridge]
            exact hstarG
          have hinjD' : UniformInjectivityScale cl.domain (⇑cl') κ :=
            (hcert (⇑cl') hclose hstarcl).1
          have hinjG : UniformInjectivityScale cl.domain
              (regionGluedMap cl (ecf k hk) R φ Rc) κ := by
            rw [← hbridge]
            exact hinjD'
          obtain ⟨hC', hfibV, hloc', hcard', hpr', H, hH0, hH1, hHtrack⟩ :=
            exists_globalInvariants_of_gluedCell cl cl' hclpr hclC hclbuf hκ hcert hclose
              hstarcl (ecf k hk) (ℓf k hk) (hVopen k) hVec (hCf k hk) (hBdf k hk) Rc Lc Ac
              hRfin hRman hRdom hRV hLspace hΩ hΩR hNb hNbfr hNbA R φ hsub hsmall hfrozen
              hpnonneg hpzero hchartbuf hbdbuf hdom' hglue hglueoff
          have hgcont : ContinuousOn (regionGluedMap cl (ecf k hk) R φ Rc) cl.domain := by
            rw [← hbridge, ← hdom']
            exact cl'.continuousOn
          have hgfiber : ∀ y, (cl.domain ∩
              regionGluedMap cl (ecf k hk) R φ Rc ⁻¹' {y}).encard ≤ 2 := by
            intro y
            rw [← hbridge, ← hdom']
            exact hcard' y
          have hwpZ := hstab Bv φ hadm hpl hsmall hfrozen hsep hmaps hgK hstarG
          have hfree : ∀ y ∈ closure (W k),
              FreeSourceGerm R Ac (regionGluedMap cl (ecf k hk) R φ Rc) cl.domain y :=
            fun y hy => freeSourceGerm_of_mem_closure cl (ecf k hk) Rc Ac R hsub hVec hΩ
              hΩcover hΩR hNbfr hNbA hsmall hactive hsep hmaps hy
          obtain ⟨ηw, hηw, hwpW⟩ :=
            wallProductBlocks_of_wallGenericity cl (fun i : Fin n => ecf i.1 i.isLt)
              (fun i : Fin n => ℓf i.1 i.isLt) Eb Eb' ⟨k, hk⟩ hsys hclfib hclpr
              hclC hκ (hVopen k) hVcl (hWV k)
              ((hWV k).trans (subset_closure.trans (hVEint ⟨k, hk⟩))) Rc Lc Ac R Bv φ
              hRfin hRdom hRV hLspace hsub hRsfin hε hadm.2.1 hsmall hpnonneg hpzero
              hfrozen hmaps hgK hKV hinjG hgcont hgfiber hguard hfree hgenskel hgenfold
              hgencross
          have hwpNext : HasWallProductBlocks (⇑cl') cl'.domain
              (fun i : Fin n => ecf i.1 i.isLt) (fun i : Fin n => ℓf i.1 i.isLt)
              Eb Bd C Qc ((↑) : (double 3 K).space → E × E × ℝ)
              (⋃ j, ⋃ (_ : j < k + 1), closure (W j)) (min (ηk / 2) ηw) := by
            rw [hdom', hbridge]
            exact (hwpZ.union hwpW).mono hZsucc
          have hbuf' : ∀ z ∈ Set.range cl'.boundary, B ∈ 𝓝[Bd] z := by
            rintro _ ⟨x, rfl⟩
            have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ frontier cl.domain := by
              rw [← hdom']
              exact x.2
            have h1 := hHtrack 1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩
            rw [hH1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩] at h1
            exact h1.2
          have hdpnew : doublePointSet (⇑cl') cl'.domain ⊆ ⋃ j, W j := by
            rw [hdom']
            exact doublePointSet_subset_of_preimage_singleton_eq_off cl.domain hfibV hcldp
              (hVW k)
          have hHB : ∀ (t : unitInterval) (x : frontier cl.domain), H (t, x) ∈ B :=
            fun t x => mem_of_mem_nhdsWithin (hHtrack t x).1 (hHtrack t x).2
          obtain ⟨c, δ₀, hcδ, hδavoid⟩ :=
            exists_boundary_loop_of_buffered_homotopy S K cl cl' bdry gl hdom' hC' hbparam
              hbavoid hbsurj H hH0 hH1 hHB hBspace
          exact ⟨cl', ⟨c, c.continuous⟩, δ₀, min (ηk / 2) ηw, hdom'.trans hdom, hC', hloc',
            hcard', hpr', hbuf', hdpnew, lt_min (by linarith) hηw, hwpNext, c.surjective,
            hcδ, hδavoid⟩
        · refine ⟨cl, bdry, gl, ηk, hdom, hclC, hclloc, hclfib, hclpr, hclbuf, hcldp, hηk,
            hwp.mono ?_, hbsurj, hbparam, hbavoid⟩
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          by_cases hjk : j < k
          · exact fun x hx => mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩
          · rw [hWn j (by omega), closure_empty]
            exact empty_subset _
  obtain ⟨A, bdry, gl, ηn, hdom, hAC, hAloc, hAfib, hApr, hAbuf, hAdp, -, hAwp, hbsurj,
    hbparam, hbavoid⟩ := key n
  obtain ⟨On, -, hOnZ, hAcross⟩ :=
    exists_normalCrossing_of_hasWallProductBlocks A (fun i : Fin n => hecf i.1 i.isLt)
      (fun i : Fin n => hℓf i.1 i.isLt) (fun i : Fin n => hBdf i.1 i.isLt) hAwp
  have hAcross' : ∀ y ∈ doublePointSet (⇑A) A.domain,
      ∃ e₃ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₃.source ∧
        HasPLNormalDoubleCrossingAt (e₃ ∘ ⇑A) (A.domain ∩ ⇑A ⁻¹' e₃.source)
          (e₃ '' (e₃.source ∩ Bd)) (e₃ y) :=
    fun y hy => hAcross y ⟨hy, hOnZ (hUW (hAdp hy))⟩
  have hAbd : Set.range A.boundary ⊆ B := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ A.domain ∩ ⇑A ⁻¹' Bd := by
      rw [hApr]
      exact x.2
    exact mem_of_mem_nhdsWithin hx.2 (hAbuf _ ⟨x, rfl⟩)
  have hAimage : A '' A.domain ∩ Bd = Set.range A.boundary := by
    rw [← image_inter_preimage, hApr]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  obtain ⟨hA⟩ := SingularTwoCell.nonempty_normalSingularCellData_of_fields (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold) A Bd B hAloc hAfib hAbd
    hAimage hAcross'
  obtain ⟨c, δ₁, hcδ, hδavoid⟩ :=
    exists_boundary_loop_of_buffered_homotopy S K A A bdry gl rfl hAC hbparam hbavoid
      hbsurj ⟨fun z => A.boundary z.2, A.boundary.continuous.comp continuous_snd⟩
      (fun _ => rfl) (fun _ => rfl) (fun _ x => hAbd (mem_range_self x)) hBspace
  exact ⟨A, hA, hdom, hAC, hAbuf, c, δ₁, hcδ, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
