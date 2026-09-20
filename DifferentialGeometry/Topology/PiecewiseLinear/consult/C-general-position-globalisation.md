# C. Globalising general position: from one chart to the whole singular disk (Moise Lemma 2, first paragraph)

*Consultation prompt, self-contained. Answer in English or Chinese.*

**Where to look.** Public repository
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only; every other branch diverges and line numbers will not match. Lean paths
below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. The book is Moise,
*Geometric Topology in Dimensions 2 and 3*, GTM 47; pages are printed pages.

### State

Moise §25, Lemma 2 (p. 184) starts from a PL map `D : Δ → M` that is locally a homeomorphism
and at most two-to-one, and says: *"we can make slight perturbations of D, preserving the
stated properties of D, so as to put |D| into general position"* — singular set a disjoint
union of polygons in `Int M` and broken lines meeting `Bd M` exactly in their end-points,
crossing (never touching) singularities. He gives no proof. Everything after that sentence
works with such *normal* cells. In Lean the normal cell is (`LoopTheorem/NormalCell.lean:78`)

```lean
structure NormalSingularCellData (D : SingularTwoCell M) (BdM B : Set M) where
  locallyInjective      : ∀ x ∈ D.domain, ∃ V ∈ 𝓝[D.domain] x, InjOn D V
  fiber_le_two          : ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2
  boundary_image_subset : Set.range D.boundary ⊆ B
  image_inter_boundary  : D '' D.domain ∩ BdM = Set.range D.boundary
  singularSet           : NormalSingularSetTriangulation D BdM
      -- a `PLPiece 3 M carrier` whose complex is a finite 1-dimensional combinatorial
      -- manifold with boundary, `map_space : … = doublePointSet D D.domain`,
      -- `map_boundary : … = doublePointSet D D.domain ∩ BdM`
  crossing              : ∀ y ∈ doublePointSet D D.domain,
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y)
```

`M` is the **double** of the triangulated 3-manifold `|K|`, a closed combinatorial 3-manifold
charted by `combinatorialChartedSpace`; `BdM` is the copy of `Bd|K|` in it, a two-sided surface.

**What is proved.**

1. *The entry cell.* `DoubleCoverDiagram.exists_projected_singular_two_cell_in_double`
   (`LoopTheorem/ProjectedCellInDouble.lean:23`): the projection `G` of the embedded disk
   upstairs is a `SingularTwoCell` in the double with `IsLocallyInjective`, fibres `≤ 2`,
   image on the `|K|` side, `G.domain ∩ G ⁻¹' BdM = frontier G.domain`,
   `G '' G.domain ∩ BdM = range G.boundary`, and boundary loop avoiding the normal subgroup.
   So four of the six fields hold for `G` on the nose. **`singularSet` and `crossing` do not:**
   the double point set of `G` can be *two-dimensional* (two disjoint sub-disks of the upstairs
   disk exchanged by the deck involution project to the same disk; fibres are exactly 2 there,
   so `fiber_le_two` does not exclude it). General position is load-bearing.
2. *One chart.* `exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_in_boundary_neighborhood`
   (`SingularGeneralPosition.lean:3447`): for a PL 2-ball `|K₀|`, `f : |K₀| → F` (`dim F = 3`)
   piecewise affine, locally injective, fibres `≤ 2`, `ℓ ∘ f ≥ 0`, `ℓ ∘ f = 0` on `∂K₀`, and
   `ε > 0`, there is an ε-close simplicial map on a subdivision, **still locally injective and
   ≤ 2-to-1**, with `ℓ(φx) = 0 ↔ x ∈ ∂K₀`, whose double point set is the space of a finite
   1-dimensional combinatorial manifold with boundary, boundary exactly on `{ℓ = 0}`, a PL
   double crossing at every double point (boundary crossing on `{ℓ = 0}`), and boundary kept in
   a prescribed neighbourhood `B`. Its hypotheses are **global in one chart**: the whole source
   ball maps into one half-space.
3. *One double point at a time, in the manifold.* `GeneralPositionWithin.lean:141`,
   `SingularManifoldLocal.lean:245`, `LoopTheorem/ProjectedBoundaryLocalNormalization.lean:20`:
   a perturbation supported in a small open `V`, **unchanged off `V`** in the fibre sense
   (`∀ z ∉ V, A ⁻¹' {z} = G ⁻¹' {z}`), normal inside a smaller set, threading the free homotopy
   class of the boundary loop and the avoidance of the normal subgroup.
4. *The step lemma* (verified today, landing on the branch shortly as
   `NormalCrossingTransport.lean`): if every double point of `G` in a set `U` has a crossing
   chart and `A` agrees with `G` off `V` in the fibre sense with `A.domain = G.domain`, then
   every double point of `A` in `U \ closure V` has one (and
   `doublePointSet A ∩ (U \ closure V) ⊆ doublePointSet G` is a consequence, not a hypothesis).
   Also: crossings transport between any two charts of the maximal PL atlas.
5. `doublePointSet` of a locally injective PL map on a compact polyhedron is compact
   (`SingularGeneralPosition.lean:649`).

**What is open:** a theorem producing `NormalSingularCellData A BdM B` for some `A` close to
`G`, same domain, boundary loop freely homotopic in `B` to that of `G`, image still on the
`|K|` side. We see two pieces, both estimated large: (P1) a finite-cover induction giving
`crossing` everywhere; (P2) assembling one global `NormalSingularSetTriangulation`.

### The questions

**Q1. Is P2 unnecessary?** Conjecture: for a PL, locally injective, ≤ 2-to-1 cell with
`crossing` at *every* double point and `image_inter_boundary`, the field `singularSet` is a
**consequence**: the double point set is a compact polyhedron (it is a subcomplex after making
`D` simplicial), `crossing` makes it locally a PL arc (half-arc at `BdM`), hence a compact
1-manifold with boundary `= doublePointSet ∩ BdM`, and it carries a triangulation that is a
`PLPiece`. Is this correct? State the exact lemma chain, and say whether anything in
`crossing` as defined (`HasPLNormalDoubleCrossingAt`, `SingularNormalForm.lean:242`: near the
point two source germs mapped PL-homeomorphically onto pieces of two planes `P₀, Q₀` with
`P₀ ⊔ Q₀ = ⊤`, plus a transversality functional at boundary points) is too weak for it — e.g.
does it exclude a double *point* that is isolated, or a double curve ending in the interior?
If the conjecture is true we would restructure: prove "five fields ⇒ `singularSet`" once, and
P2 disappears. **If it is false, the counterexample tells us which clause is missing.**

**Q2. The inductive invariant for P1.** With shrinking covers `W_k ⋐ V_k` of the compact
double point set by chart-sized open sets, the natural invariant is "after step `k`, every
double point in `W_1 ∪ … ∪ W_k` has a crossing chart". Step 4 above preserves crossings in
`U \ closure V`, but step `k+1` perturbs inside `V_{k+1}`, which **overlaps** earlier `W_j`.
So the local producer must be **relative**: perturb in `V_{k+1}` *keeping the map fixed where
it is already normal* (on a neighbourhood of a closed set `C` on which crossings are already
established), and still end normal on `W_{k+1}`. (a) Is the relative statement true in the
form "normal near closed `C`, perturb rel a neighbourhood of `C`, obtain normal near
`C ∪ closure W`"? Give the exact hypotheses; in particular what is needed along
`frontier` of the already-normal region, where new double curves must *match up* with old
ones. (b) Does the proof of the one-chart theorem (shifting vertices of a subdivision into
general position) relativise by simply not moving vertices in the star of `C`, or is there a
genuine obstruction (new double points created near `C` by moving a far vertex of a simplex
that reaches into the star of `C`)? (c) New double points can also be created *outside* every
`V_j` — between a moved sheet and a far sheet. What smallness condition excludes this, and is
it implied by fibre agreement off `V` (we think yes — that is what the hypothesis says)?

**Q3. Local versus global hypotheses of the one-chart theorem.** Theorem 2 wants the *whole*
source ball in one half-space chart. For the induction we need it for a **sub-polyhedron**
`P ⊆ Δ` with `G(P) ⊆` one chart, where `P` is not a ball and `G⁻¹(chart)` has other
components. What is the cleanest correct local statement: source a compact PL surface with
boundary `P`, map fixed on a neighbourhood of `frontier_Δ P`, fibres counted in all of `Δ`
(not just in `P`)? Is "≤ 2-to-1 counted in `Δ`" preserved, given that the perturbation is
supported in `P` but other sheets of `G` pass through the same chart?

**Q4. The two-dimensional double set.** Where sheets coincide on an open set, the
perturbation must separate them to a crossing-or-disjoint configuration. Does the one-chart
theorem's proof handle that (its hypotheses allow it), and in the global induction is there
any issue with which way the sheets separate — can an unlucky choice create a closed double
curve that is inessential but raises the complexity, and does it matter (complexity only has
to be finite at the start of Moise's induction)?

**Q5. The boundary.** The perturbation must keep `A⁻¹(BdM) = ∂Δ`, keep `A(∂Δ) ⊆ B` and keep
the boundary loop in the same free homotopy class in `B`. The one-chart theorem does this in
the half-space model with a prescribed neighbourhood `B`. In the double, `BdM` is two-sided
and the cell lies on one side. Anything that can go wrong at a double point *on* `BdM` when
two overlapping boundary charts are normalised one after the other?

**Q6. References.** A citable statement of "a PL map of a surface into a 3-manifold that is
locally injective and ≤ 2-to-1 is approximable by a normal one, relative to a closed set where
it is already normal" — Hempel, Zeeman's seminar, Rourke–Sanderson, Hudson? Precise statement
and what must be checked to apply it.

### Constraints on the answer

Exact statements (Lean-ish welcome); cite by printed page and say what you could not verify;
do not weaken existing statements. **"This is false, here is the counterexample" is the most
valuable answer you can give** — seven statements on these chains have turned out false, each
because nobody tested the quantifiers at their extremes or read how an object was constructed.
