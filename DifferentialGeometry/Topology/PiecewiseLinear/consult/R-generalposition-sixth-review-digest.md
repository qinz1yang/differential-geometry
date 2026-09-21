# Digest — external review of the redesigned A1 skeleton (snapshot `7634bd42`), 2026-09-21

Marks: **[V]** checked by the lead; **[–]** not independently verified.

**Ruling on the disagreement (worker vs consult O §1):** on the *entirely free* simplices the
four-point guard together with the source manifold condition, local injectivity and `hpzero` does
give interior transversality and transversality of the boundary traces; O §1 should not be read as
demanding two further independent general-position hypotheses. **But** "the complete source-sheet
recognition at edge–triangle points is done" still has to be proved, and the docstring's claim that
"wall degeneracies are exempted" does not match the actual quantifiers.

| Leaf / predicate | Verdict | Reason |
|---|---|---|
| `exists_transitionSubdivisionOnOverlap` | **FIX** | true as stated, but the consumer needs a covered *neighbourhood*, not a covered set (`N = {y}`, `Q` a one-vertex complex satisfies the output) |
| `hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` | **FALSE [V]** | two injective projections allow re-pairing halves of different source sheets |
| `exists_protectedSubdivision_in_adaptedChart` | **FIX** | the order `R → τ` is right; must recover the *genuine* source sheets, or consume the strengthened block predicate |
| `exists_genericVertexMap_in_adaptedChart` | **FALSE [–]** | the wall conditions have no frozen exemption, and `hwallfold` forbids boundary intersections that necessarily exist |
| `exists_normalCrossings_of_gluedCell` | **FALSE [–]** | later-chart adaptedness and the covering relation between `Nw` and the region to be checked are missing |
| `IsStableCrossingBlock` / `HasStableCrossingBlocks` | **FIX** | genuine source-sheet neighbourhoods missing; localisation may be carried or derived by a lemma |

## The fake-sheet counterexample [V]
`γ : [0,6] → ℝ²` linear through `(2,0), (0,0), (0,2), (−2,2), (−2,0), (0,0), (0,−2)`;
`S = [0,6] × [−2,2]`, `D(s,t) = (γ s, 4 + t)`, `ec = id`, `ℓ = z₃`, `BdM = {z₃ = 0}`,
`A(x,y,z) = (x,y,z−4)`, `r = 1`, `tlo = −1`. The two genuine sheets through the axis are an L in the
positive quadrant and an L in the negative quadrant: cyclic order of the four rays `AABB` — a
*touching*, not a normal crossing. Put all vertical half-sheets in `SA`, all horizontal ones in `SB`
(one of the two source lines over the axis to each): full preimage equation, both `InjOn`,
`a = b = 0`, `La = Lb = 0`, `η = 1` all hold; the projections are even bijective, but their inverses
jump to the other source sheet on the axis. (Lead checked the ray order and each field.)
**Repair of the block interface.** With inner and outer blocks `B₀ ⊆ B₁`, projections `pA, pB`,
`H₂ = ℝ²` or `ℝ × [0,∞)`: keep graph equations, margin, full preimage, and add
`IsPLHomeomorphOn pA SA (pA '' SA)`, `IsPLHomeomorphOn pB SB (pB '' SB)`,
`∀ x ∈ SA, f x ∈ B₀ → SA ∈ 𝓝[S] x ∧ pA '' SA ∈ 𝓝[H₂] (pA x)`, the same for `SB`; the outer block
has a compact buffer inside the chart domain. The seed leaf is *not* refuted by this model (it
also has `hnormal`); its FIX is a lemma recovering genuine sheets from normality, or consuming the
strengthened predicate.

## General position: guard right, wall conditions wrong
* If an interior edge–triangle pair meets, the guard excludes end points, the triangle's boundary
  and coplanar degeneracy; on the boundary any three relevant free vertices are non-collinear, so
  two meeting boundary edges cross. "**No edge–edge**" holds only in the interior: boundary
  edge–edge is exactly the boundary model. Positive height of the third vertex also uses the
  boundary structure from `hpzero`, not admissibility alone.
* **Frozen counterexample [–]:** freeze the whole local source neighbourhood of both sheets with
  the old double curve on an edge of `Qw`: every admissible perturbation keeps it, `hwallskel`
  forbids it unconditionally.
* **Free boundary counterexample [–]:** the cone over a quadrilateral with boundary vertices
  `(−1,−1,0), (1,1,0), (−1,1,0), (1,−1,0)`, apex `(0,0,1)`, `Ac = ∅`, a wall triangle
  `F ⊆ {z₃ = 0}` around the origin: every small admissible perturbation still has two boundary edges
  crossing inside `F`, violating `hwallfold`.
* **Stratify:** free interior germs use the wall conditions; the physical boundary uses the
  boundary model and does not forbid those forced incidences; frozen forced degeneracies need a
  retention certificate for the *complete source sheets* (`isStableCrossingBlock_of_eqOn_compl`
  covers only blocks whose whole preimage is untouched — **not** mixed sheets). The remaining bad
  polynomials must be shown not identically zero on the relative parameter space; this is not
  "generic" for free.
* `hwalltrans`: the straightness is *not* too strong in the free case "both preimages interior to
  triangles" — it should be derived from the local recognition. Weakening to "each branch leaves
  `aff F` immediately" still allows touching the wall from one side. Genuine two-sided crossing:
  the local parameter satisfies `λ_F (γ s) · s > 0` for `0 < |s| ≪ 1` (up to a global sign); frozen
  germs go through the retention branch instead of being forced straight.

## Crossing consumer and locality
Degenerate input: `Z = Nw = ∅`, empty `Qw`, `ℓw = 0`, `Pw = {y}` with `y` a new boundary double
point — old stability and all wall conditions hold vacuously, no output block can exist (an
interior block cannot contain `y`; a boundary block needs the third coordinate of `A` to vanish).
Add at least: `∀ i, ecw i ∈ (plGroupoid 3).maximalAtlas M`, `∀ i, ℓw i ≠ 0`, the two adaptedness
equivalences of `ecw i`/`ℓw i` for `C`, `BdM`; `∀ i, K ∩ (Z ∪ closure W) ∩ Pw i ⊆ Nw i`;
`∀ i, ⇑ec '' Nw i ⊆ interior (Qw i).space`; `IsClosed Z`; `∀ i, IsClosed (Pw i)`. Adaptedness alone
is not enough: an empty `Nw` would miss the bad overlap of O §3.
**Separation distance need not be a numeric field:** for genuine buffered sheets choose relatively
open `U_A, U_B` covering `f⁻¹(B₀) ∩ S`; compactness gives
`dist (f (S \ (U_A ∪ U_B))) B₀ > 0` when the remainder is non-empty — but under the bare definition
one cannot just claim "the remaining source set is compact". `HasStableCrossingBlocks` need not get
a parameter `N`, but needs a `localize` lemma on compact sets (or all outer blocks inside a given
open `N`). A sufficient condition for cover-level retention: `Q ⊆ N` and
`∀ z ∈ N, S ∩ g⁻¹{z} = S ∩ f⁻¹{z}` — fibres over all of `N`, not only over the old double points.

**Missing obligations:** recovery of genuine source sheets; stratified relative density and
retention of forced degeneracies; cover-level retention after localisation. **Fixture:** in the
double-ball model two transverse planar disks joined by a PL band avoiding the intersection line
into one proper immersed disk; frozen outer ring; the later chart a non-trivial affine shear; a
non-zero small perturbation in the free region. **Biggest surprise:** a target image that splits
into two graphs with a strict margin need not correspond to two sheets of the source.
