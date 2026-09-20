# C — answer digest (external consultant, 2026-09-20; reviewed branch head `c530742c0`)

Digest of the answer to `C-general-position-globalisation.md`. Checkable claims verified by the
lead are marked ✓. Notation: `S = Δ`, `F_f(y) = {x ∈ S | f x = y}`, `Σ(f) = {y | #F_f(y) ≥ 2}`,
`N ⊂ M` the chosen copy of `|K|`, `H = ∂N = BdM`.

## Q1 — YES: `singularSet` follows from the other fields (P2 disappears)

**Singular-set recognition and triangulation.** `M` a Hausdorff PL 3-manifold, `D` a
`SingularTwoCell M`, locally injective, `#F_D(y) ≤ 2`, `D(S) ∩ H = D(∂S)`, and the exact
`crossing` field ⇒ `Nonempty (NormalSingularSetTriangulation D H)`; `Σ(D)` is a compact PL
1-manifold (possibly empty) with `∂Σ(D) = Σ(D) ∩ H`. `boundary_image_subset` is not needed.
Lemma chain:
1. *Compactness*: finite injectivity cover ⇒ Lebesgue number `η`; double pairs are `η`-apart;
   `Σ(f)` is the image of the compact `{(x,x') | d ≥ η, f x = f x'}`.
   *Polyhedrality*: refine until `f` is affine on simplices and injective on closed vertex
   stars; then `Σ(f) = ⋃_{σ ∩ τ = ∅} f(σ) ∩ f(τ)`, a finite union of polytopes (the tree already
   has this formula and the Euclidean triangulation theorem under closed-star injectivity).
   "After making `D` simplicial" must mean compatible source **and target** triangulations.
2. *Germ equality*: both double-crossing predicates contain "all nearby fibres lie in `A ∪ B`",
   so near `y`: `z ∈ Σ(f) ⇔ z ∈ f(A) ∩ f(B)` — an equality of germs.
3. *Interior points*: `HasPLCrossingAt` is more permissive than two full planes ✓ — its sheets
   are `P ∩ {α ≥ 0}`, `Q ∩ {β ≥ 0}` with `α = 0 ∨ β = 0` (`GeneralPosition.lean:2370`), so alone it
   allows a half-line intersection. But for `y ∉ H`, `D(S) ∩ H = D(∂S)` puts neither preimage on
   `∂S`, and a PL homeomorphism of germs preserves intrinsic boundary, so `α = β = 0` and the
   germ is the full line `P ∩ Q`. **A double curve cannot end in `M \ H`.**
4. *Boundary points*: models `P ∩ {ℓ ≥ 0}`, `Q ∩ {ℓ ≥ 0}` with `∃ u ∈ P ∩ Q, ℓ u = 1`; the
   intersection is a genuine half-line. No isolated double point in either case.
5. *Packaging*: triangulate the polyhedron; local models give vertex degree 1 on `H`, 2 off `H`.
   **Take `carrier := doublePointSet D D.domain`**: `PLPiece 3 M carrier` does not require a
   3-dimensional source complex (the `3` is the chart dimension), so take the record's `complex`
   to be the piece's own complex and `faces_subset` is reflexivity.
The existential auxiliary half-space `M` of the boundary wrapper is **not** an obstruction to
Q1 (only the two sheet models are used). Properness `S ∩ D⁻¹(H) = ∂S` also follows.

## Q2 — the relative statement and the invariant

**(4) Buffered relative local normalization.** `S` compact PL surface, `f : S → N` PL, locally
injective, ≤ 2-to-1, `f⁻¹(H) = ∂S`; `C ⊂ M` closed with `f` normal over an open `O ⊃ C`;
`W, V` open, `closure W` compact `⊂ V`, `V` in an interior chart or an adapted boundary
half-space chart. For every `ε > 0` there are a PL `g : S → N` and an open `O_* ⊂ O`, `C ⊂ O_*`,
with: `sup d(g,f) < ε`; `g` locally injective and ≤ 2-to-1; `g⁻¹(H) = ∂S`;
`F_g(y) = F_f(y)` for all `y ∈ O_* ∪ (M \ V)`; `g` normal over a neighbourhood of
`C ∪ closure W`. With `f(∂S) ⊂ Int_H B`, also a homotopy whose boundary tracks stay in `B`.
`O_*` is **chosen by the construction**, not prescribed. For the induction also fix a finite
family of small compact PL source patches `Eᵢ` (relative interiors covering `S`, `f|Eᵢ`
embedded) and require `g|Eᵢ` embedded — this is the uniform injectivity scale.
The frontier condition is a **collar** condition: freeze the full map on a source collar of a
polyhedral interface inside the already-normal region and protect its fibres; new arcs attach
to old ones by literal equality on an open overlap.
**Quantifier defect of the existing local theorems:** their form is `∃ W ∋ y, ∀ ε, ∃ g` with
`W` chosen from the *current* map; they do not normalise a *prescribed* `W ⋐ V`. That matters
when the finite cover is fixed before the induction.

**(b) "Freeze the vertices in the star" — two separate questions.** Keeping the map fixed on a
source subcomplex: yes. Protecting the full double-point configuration over its image: **no**
(another simplex can move in). Sufficient protection: (5) `f(S \ A) ∩ closure O₀ = ∅` with `A`
the frozen source set; compactness gives a positive distance; move the rest by less.
Algebraic obstruction: the tree's relative affine-independence lemma needs the frozen subset to
be *already* affinely independent, which normality does not give (an embedded planar disk is
normal, yet four frozen vertices are coplanar). The relative proof must exempt configurations
already controlled by frozen normal models.
**"Keep the map fixed everywhere it is already normal" is FALSE as a prescription:** sheets
`{z = 0}` and `{z = |x| + |y|}` meet only at the origin; freezing the normal locus freezes a
dense set, hence the origin, and the isolated double point can never be removed. Freeze a
*chosen closed protected region with a normal neighbourhood*.

**(c)** (6) fibre agreement off `V` ⇒ `Σ(g) \ V = Σ(f) \ V`, no smallness needed. Sufficient for
fibre agreement: (7) `g x = f x` when `f x ∉ V`, **and** `g x ∈ V` when `f x ∈ V` (the second
line is not implied by "changed source points lie in `f⁻¹ V`"). But a new double point can lie
in `V_k \ ⋃ W_j`, so the prompt's invariant was incomplete.
**Double-set localization.** `S` compact metric, `f` continuous, `U` open, `Σ(f) ⊂ U`, `η > 0`
⇒ `∃ δ > 0`: every `g` with `sup d(g,f) < δ` and (8) `g x = g x' ∧ d(x,x') < η ⇒ x = x'` has
`Σ(g) ⊂ U`. (Proof: `U₀ ⋐ U`; on `{(x,x') | d ≥ η, f x ∉ U₀}` the function `d(f x, f x')` has
a positive minimum `m`; take `2δ < m`, `δ < d(closure U₀, M \ U)`.)
**(9) The invariant for a fixed finite cover `W₁…W_n`:** `Σ(f_k) ⊂ U := ⋃ W_j`; `f_k` normal
near `C_k := ⋃_{j ≤ k} closure W_j`; `f_k` satisfies a common injectivity scale (8);
`f_k⁻¹(H) = ∂S`; `#F ≤ 2`. At `k = n` every double point lies in `C_n`.

## Q3 — the local source statement; ≤ 2-to-1 is a GLOBAL condition

The inner one-chart theorem already takes any finite combinatorial 2-manifold with boundary ✓
(`SingularGeneralPosition.lean:3183`); the ball hypothesis of the wrapper is not the issue. The
issue is **artificial boundary**: for a cut-out `P ⊂ S` the interface `Fr_S P` must *not* be
sent to `H`. Setup: `closure W ⊂ V₀`, `closure V₀ ⊂ V`, `P` a compact codimension-0 PL
submanifold (corners allowed), neat relative to `∂S`, with
(10) `f⁻¹(closure V₀) ⊂ Int_S P` and `P ⊂ f⁻¹(V)`; perturbation fixed near `Fr_S P` and off `P`;
only the physical boundary is constrained to the hyperplane. (10) includes **all sheets through
the region**; without it the statement is false (two unmoved patches coinciding on a disk in
`W`). Multiplicity must be counted in all of `S`: two fixed sheets coinciding in `z = 0` and a
moving embedded sheet at `z = h` moved down give a triple sheet. The tree's
`exists_fiber_encard_le_two_of_close_of_injOn_starComplex` ✓ (`:274`) is exactly the right
mechanism (uniform injectivity scale).
**Counterexample ✓: C⁰-small + locally injective does NOT preserve ≤ 2-to-1.** `S = [-1,1]²`,
`N = [-1,1]³`, `f(s,t) = (s,t,0)`; `0 < a < min(1, ε/4)`; the polygonal path `c` equal to
`(s,0)` off `[-a,a]` and interpolating, at nine equally spaced parameters,
`(-a,0), (0,0), (a/2,a/2), (-a/2,a/2), (0,0), (-a/2,-a/2), (a/2,-a/2), (0,0), (a,0)`;
`g(s,t) = (c₁ s, t, c₂ s)` is PL, locally injective, proper, `< ε` from `f`, and
`g(-3a/4,t) = g(0,t) = g(3a/4,t)`. The missing condition is a **common** injectivity scale.

## Q4 — coincident sheets

The one-chart theorem covers open 2-dimensional coincidence sets. A coincident pair can separate
disjointly or with a new closed double curve (`z = 0` and `z = δ(max(|x|,|y|) − r)` meet in the
square `max(|x|,|y|) = r`). Complexity is not monotone under normalisation and that is harmless:
normalisation produces *some* finite complexity, the surgery descends from it. No global
separation direction is required or available.

## Q5 — boundary

Use charts adapted to the **actual pair**: (11) `e(N ∩ U) = e(U) ∩ {ℓ ≥ 0}`,
`e(H ∩ U) = e(U) ∩ {ℓ = 0}`; two such charts have side-preserving transitions.
`LoopTheorem/ProjectedBoundaryLocalNormalization.lean` already specifies both equations and uses
the image of the actual side. Homotopy requirements: (12) `F₀ = f`, `F₁ = g`,
`F_t⁻¹(H) = ∂S`, `F(∂S × I) ⊂ B`; in a convex half-space neighbourhood straight interpolation
works. End-point inclusions alone do not give a homotopy *in `B`*; artificial cut boundaries
stay fixed collars; earlier boundary crossings need the same fibre protection as interior ones.

## Q6 — references

Verified: J. L. Bryant, *Piecewise linear topology*, §4 Thms 4.2, 4.3 (relative controlled
general position with `dim(S_{f'} \ X₀) ≤ 2p − n`). **Neither is the requested statement:** a
dimension bound does not give crossing models (`{z = 0}`, `{z = |x|}` have a 1-dimensional double
set but touch). Not verified: any theorem in Hempel / Hudson / Rourke–Sanderson / Zeeman
packaging all of (4).

**Division of labour:** P2 is a consequence of the crossing predicates + compact PL structure;
P1 is a buffered relative producer on prescribed regions, with fixed-cover injectivity and
global double-set localization.

---

# Review of this answer against the tree (read-only lane P1, same day)

**Where the answer misreads the tree.**
1. *(7) and the localization lemma are not gaps.* All three manifold-level local theorems
   (`GeneralPositionWithin.lean:141`, `SingularManifoldLocal.lean:245`,
   `LoopTheorem/ProjectedBoundaryLocalNormalization.lean:20` — all the same core,
   `SingularManifoldLocal.lean:81`) conclude full fibre equality
   `∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}`. That implies both lines of (7) and
   `Σ(g) \ V = Σ(f) \ V` in two lines; the localization lemma (true as stated) is only a
   fallback for a step without fibre control.
2. *"`O_*` chosen by the construction" is not a defect.* `V` is universally quantified over
   `𝓝 y`; choose `closure V ∩ C = ∅`, put `O_* := (closure V)ᶜ`, and
   `NormalCrossingTransport.lean:215` keeps every crossing on `U \ closure V`.
3. *Affine independence: right direction, wrong example.* The relative lemma
   (`SingularGeneralPosition.lean:409`, consumer `:512`, all-frozen branch `:1554`) is not hit
   by four coplanar vertices of an embedded planar disk (faces have ≤ 3 vertices, nondegenerate
   under a star-injective map). The genuine failure is a **collinear triple (or coplanar
   four-set) of frozen vertex images from two disjoint faces**. The fix is already in the tree
   and thrown away: `exists_small_vertexMap_transverse_in_halfSpace` (`:1523`) gives general
   position for *arbitrary* vertex subsets `s`, `|s| ≤ 4`, `|s ∩ B| ≤ 3`, but `:1607` and `:3183`
   expose only `∀ s ∈ R.faces`. Carry it as an invariant; subdivide by `relDerived` rel the
   frozen subcomplex (`GeneralPosition.lean:3824`). Honest relative template:
   `exists_small_simplicialMap_transverse_on_subcomplex` (`GeneralPosition.lean:3803`).
4. *A free-boundary one-chart theorem exists for interior charts*:
   `exists_small_simplicialMap_doublePointSet_manifold` (`SingularGeneralPosition.lean:1317`,
   wrapped at `GeneralPositionWithin.lean:55`) — any combinatorial 2-manifold with boundary, no
   `ℓ`, no `hboundary`, a crossing at every double point. So the artificial-boundary obstruction
   is a *half-space* problem only: `:3183`/`:3447`/`SingularChart.lean:155` take
   `hboundary : ∀ x ∈ (boundaryComplex 2 K).space, ℓ (f x) = 0` as a hypothesis, so a cut-out
   piece is rejected at the door. Generalising `boundaryComplex 2 K` to a subcomplex
   `L ⊆ boundaryComplex 2 K` with `ℓ ∘ f = 0 ↔ ∈ L.space` is mechanical (`:2969` is already
   `L`-general; `:1607` already defines `B` as the `ℓ = 0` vertices).

**Where the answer is right and sharp.** Multiplicity is counted globally in the tree already.
Side preservation (11) is present in `ProjectedBoundaryLocalNormalization`. The produced-`W`
problem is real and **fatal for any induction driven by the existing local theorem alone**:
`W := Metric.ball y (η/2)` inside a neighbourhood with *no third sheet*
(`SingularManifoldLocal.lean:136`); each step leaves a shell `V \ W` where fibres changed and
normality is not claimed, `W` is produced after `V`, so the shell cannot be made thin, and
re-applying at shell points opens new shells. `:3183` moves **all** vertices and has no `EqOn`
clause, so the relative version is a **modification of the ~3000-line chain**
`:2969 → :1607 → :3183`, not a wrapper; only the boundary-degree half (`:2537–:2935`) is
reusable unchanged.

**Invariant (9) is false as written.** Step `k+1` changes fibres over `V_{k+1} ⊋ W_{k+1}`, and a
moved sheet can meet a third unmoved sheet at a point of `V_{k+1} \ ⋃ W_j`. **Repair:** require
`V_j ⊆ ⋃ᵢ Wᵢ` (choose the `W_j` to cover an open `U ⊇ Σ(f)`, then each `V_j` a union of `Wᵢ`'s);
then `Σ(f_{k+1}) ⊆ ⋃ Wᵢ` is maintained. Do not assume `Σ` is 1-dimensional anywhere in the
relative theorem (coincident sheets on an open set inside `W` are allowed).

**Bricks, dependency ordered.** B1 `Σ(g) \ V = Σ(f) \ V` from fibre agreement, and the iff
with (7) — small. B2 expose `:1523`'s arbitrary-subset general position in the conclusions of
`:1607`, `:3183` — small. B3 `boundaryComplex 2 K → L` in `:1607`, `:3183`, `:3447`,
`SingularChart.lean:155` — medium. B4 the cut-out piece (10) from `HasDoublePointSheetsAt`
(`LoopTheorem/DoublePointCover.lean:26`) and `exists_isPLBall_patches_at_fiber_pair` — medium.
B5 the relative (frozen collar) version of `:1607`/`:3183` — **large**. B6 the relative theorem
assembled — medium. B7 the induction over the cover via `NormalCrossingTransport.lean:215` +
B1 — medium.
