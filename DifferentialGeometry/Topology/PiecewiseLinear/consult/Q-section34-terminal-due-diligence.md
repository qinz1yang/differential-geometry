# Q — independent due diligence on the six §34 terminal leaves (read-only, no compiler)

Audit of `Skeleton/Section34Terminal.lean` (5 leaves) and `exists_section34CutFrame`
(`Skeleton/ControlledGraphNeighborhood.lean:134-157`) against the **actual Lean definitions**.
Nothing compiled, nothing edited. Method as in `consult/M-frozen-leaves-due-diligence.md`.
Unqualified `:NNN` = `Section34Frame.lean`.

## Verdicts

| leaf | verdict | one-line reason |
|---|---|---|
| `exists_section34NormalFamily` | CONFIRMED | no degenerate witness (`IsPLCellOn d` forces a nonempty cell and, for `d ≥ 1`, a nonempty intrinsic boundary); the two `→ False` clauses are satisfiable — nearly redundant given `Section34Trace` — so `NormalPlus` is not secretly inconsistent |
| `exists_section34FaceDisks` | **SUSPECT** | three of the four ingredients of the reviewer's cyclic-seam argument are **not** fields of `NormalPlus`; the one that is (innermost-disk exclusion) is an *assumption* pushed onto leaf 1, so "P6 OK" is true but hollow |
| `exists_section34ResidualBalls` | CONFIRMED | `IsPLCellOn 3 (H t) (frontier (H t))` + `O_t ⊆ interior (H t)` do make the component test an outer-component test; both N-digest counterexamples blocked, clause by clause |
| `section34SourceFace_iff_cutLe` | **SUSPECT** | the leaf silently entails *every `𝒦`-triangle carrying a face arc is a face of a tetrahedron of `𝒦`* — recorded nowhere, not implied by any cut-frame clause as written |
| `section34TargetRecognition` | **SUSPECT** | `∂V_w = ⋃E ∪ ⋃X` and `∂E_e = ⋃I` are **not** inputs anywhere; the only route is transport of the source formula along `f₁`, needing uniqueness of the intrinsic boundary of a PL cell — absent, and `IsPLHomeomorphInto.image_frontier` does not apply (it wants an **open** domain) |
| `exists_section34CutFrame` | CONFIRMED | conclusion supplies every argument the assembly consumes (checked against the 14-clause `GraphFrame` refine at `ControlledGraphNeighborhood.lean:428-466`); no degenerate `src`, no unused output |

Headline: **no statement defect of the A-side kind** — no vacuous binder, no hypothesis missing at
a call site (both directions checked). All three SUSPECTs rest on one **missing PL
invariance-of-domain package**, §4.

## 1. Both directions of the assembly wiring

`section34CellDiagram` (`Section34Terminal.lean:172-328`) passes `hdata` to `FaceDisks`;
`hdata hdisk` to `ResidualBalls`; `hdata` to `SourceFace_iff_cutLe`;
`hdata hdisk hres hface tc tcBd htcdef htcbddef` to `TargetRecognition`, where `hface` is literally
the previous leaf's output (`:180, :186`). **Nothing produced upstream is dropped, and nothing is
passed that the consumer does not use.** Destructurings are arity-correct: `hdata` 17 =
`NormalPlus`'s conjuncts (`:609-635`), `hdisk` 12 = `:644-657`, `hres` 16 = `:668-696`, `hcut`
24 = `:495-530`, `hctrl` 5 = `:485-491`, `hgraph` 14 = `:544-567`. Junk is avoided: every `H σ` in
the assembly goes through `section34LabelSimplex cr (par l)` with `par l` of dimension 3, and both
branches supply `σ ∈ 𝒦.complex.faces` (`hcrF` `:562`; `t.2.1`) — `Section34Terminal.lean:213-217`.

Local finiteness is in the right spaces and the filter change is handled correctly: `:502` is `𝓝`
in `M₁` tested on `U = ⋃ src l` (`:503`) = `hLFs`; `:487-488` is `𝓝[h '' U]`, and
`exists_nhds_finite_of_subset_carriers` (`:352-366`) legitimately upgrades it to ambient `𝓝`
because `S i ⊆ Hc (cr i) ⊆ h '' U`. **Every ambient `frontier` in the frame is of a codimension-0
set** — `H t` (`:491, :585`), `⋃ tgtV` (`:596, :647`), `section34FaceTorus` (`:598`); no intrinsic
boundary is spelled as an ambient frontier anywhere. Universes: `Section34Label` needs all eight
index types in one `Type v`; with `Ea = EuclideanSpace ℝ (Fin N) : Type` they are `Type 0`, so
`ULift.{u}` lands in `Type u` and `Section34CellDiagram.{u}` applies (`Section34Terminal.lean:285`).

## 2. Refutation probes

* `U = ∅`: `bijOn` forces `𝒦.complex.space = ∅`, all eight index types empty, `⋃ src l = ∅ = U`,
  `Trace` holds with any `r, J`. All six leaves **consistently trivial** — no vacuity pathology.
  `𝒦' = 𝒦` is legal (`IsSubdivision.refl`) and only makes the leaves harder, not false.
* **Degenerate witnesses are excluded by the cell predicate itself.** `IsPLCellOn d S B` forces
  `S ≠ ∅` (`:119`) and, since `stdSimplexBoundary 0 = ∅` while `stdSimplexBoundary (d+1) ≠ ∅`
  (`Polyhedron.lean:38`; `stdSimplex ℝ (Fin 1) = {1}`), forces `B ≠ ∅` for `d ≥ 1` and `B = ∅`
  with `S` a point for `d = 0`. Consequences: `tgtDBd s ≠ ∅` with `:646` makes digest N's **empty
  trace impossible**; `tgtABd a ≠ ∅` with `:657` forces every face arc to meet a splitting disk;
  `tgtP p` is forced to be exactly one point (`:653`); `tgtX x ≠ ∅` with `:671` forces
  `tgtR t ∩ tgtV w ≠ ∅` at every patch index. No `0 < r σ` hole: `:593` carries `∀ s, 0 < r s`.
* Index subtypes identify nothing: a face *is* its `Finset`, so two subdivision edges with the same
  vertex set are the same edge, and proof irrelevance makes the two ends of `:526-528` literally
  the two `w` with `w.1 ⊆ e.1`. A `𝒦'`-vertex that is also a `𝒦`-vertex is an ordinary member.
* `h` non-PL: the six leaves use only `IsEmbedding (U.domRestrict h)`; `h` enters through images of
  *points* (`w.1.card = 1`, so `simplexBody 𝒦' w.1` is the single point `𝒦'.map x`) and carrier
  containments. `η` huge/tiny: `Q` is existential, so `hQsep` stays achievable. No probe bites.

## 3. The reviewer's stated reasons, checked against the definitions

### (a) foreign face arcs

`d_σ ⊆ |σ|` **is** a field (`:521`). `d_σ ∩ C_v` a designated 1-cell or empty **are** fields
(`:504-505`, `:512-513`), with local finiteness `:502` and compactness from `IsPLCellOn.isCompact`
(`:114`). `Γ ⊆ Int N` is **available and in the right place**: the argument needs the *source*
neighbourhood, and `Section34GraphFrame`'s **first** clause is
`IsLocallyFiniteRegularNeighborhoodOf (section34CutNeighborhood src) (graphSkeletonSpace 𝒦) U`
(`:544-545`), whose `.mem_nhdsSet` (`PolyhedralGraph.lean:276`) gives `N ∈ 𝓝ˢ Γ` **in `M₁`**. The
target-side clause `f₁ '' N ∈ 𝓝ˢ (h '' Γ)` (`:548`) is a different statement and is **not** the one
needed — the suspicion raised in the brief is answered in the good direction.
**Missing:** "a compact polyhedron of dimension `≤ 1` has empty interior relative to a PL 2-cell".
`grep IsPLCellOn` returns hits only in `Section34Frame/Section34Terminal/ControlledGraphNeighborhood`
— the predicate has **no API** beyond `isCompact`/`nonempty`. `section34_faceArc_subset_faceDisk_iff`
does not exist.

### (b) the cyclic-seam argument, ingredient by ingredient

1. *single crossing*: **supplied**, `:599-600` (`∃ p, J s i ∩ tgtEBd e = {p}` for every incident
   `e`); `tgtEBd e` is the intrinsic boundary circle of the splitting disk — the right object.
2. *at least three seams*: **not supplied**. Needs "a subdivision restricts to a subcomplex";
   Lean's `IsSubdivision` (`Subdivision.lean:9`) is only `space_eq ∧ each K'-face inside some
   K-face`, and the file has no restriction lemma.
3. *the `γ_e` cut `∂T_σ` into cyclic annuli*: **not supplied**. Nearest fields are `:618-620`
   (`tgtE e ⊆ tgtVBd w`; two vertex balls meet inside `⋃ tgtE`). No annulus, no cyclic order.
4. *single crossing ⇒ transverse and essential*: **not supplied**. The only homotopy tool is
   `CarriesFundamentalGroupOnto` (`:208`), and `:560-561` gives surjectivity from the *rim*
   `h '' simplexRim 𝒦 s.1` onto `π₁(T_σ)` — "the rim generates", not "`J s i` is essential". No
   mod-2 intersection theory exists in the tree.
5. *innermost disk exterior*: **supplied, but as a hypothesis** — the two `→ False` clauses
   `:626-629`, `:630-635` sit in `NormalPlus`, i.e. in **leaf 1's** obligation. P6's difficulty is
   relocated, not discharged.

Counter-check (is `:626-629` *inconsistent*?): no. `IsPLCellOn 2 Dj Jd` gives `Jd ⊆ Dj`, and
`tgtEBd e ⊆ tgtE e`, so `Disjoint Dj (tgtE e)` forces `Jd ∩ tgtEBd e = ∅`; if `Jd` is a trace
circle `J s i` this contradicts `:599-600` outright. So the clause is satisfiable and nearly a
*consequence* of `Trace`; the only step not covered by a field is `Jd ⊆ frontier (⋃ tgtV)`, again
invariance of domain (§4). Worth telling the producer: the clause may be droppable.

### (c) mixed flags at degree-2 subdivision vertices

`Section34Incident s t := (s : Set Ea) ⊆ convexHull ℝ (t : Set Ea)` (`:410`) reads correctly.
Between two `𝒦`-faces it **is** the face relation: `inter_subset_convexHull` (as at
`GeometricLink.lean:16`) plus affine independence give `conv s ⊆ conv t → s ⊆ t`, so the triangles
`σ` with `Section34Incident σ.1 t.1` are exactly the four faces of `t` — no foreign triangles. For
`w` interior to an old edge `ε ⊆ t`: the `a`-part of `∂X_{tw}` (`:689-691`) ranges over the two
triangles of `t` containing `ε`, the `I`-part (`:692-693`) over the two `𝒦'`-edges of `ε` at `w`
— the **quadrilateral is right**. All three `ResidualPlus` boundary formulas match
`Section34CutStep` term for term: `:683-685` ↔ `:449, :452`; `:686-688` ↔ `:456`; `:689-693` ↔
`:453, :454`. Strong consistency check; it passes.

### (d) the outer-component test

`O_t ⊆ interior (H t.1)` (`:578-579`) **plus** `IsPLCellOn 3 (H t) (frontier (H t))` (`:491`) is
enough; neither connectedness of `O_t` nor an extra hypothesis on `frontier (H t)` is needed or
missing. `frontier (H t)` is disjoint from `interior (H t)`, hence from `O_t`, so it lies in
`H t \ O_t`; and it is connected, being the continuous image of `stdSimplexBoundary 3` (`∂Δ³ ≅ S²`).
One connected set inside `H t \ O_t` contains all of it, so exactly one component meets it — the
outer one. The obstacle uses the face **balls** `fbl s`, and `tgtD s ⊆ fblBd s ⊆ fbl s` (`:645`),
so `Δ_σ ⊆ Int H_t`: digest N's P7 carrier counterexample is blocked too.

## 4. The single missing tool behind all three SUSPECTs

`IsPLCellOn` has no API. The tree lacks:
**(i)** uniqueness of the intrinsic boundary, `IsPLCellOn d S B → IsPLCellOn d S B' → B = B'`;
**(ii)** boundary = frontier in codimension 0, `IsPLCellOn 3 S B → B = frontier S` in a 3-manifold
— `IsPLHomeomorphInto.image_frontier` (`Transition361.lean:216`) is the natural tool but requires
`hK : IsOpen K`, while `IsPLCellOn` only gives `IsPLHomeomorphInto 3 u P` with `P` a *compact* PL
ball and no extension of `u` to an open neighbourhood; **(iii)** dimension distinctness, a set
cannot be both `IsPLCellOn 1` and `IsPLCellOn 2`.

(iii) is what `Section34Terminal.lean:36-38` appeals to when it calls `d_σ ⊆ C_v` "already
excluded". (i)+(ii) are what `section34TargetRecognition` needs to transport
`srcBd (.vertexBall w) = ⋃_{m<l} src m` (`:499`) along `f₁` to `tgtVBd w`, since `NormalPlus`
gives `tgtVBd w` only through the *unrelated* existential `IsPLCellOn 3 (tgtV w) (tgtVBd w)`
(`:616`) together with `tgtV w = f₁ '' src (.vertexBall w)` (`:614`); same for `tgtEBd e`
(`:615, :617`). By contrast `tgtRBd, tgtXBd, tgtIBd, tgtDBd, tgtABd` **are** pinned by explicit
formulas, so recognition at those five labels is combinatorics only.

**Why leaf 4 needs the tetrahedron.** `src (.faceArc a) = src (.vertexBall a.1.2) ∩ src (.faceDisk
a.1.1) ⊆ src (.vertexBall a.1.2)` holds for *every* arc index by `:504-505`, so the leaf forces
`Section34CutLe (.faceArc a) (.vertexBall a.1.2)`. In `Section34CutStep` (`:445-457`) the **only**
route from `faceArc` to `vertexBall` is `faceArc → patch → vertexBall` (`:453, :448`), so a patch
index — hence a `Section34SimplexIndex 𝒦 4` above `a.1.1` — must exist; likewise
`markedPoint p ≤ splitDisk p.1.2` via `edgeArc` (`:456, :451`). The `←` direction of leaf 4 is by
contrast a clean consequence of the frame: all ten `CutStep` cases follow from `:504-530`
(`:524-525` gives case 1, `:529-530` cases 3, 7, 10), and same-dimension inclusions between
distinct labels are killed outright by `:501`.

**Settling them.** P6: prove ingredients 2–4 of §3(b), or make them fields. Leaf 4: add
`∀ s ∈ 𝒦.complex.faces, s.card = 3 → ∃ t ∈ 𝒦.complex.faces, t.card = 4 ∧ s ⊆ t` to `CutFrame`
(free at every intended call site), or derive it from `IsCombinatorialManifold 3`. Leaf 5: (i), (ii).

## 5. (e) feeding the controlled-35.1 endpoint

No mismatch. `ControlledGraphNeighborhoodStatement` quantifies `Ea : Type` (universe 0) with
`[NormedAddCommGroup] [NormedSpace ℝ] [FiniteDimensional ℝ]`; the terminal existential produces
`EuclideanSpace ℝ (Fin N) : Type` with all three. `M₁ M₂ : Type u` and `[MetricSpace M₂]` agree.
`W := U`, `ψ := η` instantiate the `W`-block (`hW := hU`, `hWU := Subset.rfl`), which is exactly
`Section34GraphFrame U U h η H …` as `:611` asks. Side note, not a defect: with `W = U` the clause
`section34CutNeighborhood src ⊆ W` (`:546`) carries no content inside `NormalPlus`. The one real
ordering constraint is that P0 must produce `𝒦` **and** `Section34CarrierControl U 𝒦 h η H` before
P1 can be invoked.

## 6. (f) the inhabitant that would test the most

Not the ℝ³ lattice of digest H: `LocallyFinitePLPieceIn Ea 3 M₁ U` demands
`BijOn map complex.space U` with `U` open, so a *finite* complex needs a **compact** `M₁`. The most
informative single inhabitant is the **5-vertex triangulation `∂Δ⁴` of `S³`**, realised in
`EuclideanSpace ℝ (Fin 4)`, with `M₁ = M₂ = |∂Δ⁴|`, `U = M₁`, `h = f₁ = id`, `η` a large constant,
`𝒦'` the first derived subdivision of the 1-skeleton: finite (local finiteness trivial), `U` open
because `U = M₁`, `IsCombinatorialManifold 3` a five-vertex link computation, all eight label kinds
nonempty, and with `h = id` the carrier/exterior/trace clauses become finite computations in `ℝ⁴`.
Estimate **L (> 3000 lines)** — dominated by an explicit `IsPLCellOn` witness per label family and
by the two `→ False` clauses, which need the §4 tools even here. A control instance `U = ∅` (all
index types empty) is **S (< 500)** and is worth doing first, to confirm no clause is contradictory.

## 7. Eight cheap sanity lemmas worth compiling

1. `IsPLCellOn d S B → B ⊆ S` — used silently everywhere (`tgtD s ⊆ fblBd s`, `tgtEBd e ⊆ tgtE e`,
   `Jd ⊆ Dj`); one line from `IsPLHomeomorphOn.1.mapsTo`.
2. `stdSimplexBoundary 0 = ∅`, `(stdSimplexBoundary (d+1)).Nonempty`; hence
   `IsPLCellOn (d+1) S B → B.Nonempty` and `IsPLCellOn 0 S ∅ ↔ ∃ x, S = {x}` — what blocks the
   empty-trace and empty-arc degenerate witnesses.
3. `Section34CutFrame … → ∀ l m, Section34CutLe m l → src m ⊆ src l` — the `←` half of leaf 4,
   mechanical over the ten `CutStep` cases; also validates every incidence spelling against `:504-530`.
4. `∀ a, Section34CutLe (.faceArc a) (.vertexBall a.1.2) ↔ ∃ t : Section34SimplexIndex 𝒦 4,
   Section34Incident a.1.1.1 t.1` — isolates the tetrahedron obligation.
5. `s ∈ K.faces → t ∈ K.faces → Section34Incident s t → s ⊆ t` (from `inter_subset_convexHull`
   and `indep`) — the fact §3(c) rests on.
6. `IsPLCellOn 3 (H t) (frontier (H t)) → O ⊆ interior (H t) → IsConnected (frontier (H t)) ∧
   frontier (H t) ⊆ H t \ O` — settles 3(d).
7. `(w : Section34VertexIndex 𝒦 𝒦') → ∃ x, w.1 = {x} ∧ simplexBody 𝒦' w.1 = {𝒦'.map x}` —
   confirms every marker clause (`:550-551, :580, :582`) is about a single point, not a body.
8. `IsPLCellOn d S B → IsPLCellOn d S B' → B = B'` (**not** cheap, but decisive): with it,
   `tgtVBd w = f₁ '' srcBd (.vertexBall w)` and leaf 5 reduces to `:499` plus combinatorics. First
   check whether `IsPLHomeomorphInto.image_frontier` (`Transition361.lean:216`) can be re-proved
   for a compact domain — its `IsOpen K` hypothesis is the only obstacle.
