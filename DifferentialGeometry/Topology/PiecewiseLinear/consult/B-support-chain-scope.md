# B — scope of B1.c / B1.d: the §31–§35.1 support chain (read-only, 2026-09-21)

Ledger items **B1.c** (`Moise351` in controlled form) and **B1.d** (`Moise341`, `Moise331`, §31, §32, §33.1, 22.8–22.10). Book =
Moise GTM 47, `D:\…\moise_gtm47.pdf`; **book page + 10 = PDF page** (verified: PDF 233 = printed 223). Pages read here: 217–222
(30.7/30.8, §31 in full), 223–229 (§32), 230–238 (§33), 159–164 (22.4–22.12); all book content below is paraphrase. Not
repeated: `SECTION32_RESEARCH_20260919.md`, `consult/A-section34-lemma-list.md` §§0–5, `consult/A2-answer-digest.md`,
`HANDOFF_CODEX_H.md` H-M2.

## 0. Two corrections to `FREE_INPUTS.md` that change B1.d's shape

1. **`Moise306` and `Moise307` are on the goal path**, not "deliberately not". Printed p. 221: *Theorem 31.1 follows by
   repeated applications of Theorem 30.7*; *Theorem 31.2 by repeated applications of Theorem 30.8*. §32's proof of 32.1 builds
   its doubly infinite family "as in the definition of a canonical configuration", i.e. through 31.1/31.2; and 30.7 invokes
   30.6. The earlier ruling came from a citation census of §§33–35 only — right for §§33–35, wrong one level down.
2. **`Moise264` (loop theorem, interior two-sided surface) is on the goal path too**, also listed as never needed. Printed p.
   217, proof of 30.7: from `π(T) ≅ ℤ+ℤ → π(Int S₂) ≅ ℤ` having non-trivial kernel one gets a *polyhedral compressing 2-cell* `Δ
   ⊆ Int S₂` with `Bd Δ = Δ ∩ T` not contractible in `T`. A tame 30.7 (bicollared outer frontier, as in
   `moise305_tame_of_moise304`) removes the wildness but **not** this step: 30.7 concludes the inner piece is a *combinatorial*
   solid torus, and that recognition is the compressing disk. The tree's `Moise264` (`MoiseChain.lean:57`) is not in that shape
   (finite complex, `L.space ⊆ K.space \ ∂K.space`, no confinement clause), so a confined orientable variant is needed —
   plausibly from `Moise252` by cutting along `T`.

## 1. Statement audit

**F** = faithful to print; **D** = faithful but deviates as noted; **W** = wrong theorem for its intended consumer.

| Prop | site | | detail |
|---|---|---|---|
| `Moise331` | `MoiseChain.lean:136` | **F** | p. 230 verbatim: finite, connected, 1-dimensional, no end-points as `neighborSet.ncard ≠ 1`, open `U ⊇ K`, `IsEmbedding (U.domRestrict h)`, constant `ε`, Euclidean target. "Regular neighbourhood" is spelled `derivedNeighborhood T L'` for a subdivision `L'` — more specific, but the standard construction and what §34 Lemma 1 needs anyway. `IsPLHomeomorphOn f N (f '' N)` = "PLH `f : N ↔ X`"; `f '' N ∈ nhdsSet (h '' L.space)` = clause (1); `dist < ε` = clause (2) |
| `Moise341` | `MoiseChain.lean:99` | **F** | p. 239 verbatim: `IsPLBall 3 C`, `ContinuousOn h C ∧ InjOn h C` (an embedding, `C` compact), constant `ε`, target `ℝ³`. Confirmed earlier by consultant A |
| `Moise351` | `MoiseChain.lean:191` | **D** | p. 248, three deviations. (i) `ContinuousOn φ U` replaces "strongly positive": a *stronger* hypothesis, so a weaker theorem; recoverable, a strongly positive function has a continuous positive minorant. (ii) `IsClosed ((↑ : U → M₁) ⁻¹' K)` is **added** — the book's own reduction step 1, so the tree states the post-reduction form and reduction (R2) becomes a separate obligation, ABSENT in the tree. (iii) the conclusion exposes only `IsLocallyFiniteRegularNeighborhoodOf N K U` and `f`, and that predicate carries **no** dual cells, splitting disks or triangulation — see §2 |
| `Moise305Tame` | `TameNestedCells.lean:27` | **F** | 30.5 + `IsBicollared (frontier C₂)`; `moise305_tame_of_moise304` proved, conditional on `Moise304` |
| `Moise306` | `MoiseChain.lean:118` | **F** | p. 217 Thm 6; no producer and no inhabitant theorem ⇒ UNTESTED in the ledger's sense |
| `Moise307` | `MoiseChain.lean:128` | **W** | the book concludes "`S` is a **combinatorial solid torus**"; the tree concludes `HasCylindricalDiagram S`. §31.1 and `Moise308Nested` both need `IsCombinatorialSolidTorus` (`CombinatorialSolidTorus.lean:19`), which exists and is unused here. Restate before §31 can consume it |
| `Moise308` | `MoiseChain.lean:257` | **W** | the spine-of-its-own-torus triviality preceding 30.8, already diagnosed. **Superseded**: `Moise308Nested` (`Moise308Nested.lean:310`) is **PROVED** unconditionally (`moise308Nested`, `:389`). That is the form §31.2 consumes |

**Vacuity discipline.** Non-degenerate inhabitant of each hypothesis set: `Moise331` — the tetrahedron 1-skeleton, trivalent, no
end-points (`Moise331.applies_to_tetrahedron_oneSkeleton`, `MoiseChain.lean:163`, already in the tree); `Moise341` — `C =
stdSimplex ℝ (Fin 4)` (`isPLBall_stdSimplex`), `h = id`, any `ε`, with the non-PL test `h (x,y,z) = (x³,y,z)`; `Moise351` — `M₁
= M₂ = U = ℝ³`, `K` a line as a locally finite polyhedral graph, the same non-PL `h`, `φ ≡ 1` (`consult/D-answer-digest.md` Part
3). No unsatisfiable hypothesis; no ambient `frontier` of a lower-dimensional ball; no PL hypothesis smuggled onto `h`; `K = ∅`
in `Moise351` is degenerate but harmless. **One item to check when `Moise351` is next touched**: local finiteness in
`IsLocallyFinitePolyhedralGraph (n := 3) K` is carried by `K`'s own `LocallyFinitePieceTower`, i.e. relative to `K`, while the
consumer needs it relative to `U`; with `K` closed in `U` these agree, but that is recorded nowhere.

**Consumers (grep).** `Moise331`: none except its own non-vacuity witness. `Moise341`: exactly one,
`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart` (`ChartLocalApproximation.lean:42`, **proved**) — precisely what
§35.1 step 7 (p. 249) needs. `Moise351`: only `SkeletonReduction.lean:237, 249`, both feeding `Moise352SkeletonExtension`, which
the tree's own audit records as `Moise352` plus two inserted hypotheses, i.e. pure weakening. **The live B1 route (`Moise352Open
⇐ Section34CellDiagram`) consumes `Moise351` nowhere**; B1.c is an obligation with no Lean consumer, which is why the controlled
form is still unwritten.

## 2. The controlled 35.1 that P1 needs

Plain `Moise351` cannot serve. P1 must choose `N` **and** `f₁` together and read the §34 Lemma 1 incidence clauses off them; an
arbitrary output of 35.1 cannot be frozen and declared to have them (`consult/A2-answer-digest.md`, P1 row). Worse,
`IsLocallyFiniteRegularNeighborhoodOf` (`PolyhedralGraph.lean:271`) exposes only an exhaustion, a neighbourhood clause and
manifold-ness: the dual balls `C_v`, splitting disks `D_e`, face disks `d_σ`, residual balls `Q_t` and patches `X_{tv}` of
(SC1–SC3) are **not recoverable from it**, so the controlled form must output the cut diagram, not just `N`. With `|𝒦¹|` the
1-skeleton's underlying set and `T_σ := ⋃_{v ∈ σ} f₁ '' C v`:

```lean
∀ {M₁ M₂} [the ten instances of `Moise351`] {U : Set M₁}, IsOpen U →
  ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
  ∀ (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U),  -- P0: triangulation, first
    IsCombinatorialManifold 3 𝒦.complex →
  ∀ (H : 𝒦.complex.faces → Set M₂), h '' S_α ⊆ interior (H α) →      -- P0: carriers, first
    (H α) locally finite in the subspace h '' U →                    --   (never in M₂)
  ∀ {W : Set M₁}, IsOpen W → |𝒦¹| ⊆ W → W ⊆ U →                      -- prescribed nbhd, after 𝒦
  ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →              -- free tolerance, after 𝒦
  ∃ 𝒦' N (C : vertices 𝒦' → Set M₁) (D : edges 𝒦' → Set M₁) (d : faces 𝒦' → Set M₁)
    (Q : tets 𝒦' → Set M₁) (X : tets 𝒦' × vertices 𝒦' → Set M₁) (f₁ : M₁ → M₂),
    IsSubdivision 𝒦' 𝒦 ∧ IsLocallyFiniteRegularNeighborhoodOf (n := 3) N |𝒦¹| U ∧ N ⊆ W ∧
    (SC1–SC3 : the source cut diagram's equations, all families locally finite) ∧
    IsPLHomeomorphInto 3 f₁ N ∧ f₁ '' N ∈ nhdsSet (h '' |𝒦¹|) ∧ (∀ x ∈ N, dist (f₁ x) (h x) < ψ x) ∧
    (∀ v, h v ∈ interior (f₁ '' C v)) ∧                              -- (G) = §34 L1(2)–(4) and L2
    (∀ e σ, (f₁ '' D e ∩ h '' σ).Nonempty → e ≤ σ) ∧ (∀ v σ, (f₁ '' C v ∩ h '' σ).Nonempty → v ≤ σ) ∧
    (∀ σ, h '' (∂σ) ⊆ interior (T_σ)) ∧ (∀ σ, π₁(h '' ∂σ) → π₁(T_σ) is surjective) ∧
    (∀ v, h '' C v ∪ f₁ '' C v ⊆ H v)                                -- carries the final estimate
```

Quantifier order is the content: `𝒦` and the carriers first; then `W` and `ψ` arbitrary (the "free tolerance" 35.2's input
needs); then `N`, the diagram and `f₁` in **one** existential. §34 Lemma 2's internal re-choice order (`f₁` first, inner torus
second) stays inside the producer. Plain `Moise351` is this with the diagram and the last six conjuncts dropped, so the
controlled form is strictly stronger and weakens nothing.

## 3. Dependency map with sizes (class of **what is missing**: S < 500 lines, M 500–3000, L > 3000)

| Book item | needed for | in the tree | missing | class |
|---|---|---|---|---|
| 26.4/`Moise264`, confined two-sided | 30.6, 30.7, §33 L9 | stated only; `Moise252` producers live (lane A) | orientable + confined variant; reduction from `Moise252` by cutting along a two-sided surface | M |
| 30.6 `Moise306` | 30.7 | 8 `ToroidalShell*` modules, `exists_connected_separating_surface_bettiOne_eq_two`, `exists_embedded_torus_compression*`, `TorusShell.lean` | the assembly; the lane-304 tail was written for exactly this and never wired | M |
| 30.7, restated to CST | 31.1 | `IsCombinatorialSolidTorus:19`, `isCombinatorialSolidTorus_derivedNeighborhood_*`, `TorusCompression.lean` | restatement (S) + the compressing-disk case split, 28.1-style | M |
| 30.8 nested | 31.2 | **`moise308Nested` PROVED** (`:389`) | only the *producer of its hypotheses* in §31's configuration (inner torus, shell, `IsSpine S₁ J`) | M |
| 28.9 | 31.4 | absent by name; `SurfaceEssentialDisk`, `SurfaceSplit*` adjacent | statement + proof | M |
| **§31** canonical configurations | §32 | nothing by that name | the *definition* (rotate a planar chain of 2-cells: circles `J_j`, annuli `A_j`, solid tori `S_j`, three-term overlap, `T''_j` pairwise in general position) + 31.1–31.4; 31.3 and 31.4 have real content (31.4 = the generator/bounding-disk dichotomy from 30.8, 28.9, commutativity of π₁ of a solid torus, a kernel argument) | M |
| **§32** pseudo-cells 32.1–32.4 | §33 | **nothing**: `PseudoCell` has zero Lean occurrences. `IsPolyhedron` is a finite union of H-polytopes hence **compact** (`Polyhedra.lean:13,23`); the non-compact layer that does exist is `IsLocallyPolyhedral` (`LocallyPolyhedral.lean:12`), `LocallyFinitePLPieceIn`, `LocallyFinitePieceTower` | the pseudo-cell representation (`body`/`rim`/`center`, with `Bd E`/`Int E` as *cell* notions, never ambient `frontier`/`interior`); "tube" (homeomorphic image of a regular neighbourhood of a graph, carrying its splitting disks and dual cells); the doubly infinite annulus family; 32.1, 32.2, 32.3, 32.4 | **L** |
| **§33.1** | 34.1 | L1–L13 all absent. Reusable: `DualCells.lean` (712), `derivedNeighborhood*`, `GeneralPosition.lean:2540` (two PL surfaces in a 3-dim normed space, relative and supported variants), `Connected/Separation.lean`, `SurfaceSphereRecognition.lean:467`, `ConeEuler.lean`, `AnnulusCapping.lean` | L1–L13 plus two asserted producers: the product structure `Bd N × (0,1) ≅ Int N' − K'` of a tube (L10) and the "sphere with holes and possible handles" step (L12; see §4) | **L** |
| **34.1** | 35.1 step 7 | `Moise341` stated; chart-local consumer **proved** | the §34 construction, compact/Euclidean instance | **L** |
| **controlled 35.1** | P1 of B1.b | `Moise351` stated; `ChartLocalApproximation` proved; 6 `DualCellPiercing*` modules cover the piercing alteration's combinatorics; `Annulus*` | pp. 248–251 steps 3–14: the `E_v` target cells, the piercing alteration, the `A_e`/`B_e` package, **27.3**, L1–L3 with the minimality argument, the global tolerance selection, the 3-stage endgame | **L** |
| 27.3 | §35.1 L1 | absent; `Annulus*.lean` is infrastructure only | statement + proof | M |
| 5.4, 18.2 (extension over disks, over 3-cells) | §33 L13, final step | `BoundaryDiskExtension.lean:11,39`, `BallFrontier.lean:102`, `BallGluing.lean:51`, `PLSchoenflies.lean` | small bridges only | S |
| 30.1–30.3 (splitting, separation) | §32, §33 | `Connected/Separation.lean`, `SurfaceSplit*`, `SurfaceCappingSeparation` | the splitting operation as §32 uses it: split a 2-manifold apart at a 2-cell, keeping a named surface fixed | M |

**Definitional gaps**, in the order they bite: *pseudo-cell* (no Lean word); *tube* (the tree's two `Tube` names are the
loop-theorem lane's seam tubes, unrelated); *handle decomposition of a tube* (= 32.3's output `N' = ⋃ C''_i`, `C''_i ∩ C''_j =
E_e`; `HandleCount.lean` is surface handle counting and `IsPLThreeHandleAttachment` a different object); *canonical
configuration*; *source cut diagram* (SC1–SC3 — an untracked `SourceCutDiagram.lean` appeared during this scoping, 158 lines,
names and containments only, no incidence equations yet; check it before restating (SC1–SC3)).

## 4. Surface classification: what §33 actually uses, and the recommendation

**Printed use.** §22's numbered theorems are all about *boundaryless* compact connected 2-manifolds (22.4 normal form, 22.5–22.7
the `χ`/`p¹` dictionary, 22.8 by `(h,m)`, **22.9 by orientability + `χ`**, 22.10 by orientability + `p¹`, 22.11 simply connected
⇒ `S²`). §33 cites **22.9 exactly once**, in Lemma 11 (p. 236: Lemma 10 gives `π(Bd X) ≅ π(Bd N)`, hence equal `p¹`; both
orientable by 26.8; apply 22.9); nothing else in §§31–35 cites 22.8–22.10. Lemma 12 then needs a *bounded* structure statement
(each `A'_v` is a sphere with holes and possible handles) which is **not** 22.4 as printed, and which Moise calls evident.

**Both can be skipped, and the replacement is already in the tree.** Lemma 11's homeomorphism is consumed nowhere: Lemma 12 uses
only `p¹(Bd X) = p¹(Bd N)`, which Lemma 10 gives directly, and Lemma 13 rebuilds a *stronger* PLH with `f(A_v) = A'_v` from
scratch via 5.4 (H-M2's finding; checks out against p. 236). Lemma 12 without normal forms: cap each of the `r_v` polygonal
boundary circles of `A'_v` with a PL disk to get a closed orientable `Â'_v`; capping Euler additivity (`ConeEuler.lean`,
`eulerChar_eq_add_one_of_faces_union_coneComplex`) plus H.4a gives `χ(A'_v) = 2 − r_v − b₁(Â'_v)`; gluing along the shared
circles gives `b₁(Bd X) = b₁(Bd N) + ∑_v b₁(Â'_v)`; Lemma 10 forces every term to vanish; then
**`isPLSphere_two_of_faceEulerChar_eq_two`** (`SurfaceSphereRecognition.lean:467`, **proved unconditional**) makes each `Â'_v` a
PL 2-sphere, and deleting the caps leaves a PL disk with holes — exactly the PL statement Lemma 13 consumes. Remaining: the
capping-complex geometry and cap-deletion recognition, plus a one-dimensional Hurewicz/abelianisation bridge avoiding the
sorried `Topology/Homology/HurewiczLowDegrees.lean`. Class **M** (H-M2's own 3–5k is at the top of M).

**Vendoring `D:\differential-geometry-moise-s\.lake\scratch\ext\classification-of-surfaces`: no.** Its top-level theorem
(`ClassificationOfSurfaces/EvalStatement.lean:23`) says a compact connected T2 space with `ChartedSpace (EuclideanHalfSpace 2)`
and `IsManifold (modelWithCornersEuclideanHalfSpace 2) 0` is homeomorphic to a sphere representative, to `Quot (OrientableRel p
n)`, or to `Quot (NonOrientableRel p n)` (`p` = genus, `n` = boundary circles; models vendored from Lean Eval,
`LeanEval/ChallengeDeps.lean:53,67`). 142 444 lines, 132 files, zero `sorry`, Lean 4.32, pinned Mathlib. It does not discharge
§33: (i) **no invariants** — `grep euler|genus|betti` hits only `Examples.lean` and the vendored file, so getting the invariant
form 22.9/22.10 out of the trichotomy means computing `χ`/`p¹` and orientability of the quotient models, new work in a foreign
representation; (ii) **wrong category for the consumer** — Lemma 13 needs a *PL* disk-with-holes with polygonal boundary to feed
5.4, which a homeomorphism onto a quotient model does not give without a 2-dimensional Hauptvermutung bridge; (iii) **input-side
bridge** — our surfaces are combinatorial 2-manifolds with boundary in a complex in `ℝ³`, so `ChartedSpace (EuclideanHalfSpace
2)` and `IsManifold` instances (star = cone over link) are themselves a module; (iv) toolchain/Mathlib pin plus 142k unaudited
vendored lines against this checkout's `AGENTS.md` regime. **Cheaper native special case: the capping route above.**

## 5. Goal-driven cuts (orientable, existence only; non-compact source + continuous tolerance kept)

* **Cross-caps disappear, and with them 22.8–22.10** — the largest cut available in B1.d. Every surface in §§31–33 lies in
   `ℝ³`/`S³` (or one chart of `M₂`), hence is orientable by 26.8: `Bd X`, `Bd N`, the `A'_v`, the tori `T''_j`. The `m = 1, 2`
   halves of 22.5–22.10, §22's Möbius analysis and `MobiusBand*.lean` are never needed; the one residual use of
   non-orientability is §33 Lemma 13's cyclic-order step ("otherwise `Bd X` would contain a Möbius band"), an exclusion, not a
   classification. Uniqueness, Hauptvermutung and isotopy never enter either: §§31–33 are existence statements throughout.
* **`Moise305Tame` helps only where it already does**, §34 Lemma 3. It does not shorten §31/§32: a tame 30.7 still needs the
   compressing disk (§0.2), and §32's own use of 30.5 is not on the §34 Lemma 3 pattern, so the tame criterion ("outer image
   cell = image of a bicollared source cell under an embedding defined near the collar") must be re-checked there. **No cut in
   §32 at all** from orientability or existence-only: the pseudo-cells live in `ℝ³` and the difficulty is the doubly infinite
   limit and the failure of local connectedness at the rim, neither an orientability nor a uniqueness question.
* **Shalen as a *local* replacement of §32–§33: no.** Per `consult/F-shalen-paper-digest.md` §A the functional equivalent of
   33.1 is 5.1 + 6.2 (PL approximation on `T ∪ 𝒟`, then fill the chambers), reached through §2 and §4. Its inputs are Dehn's
   lemma in the normal-subgroup form (absent, strictly more than the loop-theorem lane produces), **Nielsen's theorem** for `χ ≤
   0` closed surfaces (absent, chapter-scale, digest F calls it "the gate"), Epstein's two curve lemmas,
   asphericity/cyclic-cover API, a filling scale `ρ_M(ε)` ill-posed as printed, and handlebodies (zero hits) — one unformalised
   chapter traded for four. Keep Moise; the only piece worth importing locally is 6.2 (extension over 3-cells given `X − ∂E`
   connected), whose shape §34 stage 7 has.

## 6. Proposed skeleton files (`Skeleton/README.md` 3: worth writing only where the assembly is a real proof)

| file | endpoint | leaves | real assembly? |
|---|---|---|---|
| `Skeleton/ControlledGraphNeighborhood.lean` | the §2 statement | (a) `E_v`: a PL 3-cell in `M₂` containing `h '' C_v` inside a prescribed metric ball; (b) the piercing alteration `C_w ↦ C'_w` piercing `Int D_e` in a circle; (c) the `S_e, T_e, A_e, B_e` annulus package; (d) 27.3; (e) `Moise341` via the **proved** chart-local form; (f) the disk-swap/minimality step giving L2–L3; (g) global tolerance selection over a locally finite family; (h) the 3-stage endgame | **Yes.** pp. 249–251 steps 6–14 chain: conditions (2)–(8) → L1 → minimality → L2 → L3 → the `D_v` family → 3-stage extension → the `φ`-estimate from (2). Highest value: the only file that fixes B1.c's exact shape, and (e) already exists |
| `Skeleton/Section33Approximation.lean` | `Moise331` | 32.1–32.3 as one pseudo-cell-decomposition proposition; 32.4; confined `Moise264`; 30.2; 26.6; the tube product structure `Bd N × (0,1) ≅ Int N' − K'` (L10, asserted in the book); 5.4; 18.2; §4's capping bricks | **Yes.** L1–L13 are thirteen real deductions with two genuine inductions (the `p¹(Bd X)`-decreasing splitting of L7, the LTD-count induction of L9). Writing it *before* §32 exists is the cheapest way to test whether the 32.1–32.3 interface is strong enough — nobody has |
| `Skeleton/CanonicalConfiguration.lean` | 31.4 (and 31.1–31.3) | restated 30.7 (CST conclusion); 28.9; general position for a pair of polyhedral tori (`GeneralPosition.lean:2540` may already serve). `moise308Nested` is **proved**, not a leaf | **Yes, small.** 31.3 and 31.4 are real arguments. Needs the canonical-configuration definition first (S) |
| `Skeleton/PseudoCellCapping.lean` | 32.4 | a pseudo-cell representation; finite general position of `Bd C³` against the *regular part*; innermost splitting | **Yes**, and independent of 32.1 (`SECTION32_RESEARCH_20260919.md` §6). Good first contact with the pseudo-cell interface |
| *no skeleton for 32.1–32.3* | — | — | **No.** "32.1 ∧ 32.2 ∧ 32.3 → the decomposition" is modus ponens. §32 stays a named proposition (or the four numbered ones) until the pseudo-cell representation and the doubly infinite annulus family exist; the useful decomposition is that research note's Q.1, Q.2a, Q.2b, Q.2c |
| *no skeleton for §22* | — | — | **No.** §4's route is two ordinary producers on top of proved endpoints |

## 7. Estimate, most uncertain item, order

**Total size class: L**, larger than any other open block on the goal path: §32 alone is L with no floor established, §33 is L,
and the §34 construction is L and appears **twice** — compact Euclidean for 34.1, locally finite for B1.b — unless written once,
parametrised, with 34.1 as the compact instance. That is the biggest saving available and should be a design constraint on B1.b
from the start.

**Most uncertain item: 32.1** — the doubly infinite family with two-end control, the finite local surgeries, the three-type
classification and deletion, the limit separation, and the exact closure `closure U = U ∪ J`. It has no formal floor:
`SECTION32_RESEARCH_20260919.md` withdrew the earlier 18–27k figure as unverifiable and I do not restore it. Second: §33 Lemma
10's product structure of a tube, asserted in one clause, the only place where the non-PL nature of `h` must become a global
statement about `N' − K'`.

**Order** — each step chosen so something downstream stops being blocked.
1. `Skeleton/ControlledGraphNeighborhood.lean` (§2 statement + leaves). **Unblocks the §34 skeleton first**: P1 is B1.b's
   only node with an unwritten input, its chart-local 34.1 leaf is already proved, and nothing upstream is needed to write it.
2. Cheap blocking interface repairs: restate `Moise307` to conclude `IsCombinatorialSolidTorus` (S); state the confined
   orientable `Moise264` and its reduction from `Moise252` (M); move `Moise306`, `Moise307`, `Moise264` out of
   `FREE_INPUTS.md`'s "deliberately not on the goal path" list into B1.d, with the p. 217/221 evidence.
3. `Skeleton/Section33Approximation.lean` — fixes the pseudo-cell interface from the consumer side before anyone builds
   pseudo-cells; the cheapest de-risking of the L item.
4. §4's two surface bricks (capping complex + cap deletion; the Hurewicz bridge): independent, M, and they close §33's only
   classification dependency.
5. §31: definition, then `Skeleton/CanonicalConfiguration.lean`, then 31.1/31.2 once 30.6/30.7 land.
6. §32: Q.1 (representation) and `Skeleton/PseudoCellCapping.lean` (32.4) in parallel, then Q.2a (limit separation), Q.2b
   (the open disk), Q.2c (32.1 proper), then 32.2/32.3.
7. The §34 construction, once and parametrised; 34.1 falls out as the compact instance and closes B1.d.
