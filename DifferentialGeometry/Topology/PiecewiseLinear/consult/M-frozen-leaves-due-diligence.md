# M — independent due diligence on the frozen leaves (read-only, no compiler)

Audit of the FROZEN leaf statements of `Skeleton/DescentStepOrientable.lean`,
`Skeleton/ClosedBranchCaseOne.lean` and `Skeleton/GeneralPositionInDouble.lean` against the
**actual Lean definitions**, not against the digests. Nothing was compiled, nothing was edited.
Basis `HEAD = a93c4f6155f75b0f93a023eef102b002f1c9801e` (`codex/moise-integration`). **The
checkout moved mid-audit**: `a93c4f615` dropped `trace` and `branchInterior` from
`IsSourceTrackedBranchTube`; all verdicts below are against the post-commit source.

## Verdicts

| leaf | verdict | one-line reason |
|---|---|---|
| `isPLBoundaryTubeProducer_double` | CONFIRMED | with `IsClosed BdM`, `map_boundary` puts `branchCarrier ∩ BdM` inside the two half-space charts, so `BdM` off those charts is closed and misses the compact branch; `W` is forced to be a neighbourhood of the open branch by `D '' (domain \ frontier) ⊆ interior W` |
| `NormalSystem.exists_boundaryNeighborhood_realization` | CONFIRMED | `hρι` pins `ρ` to the canonical `ι`; `BoundaryDouble.lean:41` already proves `IsPLHomeomorphOn (simplicialMap K (glueEmbed₂ B id)) K.space A.space`, so `IsEmbedding ρ` and `B ⊆ range ρ` are routine and `f` is forced by injectivity |
| `exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk` | **SUSPECT** | the binder `W` is vacuous: `hVW` is equivalent to `Disjoint V BdM`; the side constraint `V ⊆ interior (C \ BdM)` recorded in `README`/`FREE_INPUTS` is **not** what Lean says |
| `exists_descendingSurgery_of_adaptedCleanCap` | CONFIRMED | `DescendingSurgery` carries `complexity_lt` and the same `BdM`, `B`; plus the boundary clause `ρ (Sg.cell (e' θ)) = γ θ`. No degenerate witness; `Branch` inhabited ⇒ old complexity ≥ 1 |
| `exists_plCrossSeamReading_of_isCrossRegluedCell` | CONFIRMED | there are exactly two adjacent pairings and `crossQuarterTurn` swaps them (computed below); `R² = -id` only relabels `Pos`/`Neg`, which the reading chooses. Disjunction is exhaustive |
| `nonempty_plSeamTubeChart_comp_crossQuarterTurn` | CONFIRMED | pure transport of `PLPieceIn` along a linear automorphism; one junk trap in `isPiecewiseAffineOn_chart_symm` (see notes) |
| `not_branchPreimage_eq_of_isOrientable` | CONFIRMED | conclusion is `False`, so no vacuity risk of the harmful kind; hypotheses minus `hor` are inhabited (ℝP²×S¹ fixture). Statement is textually identical to the CaseOne endpoint modulo `F`/`E` and the namespace prefix |
| `exists_isSourceTrackedBranchTube` | CONFIRMED | `derivedNeighborhoodFaces ⊆ (secondDerived R).faces` makes `derived` force `N.space ⊆ L.space`, which kills the abstract mapping-torus counterexample; `realisation` still pins the four rays to `ι (D (ρ (a i t, s i t)))`. Weakening is safe but was **not re-reviewed externally** |
| `exists_adaptedHalfSpaceChart_in_double` | CONFIRMED | interior points of either copy are satisfiable (`ℓ > 0` resp. `ℓ < 0` on `ec.source`); the `↔`s are consistent. `ec.source ⊆ U` is unused by the only consumer |
| `SingularTwoCell.exists_cutOutPiece_of_closure_subset` | CONFIRMED | the empty `Rc` witness is available exactly when `D.domain ∩ ⇑D ⁻¹' closure V₀ = ∅`, which is the correct trivial case; the seam clauses are jointly satisfiable (two disjoint compacts) |
| `exists_gluedCell_of_vertexMap_in_adaptedChart` | CONFIRMED | `Rc.space ∪ Rc.spaceᶜ = univ`, so `⇑D'` is fully pinned; only `IsPLOn` is open. `hmaps` is load-bearing against `ec.symm` off `ec.target` |
| `exists_normalizationPreparation_on_prescribedRegion` | CONFIRMED | `T, κ, δ, ε` are in the right order; the `∀ g` certificate is true for arbitrary (even discontinuous) `g` because only distances are used; buffer clauses follow from compactness. One fragility recorded below |
| `exists_guardedVertexMap_in_adaptedChart` | CONFIRMED | case analysis over frozen/free × in/out of `Bv` (below) shows the failure sets are proper; the guard `(s ∩ Bv).card ≤ 3` is both necessary and sufficient |
| `exists_globalInvariants_of_gluedCell` | CONFIRMED | statement sound; but its decisive hypotheses `hcert`/`hstar` are supplied **only** by the unverified A1.5a leaf, so its frozen status is contingent |
| `exists_normalCrossings_of_gluedCell` | **SUSPECT** | it receives `hfiber'` but **no** local-injectivity hypothesis for `D'`, and `hguard` does not imply star injectivity (explicit 5-point configuration below) |

## SUSPECT 1 — `exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk`

`Skeleton/DescentStepOrientable.lean:269-288`, the binder line

```
{V W : Set M} (hV : IsOpen V) (hQV : ⇑D '' Q ⊆ V) (hVW : V ⊆ interior (W \ BdM))
```

`W` occurs **nowhere else** in the statement (checked clause by clause: the conclusion mentions
only `E'`, `Δ`, `Q`, `E`, `D`, `V`). Since `W` is universally quantified and `interior (W \ BdM) ⊆
interior BdMᶜ` for every `W`, while `W := univ` realises the bound, the hypothesis `hVW` is
**equivalent**, for open `V`, to `Disjoint V BdM`. Consequences:

* The leaf is strictly *stronger* than the reviewed statement. The reviewer's OK was given for
  "for every open `V` with `D(Q) ⊆ V ⊆ interior (C \ BdM)`" (`consult/G-…:32-36`), i.e. with the
  cap forced into the good side. Lean asks for the cap for every open `V ⊇ D '' Q` merely
  disjoint from `BdM`, including `V` on the wrong side of the boundary. `README` and
  `FREE_INPUTS.md` A2.2a state the gloss, not the Lean statement.
* I believe the leaf is still **true**: `D '' Q` is compact inside the open `V`, `D '' frontier E'`
  can be kept in a small collar of `D '' T = D '' J ⊆ D '' Q`, and a small enough PL push-off of
  `D|_Q` stays in `V`; the side plays no role in the cap's *existence*, only in the consumer's
  `MapsTo … C`, which `exists_descendingSurgery_of_adaptedCleanCap` gets from its own `hΔside`.
* What would settle it: sanity lemma (1) below. Minimal repair if the intended reading is wanted:
  use `W` in the conclusion, or drop it and write `(hVBd : Disjoint V BdM)`. Either spelling is
  free at the call site `DescentStepOrientable.lean:343-345`, where `V := interior (C \ BdM)`.

## SUSPECT 2 — `exists_normalCrossings_of_gluedCell`

`Skeleton/GeneralPositionInDouble.lean:723-782`. The hypothesis list contains `hfiber'`
(`∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2`) but **no** clause asserting that `D'` is locally
injective, star injective, or an immersion. The active half has to recognise, at every
`y ∈ doublePointSet ⇑D' D'.domain ∩ closure W`, two *embedded* sheets (`HasPLDoubleCrossingAt`
asks for `A ∈ 𝓝[P] a`, `B ∈ 𝓝[P] b`, `Disjoint A B`, `IsPLHomeomorphOn f A (f '' A)`,
`SingularGeneralPosition.lean:1128-1132`); the intended supplier
`hasPLDoubleCrossingAt_and_exists_local_intersection` (`:1135-1148`) asks for
`hinj : ∀ v ∈ K.vertices, InjOn (simplicialMap K φ) (starComplex K v).space`, i.e. star
injectivity — and that does **not** follow from `hguard`.

Counterexample to "`hguard` ⇒ `StarInj`" (checked by hand, exact rationals):
`v = (2/3, 2/3, −1/6)`, `a = (1,0,0)`, `b = (0,1,0)`, `c = (0,0,1)`, `d = (0,0,0)`. Every
4-element subset of `{v,a,b,c,d}` is affinely independent (`{a,b,c,d}` is `e₁,e₂,e₃,0`;
`v ∉ {x+y+z=1}`, value `7/6`; `v ∉ {z=0}`, `{y=0}`, `{x=0}`), yet
`x = (1/2,1/2,0) = 0·v + ½a + ½b = ¾·v + ⅛c + ⅛d` lies in
`convexHull ℝ {v,a,b} ∩ convexHull ℝ {v,c,d}` and `x ≠ v`. In the source, `σ = {v,a,b}` and
`τ = {v,c,d}` can be two 2-faces of the star of an interior vertex `v` of `Rs`, so
`simplicialMap Rs φ` is not injective on `(starComplex Rs v).space` although `hguard` holds for
every `s` with `s.card ≤ 4`.

This is **not** a refutation of the leaf: the apex `φ v` itself is not a double point (any other
face containing it would give four coplanar vertices, excluded by `hguard`), and the double points
on the overlap segment are transverse plane/plane crossings. But the reviewer's OK reasons
(fourth review, `consult/J-…:195`) never checked the local-injectivity input, and the leaf as
frozen gives its prover nothing with which to produce the sheets `A`, `B`.

What would settle it, at **zero cost at the call site**: the assembly already destructures
`hloc'` from `exists_globalInvariants_of_gluedCell` at `GeneralPositionInDouble.lean:906`, three
lines before calling the crossings leaf at `:911`. Adding
`(hloc' : ∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U)` — or `hstar : StarInj T (⇑D')`,
also in scope at `:891` — is free. Until then the leaf is frozen-but-under-supplied, not OK.

## Over-correction check (the three added hypotheses)

**`IsClosed BdM` in `IsPLBoundarySide` (`BoundaryAdaptation.lean:56-63`).** *Justified*: the
reviewer's counterexample `BdM = H ∪ (V \ D '' P)` really is compatible with
`NormalSingularCellData` (its `image_inter_boundary` only sees `D '' D.domain ∩ BdM`) and with the
old `IsPLBoundarySide` (the half-space charts at `D '' frontier D.domain` can be shrunk away from
`V`). *Suppliable*: `isPLBoundarySide_double` proves it at `:132-139` from `frontier C = Bd`.
*No collateral*: `IsPLBoundarySide` occurs only in `BoundaryAdaptation.lean` and the Descent
skeleton. *Minimal*: it is the weaker of the two options offered (the other bakes a derived
conclusion into the interface), and it suffices — `NormalSingularSetTriangulation.map_boundary`
makes `doublePointSet ∩ BdM` the images of the 1-complex's boundary vertices, so a boundary branch
meets `BdM` only at its two ends and `BdM \ (e_p.source ∪ e_q.source)` is closed and disjoint from
the compact branch, hence at positive distance from it.

**`[HasGroupoid M (plGroupoid 3)]` on the 2b cap producer.** *Justified*: the counterexample is
coherent against the actual definitions. `IsPLOn = ChartedSpace.LiftPropOn` (`Manifold.lean:55`)
reads `chartAt` only, so `D.isPLOn` survives a two-chart atlas `{id, g}` that is not
PL-compatible; `NormalSingularCellData.crossing` is existential over `atlas`, so `id` serves; and
although `NormalSingularSetTriangulation.piece : PLPiece 3 M carrier` does quantify over the whole
atlas (`PLPiece.lean:181`), its carrier is the double point set, which the counterexample places
in `{z = 0}` where `g` is the identity. *Suppliable*: `combinatorialChartedSpace_hasGroupoid` at
`DescentStepOrientable.lean:507`. *Minimal-enough*: a local PL-compatibility hypothesis near
`D '' D.domain` would be weaker but does not exist in the tree. *Asymmetry checked, not a defect*:
the consumer `exists_descendingSurgery_of_adaptedCleanCap` does **not** carry the instance and
does not need it — its new cell's double point set is contained in the old one (`Δ` injective on
`E'`, `⇑Δ '' E' ∩ ⇑D '' D.domain = ⇑D '' frontier E'`), so the old `PLPiece` restricts, and
`IsPLOn` of the glued map is local in one and the same `chartAt`.

**`[MetricSpace M] [CompactSpace M]` on the A1 preparation leaf.** *Suppliable*: `CompactSpace` at
`GeneralPositionInDouble.lean:793`; `MetricSpace ((double 3 K).space)` from `Subtype.metricSpace`,
since `(double 3 K).space ⊆ E × E × ℝ`. *Not minimal, harmlessly*: only `dist` is used, so
`[PseudoMetricSpace M]` would do (`UniformInjectivityScale` is already stated over
`[PseudoMetricSpace α]`, `:249`), and compactness is used only for the uniform `ε`, `K ⋐ V` and
`Z ∩ K`, all of which follow from `IsCompact (closure V)`. *Keep in view*: five leaves sit in
`section MetricAmbient` under `[MetricSpace M] [ChartedSpace … M]`, so every consumer must supply a
metric whose topology is **defeq** to the charted space's — invisible in the statements.

## Notes on CONFIRMED leaves (fragilities, not defects)

* **`exists_normalizationPreparation_on_prescribedRegion`, junk `ec.symm`.** Clauses three and
  four (`:578-581`) apply `ec.symm z` with no `z ∈ ec.target` guard; they are junk-safe **only**
  because clause two (`:576-577`) shares the same `ε` and forces `z ∈ ⇑ec '' V ⊆ ec.target`. Split
  `ε` into a conversion and an active/boundary scale with the latter larger and both clauses
  become false by junk values. `exists_normalCrossings_of_gluedCell` receives `hactive` with no
  `hchartbuf` companion (`:762-763`) — supplied verbatim, so fine today, but not self-contained.
* **`exists_plCrossSeamReading_…`, the pairing count.** `bentArcPos = crossRayPosX ∪ crossRayNegY`,
  `bentArcNeg = crossRayNegX ∪ crossRayPosY` (`LoopTheorem/CrossSeamResolution.lean:125,129`), and
  `crossQuarterTurn (x,y,t) = ((-y,x),t)` sends `X⁺↦Y⁺`, `Y⁻↦X⁺`, `X⁻↦Y⁻`, `Y⁺↦X⁻`. Hence
  `R '' bentArcPos = X⁺ ∪ Y⁺` and `R '' bentArcNeg = X⁻ ∪ Y⁻`: the *other* adjacent pairing.
  There are only two adjacent pairings, so the disjunction is exhaustive. Residual obligation (not
  a defect): the `boundary_iff_end` field needs properness of `G` over `BdM`, which
  `IsCrossRegluedCell` gives only at image level (`G '' frontier G.domain = D '' frontier D.domain`);
  it has to be re-derived from the explicit `f₃`, `h`, `U₃` data.
* **`nonempty_plSeamTubeChart_comp_crossQuarterTurn`, junk `invFunOn`.**
  `PLPieceIn.isPiecewiseAffineOn_chart_symm` mentions `Function.invFunOn map complex.space`, a
  choice function. `invFunOn (chart ∘ R) (R⁻¹ '' S)` is not definitionally `R⁻¹ ∘ invFunOn chart S`;
  they agree on the image, which is the set the field quantifies over, so a `Set.EqOn` congruence
  is needed. Cheap but easy to miss.
* **`exists_guardedVertexMap_…`, why the guard is exactly right.** `hℓ : ℓ ≠ 0` ⇒
  `finrank (ker ℓ) = 2`, so the guard reads `(s ∩ Bv).card ≤ 3`; four `Bv`-vertices lie in the
  2-plane `ker ℓ` and are never independent, so it is necessary. It is sufficient because
  `hproper`, `hmapC`, `hCchart`, `hBdchart`, `hLspace`, `hBvL` give `ℓ (ec (D v)) = 0 ↔ v ∈ Bv` on
  `R.vertices`, so a frozen vertex outside `Bv` has `ℓ > 0`, the affine span of the frozen part
  can never equal `ker ℓ`, and the free vertex has to miss a proper affine subset of its own open
  ball (ℝ³, or `ker ℓ` for `Lc` vertices).
* **`exists_isSourceTrackedBranchTube`, process.** The frozen statement in source is no longer the
  one the reviewer saw; `trace` and `branchInterior` were dropped by `a93c4f615`. The drop is
  sound (neither field is consumed by the assembly, the conclusion only weakens, and the two
  counterexamples stay excluded by `derived` and `realisation`), but per `Skeleton/README.md`
  rule 8 an OK freezes *that* statement; the weakened form carries it only by the monotonicity
  argument recorded here.

## Ledger defects found

* `FREE_INPUTS.md` A2.5: "exactly **10** `sorry` leaves". The file has **7**
  (`DescentStepOrientable.lean:232,241,262,288,315,361,367`). A1.9's count of 8 is correct
  (`GeneralPositionInDouble.lean:247,366,387,582,647,674,720,782`).
* `FREE_INPUTS.md` A2.2a and the `DescentStepOrientable.lean` docstring both describe the cap
  producer's hypothesis as `V ⊆ interior (C \ BdM)`; see SUSPECT 1.
* Naming: the Descent leaf is `not_branchPreimage_eq_of_isOrientable`, the CaseOne endpoint is
  `NormalSingularCellData.not_branchPreimage_eq_of_isOrientable`. The statements diff clean (only
  `{F}` vs the section's `{E}`, plus `open Classical in`), but the call site at
  `DescentStepOrientable.lean:519` will need the qualified name when the leaf is replaced; that
  name is also not dot-notation usable, since its first explicit argument is `L`, not `hD`.

## Eight cheap Lean sanity lemmas worth compiling

1. `example {M} [TopologicalSpace M] (BdM V : Set M) (hV : IsOpen V) :
   (∃ W : Set M, V ⊆ interior (W \ BdM)) ↔ Disjoint V BdM` — settles SUSPECT 1.
2. The 5-point configuration: all five 4-subsets of
   `{(2/3,2/3,-1/6), (1,0,0), (0,1,0), (0,0,1), (0,0,0)}` affinely independent, together with
   `(1/2,1/2,0) ∈ convexHull ℝ {v,a,b} ∩ convexHull ℝ {v,c,d}` — settles SUSPECT 2
   (`hguard` ⇏ `StarInj`).
3. `example : crossQuarterTurn '' bentSheetPos = (crossRayPosX ∪ crossRayPosY) ×ˢ Icc (0:ℝ) 1`
   and the `Neg` twin — confirms the quarter turn swaps the two adjacent pairings, so the reading
   disjunction is exhaustive.
4. `example (R Lc : Geometry.SimplicialComplex ℝ E) : (derivedNeighborhood R Lc).space ⊆ R.space`
   — the clause that kills the abstract mapping-torus counterexample; currently only reachable
   through `derivedNeighborhoodFaces_subset`.
5. `example {α β} (f : α → β) (S : Set α) (σ : α ≃ α) :
   EqOn (Function.invFunOn (f ∘ σ.symm) (σ '' S)) (σ ∘ Function.invFunOn f S) (f '' S)` — the
   junk-free half of the quarter-turned `PLPieceIn`.
6. `example (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
   T.branchCarrier c ∩ BdM ⊆ T.piece.piece.map '' (boundaryComplex 1 T.complex).space` — the
   "a boundary branch meets `BdM` only at its ends" step that `IsClosed BdM` relies on.
7. `example {ι} [IsEmpty ι] (f : ι → EuclideanSpace ℝ (Fin 3)) : AffineIndependent ℝ f`
   with `(s.filter (· ∈ Ac.space)) = ∅` for a frozen-free `s` — confirms the guard's antecedent is
   automatic on unfrozen 4-subsets (the branch the fifth review warned about).
8. `(inferInstance : TopologicalSpace (double 3 K).space) =
   (inferInstance : MetricSpace (double 3 K).space).toUniformSpace.toTopologicalSpace := rfl`
   — the invisible defeq that the five `section MetricAmbient` leaves depend on.
