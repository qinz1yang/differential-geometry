# Digest — third external review of the two §34 skeletons (snapshot `0e4abe7ee54f`)

Marks: **[V]** checked by the lead against the source; **[–]** not independently verified.
The reviewer concedes that its previous P6 argument skipped the derivation of the cyclic seam
structure; but the worker's "foreign face arc" **is excluded by the present full input** — no new
hypothesis. Two docstring corrections: the exact intersections already exclude `d_σ ⊆ C_v`; and
"the intersection circles lie in the interiors of both annuli" does **not** express that the
annuli cross.

## `Skeleton/Section34Terminal.lean` — all five leaves OK [–]
| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34NormalFamily` | OK | realisation ambient existential, carriers closed PL balls; still the explicitly labelled P0–P5 composite |
| `exists_section34FaceDisks` | OK | foreign arcs excluded by the neighbourhood clause and dimension; no extra clause |
| `exists_section34ResidualBalls` | OK | closed ball carriers repair the exterior; the three boundary decompositions fit the mixed flags |
| `section34SourceFace_iff_cutLe` | OK | the new `d_σ ⊆ Q_t` with exact intersections and the circle / sphere boundary coverings determines the source face order |
| `section34TargetRecognition` | OK | receives the source face-order bridge; target cell-ness correctly moved out of the conclusion |

**Why foreign arcs are excluded** (to be proved as a *derived lemma*, not assumed):
`Γ = graphSkeletonSpace 𝒦`, `N = ⋃ C_v`, `d_σ = src (.faceDisk σ)`. The cut frame makes each
`d_σ ∩ C_v` a designated 1-cell or empty; local finiteness + compactness of `d_σ` leave finitely many
`C_v`, so `d_σ ∩ N` is a finite union of closed arcs, without relative interior in the 2-disk
`d_σ`; `d_σ ∩ Int N` is relatively open, hence empty; the graph frame gives `Γ ⊆ Int N`, so
`d_σ ∩ Γ = ∅`; different old triangles meet inside `Γ` and `d_σ ⊆ |σ|`, so `σ ≠ τ → d_σ ∩ d_τ = ∅`,
and a foreign arc `a_{vτ} ⊆ d_τ` cannot lie in `d_σ`. Owed lemma:
`section34_faceArc_subset_faceDisk_iff (hcut : Section34CutFrame …) (hnbhd : section34CutNeighborhood src ∈ nhdsSet (graphSkeletonSpace 𝒦)) : ∀ a s, src (.faceArc a) ⊆ src (.faceDisk s) ↔ a.1.1 = s`.
With the subdivision clauses there are at least three seams; the ball-intersection and
splitting-disk end point clauses of `NormalPlus` give the cyclic annuli; a circle meeting every seam
once cannot be tangent everywhere; the innermost trace disk is exterior. Lemma 5(7) is still not
what P6 uses.

## `Skeleton/ControlledGraphNeighborhood.lean`
| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34CutFrame` | OK | subdivision, `W`, `ψ` control and `hQsep` have the right shape |
| `exists_section34VertexPreparation` | FIX | `C''_v`, `ε_v` precede the maps but also precede the piercing geometry they must control; the target chart is missing |
| `Moise341.exists_section34VertexApproximation` | FIX | conclusion right; `hprep` does not supply the single target PL chart the proved chart-local 34.1 needs |
| `exists_section34PiercingPackage` | FIX | confuses `C'_v` with `C''_v`; annuli, regular-neighbourhood structure and the domain of the auxiliary sets unspecified |
| `exists_section34ProtectedCircleRemoval` | FIX | (8) does not express crossing; no fixed, locally finite, protected support certificate |
| `exists_section34EdgeMatching` | **FALSE [V: the leaf does not receive `hQsep`]** | all incident `Q_v` may miss a point of `h(∂σ)`; rim containment then fails |

* **Separate `C'_v` from `C''_v`.** Moise p. 249 defines `A_e, B_e` on the boundary of the *pierced*
  cell `C'_v`, then adds `S_e` to get the approximation domain `C''_v`. The code uses one `CcBd` for
  the annuli while asking `G` to be a PL embedding on `Cc` only, so `G '' Sn`, `G '' Tn` may use
  uncontrolled values outside the domain; and with `A_e = ∂C''_v ∩ T_e` condition (3) is
  contradictory (a point of `∂ G_v(C''_v)` inside `Int G_v(T_e) ⊆ Int G_v(C''_v)`). Order:
  `(C'_v, J_e, S_e, T_e, A_e, B_e, C''_v, charts) → ε_v > 0 → f_v`, recording
  `C'_v ∪ ⋃_{e∋v} S_e ⊆ C''_v ⊆ U`, `A_e = ∂C'_v ∩ T_e`, `B_e ⊆ ∂C'_w`, `A_e, B_e` PL annuli with two
  designated intrinsic boundary circles, `T_e ⊆ Int S_e`, `S_e, T_e` compatible regular
  neighbourhoods of the same `J_e`. **Target chart explicit in the preparation:**
  `∀ v, ∃ e ∈ (plGroupoid 3).maximalAtlas M₂, h '' Cc v ⊆ e.source` (suppliable from
  `Q v ⊆ H (car v)`, the closed ball carriers and containment — but it must be *passed*); then the
  PL parametrisation of `C''_v` moves the source to `ℝ³` and the existing chart-local `Moise341`
  applies. `ε_v` is bounded by the finitely many incident margins so that close embeddings keep
  (2)–(7); the marker protection concerns the retained `C'_v` and the graph core, not only the
  distance to the boundary of the larger `C''_v`. (8) by a last margin-preserving general position
  move.
* **(8).** `A = {(θ,u,0)}`, `B = {(θ,u,|u|)}`: two PL annuli meeting in one PL circle interior to
  both, tangent along it. Add the local model (PL coordinates with `A' = {z = 0}`, `B' = {y = 0}` near
  every intersection point) and the annulus / common solid torus structure; Lemma 1 (p. 250) also
  uses their homology relation. The circle-removal interface records fixed target supports
  `S'_e, T'_e`, locally finite; one step acts inside `Int S'_e`, fixes the graph core and the other
  protected data, keeps the conditions and strictly lowers the circle count; label-wise finite
  descent. (FIX, not FALSE: the tangent model refutes "(8) expresses crossing", not the leaf's
  bare `∃ G'`.)
* **Edge matching, counterexample [–] and patch.** Standard cut, one intersection circle per edge;
  `x ∈ Int C_w`, `w` not incident to `σ`, `q ∈ ∂σ`; a compactly supported PL homeomorphism `α` of
  `Int N` fixing all graph vertices and auxiliary tubes moves `x` to `q`; transport all source and
  enlarged cells by `α`; `h = g`, all `G_v = g`; choose the `Q_v` incident to `σ` missing `g(q)`.
  Every hypothesis of the leaf holds, rim containment fails. **Patch:** pass the existing
  `hQsep : ∀ w s, (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1` (leaf 1
  produces it, the assembly has it).
* **Nested torus certificate: the form is right** (`Φ : T_σ ≃ T_e` carrying `J_σ` to `J_e`, all
  existential; no unknotting requirement). Honest production: keep the *outer* torus inside one
  target PL chart with margin first; choose the inner torus after the approximation; transport
  `S_{1σ} ⊆ Int T_σ ⊆ T_σ ⊆ Int S_{2σ}` by that chart; `Φ` := the chart restricted to `T_σ`, `J_e` := the
  actual image. The certificate is not a consequence of `hpack` or of `π₁` surjectivity; it and its
  protection margins belong to the joint construction. `moise308Nested` only transfers generators.

**Missing obligations:** the derived exclusion lemma for P6; `C'_v`/`C''_v`, chart, crossing and
fixed-support preparation; `hQsep` passed to the last leaf. **Fixture:** fine standard cut with
degree-2 vertices, all eight labels, `h = g ∘ ψ`; the initial approximation locally carries one
removable pair of transverse intersection circles. **Most likely surprise:** a control field
produced upstream does not reach a universal downstream leaf — "fine in the intended application"
hides a counterexample to the leaf itself.

## Worker's due-diligence results (2026-09-21, before the third repair)
* **(3) contradictory with `A_e = ∂C''_v ∩ T_e` — partly disagree, then verified.** As the file
  stood the package never asked `Sn e, Tn e ⊆ Cc w`, so `G_v '' Tn e` was the image of an
  uncontrolled map and (3) was *satisfiable* — the defect was uncontrolled values, which is worse.
  Once `T_e ⊆ C''_v` is recorded the reviewer is right (`IsPLHomeomorphInto.image_frontier`,
  `Transition361.lean:216`). Repaired: `Aa e = CpBd (ends e).1 ∩ Tn e`, `Bb e ⊆ CpBd (ends e).2`,
  `Cp w ⊆ Cc w`, `Sn e ⊆ Cc w`.
* **Tangent annuli vs the old (8) — verified** clause by clause (`m = 1`, `P 0` the tangency circle).
  Repaired with the tree's `HasPLCrossingAt` (`GeneralPosition.lean:2370`) through a chart of the
  maximal atlas.
* **`hQsep` — verified, and the counterexample cannot be re-run**: `α` puts `q ∈ src (.vertexBall w)`
  for a non-incident `w`, so `h '' C_w ⊆ interior (Q w)` gives `g q ∈ Q w ∩ h '' |σ|` and `hQsep w σ`
  fails. Rim containment also needs local finiteness of the carriers: `hQlf` is passed too.
* **Owed P6 lemma not proved; the missing fact is named:** *a compact polyhedron of dimension ≤ 1
  has empty interior relative to a PL 2-cell*. The tree's `IsPLBall.interior_eq_empty_of_lt_finrank`
  (`BallFrontier.lean:77`) and `interior_eq_empty_of_affineSubspace_ne_top`
  (`GeneralPosition.lean:357`) are about *ambient* interiors and cannot separate a 1-polyhedron from
  a 2-cell inside `ℝ³`. The rest of the reduction is done on paper (distinct triangles put a foreign
  arc inside `graphSkeletonSpace 𝒦 ⊆ interior N`).
* Worker's own doubts: `exists_section34ProtectedCircleRemoval` asks `cnt' e = 1` for all labels at
  once with local finiteness of the supports stated inside `⋃ e, Sp e`, not inside `h '' U` —
  supports accumulating at the frontier of `h '' U` are not excluded and the infinite composition of
  single steps may fail to be continuous; and `exists_section34PiercingPackage` must deliver the
  crossing model, the support equations and `0 < cnt e` jointly.
