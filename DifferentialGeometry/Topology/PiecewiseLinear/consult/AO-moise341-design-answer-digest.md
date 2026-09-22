# Digest — answer to design consult AL (a producer for `Moise341`), 2026-09-21

Marks: **[V]** checked by the lead; **[–]** not independently verified.

**Verdict.** Option **(b)**: a separate compact-ball skeleton, with (c) used only as the *entry
reduction*. Do not retarget the open-set skeletons to `U := C`. Switch P3's direct input to
`Moise305Tame`. Result: the one-way chain `33.1 → 34.1 → controlled 35.1 → 35.2`.

## 1. Producer of `Moise341`
* **Entry.** `Skeleton/Section34Compact.lean` first proves `Moise341OnNeighborhood`:
  `∀ C V, IsPLBall 3 C → IsOpen V → C ⊆ V → ∀ h, IsEmbedding (V.domRestrict h) → ∀ ε > 0,
  ∃ f, IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε`
  from `Moise331`, `Moise305Tame` (geometry), and the proved `moise308Nested`, PL Schoenflies,
  cell extension and pasting. Then `Moise341` by a PL inward push `r : C ≅ C₋ ⊆ Int C` with
  `d(h (r x), h x) < ε/2`, the neighbourhood statement on `V = Int C`, and `f = g ∘ r` — no
  extension of `h` beyond a wild boundary, no extension of an approximation across a collar
  (the opening reduction of §34; the push is proved independently of the approximation theorem).
* **Why not (a) [V].** Not only `IsOpen U`: `Section34CutFrame` requires the boundaryless
  `IsCombinatorialManifold 3` and `⋃ src = U`, while the graph neighbourhood needs an *ambient
  open* neighbourhood of the boundary vertices; carriers must lie in the open `h '' V`, not in
  `h '' C`. Keep three objects apart: the ball `C`, the open domain `V`, the assembly domain `C ∪ N`.
* **Finite cut.** `K.space = C`, `K.faces.Finite`, `IsCombinatorialManifoldWithBoundary 3 K`; the
  eight cell kinds, plus **outer faces and outer splitting arcs at the boundary** so that all of
  `frontier C_v`, `frontier D_e` is decomposed; the p. 239 link condition (removing the relative
  interior of an edge does not separate two link vertices).
* **Leaves, one data set inherited down the table, nothing re-chosen:**
  `exists_compactCutAndGraph` (entry data, `h331` → finite subdivision, full cut, `N ⊆ V`, `f₁`, all
  of Lemma 1, carrier control, nested-torus certificate); `exists_compactFaceEnvelopes` (allowed
  open neighbourhoods of each `h '' σ`: non-incident avoidance, overlaps only in `Int N''`, the
  smallness for Lemma 4 and 5(7)); shell + general position leaves (envelopes, `h305` → small PL
  face balls with both crossing normal forms); `compactTraceHomology` (auxiliary source disk `τ` →
  whole-trace `CarriesFirstHomologyOnto`, Lemma 4); `compactCompression`, `compactBigonSlide`
  (`c⁺+1 ≤ c ∧ p⁺ ≤ p`; `c⁺ = c ∧ p⁺+2 = p`); `compactTrace_of_noOperation` (+ each trace circle
  nonzero); `exists_compactFaceDisks` (P6); `exists_compactResidualBalls` (P7, literal
  unbounded-component condition, exact boundaries, p. 245 empty sector); `compactTargetRecognition`
  (all target cells incl. outer faces, same boundary decomposition and exact meets as the source
  relation).
* **Two assembly duties that must not be hidden:** Lemma 1's joint choice is *not* a projection of
  `Moise331` — the finite cut and 33.1's derived neighbourhood must be linked by compatible
  subdivision / regular-neighbourhood comparison; outer torus and tolerance first, then `f₁`, then
  the inner torus, then `moise308Nested`. **Finite P5 needs no limit leaf:** minimise the sum over
  faces of `c_σ + p_σ`. Extension in the order marked points, splitting circles, face arcs, **the
  splitting disks themselves**, faces, vertex balls, face disks, residual balls; the cyclic order
  comes from P7's empty-sector certificate; `f|N = f₁` is not required.
* Reusable as is: domain-free leaves (`IsPLHomeomorphInto.mono_of_isPLCellOn`), the cell API, rank
  arithmetic, pasting. Frozen leaves depending on `Section34CutFrame` **cannot** be claimed to
  instantiate; shared statements and proofs go to real modules.

## 2. P3 on `Moise305Tame` — applied [V]
`exists_section34FaceBalls (h305 : Moise305Tame) (hU) (hh) (hcut) (hctrl) (hgraph) : ∃ fbl fblBd, …`
(conclusion unchanged; `section34NormalFamily` takes `h305`; the internal use of 34.1 inside the
controlled 35.1 stays). Shells around the **whole source triangle**: nested balls
`σ ⊆ Int B₁ ⊆ B₁ ⊆ Int B₂ ⋐ U` in one PL regular-neighbourhood product model with a collar beyond
`frontier B₂`; transport by `h` into the carrier chart (`h` is an embedding on an open set
containing the collar, so the outer boundary is *topologically* bicollared — all that
`Moise305Tame` needs); apply `h305`, pull the PL ball back through the chart. General position by
a separate step `exists_section34FaceBalls_generalPosition` (small PL perturbation within the
core and boundary margins, both normal forms, keeping containment, avoidance, carriers, exterior)
— part of P3, not of 34.1 nor of A1. The `H₁` surjection from Lemma 4's auxiliary disk.

## 3. Controlled 35.1 consumes only the single-chart compact-ball approximation
`ChartLocalApproximation.lean` already transports the Euclidean `Moise341` to that interface. Two
call sites: the vertex approximation and the piercing package (which must be able to shrink the
tolerance and re-approximate). No hidden multi-chart or relative-boundary consumer.

## 4. Producer ledger
| Named proposition | Status |
|---|---|
| `Moise264` | §26.4; no orientability restriction in the present statement, so not closable from `Moise252`; add an orientable restricted version (cut along the two-sided surface, apply `Moise252`), re-point §30.7 and §33 to it; the full version stays OPEN |
| `Moise306` | §30.6, torus separation beyond spheres; needs its own producer — missing from the lead's list |
| `Moise307` | §30.7 = `Moise306` + loop-theorem compression of an interior surface; `HasCylindricalDiagram` is faithful; the bridge to `IsCombinatorialSolidTorus` is owed; existence may not be back-derived from `moise308Nested` |
| `Moise303` | §30.3 local separation-preserving surgery; keep the given `Ω` and the explicit formula |
| `Moise286` | §28.6; needs a proof; no surface classification |
| `Moise267` | §26.7 with non-empty common boundary; needs a producer |
| `Moise311`–`314`, `Moise321`–`324`, `Moise331` | conditional skeletons; geometric leaves OPEN; per-triple 31.1 does not automatically supply §32's compatible infinite tower |
| `Moise341` | the compact §34 skeleton; a producer only when its leaves are proved |

Proved reductions: `Moise252 → Moise304 → Moise305Tame`; A1/A2 are not closed, so `Moise305Tame`
is not unconditional. `moise308Nested`, `schoenflies_input`, the inward push: not free inputs. The
design removes the cycle, not the proof duties. **Fixture check first:** the outer faces of the
boundary vertices and the outer arcs of the boundary edges of a tetrahedron — checking interior
stars only would miss exactly option (a)'s main interface error.
