# Orientable extended loop theorem: first review and lead due diligence

Date: 2026-09-22. Source: the owner's external-review answer to
[AU](AU-orientable-extended-loop-review-request.md), against mirror
`ac933e4c61453e5bdcb1d592cc0c5b5795fa234d`.

**Result: interface accepted; both leaf statements OK and frozen; both proofs OPEN.**
The lead checked the exact Lean clauses, assembly and cited book pages. No statement repair,
counterexample or disagreement was found. This records statement review, not a proof of
`Moise264Orientable`, the older `Moise264`, or Section 33. `Moise252` remains an explicit input.

## 1. Scope and verdicts

`ExtendedLoopTheoremStatement.lean:30` defines an independently named finite, orientable
version. Two-sidedness is in `K.space`; the surface lies in its intrinsic interior. These
ambient-manifold and interior readings agree by restricting to an open neighborhood of the
surface, rather than by treating the vector-space realization as three-dimensional.
`Connected/TwoSided.lean:11` is componentwise, as in the book's definition on p.191. Neither
`finrank E = 3` nor connectedness of `L` is required. The older `Moise264` in `MoiseChain.lean:61`
uses ambient-vector-space two-sidedness and has no orientability input. No bridge between the
two propositions has been proved or used here.

| Leaf or assembly | External verdict | Lead check |
|---|---|---|
| `exists_bicollar_complement_with_boundary_collars` | OK | One joint choice of the bicollar, finite complement and compatible half collars is required. The component retraction uses the inverse end map on its clopen surface component and a constant value on the others. No connectedness assumption is added. |
| `exists_nontrivial_boundary_loop_of_bicollar_complement` | OK | The output is a kernel loop on a whole collar-end boundary component, before applying 25.2. It need not be the original loop and does not include an embedded disk. The complement may be connected. |
| `moise264_orientable` | OK, conditional assembly | It inherits orientability, applies 25.2 and attaches the same half collar. Its proof is unchanged; transitive completion still depends on both leaves and the explicit 252 input. |

The first leaf has no loop or disk input/output. The second does not assume orientability or
two-sidedness separately: it already receives the actual PL bicollar. These are distinct
geometric obligations, not two copies of the final embedded-disk conclusion.

## 2. The missing derived boundary interface

The second leaf receives `hK`, `hL`, `hLK`, `hR`, `hρ`, `hρzero`, `hW`, `hWnhds` and
`hRspace`, with finite `K`, `L` and `R`. It does **not** receive the first leaf's `hRK`, `hRL`,
old-boundary inclusion, exact intersection or half-collar fields. Its proof must reconstruct
the relevant facts from those actual inputs. In particular it owes

```lean
(boundaryComplex 3 R).space =
  (boundaryComplex 3 K).space ∪ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ))
```

and the identification of the connected components on the right. All boundaries here are
intrinsic combinatorial boundaries. An ambient `frontier` in high-dimensional `E` cannot
replace them.

The lead and a separate read-only reviewer found the following source route; it is not yet
an assembled Lean theorem:

1. Triangulate `L.space ×ˢ Icc (-1) 1`, show that it is a three-manifold with boundary, and
   compute that boundary as the two end copies of `L`. `PrismBoundary.lean:65` already computes
   the boundary of a **disk** times an interval. `CurvePrism.lean:60,77` supplies the local
   neighborhood and boundary-comparison pattern for a **one-dimensional** base. The required
   surface version must still be provided; neither existing signature is the whole result.
2. Transport along the same `hρ` to a finite triangulation of `W`.
   `BoundaryComplement.lean:135`, `boundaryComplex_space_of_closure_sdiff`, then computes the
   boundary of the already supplied `R`. Because `hW` keeps `W` away from the old boundary,
   the two closed-difference terms reduce to the old boundary and the boundary of `W`.
   `ManifoldRelativeTopology.lean:29` supplies the corresponding `W ∩ R.space` formula once
   that manifold certificate for `W` is available.
3. For each surface component `Lα` and sign `e ∈ {-1,1}`, the set `ρ '' (Lα ×ˢ {e})` should be
   one whole boundary component. Conversely every boundary component contained in `W` has
   this form. Compactness, connectedness, disjoint end images and clopen surface components
   give the classification. `ComponentComplex.lean` provides source-component APIs;
   `SurfaceCutting.lean` contains a private closed-partition identification argument, not a
   public completed classification for this bicollar.

Do not identify a full end copy of a disconnected `L` with a single connected component.
Do not infer that the positive and negative ends belong to different connected components
of `R.space`: that fails for a nonseparating surface. The review supports derivability from
the present inputs, not an already compiled producer for these certificates.

## 3. Innermost circles and the book

The lead extracted and visually checked printed pp.191–193, PDF pages 201–203, in the local
`moise_gtm47.pdf`. Theorem 26.3 on p.192 constructs a bicollar by applying the collar theorem
on both sides. The proof of 26.4 on p.193 uses a singular disk transverse to the bicollar
boundary. Its first two cases eliminate an innermost circle; its third case is an essential
boundary loop bounding a singular disk in the complement. Only then does the book invoke
the loop theorem and attach the half collar.

The review's graph-of-groups/HNN explanation is an alternative justification for the
nonseparating case, not a theorem currently supplied by this skeleton. It must not be counted
as implementation evidence or silently used as a new input.

There is a necessary termination argument beyond decreasing the intersection count. If all
circles disappeared while preserving the boundary loop, the connected disk would lie in
the bicollar component containing that loop. Retraction to the original surface would make
the original nontrivial kernel element nullhomotopic there, contradicting `hg`. The printed
proof passes briefly from finite elimination to its third case; formalization must prove
this exclusion explicitly. A descending natural number alone does not produce an essential
remaining circle.

## 4. Assembly check

The lead read the complete current proof and its actual supporting signatures:

- `MobiusEmbedding.lean:37`, `IsOrientable.of_space_subset`, transfers orientability from
  `K` to the supplied same-dimensional cut manifold `R` using `hRK`.
- `MoiseChain.lean:40`, `Moise252`, gives `D ∩ (boundaryComplex 3 R).space` equal to the disk
  boundary. This controls **all** of the cut boundary, not just the selected component `B`.
  Together with the first leaf's old-boundary inclusion and `B ⊆ W`, it excludes old-boundary
  points from the entire disk.
- The assembly proves `A ∩ D = J` for the attached collar over the disk boundary `J`.
  This is exactly the input used by
  `DiskBoundaryCollar.lean:19`, `IsPLHomeomorphOn.exists_isPLHomeomorphOn_union_collar`.
- `hRL` and `hσL` show that the enlarged disk meets `L` exactly along its new boundary. The
  final map identity using `Function.LeftInverse p f` pulls any nullhomotopy of that boundary
  back to a nullhomotopy of `J` in `B`, contradicting 25.2's essentialness output.

No new assumptions or edits to this proof are needed for the accepted interface. The
surface-product boundary and kernel-transfer work belong upstream in the two open leaves.

## 5. Shared fixtures and proof obligations

All proposed fixtures remain **UNTESTED in Lean**:

- A standard nondegenerate PL torus in the interior of a triangulated ball, one fixed small
  bicollar, a finite triangulation of its complement closure, and a meridian basepoint/loop.
- Two disjoint small tori with disjoint bicollars, with the basepoint on one torus and the
  retraction extended constantly over the other surface component.
- In `S² × S¹`, add a local tube to a fiber sphere. The resulting compressible torus is
  nonseparating and has connected complement; the tube meridian bounds a compression disk.
  A finite PL realization may use a sufficiently high-dimensional auxiliary vector space.

The mathematical examples support joint satisfiability but are not Lean inhabitants or
counterexample certificates. No full counterexample was submitted or verified, and no FALSE
verdict is adopted. The lead found no disagreement with the review after source inspection.

Remaining work: both leaf proofs; the derived intrinsic boundary/component interface within
those proofs; the zero-intersection exclusion; a shared Lean fixture; and the Section 33
application bridge to the orientable intrinsic formulation. The older 264 and Section 33
remain OPEN, and 252 remains an explicit dependency.

## 6. Verification record

Before review-status edits, both the skeleton and `ExtendedLoopTheoremStatement.lean` matched
the AU snapshot byte for byte. The skeleton's only change is its module documentation;
imports, namespace/variable scopes, both complete leaf blocks and the whole assembly remain
byte-identical to the reviewed snapshot. The real statement module is unchanged.

Evidence is under the lead's private `claude-moise-agent-c/fill-interface-evidence-20260922`:
`orientable-extended-loop-review-comparison.json` records the initial snapshot comparison;
`orientable-extended-loop-frozen-review.json` records the final declaration comparison and
focused-check receipt. The final PowerShell lease-c check completed at
`2026-09-22T11:30:32.7436243Z` with Lean exit 0, a stable source hash, and exactly the two
authorized leaf-sorry warnings. The checked source SHA-256 is
`c38592ae839a660a062ca44a20122155b33a8cc79d0ae0d130dd8da741679e96`.
The existing copied-source
endpoint/axiom audit had exactly the expected transitive `sorryAx` plus foundational axioms;
the mathematical source has not changed, so this review does not claim a new proof audit.

No full aggregate build or audit of F's current pass is part of this review. This status
change does not reduce the skeleton sorry count. `FREE_INPUTS.md` B1.i remains the sole
progress entry; this digest records evidence and obligations.
