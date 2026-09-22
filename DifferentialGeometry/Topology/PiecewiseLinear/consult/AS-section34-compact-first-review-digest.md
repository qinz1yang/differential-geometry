# Compact Section 34: first review and due diligence

Owner supplied the review on 2026-09-21. It addresses mirror `09672b87`, not the later
snapshot `e1201fcfc` named by request AR. Marks: **[V]** checked against the current Lean source;
**[P]** a mathematical proof argument checked on paper, not a Lean certificate;
**[OPEN]** outstanding formal proof or fixture.

## Verdicts

| Leaf | Review | Lead disposition |
|---|---|---|
| `exists_compactCutAndGraph` | OK | Keep the four source closure formulas and the joint compatible-neighbourhood obligation. |
| `exists_compactFaceEnvelopes` | FIX | Add endpoint input `hV : IsOpen V`; transport of the auxiliary ball's two collars needs room in the embedding domain. |
| `exists_compactFaceShellBalls` | OK | Uses `Moise305Tame`, with source shells and an outer collar; no 34.1 input. |
| `exists_compactFaceBallsGeneralPosition` | OK | Keep both crossing normal forms and both finiteness clauses. |
| `compactTraceHomology` | OK | Whole-trace integral H1 surjectivity remains open; the fundamental-group generator is now separately proved. |
| `exists_compactCompression` | FIX | Add `hcar : Section34CompactCarrierControl K h ε H` for filling inside every incident carrier. |
| `exists_compactBigonSlide` | OK | The replacement changes one face ball and preserves the fixed `f₁` data. |
| `compactTrace_of_noOperation` | OK | Keep the per-circle nonzero conclusion for P6. |
| `exists_compactFaceDisks` | OK | Complete trace data supplies the irreducible-disk argument; `hnc`, `hnb` may be redundant. |
| `exists_compactResidualBalls` | OK | The new target patches determine the complement closures; cell recognition and full tilings are real obligations. |
| `compactSourceFace_iff_cutLe` | OK | Includes all ten label kinds and the outer incidences. |
| `compactTargetRecognition` | OK | Exact meets and face order are required in addition to cell homeomorphism types. |

The two FIX verdicts repair supply interfaces. Neither the reviewer nor the lead has exhibited
a counterexample satisfying every field of either full leaf; neither is classified FALSE.
The ten other leaf blocks are frozen. All twelve proofs remain open.

## Checks and the snapshot disagreement

**[V, P] Link condition.** `Section34CompactLinkCondition` removes
`convexHull ℝ e \ (e : Set E3)`: the open edge, with its endpoints retained. The previous
module prose about a separating chord of a disk was wrong. An edge in the triangulated sphere
or disk link belongs to a triangle. A graph path using that edge can bypass it along the other
two edges of the triangle. Thus no additional barycentric subdivision is needed for this
particular condition. The predicate and frame field are unchanged; the derived Lean lemma is
still **OPEN**. This argument says nothing about the separate subdivision needed for carrier
smallness and compatible regular neighbourhoods.

**[V] Generator.** The review's statement that `moise308Nested` was not actually consumed agrees
with its old snapshot. It does not describe `e1201fcfc`: the lead had already added
`Section34CompactGraphFrame.carriesFundamentalGroupOnto`, which applies
`carriesFundamentalGroupOnto_of_nestedSolidTorus`, and the main assembly passes the resulting
`hgen s` to `compactTraceHomology`. The exporter and its suppliers passed a foundational-axiom
audit; the exporter passed all thirteen environment linters. This closes only the
fundamental-group export, not its passage to the whole trace's H1 surjection.

**[V] Envelope.** The old leaf received `C ⊆ V` and an embedding on `V`, but no openness of `V`.
The endpoint already supplies `hV`. Passing it weakens the obligation and exposes the input
needed by the specified collar-transport proof. There is no current derived substitute from
the cut/carrier clauses. The finite escape-path argument for thickening the thin obstacle is
retained; closed envelopes must avoid the compact paths, and their bounded union must also
avoid the exterior tails.

**[V, P] Compression.** The old compression leaf did not receive the clause saying that every
`H t` is a PL three-ball. A sphere in `interior (B_R(q) \ {q})` whose bounded side contains `q`
refutes an unrestricted carrier-filling inference, but is not a counterexample to the full
leaf. The passed `hcar` supplies `IsPLCellOn 3 (H t) (frontier (H t))`. The complement of the
carrier's interior is connected and unbounded, so the bounded side of a sphere contained in
that interior stays there. The root's `hcar` is available at the existing call site.

**[V] Assembly.** Only the envelope and compression calls need the new arguments. The finite
descent theorem keeps its signature; both named approximation endpoints keep theirs. Dimension
induction extends the interior of `splitDisk`, a two-cell. Cyclic-order information comes from
P7's empty-sector and tiling clauses, followed by recognition, not from rank descent.

## Remaining obligations

The source cut and 33.1 neighbourhood must still be jointly produced; whole-trace H1, carrier
fillings, and the rectangular patches at bivalent subdivision vertices remain proof work.
The proposed common fixture uses a sufficiently fine tetrahedral ball with bivalent vertices,
small convex PL carriers, a nonzero PL translation `g`, and `h = g ∘ ψ` with a non-PL `ψ`
supported inside residual tetrahedra, together with removable circles and a clean bigon.
It remains **UNTESTED**: no joint Lean inhabitant certificate has been supplied.

No whole-file rereview is needed merely because AR named the later snapshot. A further review
can be restricted to the two added inputs and their call sites, while keeping the snapshot
disagreement about the already-exported generator explicit.

## Verification after repair

Independent lease-c receipt: `2026-09-22T04:48:43.3904043Z`, Lean exit 0, stable source,
exactly twelve leaf-sorry warnings and no other diagnostics; no shared output was modified.
Source SHA256: `74C090437C3DB2D8AF3EBAE9C572F2DB68400C7C297B73F7E0F26CB67DD3A79E`.
Against the pre-repair HEAD, exactly the two FIX leaf blocks changed; the other ten blocks,
the finite-descent signature, and both endpoint signatures are byte-identical.
