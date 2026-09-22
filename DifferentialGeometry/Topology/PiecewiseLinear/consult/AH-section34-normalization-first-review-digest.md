# Digest — first external review of `Skeleton/Section34Normalization.lean` (P2–P5; snapshot `f15c6f34`)

Marks: **[V]** checked by the lead against the Lean text; **[–]** not independently verified;
**[D]** lead disagrees or qualifies.

**Docstring corrections.** (1) The dual-ball overlap clause IS derivable from the present cut
frame (patch/face-arc labels: two different incident edges force the vertex-ball label to be
unique; every other common small cell lies in a splitting disk) — keep leaf 2 as a derived lemma,
no new cut-frame field. (2) Operation 2 MAY be an ambient homeomorphism `Φ` that moves only the
face ball: define `C_σ⁺ = Φ(C_σ)` and update no `V, E, γ` data; `Φ(γ_e) = γ_e` is not required.
Protecting the relevant `T_σ`, the other face balls, the markers and the outer collars of the
carriers is what preserves generator and exterior. (So the worker's finding 3 was right about the
*fixed* data and wrong to conclude that no ambient map is usable.) The real defects: two
finiteness fields are not general position, and the generator field is not Lemma 5(6).

| Leaf | Verdict | Reason |
|---|---|---|
| `IsPLHomeomorphInto.mono_of_isPLCellOn` | **OK** | a PL cell is a restrictable local polyhedron, both directions |
| `exists_splitDisk_src_eq_inter_vertexBall` | **OK** | keep as derived lemma |
| `exists_section34FaceBalls` | **FALSE [V]** | receives neither `IsOpen U` nor the embedding `hh`; the signature has only `h341, hcut, hctrl, hgraph` |
| `exists_section34Compression` | **FIX** | no true general position; the generator field wrongly strengthens the input |
| `exists_section34BigonSlide` | **FIX [V]** | the bigon lacks the full boundary equation and the `∂N''` clause; the single-ball replacement interface itself is right |
| `exists_section34TerminalFaceBalls` | **OK** | *given its two universal step hypotheses*: fair enumeration of labels, each changed finitely often; `Exterior` supplies fixed locally finite carriers, so every compact witness stabilises — not a limit of arbitrary homeomorphisms |
| `section34Trace_of_noOperation` | **FALSE [–]** | a trace with a tangential branch is finite, admits neither operation, and is not a family of disjoint circles |

## P3 — counterexample [V-plausible]
Standard cut in `ℝ³`, `f₁ = id`, large `η`, roomy locally finite carriers. On a small segment `I` of a
graph edge inside a vertex ball `V_v`, replace `h` by a surjection onto `int V_v`, identity elsewhere,
vertices fixed. Each affected image boundary is the old loop plus `int V_v`: connected, still
carrying the old generator, new points inside `V_v`, no wrong incidence with foreign balls or
splitting disks; carrier and distance clauses hold. Nothing in the three frame hypotheses forces
`h` continuous. But for the triangle `σ ⊇ I` the output needs `int V_v ⊆ h(∂σ) ⊆ int C_σ`, and the
compact `C_σ` then contains all of `V_v`, hence meets a vertex ball adjacent to `v` not in `σ` —
violating avoidance. **Repair:** add `(hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))`,
which the endpoint has; P4's proofs, needing compact protected image boundaries, receive the same
context rather than guessing it from `GraphFrame`.

## Invariant bundle — satisfiable, but the generator field has the wrong strength [V]
`CarriesFundamentalGroupOnto A T` (`Section34Frame.lean:306`) asks `π₁`-surjectivity from *every
basepoint's component* of `A`, and is vacuous for `A = ∅` (`nonempty_section34FaceTorus` does not
remove that vacuity). The book's 5(6) is surjectivity of `H₁(A_σ) → H₁(T_σ)` for the *whole* trace
`A_σ = ∂C_σ ∩ ∂T_σ ∩ ∂N''`. The normal "double longitude" face ball satisfies the present bundle, so
it is not unsatisfiable; but once true general position is required, an Operation-1 circle is a
trace component contractible in `V_v ⊆ T_σ` and violates per-component surjectivity — **P3 would
be forced to do P4a's work.** Replace the field by the `H₁` contract (or, since after general
position the trace is a family of disjoint circles on the torus `∂T_σ`, and disjoint simple closed
curves on a torus are parallel, by "some trace circle carries a generator" — the lead notes this
equivalence for the reviewer to confirm; the vacuity for `A = ∅` disappears in both forms).

## Terminal leaf — counterexample, and why general position must be a field [–]
In a clean crossing block of the normal fixture, `V_v = {z ≤ 0}`, `∂C_σ = {z = x}`; replace the latter
in a small block by the PL graph `z = max(x, min(−|y|, 2x + 2a))`, `a > 0`. The zero set on the wall
becomes `{x = 0} ∪ ([−a, 0] × {0})`: the trace circle with a tangential branch. The change is inside
`V_v`, avoids all splitting disks and other face balls; `O_t`, generator, both counts and the
impossibility of both operations are unchanged, yet a trivalent trace point appears and
`Section34Trace` fails. **Repair:** a field "PL transverse normal form in the atlas", including
transversality of the trace to the splitting circles. True general position + compactness +
relative local finiteness imply the two `.Finite` fields; not conversely. P4a/P4b preserve the
corrected invariant and prove respectively `c⁺ + 1 ≤ c ∧ p⁺ ≤ p` and `c⁺ = c ∧ p⁺ + 2 = p`.

## Bigon [V]
The present `Jd ⊆ B ∪ tgtEBd e` admits `Dj = tgtE e`, `Jd = tgtEBd e` — no bigon along `B` at all. At
least: `IsPLCellOn 1 B' Bb`, `B' ⊆ tgtEBd e`, `B ∩ B' = Bb`, `Jd = B ∪ B'`,
`Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w)`. **Lead's extension [V]:** the same imprecise premise is the
last conjunct (17) of the frozen `Section34NormalPlus` (`Section34Frame.lean`), copied verbatim by
the skeleton; the repair must change that clause too, which reopens the frozen T1 leaf and the
terminal leaves that consume the clause (making the premise precise *weakens* the `→ False`
clause, so producers get easier and consumers get less — the mathematically right direction).

## Endpoint rulings
② No new `f₁` is needed (see docstring correction 2). ③ Do not add 5(1)/5(6) as independent P6
hypotheses; P6 needs "each trace circle is nonzero in `T_σ`", derivable from the ≥ 3 annular
splitting circles of the cut plus `Trace`'s one-point intersections (winding once excludes an inner
disk) — add that derived bridge; 5(1) may be exported as information; 5(6) is the `H₁` form above.

**Owed:** true general position; production and preservation of the whole-trace generator;
`Trace → every circle nonzero`; the precise bigon in `Section34NormalPlus` (17). **Fixture:** fine
grid in `ℝ³`, standard cut with a bivalent subdivision vertex, `h = g ∘ ψ`, `f₁ = g` with `g` a small
non-zero PL translation and `ψ` non-PL supported inside one residual tetrahedron; normal face balls
satisfy the bundle; one removable circle and one bigon test the corrected P4. **Likely surprise:**
writing "the whole trace carries a generator" as "each component already carries one" makes P4a
vacuous under true general position.
