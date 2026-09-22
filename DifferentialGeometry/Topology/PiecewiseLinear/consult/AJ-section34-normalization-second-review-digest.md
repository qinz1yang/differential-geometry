# Digest — second external review of `Skeleton/Section34Normalization.lean` (snapshot `f13a0ba3`)

Marks: **[V]** checked by the lead against the Lean text.

**Docstring correction.** The equivalence "whole-trace `H₁` onto ⟺ some trace circle carries a
generator" is accepted, but its reason must be confined to the *essential* components (which are
parallel); contractible components may still exist — one cannot say every component has `p = ±1`.
**Interface defect:** P4a's local-Schoenflies route needs the ball-shaped single-chart carriers of
`hctrl`, and the signature did not receive them.

| Leaf | Verdict | Reason |
|---|---|---|
| `IsPLHomeomorphInto.mono_of_isPLCellOn` | OK, frozen | not re-examined |
| `exists_splitDisk_src_eq_inter_vertexBall` | OK, frozen | not re-examined |
| `exists_section34FaceBalls` | **OK** | `hU hh` present; both general positions obtainable jointly; the integral whole-trace `H₁` surjection is the right 5(6), produced by Lemma 4's auxiliary-disk argument, not by general position alone; avoidance makes this double trace the book's triple one |
| `exists_section34Compression` | **FIX [V]** → repaired | counts `c⁺+1 ≤ c ∧ p⁺ ≤ p` right; the local Schoenflies route needs the carrier input; clause (16) itself needs no change |
| `exists_section34BigonSlide` | **OK** | precise bigon contract right; replacing one ball gives `c⁺ = c ∧ p⁺ + 2 = p`; the realising `Φ` keeps `T_σ` invariant as a *set*, not pointwise; no new `f₁` |
| `exists_section34TerminalFaceBalls` | OK, frozen | the added `tgtV` only feeds the corrected bigon predicate |
| `section34Trace_of_noOperation` | **OK** | both normal forms right, the tangential branch excluded; the rank condition of the curve field already gives `P ⊕ Q = T`; `HasPLCrossingAt` allows boundary half-planes but the two boundaryless surfaces here exclude that branch |
| `section34TraceCircle_homologyMap_ne_zero` | **OK** | the cut's actual image family gives ≥ 3 cyclically ordered splitting circles; one-point meetings force winding once, so the inclusion's `H₁` is non-zero — exactly what P6 needs to exclude an inner disk; P6 works from `Trace` plus this bridge, not from the old stronger clause 17, so the precision change has no side effect |

## P4a — the missing input is the carrier, not more Operation-1 data
`Dj ∩ fblBd s = Jd` pins the compression circle; `Dj` avoiding all closed splitting disks plus the
dual-ball overlap lemma forces it onto the outer surface — clause (16) needs no boundary data.
What cannot be frozen as it stood: "after the outer compression, the retained sphere still bounds
the required PL 3-ball". Page 242 uses `ℝ³` for this; it is not a consequence of general position.
**Counter-model for a carrier-free compression [V-structure]:** `M = S² × ℝ`,
`C = (S² ∖ Int D) × [−1, 1]`, `D_J = D × {0}` with `D ⊂ Int D₊ ⊂ S²` PL disks, `V = D₊ × [−2, 0]`: `C, V`
are 3-balls, `D_J ⊆ ∂V`, `D_J ∩ ∂C = ∂D_J`; compressing `∂C` along the outer disk gives two spheres,
each a non-zero class of `H₂(S² × ℝ)`, neither bounding a ball. (Not extended to all frame
fields, hence FIX not FALSE.) **Repair applied [V]:** `(hctrl : Section34CarrierControl U 𝒦 h η H)`
added to `exists_section34Compression` (the assembly has it; conclusion and the frozen P5
signature unchanged). The proof picks a tetrahedron `t ⊇ s`, puts the old ball and the compression
disk in `interior (H t)`, and fills the compressed sphere inside the single-chart PL ball carrier.

**Owed:** the two `.Finite` fields are derivable under the full cut/graph *actual image family*
(kept as certificates; bare general position does not bound the total intersection of an infinite
circle family); the homology bridge must move into a real module for P6. **Fixture:** fine grid,
standard cut with a bivalent subdivision vertex, `h = g ∘ ψ`, `f₁ = g`, initial face balls with one
removable circle and one clean bigon, terminal state the normal face balls. **Likely surprise:**
P4a first obtains two 2-spheres; "one of them bounds the required 3-ball inside the carrier" must
be proved, not replaced by demanding that the output satisfy the invariant bundle.

**State after the repair (lead re-check, lease e):** 8 diagnostics, all `declaration uses 'sorry'`;
all eight leaves of the P2–P5 skeleton are now frozen (`exists_section34Compression` in the form the
review prescribed).
