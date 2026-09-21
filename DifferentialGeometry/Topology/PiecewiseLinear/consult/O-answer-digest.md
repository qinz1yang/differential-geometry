# Digest — answer to consult O (weaker induction invariant), 2026-09-21

**Verdict: change needed, but no return to "all of `Z`, all later charts".** Observation 1 holds;
localising to the transition zones is enough for the *current* step's normality. **What is not
closed is the production of (b) for the next steps: it is not an automatically open condition in
the current chart's vertex parameters.** Marks: **[V]** checked by the lead, **[–]** not.

## 1. Old double curves may be replaced; the boundary needs no conjugacy [–]
`exists_globalInvariants_of_gluedCell` has no `χ, ψ`: fibres `≤ 2`, `StarInj T`, properness and the
buffered boundary homotopy come from the control certificate, the seam and the boundary buffers.
The pairing was used only by the crossing leaf to transport old normality; *producing* normal
double curves afresh replaces the transport; the number of branches and the old pairing need not
persist (Moise also takes general position first and minimal complexity afterwards). At the
boundary one must also genericise the traces inside `ker ℓ`: intersection points avoid boundary
vertices, the two boundary edges cross transversally, the third vertex of each adjacent triangle
at strictly positive height — zero/positive heights alone are not enough. And generic double
points are not all interior to two triangles: normal **edge–triangle** intersection points must be
recognised too.

## 2. Protecting current normality needs only the transition zone [–]
`P_k = closure (V_k \ closure W_k)`; first make sure the closed buffer used lies in `ec_k.source`
(not automatic from `V_k ⊆ ec_k.source`). On the final `R`, simplices with a frozen vertex miss
`closure W_k` (`hsep`) and have image in `V_k`, so the crossings they take part in and that must be
checked over `Z_k` lie in `Z_k ∩ P_k`. **Do not quote stability pointwise on the old double point
set: first cover it by buffered graph blocks.** Full source preimage, compactness and the fixed
injectivity scale give: if arbitrarily small perturbations produced double points involving
frozen/mixed parts outside the blocks, a limit of source pairs would be two *different* points
(injectivity scale) over an old double point of `Z_k ∩ P_k` — contradiction. This covers "a free
sheet near a mixed one" and "an intersection segment reaching a frozen edge": check the **two
complete local source sheets**, not two triangles. A third sheet is excluded by the whole-source
`hcert`. The entirely free part is re-genericised. No stability is needed outside the zones.

## 3. The gap: the future (b) is not open in the current parameters [V]
Later chart `H(x,y,t) = (h(x,y), t)`,
`h = (y/3, −2x + 5y/3)` on `x ≥ 0, 3x ≤ y ≤ 4x`; `(4x/3, y + 2x/3)` on `x ≥ 0, y ≥ 4x`; identity
elsewhere (lead checked: continuous on `y = 3x`, `y = 4x`, `x = 0`; both determinants positive;
sectors go to sectors — a PL homeomorphism). Sheets `A = {y = 0}`, `B = {y = x}`: `H` is the
identity on them, so the old crossing has a strict graph margin in **both** charts. Translate both
sheets by `(a, 3a, 0)`, `a > 0` arbitrary: still two transverse planes in the current chart, but
the crossing `(a, 3a)` now sits on the wall `y = 3x`, and in the later chart the four rays are
`A: (1,0), (0,1)`, `B: (1,1), (−1,1)` (lead checked: the sector map sends `(−1,0) ↦ (0,2)` and
`(−1,−1) ↦ (−1/3, 1/3)`) — the normal bent model **without** margin `(*)`; a further small move of
`B` creates a touching. So an old margin in a later chart gives no safe open ball in the current
chart's parameter space; interpolating the translation to zero in an outer ring shows that a
frozen ring does not remove the problem. (This also limits consult L §3: it proposed a multi-chart
production route, it did not prove that later-chart margins survive one shrinking of the radius.)

## 4. What to change
**Keep the localisation to the transition zones; list "relative multi-chart generic production" as
its own obligation.** No global `𝒬` is needed: record, on the relevant compact overlap blocks only,
the finite affine pieces of the chart transitions, and where (b) has to be re-produced require
`Σ(g) ∩ |𝒬^(1)| = ∅`, `Σ(g) ⋔ relint F`, and exclude compound degeneracies (a source fold edge and a
target wall meeting the double curve at the same point, …). **Degeneracies forced by frozen data
are not a "proper algebraic bad set"**: they need their own retention/recognition proof; density
is proved for the remaining parameters. Two tempting shortcuts do not work: "transition maps affine
on the overlaps" is not an available atlas hypothesis; "link circles cross at interior points of
link edges" is not intrinsic nor subdivision invariant (subdivide the intersection line into source
edges and the crossing points become vertices).

**Final judgement of the consultant:** the local protection argument for the current (a) holds; the
producer `(a)+(b) → next (a)+(b)` still needs proof — not FALSE, not to be frozen. There is no
counterexample to the spatial localisation and no reason to call L §3's global version minimal.
Besides the seed and crossing leaves, the **induction type** must change; if multi-chart genericity
is not listed separately it hides inside the seed again and does not vanish with the pairing.

## Lead's plan
Redesign of `Skeleton/GeneralPositionInDouble.lean` (sixth iteration, the first that changes the
induction): invariant = (a) normality over `Z_k` + (b) margin-stable buffered graph blocks over
`Z_k ∩ P_m` in the chart `ec_m`, for every `m ≥ k`. Leaves affected: the seed (becomes consult L §2
with `φ_* = ec ∘ D`, consuming (b) at `m = k`; no pairing, no `𝒢`), the generic choice (guard +
edge–triangle recognition + boundary-trace transversality + the wall conditions on the fixed
overlap blocks; frozen-forced degeneracies exempted with a separate retention leaf), the crossing
leaf (produces (a) and (b) for the next index; pairing certificate removed). Frozen leaves expected
to survive unchanged: adapted charts, cut-out, gluing, global invariants, preparation.
