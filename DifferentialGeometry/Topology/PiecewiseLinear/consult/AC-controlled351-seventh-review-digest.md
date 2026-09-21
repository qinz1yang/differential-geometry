# Digest — seventh external review of `Skeleton/ControlledGraphNeighborhood.lean` (2026-09-21)

Marks: **[V]** checked by the lead against the Lean text; **[–]** not independently verified.
The three frozen leaves were not re-examined. No complete counterexample to any of the four
unfrozen leaves was found; the two FIX verdicts are "producer basis not closed", not "statement
false".

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34VertexPreparation` | **FIX** (core / scale part OK) | must also output the source-side control that yields isolation of **whole closed overlaps**; not a consequence of the tube margins |
| `exists_section34PiercingPackage` | **FIX** | foreign-ball exclusion has a proved producer; closed-overlap isolation cannot be proved from `Sp` pairwise disjoint |
| `exists_section34DeletedBalls` | **OK** — freeze; isolate a single-cap lemma | one transverse circle + overlap isolation + foreign-ball exclusion support cap-by-cap deletion and keep the designated vertex; that the literal difference is a ball needs genuine PL topology |
| `exists_section34EdgeMatching` | **interface OK** — freeze | receives the prescribed differences, ball/disk structure, overlap incidence and the whole-graph neighbourhood; the relative PL extension and the outer torus part are still real work |

## 1. `Kcore` and the certified scale — correct
`Γ ⊆ ⋃ K_w` and `h(K_w) ⊆ int P_w` give `h(Γ) ⊆ int ⋃ P_w`: the whole-graph neighbourhood, proved as
`mem_nhdsSet_iUnion_image_of_section34Core` **[V]** (exists, `Section34Frame.lean`). No compactness
of the graph is needed, only of each core. The quantifiers are right: the certificate is about the
**same, already chosen** `ε w` and all PL embeddings within it; the producer first gets `δ_w` from
the stability theorem, then chooses `ε_w ≤ δ_w` together with the other margins — never shrinks
after receiving `G`. The stability proof (`PLCellOnStability.lean`) stands: invariance of domain,
local connectedness, finite cover of the compact core; no degree, no single chart for the target
ball.

## 2. The two image conditions
* **Foreign-ball exclusion: passes, already proved** (`section34MarkerConditions`) **[V]**: for
  `y = G_{w'} x ∈ h(vertex w)`, closeness gives `d(y, h x) < ε_{w'}` and the preparation margin the
  opposite strict inequality; the scale is that of the *perturbed* ball `w'`.
* **Closed overlaps of different edges: the consumer needs it, the producer cannot supply it.**
  `Sp_e ∩ Sp_d = ∅` controls the surgery supports near the intersection circles;
  `(P_{e₁} ∩ P_{e₂}) ∩ (P_{d₁} ∩ P_{d₂}) = ∅` controls whole ball overlaps, in particular triple
  covers far from the circles. **[V]** — lead read `Section34VertexPreparation`: the only source
  disjointness is for *non-adjacent* balls (last clause) with its margin; for three pairwise
  adjacent vertices `a, b, c` (a triangle of `𝒦'`) nothing excludes `Cp a ∩ Cp b ∩ Cp c ≠ ∅`, and no
  margin speaks about it.
  **Counterexample to the inference "separated circles/tubes + private markers ⇒ overlap
  isolation" [V]** (lead recomputed): `B₁ = {|x+1|+|y|+|z| ≤ 2}`, `B₂ = {|x−1|+|y|+|z| ≤ 2}`,
  `B₃ = {|x|+|y|+|z| ≤ 1.8}`; the three boundary intersection circles lie in `x = 0, −0.4, 0.4`,
  pairwise disjoint; each ball has a private interior point; the origin is interior to all three.
  Not a counterexample to the full `hprep`.
  **Repair (non-circular):** the preparation certifies, with
  `V_w = ⋃_{x ∈ Cp w} ball (h x) (ε w)`,
  `∀ e d, e ≠ d → Disjoint (V (ends e).1 ∩ V (ends e).2) (V (ends d).1 ∩ V (ends d).2)`.
  From `P_w ⊆ V_w` the package clause is immediate. Producible: make the *source* overlaps of
  different edges disjoint first, then use compactness (`N_ε(A) ∩ N_ε(B)` shrinks to `A ∩ B`) and
  local finiteness to choose the scales; never the other way round. The carriers of whole overlaps
  are **not** the thin tube supports `Sp`.

## 3. Deleted balls — keep the literal formula
`D_v = P_v \ ⋃_{e : end₂ e = v} int P_{end₁ e}`: a *directed* deletion of neighbours' interiors — keep.
Overlap isolation makes different caps independent; foreign-ball exclusion keeps the vertex in the
retained part. The cores need **not** stay in the ball of the same index: prove
`⋃ D_v = ⋃ P_v` (a point lies in at most two balls; if in two, it is deleted from one designated end
only) and transport the certified whole-graph neighbourhood. The worker's choice "cores avoid the
surgery supports, not the whole overlaps" is right — demanding the latter would exclude the graph
passing normally through an overlap.
**Single-cap lemma to isolate.** For PL 3-balls `A, B` whose boundaries meet transversally in
exactly one PL circle: the *designated* set `A \ int B` is a PL 3-ball, with its boundary identified
and `A ∩ ∂B` recognised as the cutting disk; with `p ∈ int A \ B` also `p ∈ int (A \ int B)`. Key step:
`A ∩ ∂B` is a properly embedded PL disk in `A`, and the designated side it cuts off is the
difference. Then finitely many inductions per ball using overlap isolation.

## 4. PL Schoenflies in the tree
The reviewer saw `exists_isPLBall_of_isPLSphere_two (I : SchoenfliesInput)` and warned that the
input must not be smuggled into 35.1. **[V] — settled by the lead:** `SchoenfliesFoundations.lean`
proves `schoenflies_input : SchoenfliesInput` (four fields, no `sorry`), so PL Schoenflies in `ℝ³`
is unconditional here. What remains true: it yields *some* filling ball for a PL 2-sphere in `ℝ³`;
the single-cap lemma still needs (a) the cutting disk and the new boundary sphere, (b) the
identification of the filling ball with the literal difference, (c) the transport from the chart
model back to `IsPLCellOn`. The reviewer did not verify the exported statements of 23.9–23.11, so
no ready-made single-cap theorem is certified.

**Hardest parts:** certifying whole-overlap isolation *before* the perturbation is given, and the
literal difference cut by one transverse circle being a PL ball.
