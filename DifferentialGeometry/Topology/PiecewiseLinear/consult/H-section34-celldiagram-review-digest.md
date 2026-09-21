# Digest — external review of `Section34CellDiagram` (snapshot `06a96eb1de64`)

Verdict: **OK** — true for every quantified `U, h, η`, non-vacuous, no missing terminal gluing
hypothesis. It packages essentially the whole remaining approximation problem; it is a terminal
forgetful interface, *not* an intermediate interface for P0, P1 or normalization.

## Corrections to our own text (applied 2026-09-21)
* "There is no locally finite triangulation theorem for an arbitrary open subset of a PL
  3-manifold" is **false as mathematics**. The open subset inherits a PL structure and has a
  compatible locally finite triangulation; what need not exist is a realisation of the whole
  triangulation in one chart. The honest sentence is "not formalised in this repository". Fixed in
  `Section34Endpoint.lean` (module docstring) and `E3_ASSEMBLY_DESIGN_20260920.md`.
* `hsmall` bounds **pairwise distances** strictly; that is not "diameter `<` tolerance" for a
  non-compact carrier (`(0,1)`: pairwise `< 1`, diameter `= 1`). The pairwise form is sufficient and stays.
* The conditional assembly does not establish its input, and one fixture does not establish the
  universal proposition. Three separate milestones: **finite assembly fixture**, **controlled
  source infrastructure**, **universal P0–P8 producer**. A fixture is never progress on the third.

## Why the statement is true and the right size
With compatible locally finite PL triangulation + subordinate subdivision available,
`Moise352Open 3 → Section34CellDiagram`: approximate with `η/3`, choose `O_a` with `η > η(a)/2`,
`d(h x, h a), d(f x, f a) < η(a)/12`, triangulate subordinate to `{O_a}`, put `T_λ = f(S_λ)`,
`H_λ = h(S_λ) ∪ f(S_λ)`, `Q = P`, `s = r`, `v = f ∘ u`. So the two universals are equivalent
(a size certificate, circular as a proof). Extremes: empty `U` — empty label type; `η → 0` at
infinity — the diagram is chosen after `η`; no properness into `M₂` needed; local finiteness is
tested only at points of the unions, which is local finiteness in the subspaces.

## Intended final labels
| dim | source | target |
|---|---|---|
| 0 | `p_{σe}` | `p''_{σe}` |
| 1 | `a_{vσ}`, `I_{te}` | `a''_{vσ}`, `I''_{te}` |
| 2 | `D_e`, `d_σ`, `X_{tv}` | `E_e`, `Δ_σ`, `X''_{tv}` |
| 3 | `C_v`, `Q_t` | `V_v`, `R_t` |

The splitting circle is decomposed into the sector arcs `I_{te}`; a whole graph neighbourhood `N`
is not one 3-ball label. The interface may forget generator certificates, compression histories,
exterior markers, ranks, buffers — but not their consequences (sector order, every intrinsic
boundary decomposition, exact intersections in all dimensions, target local finiteness).

## Producer obligations the ledger must carry (B1.b)
1. **Controlled source triangulation**: a compatible locally finite triangulation of an arbitrary
   open subset of an atlas-defined PL manifold, fine enough for P0's control supports. Not
   "triangulate a polyhedron in ℝ³". Supplies `hdim`, source presentations, source
   boundaries/intersections, `hLFs`, `hcover`.
2. **Target recognition**: `hs`, `hv` from P1 (`V_v`, `E_e`), P6 (exterior face disks, arcs),
   P7–P8 (residual balls, patches); `htargetBoundary`, `htargetInter` from the full P6–P8
   recognition including the marked-sector condition.
3. **`hLFt` — the most likely surprise.** Sufficient: `T_λ ⊆ H_λ ⊆ h(U)` and `(H_λ)` locally
   finite in `h(U)`. The containment in `h(U)` matters: `W = (0,1)`, `H_0 = {0, 3/4}`,
   `H_n = {1/(n+2)}` is locally finite at every point of `W`, yet `T_0 = {0}`, `T_n = H_n` is not
   locally finite in its own union. Must be proved without invoking the assembled homeomorphism.
4. **Parent-carrier exporter** (small): carriers are controlled for top cells
   (`h(C_v) ∪ V_v ⊆ H_v`, `h(Q_t) ∪ R_t ⊆ H_t`); for each label choose an incident top label
   `p(λ)` with `S_λ ⊆ S_{p(λ)}`, `T_λ ⊆ T_{p(λ)}` and put `H_λ := H_{p(λ)}`. Do not weaken `hsmall`.
5. **P0 must not freeze the neighbourhood `N`** before the joint P1 choice (digest D): P0 fixes
   control data and constraints; P1 chooses the adapted cut diagram and `f₁` together.

Not needed as extra fields: compactness/closedness of cells; reflexivity/transitivity of `face`
(forced: `μ ∈ face λ ↔ S_μ ⊆ S_λ`); finiteness of each face set; global finiteness of `Λ`.

## Fixtures
* **A (basic).** One simplex with all nonempty faces, `d ∈ {1,2,3}`, labels = nonempty
  `J ⊆ {0..d}` (3 / 7 / 15), `w_0 = 0`, `w_i = e_i`, target translated by `a = 4e₁`,
  `u = v = id`, barycentric `r_J`, `s_J`. Tests edges, faces, one 3-ball; no junction of two 3-cells.
* **B (recommended first).** Bent double simplex: base `B = {0, e₁, …, e_{d−1}}`, source apices
  `±e_d`, target `b ↦ a + b`, `e_d ↦ a + e_d`, `−e_d ↦ a − 2e_d`; labels = nonempty faces of the
  two simplices, shared ones once: `3·2^d − 1` = 5 / 11 / **23** (5 vertices, 9 edges, 7
  triangles, 2 tetrahedra). Cross intersections: a common point has `x_d = 0`, so both apex
  coefficients vanish and uniqueness of barycentric coordinates in the base finishes. No single
  affine map realises the matching (`F(e_d) + F(−e_d) = 2F(0)` fails); explicit realisation
  `G_d(x) = a + x + min(x_d, 0)·e_d`. The theorem must have **no free geometric hypotheses**.
* **C (full diagram, on paper only).** `U = ℝ³`, `η ≡ 1`,
  `h(x) = (x₁ + x₁/(10(1+|x₁|)), x₂, x₃)` (a non-PL homeomorphism), `f(x) = x + e₁/10`, a
  consistent simplicial subdivision of the cubic lattice of mesh `1/10`, `T_λ = f(S_λ)`,
  `H_λ = h(S_λ) ∪ f(S_λ)`; pairwise carrier distance `≤ √3/10 + 1/5 < 1`. One instance only.
