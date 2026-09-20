# B2 — answer digest (external consultant, 2026-09-20; reviewed branch head `8ded861f8`)

Digest of the answer to `B2-marked-chain.md`. The statements are proposed lemmas, not compiled
Lean. Claims about the tree and the three counterexamples were verified by the lead (✓).
`∂D` of a PL disk means its **intrinsic** PL boundary, never its ambient frontier.

## Verdict

**Route II (marked dual-cell induction) works**, with two qualifications: the boundary chart
must be adapted to the actual pair `(W, H)` by a new relative straightening theorem (no change
to `NormalSingularCellData`), and **one sheet `Bool` does not determine the adjacent-ray pairing
of the cross reglue** — carry both partitions, or transport the pairing through the actual
interface maps. All new topology is 2-dimensional (disk-sector extensions); coning and finite
gluing give the 3-dimensional blocks.

## Corrections

1. **Two labelings, not one ✓.** Rays `r₀ = +e_x, r₁ = +e_y, r₂ = −e_x, r₃ = −e_y`. Original-sheet
   partition `{r₀,r₂} | {r₁,r₃}`; bent-sheet partition `{r₀,r₃} | {r₁,r₂}`. The reflection
   `(x,y) ↦ (x,−y)` preserves the first and sends the second to `{r₀,r₁} | {r₂,r₃}`. Use page
   labels `a, b : Fin 4 → Bool` (alternating old-sheet label, adjacent bent-sheet label); a page
   permutation `π` transports them when (L) `a'(π i) = ε_a (a i)`, `b'(π i) = ε_b (b i)`.
   Dihedrality of `π` is automatic; strict cyclic-order preservation is not and is not needed.
2. **The end-point chart equality is false in the existing chart ✓.** Coordinates `(x,y,t)`,
   sheets `S₀ = {y = 0, t ≥ 0}`, `S₁ = {x = 0, t ≥ 0}`, `H = {t = −min(|x|,|y|)}`,
   `W = {t ≥ −min(|x|,|y|)}`: all hypotheses hold, `S₀ ∩ H = {y = t = 0}`,
   `S₁ ∩ H = {x = t = 0}`, yet `(s,s,−s/2) ∈ W \ {t ≥ 0}`. The chart theorems straighten the
   existential half-space witness, not `W`.
3. **Chart boxes settle individual unprescribed blocks only**; they do not extend a prescribed
   parametrisation of an arbitrary embedded interface disk. Route II avoids the problem because
   `C_j ∩ C_{j+1} = cone_{z_j} L_j` and non-adjacent cells are disjoint are *exact*
   (`ArcCellGluing.lean:48`, `ArcChainCells.lean:53`).
4. **"Two circles meeting in two points" is not enough**: four meridians `γ₀…γ₃` in cyclic
   order with circles `γ₀ ∪ γ₁`, `γ₂ ∪ γ₃` meet in the two poles but *touch*. The link
   conclusion must keep the sheet assignment and the **alternating** incidence; the two-sided
   crossing germ supplies it.
5. **The end-point link disk is top plus walls ✓**, not the top square:
   `L_* = (Q × {1}) ∪ (∂Q × [0,1])`, `∂L_* = ∂Q × {0}`, apex `p_* = (0,0,0)`, `v_* = (0,0,1)`,
   model spoke `λ_i = ([0,r_i] × {1}) ∪ ({r_i} × [0,1])`; then `p_* * L_* = Q × [0,1]`,
   `p_* * ∂L_* = Q × {0}`, `p_* * {v_*} = {0} × [0,1]`, `p_* * λ_i = [0,r_i] × [0,1]`.
   (Sending the whole link disk to the top square is impossible: `L ∩ (p * ∂L) = ∂L ≠ ∅`.)
6. `exists_normalized_trimmedArcCellUnion_of_cutModel` assumes `Module.finrank ℝ E = 3` ✓; the
   marked statements below are for arbitrary finite-dimensional realisations with intrinsic
   boundaries.
7. `crossRegluedPullback` is **not continuous across a seam** (one side approaches a point of
   the crosscut `A`, the other its partner in `C`); never prove PL-ness through it globally.
8. Do not demand all maps simplicial for one fixed triangulation (an increasing non-identity PL
   homeomorphism of an interval is not simplicial for any fixed one); use finite compatible
   subdivisions and finite PL gluing. Preimages of subpolyhedra under PL maps of compact
   polyhedra are subpolyhedra.

## Statements

**Theorem A — boundary adaptation relative to the two half-sheets.** `W` a closed PL
3-manifold with boundary in a PL 3-manifold, `H = ∂W`, `y ∈ H`; a PL chart at `y ↦ 0` carries the
sheet germs to `S₀ = {y₂ = 0, t ≥ 0}`, `S₁ = {y₁ = 0, t ≥ 0}` with (A1) `S_i ⊂ W`,
`S₀ ∩ H = {y₂ = t = 0}`, `S₁ ∩ H = {y₁ = t = 0}`, `S_i \ H ⊂ Int W`. Then there are
neighbourhoods `U, V` of `0` and a PL homeomorphism `k : U → V` with `k 0 = 0`,
`k = id` on `(S₀ ∪ S₁) ∩ U`, `k (W ∩ U) = V ∩ {t ≥ 0}`, `k (H ∩ U) = V ∩ {t = 0}`.
Proof: small convex polyhedral ball, all germs conical; `J = H ∩ Σ` a PL circle, `D = W ∩ Σ` a
PL disk, `T = (S₀ ∪ S₁) ∩ Σ` a four-spoke tree in `D` (uses all of (A1)); T₄ fixing `T`
pointwise onto `D_std = Σ ∩ {t ≥ 0}`; extend over the complementary disk; cone. Not derivable
for arbitrary sets `BdM`, `W`; `preimage_boundary_eq_frontier` gives properness, not the side.

**Theorem B1 — derived cells restrict to subcomplexes, no fullness ✓ tools exist.**
`L.faces ⊆ K.faces`, `s ∈ L.faces` ⇒
`(derivedNeighborhoodCell K s).space ∩ L.space = (derivedNeighborhoodCell L s).space`, from
`closedStar_barycentricSubdivision_inter_space_eq` (`StarIntersection.lean:10`). Bases likewise
(B2) `B_K(s) ∩ |L| = B_L(s)`, hence (B3)
`|L| ∩ cone_{p_s} B_K(s) = cone_{p_s} (B_K(s) ∩ |L|)` via
`derivedNeighborhoodCell_space_eq_coneSet` (`DerivedCellCone.lean:12`). False for an arbitrary
cone presentation ✓ (tetrahedron `K = p * σ²`, `L = ∂K`).

**Theorem B2 — transfer of conical marked links.** Finite PL cones `C = p * Σ`, `C' = p' * Σ'`
with marked conical subpolyhedra `p * Γ_i`, `p' * Γ'_i`; a PL homeomorphism of neighbourhoods of
the apices matching every marked germ ⇒ a PL homeomorphism `ℓ : Σ → Σ'` with `ℓ Γ_i = Γ'_i`
(triangulate with apex and marks as subcomplexes; compare links simplicially after refinement).
Apply after shrinking the crossing charts to be **source-saturated** (only the two source sheets
give the image in the chart); mesh control puts each cell in one shrunk chart.

**End-point cells (B4).** At a boundary vertex `p`, `K_H = ∂K`: `B_K({p})` is a PL 2-disk,
`B_K({p}) ∩ |K_H| = ∂B_K({p})`, `C_K({p}) ∩ |K_H| = p * ∂B_K({p})`; the sheet trace is a four-spoke
tree; the interface with the neighbour is an interior sub-disk containing the tree's centre.

**Four-spoke disk (C1).** `(D; c; T₀…T₃; v₀…v₃)`: `D` a compact PL 2-disk, `c ∈ Int D`, `T_i` a
PL arc from `c` to `v_i ∈ ∂D`, `T_i ∩ ∂D = {v_i}`, `T_i ∩ T_j = {c}`, the `v_i` distinct and in
this cyclic order on `∂D`.

**Theorem T₄.** `g : ∂D → ∂D'` a PL homeomorphism, `π` with `g v_i = v'_{π i}`, PL
homeomorphisms `q_i : T_i → T'_{π i}` with `q_i c = c'`, `q_i v_i = g v_i` ⇒ a PL homeomorphism
`F : D → D'` with `F = g` on `∂D` and `F = q_i` on `T_i`. (The spokes cut `D` into four PL disks;
extend over each sector — Moise Thm 5.4, pp. 43–44 — and glue.) Under (L), `F` carries old-sheet
and bent-sheet unions as prescribed (C2).

**Theorem T₄-cap.** `E ⊂ Int D`, `E' ⊂ Int D'` compact PL disks with `c ∈ Int E`, each `T_i ∩ E`
the initial subarc from `c` to `w_i`, `T_i ∩ ∂E = {w_i}` (same primed); `g : E → E'` PL
homeomorphism, `g c = c'`, `g (T_i ∩ E) = T'_{π i} ∩ E'` ⇒ a PL homeomorphism `F : D → D'` with
`F = g` on `E`, `F T_i = T'_{π i}`; a boundary homeomorphism `γ` with `γ v_i = v'_{π i}` may also
be prescribed. (The remaining spoke segments cut `D \ Int E` into four disks.)

**Theorem C — marked suspension-cone extension** (four-page analogue of
`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked`, `ConeDiskPairExtension.lean:20`).
`Σ, Σ'` PL 2-spheres, cone bases at `p, p'`; arcs `γ₀…γ₃ ⊂ Σ` from `u` to `v`, `u ≠ v`,
`γ_i ∩ γ_j = {u,v}`; a PL disk `E ⊂ Σ`, `u ∈ Int E`, `v ∉ E`, each `γ_i ∩ E` an initial subarc
meeting `∂E` once (same primed); `g : E → E'` PL homeomorphism, `g u = u'`,
`g (γ_i ∩ E) = γ'_{π i} ∩ E'` ⇒ a PL homeomorphism `G : p * Σ → p' * Σ'` with `G = g` on `E`,
`G p = p'`, `G u = u'`, `G v = v'`, `G Σ = Σ'`, `G (p * γ_i) = p' * γ'_{π i}`,
`G (p * {u,v}) = p' * {u',v'}`; labels transported under (L). *Two-cap strengthening:* with
outgoing disks `E₊ ∋ v`, `E'₊ ∋ v'` meeting each meridian in a terminal subarc, also
`G E₊ = E'₊` — the outgoing map is **produced, not prescribed**; this lets each block map to its
own slab with no renormalisation of the accumulated union.

**Theorem E — end-point marked-cone extension.** `C = p * L`, `L` a PL disk and cone base at `p`,
`C ∩ H = p * ∂L`, `L` carrying a four-spoke tree centred at `v` ⇒ a PL homeomorphism
`G : C → Q × [0,1]` with `G p = p_*`, `G L = L_*`, `G (C ∩ H) = Q × {0}`,
`G (p * {v}) = {0} × [0,1]`, `G (p * T_i) = [0, r_{π i}] × [0,1]`; and `G = g` on a prescribed
interior interface `E` mapped to `Q × {1}` (T₄-cap). The other end uses `t ↦ 1 − t`.

**Chain.** With the canonical cells `C₀…C_m`, the marked-link data and caps of C, the end data
of E, and page markings agreeing on common interfaces: a PL homeomorphism
`Φ : ⋃ C_j → Q × [0, m+1]` with `Φ C_j = Q × [j, j+1]`, `Φ (C_j ∩ C_{j+1}) = Q × {j+1}`,
`Φ A = {0} × [0, m+1]`, `Φ (page i) = [0, r_i] × [0, m+1]`,
`Φ (H ∩ ⋃ C_j) = Q × {0, m+1}`. Prescribe the incoming interface map at each attachment; the
extension produces the outgoing one; disjoint slab interiors give injectivity.

**Theorem D — four source pages give the PL bent-sheet reading.** `φ : Q × I → N ⊂ W` a PL
homeomorphism onto the tube, `P = Δ' ∩ G⁻¹ N`. Compact source subpolyhedra `Z₀…Z₃` with
`P = ⋃ Z_i`, `G : Z_i → φ([0,r_i] × I)` PL homeomorphisms, `Z₀ ∩ Z₃ = J₊`, `Z₁ ∩ Z₂ = J₋` with
`G : J± → φ({0} × I)` PL homeomorphisms, all other mixed intersections empty ⇒
`P₊ = Z₀ ∪ Z₃`, `P₋ = Z₁ ∪ Z₂` are disjoint compact PL 2-disks, `φ⁻¹ ∘ G` is a PL homeomorphism
of each onto its model bent sheet, and the tagged `coord` satisfies
`G = φ ∘ crossSeamInclude ∘ coord` on `P`. **The substantive producer is the four-page source
trace**; simpliciality of `D` is no substitute. Source side: with
`V₁ = P' ∩ h⁻¹ P`, `V₂ = P' ∩ h⁻¹ Q`, `V₃ = Q'` and `F₁ = f₁ ∘ h`, `F₂ = f₂ ∘ h`, `F₃ = f₃`:
`G = D ∘ F_i` on `V_i`; seams `J₁₂ = P' ∩ h⁻¹(P ∩ Q)`, `J₂₃ = P' ∩ Q'` with
(D2) `V₁ ∩ V₂ = J₁₂`, `V₂ ∩ V₃ = J₂₃`, `V₁ ∩ V₃ = ∅`, `J₁₂ ∩ J₂₃ = ∅`, and the pointwise seam
compatibilities (D3) `F₂ x = g (F₁ x)` on `J₁₂`, `F₃ x = g (F₂ x)` on `J₂₃`. The page trace is one
page from `U₁`, two disjoint pages from `U₂`, one from `U₃`; the raw sheets are
(outer `A`) ∪ (middle `C`) and (middle `A`) ∪ (outer `C`).
**Boundary and wall clauses are consequences**: from properness of the raw cell
`Δ' ∩ G⁻¹ H = ∂Δ'` (prove it from the source gluing — `G` is not normal on the seam, so do not
use a normality theorem), `N ∩ H = φ(Q × {0,1})` and neatness
`φ(Int Q × I) ⊂ Int_W N`: `x ∈ P ∩ ∂Δ' ⇔ t(coord x) ∈ {0,1}`, `F := closure(Δ' \ P)` is a
subpolyhedron, and `x ∈ P ∩ F ⇒ φ⁻¹(G x) ∈ ∂Q × I`. No separate transversality perturbation.
