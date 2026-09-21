# Digest — external review of the A1 skeleton, ninth iteration (wall-adapted design; snapshot `b2208776`)

Marks: **[V]** checked by the lead; **[–]** not independently verified.
Docstring claim wrong: "fixed 3-cells / 2-dimensional walls / 1-skeleton" is **not guaranteed by the
present types** (the wall system is a family of unrelated sets); and the docstring's free boundary
fixture is excluded by the present `hgenfold`. The eight frozen statements need no change. All
defects are interface defects of the abstract wall system and missing pass-through hypotheses — the
design of `consult/Y-…` stands.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_commonWallComplex` | **FIX** | the output lacks genuine dimensions, cell incidence and a supply of the walls' local flatness |
| `wallProductBlock_transport` | **FALSE [V]** | `cellInt c ⊆ cell c` is not required (lead checked: the leaf does not receive `hcellsub`); nor that the old chart is adapted to the actual pair |
| `hasStableCrossingBlocks_of_wallProductBlocks` | **FALSE [V]** | the same fake-cell counterexample; the missing item is not `Q' ⊆ C` |
| `wallProductBlocks_stable_on_fixedSubdivision` | **FALSE [–]** | the base interpolation on the final `R` is not required to equal `D` |
| `exists_wallGenericVertexMap` | **FALSE [–]** | `skel1` may be the whole space; and free boundary double points are wrongly forbidden |
| `wallProductBlocks_of_wallGenericity` | **FALSE [V]** | `hfiber` constrains the old `D`, not the new `g` (lead checked) — triple points allowed |

## 1. Wall system, transport, finite subcover
**Fake cells:** `cell * = ∅`, `cellInt * = M`, no walls, `skel1 = ∅`: type (i) blocks exist and every `haff`
clause is vacuous. `M = ℝ³`, `C = {t ≥ 0}`, two flat sheets `y = 0`, `y = x` near height 4,
`A(x,y,t) = (y, y − x, t − 4)`, `La = Lb = 0`, `η = 1`; second chart = the bent `H` of consult U: both
sheets bend, no transverse affine slice has a straight sheet, so `La·Lb = 0` is impossible.
**Repair — a genuine certificate produced by the first leaf and passed on:** `𝒬` a finite common
subdivision of the existing double complex, `ρ : |𝒬| ≅_PL M`, `cell σ = ρ(|σ|)`,
`cellInt σ = ρ(relint |σ|)`, `wall F = ρ(|F|)`, `skel1 = ρ(|𝒬^(1)|)`; `C`, `BdM` designated subcomplexes;
every chart adapted to that pair and affine on the relevant simplices; keep the buffers and the
star clause. Then the wall/3-cell incidence gives `wall w ⊆ Ea' i` and the present `hwallflat` becomes
usable. The producer cannot stay agnostic about `BdM`, `C`.
* **(i) no span clause needed:** where a block crosses a wall, the type (ii) zero-set equality gives
  a relatively open piece of the wall plane; the two affine branches agree there, hence on the
  whole plane — (*) follows; make it a derived lemma.
* **(ii) no `Q' ⊆ C`:** the compact set is `K = Σ_f ∩ Q'`, `hmapC` gives `K ⊆ C`; boundary blocks give
  neighbourhoods relative to `C`; cover `K` with them.

## 2. Stability on the fixed subdivision
The leaf allows `p₀ = simplicialMap R (ec ∘ D) ≠ ec ∘ D`: the frozen seed outputs facewise
affineness, but the assembly discards it with `_`. Counterexample: true wall `x = 0`; interpolated
sheets `y = 0`, `y = x` (double line inside the wall); the old `D` has second sheet
`y = x + a·q(x,t)` with a PL bump `q` vanishing at all coarse vertices and equal to 1 near the point:
the old double line avoids the point, `Z` = that point has an old certificate, everything outside
frozen, `a` arbitrarily small; the original vertex values are admissible for every `τ`, yet the
interpolation always has the double line inside the wall. **Repair:** pass the seed's field
`hlinear : ∀ s ∈ R.faces, ∃ A₀ : E₂ →ᵃ[ℝ] E₃, EqOn (fun x => ecf i₀ (D x)) A₀ (convexHull ℝ ↑s)`.
Then `Lip ((p_φ − p₀) ∘ q_sheet⁻¹) ≤ C_{R,𝓑} ‖φ − φ₀‖_∞`. **Keep the fixed wall and its normal
coordinate, re-choose only the source sheets and the small box** — that is what keeps the new
block adapted to the same wall system; existence of an ordinary block is no substitute.

## 3. Generic producer
Besides `skel1 = M`: on a genuine wall system, two free boundary edges
`(−1,0,0)–(1,0,0)`, `(0,−1,0)–(0,1,0)` still cross on the physical boundary after any small
admissible perturbation; the crossing is on a source edge image and on a boundary wall — it
violates the present `hgenfold`. **Repair (same clause in producer and consumer):** the premise of
`hgenfold` is `IsFreeDoubleGerm R Ac g D.domain BdM y` (which contains `y ∉ BdM`), not
`FreeSourceGerm`; the physical boundary only has to avoid `skel1`. The producer also receives
`hlinear` (otherwise a coarse triangle with three boundary vertices is interpolated into the
boundary and density may fail). **(iii)** with genuine wall data and the new map's two-point
fibres, accumulation on both sides **suffices, no quantitative angle**: a wall point off the
source edge images has a straight local double set; accumulation on both sides forces a non-zero
wall-normal component; angle and block constants are taken after `φ`.

## 4. Recognition
Three free triangles whose planes cross at one point inside an open 3-cell, nine vertices under
the four-point guard: not excluded by the wall conditions, nor by the injectivity scale; the old
`D`'s two-point fibres do not constrain the new `g`; a two-sheet full-preimage block cannot cover a
triple point. Also nothing guarantees continuity across the gluing seam, so compactness of the new
double point set is unavailable. **Add** (both available in the assembly from `cl'` and `hcard'`
through `hbridge`): `(hgcont : ContinuousOn g D.domain)`,
`(hgfiber : ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)` with `g := regionGluedMap D (ecf i₀) R φ Rc`.

**Missing:** the genuine common wall certificate; `hlinear` on the final mesh; continuity and
two-point fibres of the new map. **Fixture:** in a double cube, `γ × [−1,1]` with `γ` through
`(−2,−1), (1,1), (−1,1), (2,−1)`, a genuine common subdivision, a non-zero small perturbation of free
vertices. **Most likely next surprise:** the fixed-mesh Lipschitz estimate across the frozen seam —
not another angle field.
