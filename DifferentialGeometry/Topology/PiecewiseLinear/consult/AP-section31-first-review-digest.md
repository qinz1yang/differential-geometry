# Digest — first external review of `Skeleton/Section31CanonicalConfiguration.lean` (snapshot `c1d5ba63`)

**All nine leaves OK — frozen.** Two docstring corrections and one interface FIX for the §31 → §32
hand-off (not a false leaf).

**Docstring.** L7's explanation misses a step: **28.11 gives an integer 1-cycle, not a polygon**; it
must be resolved into pairwise disjoint curves *inside the prescribed open set* and then 28.8
extracts the generator — count this normalisation as implementation work (the reviewer's "most
likely surprise"). ⑦ The two `standard` inhabitants clear "no non-degenerate model" but must be
labelled **CONDITIONALLY INHABITED**: they depend on reviewed leaves, and the canonical one on
`Moise307`; they are not independent sorry-free tests.

| Leaf | Verdict | Ruling |
|---|---|---|
| `isSpine_revolutionOf_of_mem_cellInterior` | OK | the product structure of the revolution gives the spine; ⑥ `moise312` correctly uses the tree's spine → `π₁` bijection, no `Moise308` |
| `revolutionOf_cellInterior_subset_interior` | OK | the open half-plane excludes the axis; a genuine 3-dimensional interior point |
| `exists_isTopologicalCellWithInterior_union_consecutive` | OK | ① **the `U`-transfer route is accepted**: the shared core makes both `π₁` maps to `U` isomorphisms; `apart`'s `P₂ ∉ D₀`, `P₁ ∉ D₂` suffice; no definition change, no symmetric L7 |
| `exists_innerSolidTorus_toroidalShell_of_annulusImage` | OK | ② true and exactly 30.7's missing input: an inner sub-cell containing the whole compact segment, its complementary annulus revolved into the shell, transported by `h`; calling it §31's deepest gap overstates it |
| `isCombinatorialSolidTorus_of_hasCylindricalDiagram` | OK | ④ the bridge is true; reversed disk gluing must be excluded; the verified with-boundary input is `Orientation.lean`'s `isOrientable_of_space_subset_convexHull` (a finite triangulation inside one 3-simplex); **the full signature of `isOrientable_euclidean_three` was not checked** — do not assert from its name that it covers the with-boundary case |
| `exists_generalPosition_solidTorus_triple` | OK | ③ input is exactly `hstep`'s full output (CST, annulus inside, strict outer containment; the shell is consumed by 30.7 and need not be passed on); but this finite conclusion gives no cross-triple compatibility |
| `exists_polygon_carrier_of_spine` | OK | ⑤ the right strengthening of 28.11 + single-polygon extraction, not a literal translation; no general position of the two tori needed; one-directional form may stay |
| `carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier` | OK | ⑤ the boundary-torus dichotomy; the **polygon-carrier special case** of 28.10 matching the strengthened L7 — not a claim to have proved the polyhedral-carrier version |
| `exists_isPLCell_frontier_of_polygon_nullhomotopic` | OK | a null-homotopic class excludes the longitudinal component; an essential boundary curve is then a meridian with linking number `±1` with the interior generator, so no disk avoiding the carrier exists |

## §31 → §32 interface: FIX (the worker's finding is right)
`(∀ i, ∃ admissible triple_i)` does not give `∃ (S''_i), ∀ i, (S''_i, S''_{i+1}, S''_{i+2})` admissible:
adjacent calls need not choose the same tori on the two shared indices, and `moise311` re-chooses
the whole `S'' : Fin 3 → Set E3` each time. **Expose the relative version — choose only the new
torus, the chosen ones fixed.** Extract the existing `hstep` as the single-torus producer and
derive L6 from the interface (suggested names, not existing identifiers):
```
Fits A U S := IsCombinatorialSolidTorus S ∧ A ⊆ interior S ∧ S ⊆ U
PairGP R S := frontier R and frontier S satisfy HasPLCrossingAt at every common point, and
             the intersection is a finite union of pairwise disjoint IsPLSphere 1 polygons
theorem exists_generalPosition_solidTorus_relative {A U S₀ : Set E3} {m : ℕ}
    (hA : IsCompact A) (hU : IsOpen U) (h₀ : Fits A U S₀)
    (F : Fin m → Set E3) (hF : ∀ i, IsCombinatorialSolidTorus (F i)) :
    ∃ S, Fits A U S ∧ ∀ i, PairGP S (F i)
```
`F` is a given parameter, never a re-chosen output. With `A = h(A_i)`, `U = Int h(S_i)`, enumerate the
integer indices in natural order, choosing each torus relative to the already chosen neighbours;
this makes all overlapping triples compatible. Approach to the boundary, approach to the centre
and local finiteness for §32 must still come from the outer control of the `S_i`, not from this
lemma. **Owed:** hoist the relative statement to a real module so the §32 tower leaf can consume it.

**Fixture:** the standard three-rectangle revolved chain under `h(x, y, z) = (x, y + |z|/10, z)`;
inside, fine polygonal annular cylinders at different heights with longitudinal polygons and
small boundary disks — not `h = id` or empty intersections.
