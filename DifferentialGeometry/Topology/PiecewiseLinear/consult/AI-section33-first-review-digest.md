# Digest — first external review of `Skeleton/Section33Approximation.lean` (snapshot `fdf15d1c`)

Marks: **[V]** checked by the lead. **All twelve leaves OK — frozen.** One docstring tightening:
`hgD` (the boundary match sends `Dbd e` onto `Ec e ∩ frontier X`) is not an independent
obligation: from `IsTube.interEdge`, `splitProper` and the injectivity of `g`, `A_u ∩ A_v = Dbd e`;
kept as an output for the extension, no "dual cells have disjoint interiors" field.
**Conditional acceptance of the statements is not closure of the `Moise264` dependency.**

| Leaf | Verdict | Ruling |
|---|---|---|
| `exists_section33TubeFrame` | OK | AA risk 1 handled: small `h '' C v` first; the proved `exists_section33HandleFrame` then prescribes neighbourhoods by the compact sets' maximal distance plus slack and calls `Moise323` |
| `exists_isPolyhedralTubeNeighborhood` | OK | `Bd X` avoids centres and pseudo-cell rims; general position only on the locally polyhedral regular part |
| `exists_hasSinglePolygonTraces` | OK | **② keep the present form**: under `hd + h2` one trace splits `Eint` into the centre side and the outside, `E ∩ X` is the closed centre disk; equivalent to L3∧L4; L4 removes the outer annuli without recreating L3's bad circles |
| `exists_hasConnectedHandlePieces` | OK | **⑤ the equality is producible** (transversality makes each incident trace the intrinsic boundary of both sides); **⑥** delete core-free components, fill bounded complementary regions, keep the one trace, stay in `Int N'` |
| `exists_hasNoHandleLoopTheoremDisk` | OK | ⑥ the order alone is not enough, but the operation preserves the invariants: compress off all `E` first, keep the component separating all of `K'` from `Bd N'`; the traces survive, re-apply L6, first Betti number strictly drops |
| `section33_disk_meets_graph` | OK | **④ the worker's reading is right**: the printed "all of `Δ` misses other `Cpp`" contradicts the non-empty `Bd Δ ⊆ E₁`; the most literal repair is "`Int Δ` misses other `Cpp`", which agrees with the present `hmiss` under the overlap clauses and `hbd` |
| `section33_not_isLoopTheoremDisk` | OK | `h8` supplies the centre exclusion for innermost-circle removal, single-polygon traces the arc removal; the measure is the total number of components of LTD ∩ pseudo-cells; no extra L6 |
| `section33_tube_product` | OK | `derivedModel` is a genuine regular-neighbourhood structure; transport the source de-cored product by `h` |
| `section33_fundamentalGroup_map_bijective` | OK | **① keep `h264` explicit**; **③ `N' − K'` may stay**: after proving on `Int N' − K'`, a boundary collar gives the inclusion isomorphism |
| `section33_faceEulerChar_handlePiece` | OK | `2 − deg v` is right (planar surface with `deg v` boundary components; AA §7's "disk with `deg v` holes" is off by one); the global Euler identity plus capping bounds force equality piecewise, no direct 22.9 |
| `exists_section33BoundaryMatch` | OK | orientation compatibility of the matched boundaries is forced by orientability of embedded closed surfaces; `hgD` derivable, harmless as output |
| `exists_section33Extension` | OK | **⑦ closed**: `Cpp v` compact, so cap scales can be chosen with `d_v + 2δ < ε/4`; small caps, label preservation and cell extension produce `hfv`, `hfsmall`; no `f v = h v` assumption needed |

**Accounting boundary [V].** Chain `Moise323 → Moise324 → Moise264 → Moise331`. The ledger plans
only a *restricted* producer of the extended loop theorem via the orientable loop route; it is not
a proof of the present full `Moise264`. At integration the parameter may be narrowed to the `ℝ³`
local version; it must not be deleted to hide the dependency inside Lemma 10, whose proof must
also enclose the compact support of a null-homotopy in a finite PL 3-manifold inside `Int N' − K'`.
**⑦ arithmetic [V]:** with `y ∈ C_v`, `f y = h v` from `hfv`: `d(fx, hx) ≤ d(fx, fy) + d(hv, hx) < ε/4 + ε/4`;
the smallness is the extension's *conclusion*.

**Owed:** no geometric hypothesis to add to the `X` invariants; the restricted producer of the
extended loop theorem and its exact accounting; the collar bridge is leaf 9's proof duty.
**Fixture (geometric, not a Lean inhabitant):** a small triangle core with its polyhedral solid
torus, a non-identity affine shear `h`, `Ec = h '' D`, `Cpp = h '' C`, an inner solid torus `X`.
**Likely surprise:** the small caps of leaf 12 must keep disjointness, the fixed traces and the
vertex labels at once; "each new sphere is small" does not replace the last two.
