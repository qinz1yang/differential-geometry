# Digest — first external review of `Skeleton/PLSmoothingCompact.lean` (C1; snapshot `93051952`)

**All eleven leaves OK — frozen with their present signatures.** Scope §4's supply notes
corrected: L3/L4 smooth only the *image* of the attaching region, not `ψ`; parameter matching
belongs to the attachment leaves; L7's cone extension settles topological matching only, not the
smooth collar cap.

| Leaf | Verdict | Ruling |
|---|---|---|
| `boundaryComplex_space_of_isPLCellAttachmentWith_zero` | OK | attached ball disjoint from the old stage; the whole sphere is added; `hatt`'s fixed map and quotient identification exclude extra points |
| `…_one` | OK | removes the *relative interiors* of the two end disks, adds the side annulus; both end circles stay in the boundary |
| `…_two` | OK | removes the relative interior of the side annulus, adds the two end disks — not the whole closed annulus |
| `…_three` | OK | the attaching sphere is one whole old boundary component, which disappears; no connectedness of the old stage needed; all four traces are intrinsic-boundary computations compatible with PL boundary invariance |
| `isSmoothHandleStage_adjunction_zero` | OK | empty attaching region, disjoint union; the standard smooth 3-ball gives the boundary correspondence; no taming input |
| `exists_homeomorph_smooth_disks_of_isClosedEmbedding` | OK | L5 may be internal: build the boundary isotopy from the identity and extend through a collar (not "every boundary self-homeomorphism extends"); compactness gives the compact boundary and σ-compactness the collar needs |
| `isSmoothHandleStage_adjunction_one` | OK | consumes exactly `θ ∘ ψ` after L3; the image condition suffices, but the proof first aligns the orientations/parameters of the two smooth disks, adds free annuli, extends to the ball — `ψ` is not a smooth map |
| `exists_homeomorph_smooth_annulus_of_isClosedEmbedding` | OK | L5 internal likewise; `S¹ × ℝ` gives smooth room on both sides of the closed annulus; the embedded annulus carries its framing, no orientability needed |
| `isSmoothHandleStage_adjunction_two` | OK | consumes `θ ∘ ψ` after L4; the annulus parameter difference is absorbed by first filling the two end disks, then extending to the ball; only a homeomorphic smooth model is asked, so no smoothness of `ψ` is missing |
| `exists_isSmoothEmbedding_sphere_of_isClosedEmbedding` | OK | by invariance of domain and compactness `range ψ` is a closed-and-open sphere component of the boundary, never wild; take the abstract smooth surface inside the leaf, recognise the 2-sphere, compose with the boundary inclusion; uniqueness of smooth structures in dimension two supports the identification; no abstract-surface signature needed |
| `isSmoothHandleStage_adjunction_three` | OK | consumes **L6**, not L3/L4; `hdbd` from `hψbd` and the image equation; smooth collar cap first, cone extension absorbs the parameter difference, remaining boundary right |

**Owed:** nothing to add to signatures or as a separate leaf; parameter extension, corner rounding
and exact boundary identification are proof duties of the attachment leaves. ① `IsSmoothHandleStage`
suffices: the smooth model may be re-chosen at every step; only the homeomorphism and the boundary
equation are kept. ⑤ empty `X → IsManifold.empty`; final stage `∂M = ∅` → `interiorChartedSpace` →
pull back along `Homeomorph.ulift`: closed. ⑥ no simple connectivity, connectedness or
orientability of the input is used. **Fixture:** a finite PL triangulation of `S¹ × S²` (triangle
loop × tetrahedron boundary) with its actual derived-neighbourhood filtration — all four handle
kinds occur; stage homeomorphisms may be non-smooth, non-identity collar conjugates to test
genuine taming. **Likely surprise:** L6, the smooth 2-sphere recognition, stays an independent
deep producer; the "embedded image" form tidies the interface but removes none of that work, and
no topological Alexander extension or 3-dimensional Poincaré argument may replace it.
