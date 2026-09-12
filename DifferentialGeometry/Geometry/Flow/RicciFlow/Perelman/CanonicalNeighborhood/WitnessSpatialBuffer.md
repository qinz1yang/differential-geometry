# WitnessSpatialBuffer

Chapter25 task; claimfaeb826a-8480-4bbf-9379-b24db5919e4d.
VERIFIED 2026-09-10: saved check7 EMPTY24.04s, named refresh1 passed36.11s,
fresh WitnessSpatialAxioms1 passed23.20s, all four publics standard-only.
Receipt: E:/lean-tools/chapter25-book-20260910/witness-spatial-completion.json.

Book witness openness needs room for moving the normalized model center.
The original embedding already contains a compact closed unit-buffered ball;
its open source therefore contains a strictly larger closed ball. The proof
minimizes actual Riemannian extended distance on the compact part of the
complement inside radius R+1. It needs no connectedness hypothesis and does
not replace the actual distance with a chosen compatible metric.

The witness consumer supplies completeness and compactness from its actual
ancient model. The same embedding is retained. A common eta also allows every
center within eta and every radius at most R+eta, using the actual distance
triangle inequality. This is only the spatial-room step; it does not prove
renormalization, time-jet perturbation, source capture after
renormalization, or openness. Next use scalar normalization near the model
basepoint and the strict finite-jet margin on the common smaller domain.

Receipts: E:/lean-tools/chapter25-book-20260910/. Compiler and claim ownership
remain controlled by WORKING_STATUS.md.

Lean details: `continuous_riemannianEDist` is in Geometry.Riemannian and requires
its explicit continuity import here. The triangle inequality is in Manifold.
For the latter, open Bundle to enable its scoped Riemannian fiber instances,
and locally disable the Tensor0SBundle tangent norm instances as DistanceScaling
does. Otherwise the actual g-induced norm is replaced by the ambient model norm,
or no ENorm family can be synthesized. No global instance was changed.
