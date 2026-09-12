# Chart orientation comparison candidate

- Unregistered source-only candidate; imports current Homology for development. Root must migrate the proof block before `exists_unique_localOrientationClass`, importing only the lower LinearOrientation leaf. Never import this candidate back into Homology.
- Actual nonlinear derivative uses native coordinates and `OpenPartialHomeomorph.hasFDerivAt_symm`; no regularity away from the existing chart center is added. Positive determinant follows from the two existing orientation fields.
- The literal derivative blend is controlled in a convex target ball. A common positive radius controls the entire compact GL homotopy family; no homogeneity of its intermediate maps is assumed. Both full simplex families and boundary avoidance are constructed, then existing same-chart radius invariance recovers the original simplices.
- All bodies are source-written with no new placeholders; they are UNVERIFIED until the root's focused check and endpoint axiom audit. The candidate does not use the existing uniqueness theorem or its chosen local orientation class. Claim token: aa64b3bd-0825-40bf-8abe-2de32d8e7c43.

## Paused delivery — 2026-09-09

Final revised source SHA256: `9DA2D099740896AACB9EDB57C32AEA2946ED9EF4C8B7472ADAC3207ABFB3C39F`.
The earlier candidate produced eleven errors in a guarded warm REPL (5.968 s).
The worker revised those locations using native local tangent-space instances,
explicit derivative normalization, homotopy endpoints, and lambda continuity.
The user then stopped proof work: this final revision has NOT been checked,
lint-built, axiom-audited, registered, migrated into Homology, or committed.
Its source is retained verbatim in the handoff; no successful proof is claimed.

The warm setup (30.780 s, no errors) used the actual Homology source prefix
strictly before `exists_unique_localOrientationClass`, with lower imports,
and did not import Homology itself. Candidate evaluation always started at
that pre-target environment. The failed response environment must never be
reused. Requests, responses, and prefix hashes are in `Handoff/Evidence/repl/`;
the final revision is a separate snapshot. No corrected-success result,
wrong-proof control, independent saved-file check, or new target audit occurred.
The REPL and ordinary file claim were released at the user's stop request.
