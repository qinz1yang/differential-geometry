# FiniteHornArmSubsequence

Owner: Chapter25 continuation; claim 87c1b7a6-7217-41ca-ab3f-d0e01a8b56cc.
Saved focused4 EMPTY on 2026-09-09 (26.110s), SHA256
5bdb5b2bdbe402fecf0e4a4d0bb85e04a2cfebeb27261ba7dbfead65b7578211.
Named1 own-leaf lint-clean (90.529s) and fresh audit1 (26.460s) passed;
the public endpoint depends only on propext, Classical.choice and Quot.sound.
Landed as 9b2913896; all source and root claims released16:21:31 UTC.
Final refresh exceeded the nominal return time by about one minute; the
actual handback was published only after all owned workers exited. Reserve
more than two minutes for the final refresh/audit of this large import cone.
Checks1/3 stopped before elaboration with read failures on different old,
unchanged upstream artifacts. Check2 reached the zero-parameter simp goal;
the saved fix passed check4 after the unrelated CircleEngineProbe exited.
No upstream artifact was rebuilt to address the transient read failures.

Combine the actual compact-tail closure, uniform whole-segment subsequence
selection, and completion-segment identification. Normalized minimizing arms
from bases approaching the missing endpoint to a fixed strictly interior
point on an extendible ray have a subsequence converging uniformly to that
prescribed ray, including the endpoint value in the completion. All input
curve data are exactly what CommonArms produces after normalization; no
convergence or limiting-ray identification is assumed.

Following assembly: select for one arm and then the other; composition of
the two strict subsequences preserves the first uniform limit and every
whole-arm/connector field. For a requested interval ending at a.length,
truncate outer target radii upward to a.length and diagonalize. Parameters
may be clamped at the truncated endpoint (RayApproximation requires monotone,
not strictly monotone, parameters); no unproved extension beyond the ray's
given length is needed. These assembly steps are not yet claimed proved.

Concrete diagonal route: for each requested arm choose strict outer radii
r(n) tending to min(a.length, D), with D greater than the requested near-end
cutoff. Each fixed n supplies a common-base two-arm family and two composed
uniform subsequences. Choose one large index in that family for tolerance
1/(n+1), simultaneously controlling both arm lengths, base distance and
uniform errors. Use parameter (length/r(n))*min(s,r(n)). It is monotone and
stays on the whole approximating arm; clamping error tends uniformly to zero
on the requested interval even when hi=a.length. All cross-connectors and
closed tail buffers are inherited from CommonArms. This still needs actual
Lean assembly and retains the explicit collar-depth requirement.
