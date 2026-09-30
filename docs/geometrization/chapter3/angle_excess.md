# Full AC57: absolute excess from opposite comparison angles

Ten public theorems in five leaves establish the exact blueprint estimate

    0 <= 2L-c <= -(2/sqrt(sigma))*log(cos(sigma/2)) <= sigma^(3/2)/2.

Here 0<sigma<=1, the two actual distances from the basepoint are L>0,
c is the actual distance between the endpoints, and the comparison angle in
curvature -sigma is at least pi-sigma. The proof allows EVERY positive L;
the written AC57 length L=1/sigma is therefore a direct specialization.
No source curvature, geodesic, completeness or properness is assumed.
Curvature is passed as sigma, with hyperbolic scale sqrt(sigma).

The shared proof gives an exact squared half-angle identity for arbitrary
positive curvature magnitude kappa and equal positive arms, including degenerate
triangles. Cosine antitonicity gives the half-angle inequality for angular error
in [0,pi]. The log-shift inequality holds for every real A and 0<q<=1; it does
not silently assume A+log(q)>=0. A separate scalar estimate proves
-log(cos(t))<=t^2 for |t|<=1 using the cosine quadratic bound and
1-1/q<=log(q). This is an elementary alternative to the blueprint's derivative
and integral argument, with the SAME final numerical modulus. Real.rpow at 3/2
is explicitly identified with sigma*sqrt(sigma), so the exact constant is retained.

The metric wrapper derives BOTH triangle inequalities from actual distances.
The sequential theorem proves vanishing ABSOLUTE excess for varying metric
spaces and any positive arm lengths. Only eventual opposite-angle control is
needed. Sigma may exceed one at early indices; convergence to zero supplies the
needed late bound without discarding or reindexing the original source sequence.
No arm divergence is assumed by this estimate; AC59/61 uses it separately.
The boundary c=2L, angle pi, remains included. Sigma=0 is intentionally excluded.

Fresh source checks: blueprint207A AC57 full4990-5031; accepted ModelAngle
1-66 and ModelSide88-136; pinned AKP vol1 commit
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 model.tex71-95 and191-206;
archived AKP PDF printed/PDF15-17; retained July12,2026 erratum both pages.
The September26 retained erratum text is also read and agrees on the relevant
absence of model-trigonometry corrections. Published GSM236 erratum numbering,
archived PDF and pinned TeX are distinct. No current remote clearance is claimed.
The explicit numerical modulus is the blueprint calculation expanding KL4.15(2),
not a constant quoted from KL. Mathlib scalar dependency bodies and exact locators
are recorded in the source receipt.

An independent agent checked normalization, hypotheses, constants and edge cases;
a second agent implemented and compiled the half-angle pair. Root reviewed the
actual proof and integrates, builds, lints and audits all leaves. AC57 is complete.
AC61 assembly is next; common multi-axis splitting and cross-pair orthogonality
remain separate unfinished work. Earlier accepted mathematical leaves and the
frozen blueprint207 are unchanged. Migration interfaces remain paused.
