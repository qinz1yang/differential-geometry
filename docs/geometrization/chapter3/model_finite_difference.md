# Hyperbolic finite differences: AC19

Five public theorems in two new leaves prove the uniform model estimate
AC19 and its actual metric-triangle application. The comparison angle
is the existing `comparisonAngleNegCurvature 1`: actual curvature -1.

For a>0, a<=r<=A, 0<t<=min(1,a/2), and |r-t|<=c<=r+t,
the scalar theorem proves exactly

    |c-r+t*cos(theta)| <= (4*cosh(A+1)/sinh(a))*t^2.

The metric theorem substitutes r=d(x,z), t=d(x,y), c=d(y,z) and
proves the triangle inequalities itself. It requires no curvature,
completeness, length-space structure, tangent angle or minimizing curve.
Degenerate triangles at both extremes are retained. The anchor and
short-side positivity hypotheses justify the actual cosine law.

Three analytic lemmas prove cosh(t)-1<=t^2 and |sinh(t)-t|<=t^2
on [0,1], and an explicit cosh linear-remainder bound on a positive
interval. Convexity of cosh(sqrt(x)), already proved in this branch,
gives the first small-argument bound; the mean-value theorem gives
the other bounds. The remainder estimate used here is M*t^2 with
M=cosh(A+1), weaker than the blueprint's intermediate (M/2)*t^2
Taylor estimate. The three resulting error terms sum to at most
3*M*t^2, so the theorem still proves the EXACT advertised constant
4*M/sinh(a). No stronger intermediate Taylor claim is made.

## Sources and scope

Reopened blueprint207A AC19, full statement and proof, lines2980–3011,
and AC20's adjacent statement/proof to check the intended later use.
Reopened the pinned AKP vol1 source at commit
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, model.tex lines74–90 and
174–211, for curvature-minus-one functions and the model cosine law.
The project constant is not an AKP constant. The source identities and
author-errata checks retained in the preceding model/curvature milestones
are reused where unchanged. This proof imports no local-to-global or
geodesic comparison theorem. Exact hashes are recorded in the source receipt.

The geometric almost-radial point AC20 and paired moves AC21 remain
separate producers. AC22's arithmetic and AC23's complete-buffer consumer
were proved in prior checkpoints, but full local openness from the
geometric paired packet is not yet claimed. Earlier mathematical leaves,
blueprint207 and migration interfaces remain unchanged.
