# Almost-radial points without minimizing curves: AC20

Six public theorems in three new leaves prove AC20, including the
blueprint's exact C and nu and the containment of the initial curve.
One private analytic helper is also audited.

The metric leaf first constructs the least parameter where a continuous
curve reaches a prescribed radius. Compactness of its PARAMETER interval,
not compactness or completeness of the metric space, gives the first hit.
The intermediate-value theorem proves every earlier point stays in the
closed ball. Actual variation additivity bounds the remaining endpoint
distance. The arbitrary-short-curve consumer retains the same whole curve,
its length bound, its first-hit point and all initial containment evidence.
Both zero radius and radius equal to the endpoint distance are allowed.

The model leaf bounds two comparison angles from a small triangle excess.
It uses the actual hyperbolic cosine law, positive adjacent sides and a
mean-value bound for cosh. The excess budget is the explicit inequality

    sinh(A+1)*eta <= (1-cos(delta))*sinh(a/2)*t.

The angular tolerance need only be nonnegative in this scalar lemma;
no unnecessary upper bound is imposed. In the AC20 application it satisfies
the blueprint's 0<delta<=1/100. The scalar near-straight triangle is built
from the same actual distances produced by the curve theorem.

The final theorem proves C=sinh(A+1)/sinh(a/2)>0 implicitly in the
constant calculation and explicitly proves positivity and all required
bounds for nu=min(delta^2,min((1-cos(delta))/C,1)). It constructs y with

    d(p,y)=t,
    r-t <= d(y,u) < r-t+nu*t,
    angle_y(u,p) >= pi-delta,  angle_p(u,y) <= delta,
    (1-delta^2)*t <= r-d(y,u) <= t.

It also retains an actual continuous p-to-u curve of variation less than
r+nu*t, a parameter at y, and containment of its entire initial portion
in the same closed t-ball. Thus no minimizing segment, properness, tangent
space or curvature assumption has entered before the later geometric moves.
The rest of the almost-short curve need not remain in that ball.

## Source and comparison checks

Read blueprint207A AC20's complete statement/proof, lines3013–3054,
with AC19 and AC21's neighboring contracts. Reuse the unchanged pinned
AKP model.tex cosine-law source and exact revision from the AC19 receipt.
BGP1992 proof5.8 and BBI2001 Proposition10.8.15 motivate the almost-short
correction route; the fresh reading and author-errata qualifications from
the residual-correction receipt are reused. The explicit negative-curvature
constants and scale-dependent path excess are project estimates, not
printed BGP/BBI constants. No omitted source argument is imported.

## Remaining scope

AC21 still needs to use the four-point inequalities at the actual endpoints
in one comparison neighborhood to derive the paired and cross-coordinate
moves. AC22 arithmetic and AC23 complete-buffer convergence are already
proved, but full geometric local openness is not claimed here. The original
migration boundary and blueprint207 remain unchanged. Verification and
compiled nonvacuous examples are recorded in the review.
