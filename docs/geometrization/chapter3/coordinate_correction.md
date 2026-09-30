# Largest-coordinate correction and exact preimages

Six public theorems in two new leaves prove AC22's finite-coordinate
arithmetic and compose it with AC14/AC23's complete-buffer convergence.
The target is Mathlib's actual `PiLp 1 (fun _ : iota => Real)`, with its
sum metric, not the default supremum metric on a function type.

## Exact scope

`Real.dist_le_mul_of_directed_step` handles both signs of a selected
coordinate residual. A directed move of size between alpha*h and h,
where h is that coordinate's distance to its target, cannot overshoot.
It reduces the selected residual to at most (1-alpha)*h.

`PiLp.dist_le_sub_of_coordinate_correction` adds the other coordinates:
if each changes by at most beta*h, the total residual decreases by
at least mu*h, where mu=alpha-(card(iota)-1)*beta. This budget theorem
requires a supplied index, so does not need a separate nonempty instance.
`dist_le_mul_of_largest_coordinate_correction` then uses maximality and
mu>=0 to prove e_next <= (1-mu/card(iota))*e.

`Metric.exists_residual_correction_of_coordinate_moves` chooses an actual
maximal coordinate in a nonempty finite index type and an actual point
y from supplied directed coordinate moves. It retains y's membership in
the supplied set V, proves e/card(iota)<=d(x,y)<=e, and proves both the
contraction and the displacement budget. The scale hypothesis is a bound
on EACH initial coordinate residual, as in AC22's maximum bound, rather
than the unnecessarily stronger e<=t0. Moves are actual changes of the
same supplied map f and have displacement exactly their length t.

`Metric.paired_correction_constants` proves the blueprint's exact bounds
for m>=1 and 0<delta<=1/(100*m):

    mu=1-3*delta^2-6*(m-1)*delta,
    9/10<=mu<1,  0<=1-mu/m<1.

Thus alpha=1-3*delta^2 and beta=6*delta give the stated AC22 constants,
including m=1. AC21's decrease toward the first anchor has the stronger
coefficient 1-delta^2; it may be weakened to the common alpha.

`Metric.exists_preimage_of_coordinate_moves` is the actual convergence
consumer. It assumes only a complete closed source ball and continuity
there, alpha<=1, beta>=0, mu>0, and initial residual e0<=min(t0,mu*r).
The coordinate-move premise is restricted to positive lengths at most
both t0 and e0; no move outside that scale range is requested. Correction
witnesses need not belong to the complete ball. The previous invariant
proves containment and yields a point in that SAME ball mapping exactly
to the target, with distance from the center at most e0/mu. Zero initial
residuals and solutions on the complete-ball boundary are included.

## Sources actually checked

Blueprint207A AC21–AC23, especially AC22's statement and full proof in
lines3123–3156, were read, with revision65's source comparison. BGP1992
English proof5.8 (printed19/PDF20) and BBI2001 Proposition10.8.15's full
proof (printed385–386/PDF400–401) motivate the largest-coordinate method.
The exact constants and negative-curvature route are project estimates,
not printed-source constants. The fresh reading and hashes from the
immediately preceding residual-correction milestone are reused unchanged.
The retained July6,2024 BBI author errata and bounded BGP errata search
have the same scope and qualifications as that record. No omitted
geometric source argument is imported as a Lean premise in disguise.

## Remaining producers

The explicit coordinate-move hypotheses still need AC19–AC21's geometric
proofs from a common paired packet. This milestone proves their finite
coordinate consequence, not those geometric inputs, full AC23, AC46, or
curvature-to-covering production. No migration interface or existing
mathematical leaf is changed. Builds, transitive axiom checks, declaration
linters and compiled nonvacuous consumers are recorded in the review.
