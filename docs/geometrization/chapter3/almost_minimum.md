# Almost minimum using one complete closed ball

One public theorem proves ALG03 with the exact radius r(o)/epsilon^2,
0<epsilon<1. The radius function is an actual positive real-valued function.
It need not be continuous. Positive local lower bounds are required only
at points of the complete closed ball. The selected p lies in that ball,
satisfies r(p)<=r(o), and for EVERY q in the ambient space with
d(p,q)<=r(p)/epsilon satisfies r(q)>(1-epsilon)*r(p). The quantifier is not
restricted to the original complete ball.

The proof argues by contradiction and selects a geometric descent inside
S={x | epsilon^2*d(x,o)+r(x)<=r(o)}. The triangle inequality and each
relative decrease keep every new point in S, although it is chosen in
the full space. Positivity puts S inside the required complete closed ball.
Geometrically summable step lengths give a Cauchy sequence in that ball.
Its radius values tend to zero, contradicting the local positive lower
bound at its actual limit. No compactness, ambient completeness, smoothness,
curvature, or length-space hypothesis is used. The non-strict distance
threshold is retained both in the conclusion and in the negated step.

Sources: frozen blueprint207A ALG03, lines7416-7445, and pinned AKP
vol1 ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, defs-CBB.tex1091-1130,
lem:alm-min, full statement and proof. The source's complete-space and
sequential lower-bound presentation is adapted as written in the blueprint
to one complete subset and explicit neighborhood lower bounds. The proof
handles the non-strict step bound directly, without importing a strict-step
assertion from the source text. Existing PointPicking was inspected: its
compactness and continuity hypotheses do not provide this contract.
Mathlib's geometric Cauchy and complete-subset convergence proofs and the
accepted ResidualCorrection proof pattern were read and reused. Exact source
hashes and locators are in evidence/almost_minimum_sources.json.

This proves ALG03. The cradle, its use in globalization and the remaining
localization consumers are separate unfinished work. Blueprint207 and all
earlier mathematical leaves remain unchanged. No PC migration dependency
is introduced.
