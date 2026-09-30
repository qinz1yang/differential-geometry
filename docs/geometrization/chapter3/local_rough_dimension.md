# AC18 and the AC33 local rough-dimension producer

Nine public theorems and two definitions in four leaves supply the real
asymptotic estimate, actual rough volume/dimension, zero-dimensional branch,
and the geometric local producer. The definitions retain BGP6.2 and the
blueprint convention: non-strict finite packing, possibly infinite, and
roughVolume(a,S)=limsup as epsilon decreases to zero of
ofReal(epsilon^a) * P_S(epsilon), in ENNReal. roughDim is the infimum over
nonnegative real exponents whose rough volume is zero; an empty index set
gives infinity. The definitions extend to arbitrary sets; boundedness is
not silently substituted for finite packing.

For a polynomial floor bound (1+C/epsilon)^m with C>=0, the weighted
packing function tends to zero for EVERY b>m. The real identity is
 epsilon^b (1+C/epsilon)^m = epsilon^(b-m) (epsilon+C)^m
on positive epsilon. Squeezing in ENNReal yields roughVolume(b,S)=0 and
roughDim(S)<=m. Infinite ENat packing is coerced order-preservingly, not
sent to a finite default. The critical exponent is not claimed to vanish.
Empty and singleton sets have packing at most one and rough dimension zero.

AC18 is proved in the stronger continuous-curve setting: if every point is
joined to p by a continuous curve and a positive ball at p has dimH<1,
the entire space is a singleton. A nonconstant curve and the distance map
produce a nondegenerate interval in the image of that ball; Lipschitz
monotonicity forces dimension at least one. No curvature, completeness,
rectifiability or minimizing segment is required for this implication.

The geometric producer assumes almost-shortest continuous curves, an open
common four-point comparison domain at curvature minus one, locally
complete closed balls there, and its actual Hausdorff bound dimH<=n.
For every prescribed p, it gives h>0 with B(p,h) inside the domain, a
natural m<=n, roughDim(B(p,h))<=m, and vanishing rough volume for every
b>m, all on the SAME ball. No positivity restriction on n or nontriviality
assumption remains: AC18 supplies the positive-rank branch when needed,
and the singleton branch uses m=0. Constants/radii are not family-uniform.

Source checks: BGP Definition6.2 printed20/PDF21, full body; Lemmas6.3–6.4
printed20–21/PDF21–22; BBI Corollary10.8.20 printed388–389/PDF403–404 and
retained errata PDF13; blueprint207A definitions2832–2848, AC18 2930–2946,
and AC33 3730–3768. The scalar proof is elementary and checked directly.
Mathlib proof bodies for rpow subtraction/continuity, ENat-to-ENNReal order,
ENNReal ofReal multiplication, limsup of a convergent function, Lipschitz
Hausdorff monotonicity and interval dimension were read at the pinned commit.

This finishes AC18 and AC33's explicit common-comparison metric core,
including its rough-dimension conclusion. It does not bind the separate
intrinsic/ambient comparison adapter or assert the global equality of
rough and Hausdorff dimensions. Global AC47, full AC48 and family-uniform
curvature-to-covering production remain. Chapters3–4 and the migration
are still incomplete. Blueprint207 and earlier mathematical leaves stay
unchanged; no new PDF/Overleaf or migrated-root build is claimed.
