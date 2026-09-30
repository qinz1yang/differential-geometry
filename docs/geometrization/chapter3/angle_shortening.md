# Full AC63: numerical radial shortening and its exact angle limit

Ten public theorems in seven leaves prove the finite shortening inequality,
the clipped angle lower bound, its limiting value, the exact comparison-angle
liminf statement, and the original reciprocal-scale specialization.

For curvature parameter kappa>0 (curvature -kappa), equal original arms L>=r>0,
valid original/shortened sides c,d, and original comparison angle at least
0<theta, the only additional metric input is c-2(L-r)<=d. With
q=sin(theta/2), B=sqrt(kappa)*r, the result is

    q-(q inverse-q)/(exp(2B)-1) <= sin(shortenedAngle/2).

The actual metric theorem derives both side-triangle bounds and this tail-loss
inequality from the specified points p,a,b,ar,br and exact radial/tail distances.
It returns the explicit angle bound 2arcsin(max(0, the expression above)).
No source curvature, local compactness, completeness or geodesic existence is
assumed in this numerical step. Supplied radial minimizing segments provide
its distance hypotheses directly without changing their endpoints.

Shared lemmas prove the exact equal-side hyperbolic half-angle identity,
including degenerate sides, and the exact logarithmic sinh ratio. The ratio
requires only q>0 and B>0, even when B+log(q)<0. The finite shortening argument
uses q<=1 for the log shift, deriving theta<=pi from the original model angle.
No artificial positivity of the un-clipped lower bound is imposed; max0 is
essential when it is negative. Native kappa= lambda squared translates the
blueprint's lambda>0 convention via sqrt(kappa)=lambda; in the strainer case
kappa=sigma and lambda=sqrt(sigma).

The general limit theorem allows theta_i->theta0 in(0,pi] and B_i->infinity,
without restrictions on their early terms. The explicit clipped lower bound
tends to theta0. A separate theorem proves theta0<=liminf of the ACTUAL
shortened comparison angles, using the finite side/tail conditions and only
eventual original angle control. It handles theta0=pi as well as pi/2.

The reciprocal specialization proves sqrt(sigma_i)*(sigma_i inverse/C)->infinity
for EVERY fixed C>0 and sigma_i>0 tending to zero. It then proves that the exact
lower angle for theta_i=pi/2-sigma_i tends to pi/2. Taking C=1024 supplies ALG08's
radius L_i/1024 and its completed 256r<L buffer; C=100 is also a numerical
specialization. This does not claim the old sharp8r AC64 comparison theorem.

Fresh source bodies: blueprint207A AC63 full5303-5351 and ALG08 radius choice
7630-7643; pinned AKP vol1 commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245
model.tex71-95,191-206 and archived AKP printed/PDF15-17; KL Section3.3/Def3.6
printed22-23/PDF17-18 and4.15(2) printed31-32/PDF26-27. Independent review
rechecked normalization, all signs, degenerate triangles and sequence quantifiers.
AKP/KL retained corrections are reused unchanged; no current remote claim.
The modulus and constants100/256/1024 are blueprint calculations, not constants
quoted from AKP or KL. Mathlib scalar limit/clamp source locators are recorded.

AC63 is complete. The actual coarse-buffer comparison adapter and fixed-target
two-sign orthogonality helper are separate drafts. AC65 must use ONE extraction
of the SAME AC62 minimizing segments for both cross angles and coordinates.
Chapters3-4 and compatibility remain unfinished. Earlier accepted math,
blueprint207 and migration interfaces are unchanged.
