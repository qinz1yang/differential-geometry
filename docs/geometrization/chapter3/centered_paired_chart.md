# AC28: centered distance charts in every comparison neighborhood

Five public theorems and one definition complete AC28, building on the
accepted exact finite hierarchy and maximal packet selection. Given a
nontrivial metric space with actual continuous almost-short curves, a common
curvature-minus-one four-point comparison domain Omega, nonempty open
O contained in Omega, local complete closed balls at points of Omega,
and dimH(Omega)<=n for an integer n>=1, there is an actual point q in O,
1<=m<=n, anchors a:Fin(m)->X in Omega, and r>0 with B(q,r) contained in O.

The resulting homeomorphism from that ball onto an open subset of PiLp2
has EXACT coordinate value F(x)-F(q), where F_i(x)=dist(x,a_i). Its value
at q is zero. Both metric bounds hold with the blueprint constant
L_n=max(sqrt(n),(100*pi/tau_1)^2): L_n^(-1)*dist(x,y)<=dist(phi(x),phi(y))
<=L_n*dist(x,y). The definition explicitly squares the second maximum
argument. No normalization, improvement of quality, alternate chart or
uniform positive radius is assumed.

The uncentered intermediate chart retains its original anchors, quality
lower bound and sqrt(m) Lipschitz constant. The proof localizes the selected
strict pointwise packet to quality delta=2*tau_m=beta/100, supplies all
AC27 scale conditions, and uses maximality over all centers in O. Centering
is an exact isometric translation of these coordinates; its open image and
homeomorphism are constructed from the actual map. The dimension-only
inverse estimate follows from tau_1<=tau_(m+1).

Blueprint207A AC28 full statement/proof, lines3442–3515, was reread. The
prior BGP1992 Remark6.9, printed22/PDF23, and BBI/BGP source and correction
checks remain applicable and are reused. The project exact constants are
proved, not quoted as BGP's constants. Mathlib topology and inverse/Lipschitz
proofs are used at the pinned source revision.

This proves AC28 at its explicit metric scope. AC29's intrinsic/local
comparison adapter, transporting compactness/packing to every prescribed
point, curvature-to-covering production, AC47's global one-dimensional
classification and full AC48 remain open. No full Chapters3–4 completion,
PC migration acceptance or Riemannian integration is claimed.
