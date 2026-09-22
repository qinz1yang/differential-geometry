# Annular separator surgery: first review and lead due diligence

Date: 2026-09-22. Owner-supplied answer to [AW](AW-section30-separation-review-request.md),
against mirror `e9735916425f40f5b34f3eda3287e32e9bcc6212`.

**`exists_annular_split_ball`: OK and frozen; proof OPEN.** The lead and an independent
read-only reviewer checked the complete output fields, assembly and explicit fixture.
No missing endpoint assumption, complete counterexample or substantive disagreement was
found. A relative neighborhood equality needs the precise formulation below.

## The joint geometric construction

`hnear` supplies an open neighborhood `V` of the common disk such that
`C ∩ V = (D₁ ∪ D₂) ∩ V`; it does not assert `C ∩ V = D₁ ∪ D₂` without restriction.
The whole relatively closed set `C` need not be a finite polyhedron. Work locally in `V∩Ω`
with a common finite subdivision of the disks and their intrinsic boundaries. A sufficiently
small compatible derived neighborhood must respect the three-page edge sections, the
shared arcs in vertex links, and all endpoints and seams.

The reviewed route sets `E_i=N∩D_i` and `A_i=closure(E_i\Δ)`. The relevant `Q` is the
closed side of the disk cut containing `A₁`, with

\[
\partial Q=E_2\cup\Delta_1\cup S,\qquad
\partial Q\cap C'=E_2\cup\Delta_1.
\]

The interior of the closed annulus `S` avoids the original `C`. Replacing `Q` by all of `N`
would leave a second, disjoint open disk on the safe boundary. The exact annulus formula,
not merely the abstract homeomorphism type, is required for rerouting.

There are existing ingredients: `SeparatingSurface` gives a finite ambient manifold
neighborhood for compact data; `SurfaceSplitCompatibleSubdivision` and `SurfaceSplitLocalTrace`
give compatible subdivision, local cut and trace data with an explicit finite ambient
manifold input. They do not certify that arbitrary `C` is PL and do not yet supply this
entire frozen package. `exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk` can support the
boundary parametrization. The same choice of neighborhood, cut ball, new disk, annulus and
end circles must still be assembled; no added transversality assumption or 30.3 input is
available to bypass this work.

In particular, `exists_surface_split_local_traces_with_side_trace` currently writes its
whole ball boundary as the second disk together with a complementary **large disk**, and
its own replacement covers that whole boundary. Substituting that large disk directly for
the frozen leaf's new disk would leave no safe annulus. One must choose the smaller disk
bounded by the fixed first outer circle, retaining the annulus between the two outer circles;
the sphere disk-pair and disjoint filling APIs are ingredients for this remaining step.

## The separation assembly

The leaf contains neither the target sets nor a separation hypothesis/conclusion. In
`moise303`, the ambient-open `O` and its exact trace prove that the replacement is relatively
closed in `M`. The entire deleted annulus and new disk lie in `Q`, so the old and new sets
agree outside `Q`; `Q⊆Ω` keeps both targets outside it. The safe annulus is path connected
and avoids the old separator. `JoinedIn.compl_of_frontier_replacement` performs actual
rerouting, and `separates_of_not_joinedIn` gives separation by grouping all components that
meet the first target. The targets need not be connected. The named signature is unchanged.

The lead visually checked printed p.215. Its proof explicitly distinguishes the full
regular neighborhood's annulus-plus-disk boundary from the selected cut three-cell used
to reroute the path. The current interface retains that distinction.

## Complete paper fixture

Let `P=[-1,1]²`, `P_b=[-b,b]²`, `ρ=max(|x|,|y|)`, and set

\[
\begin{gathered}
M=\mathbb R^3,\quad C=\partial(P\times[-1,1])\cup\Delta,\quad\Delta=P\times\{0\},\\
D_1=\Delta\cup(\partial P\times[0,1/4]),\quad
D_2=\Delta\cup(\partial P\times[-1/4,0]),\\
\Omega=(-3/2,3/2)^2\times(-1/2,1/2).
\end{gathered}
\]

All three disks have PL simplex parametrizations. Their required exact intersection and
intrinsic-interior containments hold; `|z|<1/4` witnesses the relative neighborhood condition.
Use `H={(0,0,3/4),(0,0,-3/4)}` and `K={(3,0,0)}`, outside `Ω`.

For `0<e<1/8`, `b=1+e`, choose

\[
\begin{gathered}
N=P_b\times[-e,e],\quad Q=N\cap(\{z\ge0\}\cup\{\rho\ge1\}),\\
A_1=\partial P\times[0,e],\quad\Delta_1=P\times\{e\},\quad
J_1=\partial P\times\{e\},\quad O=\{0<z<e\}.
\end{gathered}
\]

`O` is ambient open; the leaf does not require `O⊆Ω`. Its trace is exactly
`C∩O=∂P×(0,e)`. The whole `A₁`, including both ends, and `Δ₁` lie in `Q⊆Ω`.
The upper box and four lower side boxes can be chosen with disjoint interiors and attached
successively along disks, giving a PL three-ball; a union-of-boxes assertion alone would
not prove ballness.

Put `J₂=∂P×{-e}` and

\[
S=((P_b\setminus\operatorname{Int}P)\times\{-e,e\})
  \cup(\partial P_b\times[-e,e]).
\]

Then `S∩C=J₁∪J₂` and `frontier Q\C'=S\(J₁∪J₂)` exactly. Use `J=∂P×{0}` and the
four parameter levels `0,1/3,2/3,1`, with corner images on the upper inner, upper outer,
lower outer and lower inner circles. The twelve rectangles give twenty-four triangles;
affine extension maps them to nondegenerate convex trapezoids or vertical rectangles,
agrees on common edges and keeps both end circles injective. The open product has exactly
the safe-boundary image. Continuous scaling `λ(t)q` is generally bilinear and is not this PL
construction.

The replacement is precisely
`C'=∂(P×[-1,0]) ∪ ∂(P×[e,1])`. The two retained box interiors contain the two `H` points;
the exterior contains `K`. Thus the fixture also checks disconnected targets. This is a
paper verification, **not a compiled joint Lean fixture: UNTESTED remains**.

## Verification boundary

The geometric leaf and shared Lean fixture remain OPEN/UNTESTED. No extra leaf or endpoint
assumption was added. Only module documentation changes; the full leaf, scopes and assembly
are unchanged from AW. The private lead evidence directory
`claude-moise-agent-c/fill-interface-evidence-20260922` retains
`four-producer-review-snapshot-comparison.json`, `four-producer-frozen-review.json` and the
unchanged-source `Section30Separation-audit.json`. The final lease-c check passed with Lean
exit 0, a stable source hash and only one authorized leaf-sorry warning. No completed producer or full root build is claimed.
The sole progress entry is `FREE_INPUTS.md` B1.k.

Final check UTC: `2026-09-22T13:28:06.4191447Z`. Checked source SHA-256:
`7a258b8caa58106947bab6413d628c04270b77cac3e25c46763fb1f3593bc8c7`.
