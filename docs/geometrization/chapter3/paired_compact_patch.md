# Compact inner patch from the actual AC28 chart

Three public theorems in two leaves prove the compact-patch consequence
written immediately after AC28 in blueprint207A, lines3498–3507. A complete
metric subset with a bilipschitz map into a proper target and bounded image
is compact: the image is complete, hence closed, and bounded; target
properness gives compactness, which transfers along the embedding. This
uses properness ONLY of the Euclidean target, not of the source space.

The ball version allows any closed inner radius s<r, and assumes only that
this particular closed ball is complete. Its restricted chart image is
bounded by C*2s. The theorem also permits empty inner balls; the geometric
consumer supplies a strictly positive radius, so is not vacuous.

Under the exact AC28 hypotheses, the final theorem produces q in the
requested nonempty open O and s>0 such that the actual ambient closed ball
is contained in O and is compact. It restricts the already constructed
centered chart to min(r/2,R), where R is a complete-ball radius at q.
Completeness of the smaller closed ball is proved directly for Cauchy
filters; no ambient completeness or local compactness is inserted.

Blueprint207A's compact-patch paragraph and AC28 proof were reread. The
accepted source checks for that chart are reused. Mathlib at
c55e6e786f49471c72fbddbec5415808896aec1e supplies complete-image/embedding
proofs (Antilipschitz.lean145–184), compactness transfer
(Compactness/Compact.lean998–1034), Heine–Borel
(MetricSpace/Bounded.lean320–335), and the complete-set Cauchy-filter
criterion (UniformSpace/Cauchy.lean37–38,445–448).

This is a patch near some selected q in every eligible O. It does not yet
prove compactness at every prescribed point, the polynomial packing bound,
the intrinsic comparison adapter or AC33. Earlier mathematical leaves and
the PC migration boundary are preserved; Chapters3–4 are still incomplete.
