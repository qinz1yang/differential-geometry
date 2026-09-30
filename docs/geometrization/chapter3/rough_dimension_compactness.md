# AC17: compactness from actual finite rough dimension

Four public theorems in two leaves prove the blueprint's rough-dimension
compactness route. Vanishing actual rough volume gives finite packing
numbers at every sufficiently small positive scale. Finite rough dimension
supplies a nonnegative exponent with vanishing volume, by the defining
infimum. For every desired net radius choose a smaller positive scale
with finite packing, then use the accepted finite maximal-net theorem.
This proves total boundedness without assuming source completeness,
compactness, an infinite maximal separated set, or a polynomial estimate.

If a neighborhood S of p has finite rough dimension and some positive
closed ball at p is complete, a smaller closed ball inside S is complete
and totally bounded, hence compact. The comparison-domain consumer first
applies the accepted AC33 producer, then this generic theorem. It allows
all natural dimension bounds including zero and requires neither a
nontrivial-space instance nor a positive-rank assumption. It produces an
actual compact ambient closed ball at the prescribed point, contained in
the same open common comparison domain.

Blueprint207A AC17 full proof2890–2924 was reread, as were the AC33
consumer3769–3779 and BGP6.2 definition. The generic proof formalizes the
written finite-selection argument using the accepted MC02 maximal finite
net. Its limsup step uses Mathlib's eventually_lt_of_limsup_lt dual proof
in Order/LiminfLimsup.lean605–613; ENat.ne_top_iff_exists at
Data/ENat/Basic.lean324 preserves the actual finite value. Both source
bodies were read at c55e6e786f49471c72fbddbec5415808896aec1e.
Earlier BGP/BBI/errata checks and rough-dimension definitions are reused.

This supplies AC17's metric core and its actual common-comparison consumer
in the intended AC33-to-AC17 order. The separate intrinsic/ambient adapter
remains unbound, so the full controlled-region wrapper is not claimed.
Global AC47/full AC48 and family-uniform curvature-to-covering remain.
Blueprint207 and earlier leaves are unchanged; no full migrated-root or
PDF/Overleaf build is claimed.
