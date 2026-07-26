# RzMaster

## Result

All 64 settled residual reductions remain private in one compact module. The only
public result is `master_nf`, the complete finite-index zeroth-order DeTurck normal
form assembled from `stage_a1` through `nf_d1r` and the residual chain.

Repeated hypothesis headers are mechanically joined to keep the source below the
3000-line limit without exporting generated intermediate lemmas.

## Verification

Targeted verification passed without `sorry`. The first assembly check exposed
that `nf_p1` through `nf_p4` now have weaker public signatures than their old
private versions; updating the master call sites to those live signatures closed
the only error.

## Frontier

`master_nf` is exact finite algebra. The mixed low-regularity tame endpoint remains
unstated; the next producer is the geometric realized-family instantiation and its
bridge to the three-arm path identity.
