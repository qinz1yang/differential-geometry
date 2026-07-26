# CompactParametricIntegral status

## Proved in source

`integral_contOn_cpt` states the fixed-measure compact parametric integral
lemma needed by finite Galerkin operators: joint continuity on `K × X`, with
both `K` and `X` compact and the measure finite, implies continuity on `K` of
the Bochner integral.

The proof obtains a uniform norm bound on the compact product and applies
dominated convergence.  It introduces no new class, instance, axiom, or
placeholder.

## Verification

Source and static review only.  Focused Lean verification is queued behind the
single active Ricci--DeTurck edge-energy named build.

## Consumer

The immediate consumer is `HarmonicStateMass.lean`: joint continuity of the
pointwise faithful state mass will imply continuity of the finite mass
operator for a fixed domain metric.  Moving-time continuity additionally
requires the existing chart-density decomposition for a varying Riemannian
volume.
