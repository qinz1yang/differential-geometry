# SmallExhaustion

## Result

`lInj_eventually` proves that every fixed initial tangent `Z` lies in the
strict minimizing L-injectivity domain for all sufficiently small positive
backward times:

```text
forall eventually tau in nhdsWithin 0 (Ioi 0),
  Z in lInjDomain S T x tau.
```

The theorem assumes only the existing compact fixed-manifold setting and
regularity of the terminal time.  It introduces no injectivity assumption,
consumer wrapper, generalized flow object, or foundational class.

## Proof route

The proof argues against a sequence of positive bad times converging to zero.
It doubles each bad time to obtain a strict later witness time and writes its
square root as `B n`.

The fixed-ray limit `lRayAct_zero_lim` bounds the action of the prescribed
`Z` ray by a constant times `B n`.  A compact regular slab gives uniform
regularized-ray domains.  At each later time `exists_lMinVec_ray` supplies a
minimizing initial tangent with the same endpoint.  Minimality and
`lCost_le_ray` transfer the fixed-ray action bound to these minimizing
tangents.  Then `lRegInit_shrink` puts their full range in one bounded tangent
ball.

After enlarging that ball to contain `Z`, `lEnd_inj_small` makes the endpoint
map injective there for the remaining tail.  The minimizing tangent therefore
equals `Z`, and the doubled time is the strict minimizing witness forbidden by
the chosen bad sequence.

The theorem lives above `ShortMinimizing`, `SmallEndpoint`, and `SmallTime`.
This placement reuses the checked fixed-ray action limit without introducing
an import cycle or duplicating its proof.

## Verification

Focused verification is GREEN and warning-free.  There are no placeholders,
admitted facts, or reference-tree imports.

## Next exact stage

The pointwise strict-domain exhaustion theorem `lInj_eventually` and its direct
proof are **100%**.  The dedicated global source-exhaustion machinery is now
roughly **70--75%**; the remaining stage must promote pointwise eventual
membership to the source-domain exhaustion and integral limit needed by the
separate `redVolume_zero_lim` capstone.

`redVolume_anti` remains **100%**.  `redVolume_zero_lim` remains unstated and
unproved at **0%**, while its pointwise zero-time density machinery is already
**100%**.  Reused generic infrastructure for this brick is **100%**.  P2
remains below **1%**, and the whole Poincare program remains approximately
**3--5%**.
