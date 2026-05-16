# RSTensor/Tensoriality

## Goal

Record the general tensoriality facts that are already justified by the
`RSTensor` fiber definitions.

## Result

- A fixed fiberwise linear map `V x -> A`, evaluated on `sigma x`, is
  `TensorialAt`.
- A fixed `(0,s)` tensor is tensorial in each tangent-vector-field slot.
- A fixed `(r,s)` tensor is tensorial in its whole `(0,r)` input tensor field,
  using the current Hom representation
  `Tensor0SSpace r I x ->L Tensor0SSpace s I x`.
- A fixed `(r,s)` tensor, evaluated on fixed output vector slots, is tensorial
  in its whole `(0,r)` input tensor-field slot.
- After applying a fixed `(0,r)` input, a fixed `(r,s)` tensor is tensorial in
  each output tangent-vector-field slot. This is just the `(0,s)` theorem
  applied to `T input`.

## Lesson

The clean theorem for individual vector-field slots is naturally a `(0,s)`
statement. For `RS` tensors, individual upper/covector-slot tensoriality is not
the primitive statement in the current Hom encoding; it would need a separate
evaluation interface expanding a `(0,r)` input tensor into decomposable covector
slots.

There is also a mathematically valid theorem saying a fixed
`T : TensorRSSpace r s I x` is tensorial in its whole `(0,r)` input tensor
field, because `T` is a continuous linear map
`Tensor0SSpace r I x ->L Tensor0SSpace s I x`. The first implementation attempt
incorrectly treated a typeclass failure as missing structure. The structure was
already present in `Defs.lean`; the theorem file needed the same transparency
setting used there:

```lean
set_option backward.isDefEq.respectTransparency false
```

With that setting, Lean can match the reducible tensor-model aliases carrying
hidden instance arguments, and the whole-input `RS` tensoriality theorem proves
directly from the generic fiberwise-linear-map lemma.
