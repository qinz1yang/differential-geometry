# Local Coordinate Tensor Proofs

## Design

Local coordinates should project invariant tensor statements.  They should not
own tensor algebra, smoothness proofs, or Hom-representation manipulation.

For `(0,s)` tensors use:

```text
component0S basis A slots = A (fun a => basis (slots a))
```

For mixed `(r,s)` tensors use:

```text
componentRS basis T upper lower =
  component0S basis (T (basisTensor0S basis upper)) lower
```

The Hom implementation of `TensorRSSpace` is an internal detail.  Downstream
coordinate files should not hand-write `basisTensor0S` or unfold
`TensorRSSpace = Tensor0SSpace r ->L Tensor0SSpace s` unless proving the
component API itself.

## Proof Pattern

1. Prove an invariant or pointwise-basis theorem first.
2. Project it through `component0S` or `componentRS`.
3. For local frames, use `hframe.toBasisAt hx`.
4. For coordinate frames, use `coordinateFrameAt_toBasis x₀` or the existing
   `coordComponent*At` wrappers.
5. Add arity helpers for readability instead of unfolding `Fin s -> Idx`.

## Basis Trick

To prove tensor equality from components, use finite-dimensional basis
extensionality:

```text
∀ slots, A (basis ∘ slots) = B (basis ∘ slots)
```

For multilinear maps this avoids repeated low-level expansion of arbitrary
vectors.  If the proof begins with manual `Fin.cons`, `Function.update`, or
Hom-currying bookkeeping, first check whether a component wrapper or slot
algebra lemma belongs in a lower module.

## Trace Contraction In A Basis

The Ricci trace bridge follows this pattern:

```text
Ric(Y,Z) = trace (X |-> R(X,Y)Z)
```

Project to a pointwise basis, rewrite the coordinate covector through the
inverse metric, and lower `Rm13` with the metric:

```text
Ric_ij = sum_a sum_k g^{ak} Rm04(e_k,e_a,e_i,e_j).
```

Future curvature calculations should reuse this theorem rather than
re-expanding `contract_trace` directly.

## How To Use

- Local-frame component: `component0S (hframe.toBasisAt hx) A slots`.
- Mixed local-frame component: `componentRS (hframe.toBasisAt hx) T upper lower`.
- Coordinate-frame component: `coordComponent0SAt` or `coordComponentRSAt`.
- Common arities should use wrappers such as `slots2`, `slots3`, `slots4`,
  `(0,2)`, `(0,4)`, `(1,2)`, and `(1,3)` component helpers.
