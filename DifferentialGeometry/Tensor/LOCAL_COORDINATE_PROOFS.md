# Local Coordinate Tensor Proofs

This folder should use local coordinates as an evaluation layer, not as the
definition of tensorial objects.

## Design

- Define tensor operations intrinsically on fibers first.
- State coordinate formulas with a genuine pointwise basis:
  `basis : Module.Basis Idx Real (TangentSpace I x)`.
- Use local frames only after converting them to pointwise bases via
  `hframe.toBasisAt hx`.
- Keep inverse metric hypotheses basis-level:
  `MetricInverseInBasis g x basis gInv`.
- Prove arbitrary-frame formulas only through a bridge that supplies a basis.
  A raw finite family of tangent vectors is not enough for tensor coordinate
  identities.

The current model example is:

- `Tensor0SBundle.normSq0S_two_eq_coord`
- `DifferentialGeometry.Realized.normSq02_eq_coord`

The first theorem proves the intrinsic `(0,2)` norm-square formula in a basis.
The second theorem specializes it to local-frame components by using
`metricInverseInBasis_of_frame`.

## Proof Pattern

For a tensor formula in local coordinates:

1. Define the tensor expression intrinsically.
2. Prove a basis-coordinate theorem in the tensor layer.
3. In a realized/local-frame file, convert the local frame to a basis using
   `hframe.toBasisAt hx`.
4. Convert frame inverse-metric hypotheses to `MetricInverseInBasis`.
5. Rewrite local-frame components with `IsLocalFrameOn.toBasisAt_coe`.

This keeps coordinate formulas robust under overlap changes: two different
frames give the same scalar because both coordinate sums equal the same
intrinsic tensor expression.

## Basis Trick

The useful Lean bridge from intrinsic metric contractions to coordinates is:

- reconstruct basis coefficients using inverse metric contractions;
- expand traces with `LinearMap.trace_eq_matrix_trace`;
- rewrite matrix diagonal entries with `LinearMap.toMatrix_apply`;
- translate the metric adjoint back with `MetricFiberData.adjoint_inner`;
- use `cotangentMetricData_inner_eq_coord` for the remaining covariant slot.

In `normSq0S_two_eq_coord`, this appears as:

- `basis_repr_eq_sum_inv_inner`;
- `hom_normSq_eq_basis`;
- `tensor0S_curry_one_apply`;
- `cotangentMetricData_inner_eq_coord`.

The key idea is that the Hom/Hilbert-Schmidt norm of the curried `(0,2)`
tensor reduces to

```text
sum_i sum_k gInv i k * inner_cotangent (A(e_i, -)) (A(e_k, -)).
```

Then the cotangent coordinate theorem expands the second slot, giving the
standard four-index expression.

## Later Use

For Bochner, Ricci norm, curvature contractions, and evolution calculations,
prefer this order:

- prove the intrinsic tensor object or scalar first;
- prove the basis coordinate formula in `Tensor/RSTensor`;
- consume it in `Realized/*` or `Coordinates/*` using `hframe.toBasisAt hx`;
- keep hard geometric producer facts as explicit hypotheses until the
  Levi-Civita/time-evolution infrastructure proves them.

If a proof gets stuck, stop at a precise basis-level theorem. Do not replace an
intrinsic definition by a coordinate definition just to make downstream algebra
typecheck.

## Trace Contraction In A Basis

The reusable trace-contraction bridge is:

- `Tensor0SBundle.model_contract_trace_apply_basis`

It lives in `Tensor/RSTensor/Contract.lean` and is the model-fiber statement
behind Ricci-as-trace coordinate calculations.  In mathematical notation, for

```text
T : (V*)^(r+1) -> (V*)^(s+1)
β : (V*)^r
tail : V^s
```

it proves:

```text
(tr T β)(tail)
  = sum_i i_{e_i}
      (T((e^i) ⊗ β))(tail),
```

where `basis i = e_i` and `basis.coord i = e^i`.  This is exactly the finite
basis trace formula: contract the first contravariant/covariant pair by feeding
the dual basis covector into the input side and the basis vector into the output
side.

### Proof Idea

The definition of `model_contract_trace` is initially expressed using
`Module.finBasis`.  The theorem upgrades it to an arbitrary basis by proving the
trace sum is basis-independent.

The proof has three steps:

1. Unfold the model trace:

   ```lean
   rw [model_contract_trace_apply]
   rw [ContinuousLinearMap.sum_apply]
   rw [ContinuousMultilinearMap.sum_apply]
   ```

2. Package the summand as a bilinear functional

   ```lean
   model_trace_pairing_first ... :
     (E ->L[𝕜] 𝕜) ->L[𝕜] E ->L[𝕜] 𝕜
   ```

   and rewrite the desired summand with
   `model_trace_pairing_first_apply`.

3. Apply the private basis-change lemma
   `trace_bilinear_basis_coord`, which proves

   ```text
   sum_i F(e^i, e_i)
     = sum_j F(finBasis.coord j, finBasis j)
   ```

   for any continuous bilinear `F`.  Its proof expands each arbitrary basis
   vector in `Module.finBasis`, reconstructs `finBasis.coord j` from
   `sum_i finBasis.coord j (basis i) • basis.coord i`, swaps finite sums, and
   uses bilinearity.

This is why `model_contract_trace_apply_basis` is not a coordinate definition:
it is a theorem that the intrinsic trace contraction can be evaluated in any
pointwise basis.

### How To Use It

Use it whenever an intrinsic trace has to become an explicit coordinate sum.

The typical pointwise proof shape is:

```lean
unfold contract_trace
change ((model_contract_trace ... (TensorRSSpace.toModel T))
    (Tensor0SSpace.toModel β)) tail = _
rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basis r s]
```

Then simplify the model-level input tensor and the resulting `Fin` vectors until
the summand is the component expression you want.

The current curvature example is:

- `DifferentialGeometry.Realized.contract_trace13_component_basis`
- `DifferentialGeometry.Realized.ricciFromRm13_comp_eq_rm04_trace`

For `r = 0` and `s = 2`, the first theorem proves:

```text
((contract_trace 0 2 Rm13) 1)(e_i,e_j)
  = sum_a Rm13(e^a)(e_a,e_i,e_j).
```

The second theorem then rewrites the coordinate covector by the inverse metric:

```text
e^a(-) = sum_k g^{ak} g(e_k, -),
```

and lowers `Rm13` with the metric, giving:

```text
Ric_ij = sum_a sum_k g^{ak} Rm04(e_k,e_a,e_i,e_j).
```

This is the correct bridge from the intrinsic definition

```text
Ric(Y,Z) = trace (X |-> R(X,Y)Z)
```

to the lowered Riemann component formula.  Future curvature calculations should
reuse this theorem instead of re-expanding `contract_trace` directly.
