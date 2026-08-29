# CutExist

## Result

`exists_lMinVec_ray` proves that every endpoint of a positive regular
L-ray is reached, at the same backward time, by a minimizing initial
L-tangent.

The proof globalizes the regular ray with `exists_lReg_clamp`, uses the
resulting globally smooth curve as the honest competitor for
`exists_lMinVec`, and preserves the endpoint because the clamp is the
identity on the required square-root-time interval.

## Implementation notes

- The joint smoothness composition must first name the fixed tangent as an
  element of the model space `E`; coercing it only inside the pair can make
  Lean infer a dependent tangent-fiber product instead of `E × Real`.
- Regularity and carrier hypotheses are recovered from `lExpPosDom_reg` and
  the square-root change of variables.  No additional flow or compactness
  assumption is introduced.

## Verification

Focused verification passed without warnings or placeholders.

## Project position

This closes the minimizing-vector existence input above a candidate cut time.
The boundary cut alternative itself remains unproved; it additionally needs
initial-vector compactness and regular-ray continuation on a compact regular
time slab.
