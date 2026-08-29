# MetricFamilyGramSmooth

## Role

This module is the fixed-chart smoothness producer for the Gram operator of a
smooth metric family. It extends `MetricFamilyGram` at the operator layer and
does not depend on time-Sobolev or L-geometry consumer definitions.

## Native route

- `MetricFamilySmoothOn.chartGramOnE_contDiffOn` gives joint smoothness of each
  fixed-chart Gram entry on regular time times the interior chart target.
- The finite expansion already used by `chartGramBilin` assembles the entries
  into a smooth bilinear-form-valued map.
- The existing continuous linear map `IsCoercive.gramCLM` transports this to
  the Hilbert-space Gram operator.

No reference-tree result was needed, and no tensor or Hom representation was
unfolded.

## Public API

- `chartGramOp_smooth`: joint `C∞` regularity on `D.regular ×ˢ K`, assuming
  exactly that `K` lies in the interior target of the fixed extended chart.

## Verification

Focused verification passed without warnings or placeholders.

## Project position

`chartGramOp_smooth` and its dedicated fixed-chart assembly are complete
(100%). The post-density Tonelli regularity theorem is not stated or proved in
this module (0%); this producer supplies one of its dedicated regularity inputs.
The global L-minimizer endpoint and `redVolume_anti` remain separate endpoints
and are not completed by this infrastructure (0% each).
