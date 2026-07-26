# ParametricJetIntegral

## Purpose

This module supplies the low-layer parameter-family API needed by the
low-regularity Ricci--DeTurck path construction.  It proves that jointly smooth
mixed-tensor families are closed under fibrewise addition and subtraction and
that a uniform finite covariant `L2` jet bound passes to the interval-integrated
coefficient field.

## Current state

`joint_rs_add`, `joint_rs_sub`, and `path_jetL2_le` are implemented without new
analytic assumptions.  The jet theorem packages the already proved covariant
derivative/integral commutation and fibre-norm integral estimates behind one
joint-smooth-family interface.

Focused verification passes without local warnings or sorries, and the module
object has been refreshed for downstream use.  The only setup required beyond
the imported APIs was the finite-dimensional complete-space instance and the
namespace containing `iteratedCovGrad`; the earlier failures were stale object
files rather than a mathematical obstruction.

## Project accounting

This is infrastructure, not a Ricci--DeTurck existence theorem.  Uniform
low-regularity existence and `ricci_flow_unif_existence` remain theorem-level
0%.  This module closes one reusable integration bridge required by the
mixed-remainder producer.
