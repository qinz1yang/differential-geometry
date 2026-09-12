# SlabFrameControl

2026-09-10 SOURCE-WRITTEN / UNVERIFIED. Claim
dcdfc64f-ab21-4f1b-97fa-ad087de92dd0. Source only during Chapter23's window.

Input: native tensor0SFamilyContinuousOnSet for the actual metric tensor.
Output: one fixed smooth local frame and an open neighborhood in the relative
time carrier times its actual domain, with the all-rank component comparison
required by compL2_tower_le and SlabKoszulControl.metric_component_succ_le_metric_error.
The frame is orthonormal at the chosen spacetime point; continuity of the
inverse Gram matrix gives the uniform comparison nearby. Time endpoints use
the subtype topology and require no forward extension.

Native producers reused: exists_trivONBasis, metric tensor eval_continuous,
frame_e_mdiffOn, gramInv_inverse, gramInv_symm, quad_lb_of_near_id and
sum_comp_sq_le_pow_normSq0S. This extends the existing fixed-metric GoodFrame
argument to a merely continuous time family, without assuming smoothness.

Actual IsSlabLimit.metricTensor_cont was independently accepted in
SlabMetricTensorLimit; it supplies the public hypothesis for the pending
coordinate-jet induction. This leaf does not supply higher Christoffel jets,
coordinate derivative reconstruction or the final induction.

Saved EMPTY check, named lint refresh and fresh public axiom audit are pending.
