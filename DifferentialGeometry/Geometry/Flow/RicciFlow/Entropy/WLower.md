# WLower

## 2026-07-16 fixed-metric W lower bounds

`w_fixed_lower` is checked without warnings or a local `sorry`.  It proves the
actual canonical `wFunctional` lower bound on a fixed closed three-manifold for
all positive normalized smooth amplitudes and all positive scales bounded by
`tauMax`.  Its constant is chosen before both the scale and the amplitude.  The
dimension equation constructs the needed local `NeZero` instance, so the public
statement does not add a redundant consumer assumption.

`w_density_lower` is also checked.  It applies `w_fixed_lower` to `sqrt u` and
provides exactly the smooth strictly positive unit-mass density normal form
used by the conjugate-heat lane.  Both the amplitude and density theorems are
**100%**.

These are genuine fixed-metric entropy producers, not a no-local-collapsing
wrapper.  The quantitative intrinsic ball cutoff and cutoff contradiction are
still **0%**; consequently `NoLocalCollapsing` and `ham3_noncollapse` remain
theorem-level **0%**.  The branch continues to inherit the existing
`ShortTime/WeylEigenvalueCountingBound.lean` `sorry`.

## 2026-07-16 cutoff interface correction

The branch does have full `W^{1,p}` chart-density infrastructure:
`contMDiff_dense_in_WkpChart`, per-chart strong-support approximation, smooth
multiplication, and smooth chart-to-intrinsic gradient bounds. The missing
producer is narrower and deeper: the intrinsic distance tent must first be
placed in `MemWkpChart g 1 2` with its `r^-1` weak-gradient scale controlled
uniformly in the center and small radius. Current intrinsic/chart bridges do
not accept that nonsmooth Lipschitz input.

After this Rademacher/weak-gradient producer, a smooth outer bump and the
existing multiplier estimate suffice to preserve ball support and obtain the
mass/energy form needed by W. A fixed-metric constant `C_g` is sufficient; the
chart route does not justify, and the consumer does not require, a universal
numerical constant. Consequently `w_fixed_lower` and `w_density_lower` are
still **100%**, while the proposed `exists_cutoff_energy` theorem and the
cutoff contradiction remain **0%**.
