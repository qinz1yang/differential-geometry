import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall

set_option autoImplicit false

/-!
# Polar-measure layer of the segment domain: capped Bishop–Gromov inputs

This file states the two volume-comparison inequalities that brick B5 of the
A0′ `VolumeComparisonInput` lane (`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`)
composes into the capped relative Bishop–Gromov bound.  For a fixed complete
member `(M, g)` with `Ric ≥ -(n-1)q²` (`n = finrank ℝ E`):

* `segBall_vol_le` — **absolute** upper bound (deliverable B2(α)(1)):
  `V(x,R) ≤ σ · v(R)`, where `V(x,R)` is the Riemannian volume of the open
  `edist`-ball, `v(R) = hypRadVol q (n-1) R` is the *radial* model volume, and
  `σ = (modelHaar E).toSphere Set.univ` is the **model sphere mass**
  (`= finrank · vol(unit ball)`, e.g. `2π` in dimension 2).  The `σ` factor is
  the sphere-integral the polar decomposition contributes on top of the radial
  `hypRadVol`; **it must NOT be dropped** — without it the bound is false (see
  the counterexample below).
* `segBall_vol_fin` — the B6-facing finiteness corollary `V(x,R) < ∞`, derived
  from `segBall_vol_le` (`σ` is finite: `Measure.toSphere` `IsFiniteMeasure`).
* `segBall_vol_rel` — **relative** capped bound (deliverable B2(α)(2), the form
  B5 needs), in multiplicative (division-free) shape:
  `V(x,R) · v(s) ≤ v(R) · V(x,s)` for `0 < s ≤ R`.  Here `σ` cancels across the
  ratio, so this form is normalization-independent and carries no `σ`.

## Counterexample fixing the constant (do NOT re-drop `σ`)

`M = E = ℝ²` flat (complete, connected, `RicciBoundedBelow g 0` with `q = 0`):
`V(x,R) = πR²`, but `hypRadVol 0 1 R = ∫₀ᴿ t dt = R²/2`, and `πR² > R²/2`.
The corrected bound is an equality here: `σ = 2π`, so `σ · (R²/2) = πR²`.
Dimension 1 (`ℝ`): `V = 2R`, `hypRadVol 0 0 R = R`, `σ = 2`, `2R ≤ 2·R`.

## Frontier status (honest — updated 2026-07-25, B5c)

Both statements are still `sorry`, but the frontier has MOVED.  The B2-era
"missing bridge" — the manifold-valued non-injective area inequality — is now
**in-tree and proved** (`riemVol_exp_image_le`, `SegmentArea.lean`, sorry-free):
for compact `K`,
`riemannianVolumeMeasure g (expMapIntrinsic x '' K) ≤ ∫⁻ v in K, ofReal (curveDensity
g (intrinsicGeodesic x v) (intrinsic Jacobi frame) 1) ∂modelHaar`, past the cut
locus, no injectivity — via a POU-weighted `Measure.sum` decomposition, the
weighted Euclidean area inequality `image_lintegral_le`, and the density identity
`exp_density_curve`.  Off-zero regularity is `intrinsicFiber_smooth` /
`expChart_contDiffAt` (the previously-cited `expMap_contMDiffAt_of_ne_zero` was
fictional; the intrinsic exponential is globally `C^∞` in the velocity).

The proof route for these two statements:

1. `ball_sub_image_segDom` (`SegmentDomain.lean`) covers the ball by
   `expMapIntrinsic '' (SegDom ∩ gBall)` — no injectivity, past the cut locus.
2. `riemVol_exp_image_le` (SegmentArea.lean, DONE) with the compact launch set
   `K = SegDom ∩ closedGBall R` bounds `V(x,R)` by `∫⁻ v in K, ofReal (curveDensity
   full-n-frame v) ∂modelHaar`.
3. **REMAINING FRONTIER (the absolute Bishop bound `∫⁻_K curveDensity ≤
   σ·hypRadVol`, brick L6).**  This is NOT assembly — no absolute
   `V ≤ σ·hypRadVol` template exists in any regime (the diffeo regime has only
   the polar EQUALITY `normalBall_polar` and RELATIVE ratio bounds
   `normalBall_cross`/`localBall_cross`).  It needs: (a) a GLOBAL Gauss
   block-determinant factorization of the full `n`-frame density into
   radial × transverse (`intrinsic_gauss` gives the global orthogonality; the
   `endpoint_det_split`/`density_det_eq` block-det machinery in `RadialGram.lean`
   is chart-scale + `private`, so must be redone past the cut locus); (b) the
   `√det(gₓ)` E-vs-`gₓ` Haar constant reconciling `modelHaar`/`toSphere`
   (E-orthonormal sphere) with the `gₓ`-arclength model; (c) a **SHARP** (`N = 1`)
   transverse bound `curveDensity(orthonormal transverse frame) ≤ hypDensity`
   — the in-tree `intrDens_le_hyp` has a NON-sharp `N = M₀/c` (from `intrPoleCap`,
   non-orthonormal frame), so integrating it yields only `σ·N·hypRadVol`; the
   sharp `N=1` needs a `gₓ`-orthonormal parallel frame (`exists_intrFrame`) with
   pole ratio `→ 1`; (d) polar integration (`lintegral_polar`) to `σ·hypRadVol`.
   The relative bound `segBall_vol_rel` further needs the truncated polar Fubini
   (cut-time `τ(θ)`) + the cross-Chebyshev lemma (`lintegral_cross_le`, B4) +
   injectivity of `expMapIntrinsic` on the open minimizing interior.

So the remaining blocker is the absolute (and then relative) Bishop–Gromov
volume comparison built on `riemVol_exp_image_le`.  See `SegmentPolar.md` and
`SegmentArea.md`.
-/

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Absolute Bishop volume upper bound** (deliverable B2(α)(1)).

For a complete member with `Ric ≥ -(n-1)q²`, the Riemannian volume of the open
`edist`-ball of radius `R` about `x` is at most `σ · hypRadVol q (n-1) R`, where
`σ = (modelHaar E).toSphere Set.univ` is the model sphere mass
(`= finrank · vol(unit ball)`).  The sphere factor `σ` is essential — dropping
it makes the inequality false (flat `ℝ²`: `V = πR² > R²/2 = hypRadVol 0 1 R`;
with `σ = 2π` the bound is the equality `πR² ≤ 2π·(R²/2)`).

FRONTIER (`sorry`): the non-injective area inequality is now DONE
(`riemVol_exp_image_le`, `SegmentArea.lean`); the remaining gap is the absolute
Bishop bound `∫⁻ v in SegDom ∩ closedGBall R, ofReal (curveDensity v) ∂modelHaar
≤ σ·hypRadVol` — global Gauss radial/transverse split + sharp (`N=1`) transverse
density bound + Euclidean polar.  See the file header and `SegmentPolar.md`. -/
theorem segBall_vol_le [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      ≤ ((modelHaar (E := E)).toSphere Set.univ)
        * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) := by
  sorry

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Finiteness of the ball volume** (B6-facing corollary of `segBall_vol_le`).

Under `Ric ≥ -(n-1)q²` the open `edist`-ball has finite Riemannian volume — the
positivity+finiteness input the packing/counting step (brick B6) consumes.
Immediate from `segBall_vol_le`: the model sphere mass `(modelHaar E).toSphere`
is a finite measure and `hypRadVol` is real. -/
theorem segBall_vol_fin [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} < ⊤ :=
  lt_of_le_of_lt (segBall_vol_le (I := I) g hEnorm x hq hR hRic)
    (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Capped relative Bishop–Gromov volume comparison** (deliverable B2(α)(2)),
multiplicative (division-free) form — the input brick B5 composes into
`V(x,R) · v(s) ≤ v(R) · V(x,s)`.

For a complete member with `Ric ≥ -(n-1)q²` and `0 < s ≤ R`, writing
`V(x,t)` for the Riemannian volume of the open `edist`-ball of radius `t` and
`v(t) = hypRadVol q (n-1) t` for the model volume,
`V(x,R) · v(s) ≤ v(R) · V(x,s)`.

FRONTIER (`sorry`): the non-injective area inequality is now DONE
(`riemVol_exp_image_le`, `SegmentArea.lean`); the remaining gap is the truncated
polar representation past the cut locus (per-direction cut time `τ(θ)`), the
cross-Chebyshev lemma `lintegral_cross_le` (brick B4), and injectivity of
`expMapIntrinsic` on the open minimizing interior.  See the file header and
`SegmentPolar.md`. -/
theorem segBall_vol_rel [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (x : M) {q s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) s)
      ≤ ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R)
        * riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  sorry

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
