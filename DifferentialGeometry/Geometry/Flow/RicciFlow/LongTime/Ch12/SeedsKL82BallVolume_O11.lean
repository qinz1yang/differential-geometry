import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale

/-!
# CH12-O11, Group G3: small-ball volume from large-ball volume under `sec ≥ −q²`

Local Bishop–Gromov with explicit constants, the volume step of KL 82.1 / Perelman I.11.6(b)
(`[FROZEN v2] CH12-O11 kl82_1`, items VT and PK): if `sec ≥ −q²` on `B(p, R)` and
`vol B(p, R) ≥ w R³`, then `vol B(p, s) ≥ w s³ / e^{2qR}` for `0 < s ≤ R`.
With `q = 1/r0`, `R = r0`, `s = r0/4` this is `≥ w (r0/4)³ / e²`.
Proof: `ballVolume_cross_endpoint_of_sectional_three`, `V₋q²(s) ≥ ω₃ s³`
(`sectionalThree_euclidean_le_model`) and `V₋q²(R) ≤ ω₃ R³ e^{2qR}` (`modelVolume_neg_sq_three_le`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse
open scoped ENNReal Manifold ContDiff

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

/-- **G3.** Small-ball volume from large-ball volume under a local lower sectional bound. -/
theorem ballVolume_small_of_sec_O11 (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {q w s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ z ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g z (-(q ^ 2)))
    (hvol : ENNReal.ofReal (w * R ^ 3) ≤ ballVolume g p R) :
    ENNReal.ofReal (w * s ^ 3 / Real.exp (2 * q * R)) ≤ ballVolume g p s := by
  rcases le_or_gt w 0 with hw | hw
  · have hle : w * s ^ 3 / Real.exp (2 * q * R) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hw (by positivity))
        (Real.exp_pos _).le
    rw [ENNReal.ofReal_of_nonpos hle]
    exact bot_le
  have hR : 0 < R := hs.trans_le hsR
  have hcross := ballVolume_cross_endpoint_of_sectional_three g hg hdim p (sq_nonneg q) hs hsR
    hsec
  have heu := sectionalThree_euclidean_le_model (κ := q ^ 2) (sq_nonneg q) hs.le
  have hup := modelVolume_neg_sq_three_le hq hR.le
  have hω := euclideanUnitBallVolume_pos 3
  set A : ℝ := euclideanUnitBallVolume 3 * R ^ 3 * Real.exp (2 * q * R) with hA
  have hApos : 0 < A := by positivity
  have hexp : 0 < Real.exp (2 * q * R) := Real.exp_pos _
  have heq : ENNReal.ofReal (w * s ^ 3 / Real.exp (2 * q * R)) * ENNReal.ofReal A =
      ENNReal.ofReal (w * R ^ 3) * ENNReal.ofReal (euclideanUnitBallVolume 3 * s ^ 3) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hA]
    field_simp
  have hchain : ENNReal.ofReal A * ENNReal.ofReal (w * s ^ 3 / Real.exp (2 * q * R)) ≤
      ENNReal.ofReal A * ballVolume g p s := by
    rw [mul_comm, heq]
    calc ENNReal.ofReal (w * R ^ 3) * ENNReal.ofReal (euclideanUnitBallVolume 3 * s ^ 3)
        ≤ ballVolume g p R * ENNReal.ofReal (modelVolume (-(q ^ 2)) 3 s) :=
          mul_le_mul' hvol (ENNReal.ofReal_le_ofReal heu)
      _ ≤ ENNReal.ofReal (modelVolume (-(q ^ 2)) 3 R) * ballVolume g p s := hcross
      _ ≤ ENNReal.ofReal A * ballVolume g p s :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hup) le_rfl
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hApos).ne' ENNReal.ofReal_ne_top).mp
    hchain

end GC.LongTime.Ch12
