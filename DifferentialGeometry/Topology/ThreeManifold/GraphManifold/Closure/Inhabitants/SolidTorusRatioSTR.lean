import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusPlanarSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusBallConsumerSTI

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G3 part 2: the ball zero domains with the descending ratio

`ballZeroDomainsL_STR : ZeroDomains Wc` is the cap `Re z₂ ≥ 4/5` (same piece as
`ballZeroDomains_STI`) with the ratio `Λ(z₂) (κ - Re z₂)` (`Λ > 0` smooth): same zero set, same
sublevel, same regular zeros, and a function of the edge coordinate near the rim fibres.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_RatioSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_RatioSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

/-- The planar ratio `Λ(q)(κ - Re q)`. -/
def ratioP_STR (q : ℂ) : ℝ := lamMix_STR q * (kap_STR - q.re)

/-- The descending ratio of the ball on the carrier. -/
def ratioL_STR (p : Wc.Carrier) : ℝ := ratioP_STR (sphereSecond p.val)

theorem contDiff_ratioP_STR : ContDiff ℝ ∞ ratioP_STR := by
  unfold ratioP_STR
  exact contDiff_lamMix_STR.mul (contDiff_const.sub Complex.reCLM.contDiff)

theorem contMDiff_lamMixW_STR :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun p : Wc.Carrier => lamMix_STR (sphereSecond p.val)) :=
  (contDiff_lamMix_STR.contMDiff.comp contMDiff_sphereSecond).comp contMDiff_solidTorus_val

theorem contMDiff_ratioL_STR : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ ratioL_STR :=
  (contDiff_ratioP_STR.contMDiff.comp contMDiff_sphereSecond).comp contMDiff_solidTorus_val

theorem ratioL_eq_mul_STR :
    ratioL_STR = (fun p : Wc.Carrier => lamMix_STR (sphereSecond p.val)) * ratioBall_STI := by
  funext p
  rfl

theorem ratioL_eq_zero_iff_STR {p : Wc.Carrier} : ratioL_STR p = 0 ↔ ratioBall_STI p = 0 := by
  change lamMix_STR (sphereSecond p.val) * ratioBall_STI p = 0 ↔ _
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (lamMix_pos_STR _).ne'
  · intro h
    rw [h, mul_zero]

theorem ratioL_le_zero_iff_STR {p : Wc.Carrier} : ratioL_STR p ≤ 0 ↔ ratioBall_STI p ≤ 0 := by
  change lamMix_STR (sphereSecond p.val) * ratioBall_STI p ≤ 0 ↔ _
  constructor
  · intro h
    by_contra hcon
    exact absurd h (not_le.mpr (mul_pos (lamMix_pos_STR _) (not_le.mp hcon)))
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (lamMix_pos_STR _).le h

theorem ratioL_regular_STR (p : Wc.Carrier) (hp : ratioL_STR p = 0) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) ratioL_STR p ≠ 0 := by
  have hg : ratioBall_STI p = 0 := ratioL_eq_zero_iff_STR.1 hp
  have hreg := ratioBall_regular_STI p hg
  have hΛ := (contMDiff_lamMixW_STR p).mdifferentiableAt (by simp)
  have hgm := (contMDiff_ratioBall_STI p).mdifferentiableAt (by simp)
  have hd := hΛ.hasMFDerivAt.mul hgm.hasMFDerivAt
  rw [ratioL_eq_mul_STR, hd.mfderiv]
  intro h
  apply hreg
  have hpos : lamMix_STR (sphereSecond p.val) ≠ 0 := (lamMix_pos_STR _).ne'
  ext v
  have h1 := DFunLike.congr_fun h v
  let a : ℝ := mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) ratioBall_STI p v
  let b : ℝ := mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) (fun p : Wc.Carrier => lamMix_STR (sphereSecond p.val)) p v
  have h2 : lamMix_STR (sphereSecond p.val) * a + ratioBall_STI p * b = 0 := h1
  rw [hg, zero_mul, add_zero] at h2
  have h3 : a = 0 := (mul_eq_zero.mp h2).resolve_left hpos
  exact h3

/-- **The ball zero domains with the descending ratio.** -/
def ballZeroDomainsL_STR : ZeroDomains Wc where
  count := 1
  piece _ := capPiece_STI
  disjoint i j h := absurd (Subsingleton.elim i j) h
  ratio _ := ratioL_STR
  near _ := ballNear_STI
  near_interior _ := ballNear_interior_STI
  ratio_smooth _ := contMDiff_ratioL_STR
  ratio_regular _ p hp := ratioL_regular_STR p hp
  zero_subset_near _ _ hp :=
    cliffordHeight_lt_of_ratio_STI ((ratioBall_eq_zero_iff_STI.1 (ratioL_eq_zero_iff_STR.1 hp)).ge)
  boundary_eq _ := by
    rw [pieceBoundary_capPiece_STI]
    ext p
    exact ratioL_eq_zero_iff_STR.symm
  range_eq _ := by
    rw [range_capPiece_STI]
    ext p
    exact ratioL_le_zero_iff_STR.symm
  model _ := Sum.inl (.ball (Diffeomorph.refl (𝓡∂ 3) (ClosedCell 3) ∞))

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
