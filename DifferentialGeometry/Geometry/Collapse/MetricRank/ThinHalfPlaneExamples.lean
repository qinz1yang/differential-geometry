import DifferentialGeometry.Geometry.Collapse.MetricRank.ThinHalfPlaneRank
import DifferentialGeometry.Geometry.Collapse.MetricRank.ThinOnlyExamples

/-!
# Explicit consumer of the thin half plane rank (S-X144c, group G11)

Numbers of `RankAdaptersExamples` (S-X144b, G8): scale `ρ ≡ 2`, register
`β = (1/20, 1/10, 3/20)` (`betaRegister_SMR`), the point `(0, 1/50)` of the closed upper half
plane `H`; the thin factor is `[0, 1/400]` (`ThinOnlyExamples`: halved to `[0, 1/800]`,
`D = 1/800`), the half-scaling `(v, t) ↦ (v/2, t/2)` is a Kleiner-Lott `1/200`-approximation of
the rescaled metric of `M = H ×₂ [0, 1/400]` into `H ×₂ [0, 1/800]` (`δ + D = 5/800 ≤ 1/100`),
and the base point of the rescaled picture is `(0, 1/100)`, `h = 1/100 ≤ 1/20`:

* `halfplane_half_dist_SMR`, `halfplane_half_surjective_SMR`: the half-scaling `H → H`;
* `thin_halfplane_only_scaledSplittingRank_one_SMR` : `scaledSplittingRank = 1` at
  `((0, 1/50), 0)` (no explicit one-splitting: derived with `β 1 = 1/20` from `δ = 1/200`);
* `thin_halfplane_only_scaledSplittingRank_one_hundredth_SMR` : the register form with
  `δ = 1/300`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

local notation "ZT" => {t : ℝ // t ∈ Set.Icc (0 : ℝ) (1 / 400)}
local notation "HP" => {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}

/-- The half-scaling `v ↦ v / 2` of the closed upper half plane. -/
noncomputable def halfplaneHalf_SMR (v : HP) : HP :=
  ⟨(2 : ℝ)⁻¹ • v.1, by simpa using mul_nonneg (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)) v.2⟩

theorem halfplane_half_dist_SMR (x y : HP) :
    dist (halfplaneHalf_SMR x) (halfplaneHalf_SMR y) = 2⁻¹ * dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq]
  change dist ((2 : ℝ)⁻¹ • x.1) ((2 : ℝ)⁻¹ • y.1) = _
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]

theorem halfplane_half_surjective_SMR : Function.Surjective halfplaneHalf_SMR := by
  intro y
  refine ⟨⟨(2 : ℝ) • y.1, by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) y.2⟩, ?_⟩
  apply Subtype.ext
  change (2 : ℝ)⁻¹ • (2 : ℝ) • y.1 = y.1
  simp [smul_smul]

/-- **Thin half plane at an edge point, rank exactly one from the approximation alone.**
`M = H ×₂ [0, 1/400]` at `((0, 1/50), 0)`, scale `ρ ≡ 2`, register `β = (1/20, 1/10, 3/20)`:
the one-splitting at `β 1 = 1/20` is produced from `δ = 1/200` by
`exists_splitting_of_thin_halfplane_SMR`, the exclusion of ranks `2` and `3` is the half-plane
kernel (`π p = (0, 1/100)`, `h = 1/100 ≤ 1/20`). -/
theorem thin_halfplane_only_scaledSplittingRank_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (HP × ZT) => (2 : ℝ)) (fun _ => two_pos)
      betaRegister_SMR (WithLp.toLp 2 (halfplanePoint_SMR, thinBase_SMR)) = 1 :=
  scaledSplittingRank_eq_one_of_thin_halfplane_only_SMR (D := 1 / 800) (h := 1 / 100)
    (thin_halfscale_approx_SMR halfplaneHalf_SMR halfplane_half_dist_SMR
      halfplane_half_surjective_SMR halfplanePoint_SMR (δ := 1 / 200) (by norm_num)
      (by norm_num)).some
    thin_factorH_dist_SMR (by norm_num) (by rw [betaRegister_one_SMR]; norm_num)
    (by rw [betaRegister_one_SMR]; norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_three_SMR]) (by norm_num) (by norm_num)
    (by simp [halfplaneHalf_SMR, halfplanePoint_SMR])
    (by simp [halfplaneHalf_SMR, halfplanePoint_SMR]; norm_num)

/-- The register form (`1/50 ≤ β 1 < 1`) at `δ = 1/300`. -/
theorem thin_halfplane_only_scaledSplittingRank_one_hundredth_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (HP × ZT) => (2 : ℝ)) (fun _ => two_pos)
      betaRegister_SMR (WithLp.toLp 2 (halfplanePoint_SMR, thinBase_SMR)) = 1 :=
  scaledSplittingRank_eq_one_of_thin_halfplane_only_of_hundredth_SMR (D := 1 / 800)
    (h := 1 / 100)
    (thin_halfscale_approx_SMR halfplaneHalf_SMR halfplane_half_dist_SMR
      halfplane_half_surjective_SMR halfplanePoint_SMR (δ := 1 / 300) (by norm_num)
      (by norm_num)).some
    thin_factorH_dist_SMR (by norm_num) (by rw [betaRegister_one_SMR]; norm_num)
    (by rw [betaRegister_one_SMR]; norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_three_SMR]) (by norm_num) (by norm_num)
    (by simp [halfplaneHalf_SMR, halfplanePoint_SMR])
    (by simp [halfplaneHalf_SMR, halfplanePoint_SMR]; norm_num)

end GC.MetricGeometry
