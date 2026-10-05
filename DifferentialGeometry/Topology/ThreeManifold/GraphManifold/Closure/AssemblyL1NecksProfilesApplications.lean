import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksProfiles

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the profiles of the necks

Lane ASM-L1e, group B′. Consumers of `AssemblyL1NecksProfiles`, in the form the necks use them.

* `exists_rimCompression`: the radial rim-coordinate compression `f` (identity on `[-3/4, 3/4]`,
  values in `(-1, 1)`), from `exists_compression_profile`.
* `exists_heightCompression`: the height compression `g` (identity on `[0, 3/4]`, values in
  `(-η, Y)`), from `exists_compression_profile`.
* `handleDiskMap A P z = A (P (‖z‖²) • z)`: the disk coordinate of the handle side of a neck, for
  the profile `P` of `exists_handleRadialProfile`: smooth, injective on the closed unit disk, of
  bijective differential there, mapping the open (closed) disk into itself, and equal to
  `(ρ (8 (‖z‖ - 1)) / ‖z‖) • A z` near the rim (`radialMap`, `bijective_fderiv_radialMap`,
  `radialMap_injOn`).
* `neckRounding_compress_nonpos_iff`: the rounded side of the neck read through the compressions
  (`standardRimRounding_comp_nonpos_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Real
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- The rim-coordinate compression. -/
theorem exists_rimCompression :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ StrictMono f ∧ (∀ x, 0 < deriv f x) ∧
      (∀ x ∈ Icc (-3 / 4 : ℝ) (3 / 4), f x = x) ∧ ∀ x, -1 < f x ∧ f x < 1 := by
  obtain ⟨f, hf, hfd, hfid, hfb⟩ :=
    exists_compression_profile (c₁ := -3 / 4) (c₂ := 3 / 4) (κ := 1 / 4) (by norm_num)
      (by norm_num)
  refine ⟨f, hf, strictMono_of_deriv_pos hfd, hfd, hfid, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hfb x
  constructor <;> linarith

/-- The height compression. -/
theorem exists_heightCompression {η Y : ℝ} (hη : 0 < η) (hY : 3 / 4 < Y) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ StrictMono g ∧ (∀ y, 0 < deriv g y) ∧
      (∀ y ∈ Icc (0 : ℝ) (3 / 4), g y = y) ∧ ∀ y, -η < g y ∧ g y < Y := by
  obtain ⟨g, hg, hgd, hgid, hgb⟩ :=
    exists_compression_profile (c₁ := 0) (c₂ := 3 / 4) (κ := min η (Y - 3 / 4)) (by norm_num)
      (lt_min hη (by linarith))
  refine ⟨g, hg, strictMono_of_deriv_pos hgd, hgd, hgid, fun y => ?_⟩
  obtain ⟨h1, h2⟩ := hgb y
  have := min_le_left η (Y - 3 / 4)
  have := min_le_right η (Y - 3 / 4)
  constructor <;> linarith

/-- The disk coordinate of the handle side of a neck. -/
def handleDiskMap (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (P : ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  A (P (‖z‖ ^ 2) • z)

section HandleDisk

variable (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {P : ℝ → ℝ}
  (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
  (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)

include hP in
theorem contDiff_handleDiskMap : ContDiff ℝ ∞ (handleDiskMap A P) :=
  A.toContinuousLinearEquiv.contDiff.comp (contDiff_radialMap hP)

include hP hPmono in
theorem strictMonoOn_handleRadius :
    StrictMonoOn (fun r : ℝ => r * P (r ^ 2)) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    ((continuous_id.mul (hP.continuous.comp (continuous_pow 2))).continuousOn)
  intro r hr
  rw [interior_Icc] at hr
  exact hPmono r hr.1.le hr.2.le

include hPpos in
theorem norm_handleDiskMap {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ ≤ 1) :
    ‖handleDiskMap A P z‖ = ‖z‖ * P (‖z‖ ^ 2) := by
  have hpos : 0 < P (‖z‖ ^ 2) := hPpos _ (by positivity) (by nlinarith [norm_nonneg z])
  rw [handleDiskMap, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg hpos.le,
    mul_comm]

include hP hP1 hPpos hPmono in
theorem norm_handleDiskMap_lt_one {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ < 1) :
    ‖handleDiskMap A P z‖ < 1 := by
  rw [norm_handleDiskMap A hPpos hz.le]
  have := strictMonoOn_handleRadius hP hPmono ⟨norm_nonneg z, hz.le⟩ ⟨zero_le_one, le_rfl⟩ hz
  simp only [one_pow, hP1, mul_one] at this
  exact this

include hP hP1 hPpos hPmono in
theorem norm_handleDiskMap_le_one {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ ≤ 1) :
    ‖handleDiskMap A P z‖ ≤ 1 := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [norm_handleDiskMap A hPpos hz, h, one_pow, hP1, mul_one]
  · exact (norm_handleDiskMap_lt_one A hP hP1 hPpos hPmono h).le

include hP hPpos hPmono in
theorem handleDiskMap_injOn : InjOn (handleDiskMap A P) (Metric.closedBall 0 1) := by
  intro z hz z' hz' h
  apply radialMap_injOn (φ := P) (R := 1)
    (fun r hr0 hr1 => hPpos _ (by positivity) (by nlinarith))
    (strictMonoOn_handleRadius hP hPmono) hz hz'
  exact A.injective h

include hP hPpos hPmono in
theorem bijective_fderiv_handleDiskMap {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ ≤ 1) :
    Bijective (fderiv ℝ (handleDiskMap A P) z) := by
  have hrad := bijective_fderiv_radialMap hP (z := z)
    (hPpos _ (by positivity) (by nlinarith [norm_nonneg z])).ne'
    (by
      have := hPmono ‖z‖ (norm_nonneg z) hz
      rw [deriv_mul_comp_sq hP] at this
      exact this.ne')
  have hcomp : handleDiskMap A P = A.toContinuousLinearEquiv ∘ radialMap P := rfl
  rw [hcomp, fderiv_comp z A.toContinuousLinearEquiv.differentiableAt
    ((contDiff_radialMap hP).differentiable (by simp) z), ContinuousLinearEquiv.fderiv]
  exact A.toContinuousLinearEquiv.bijective.comp hrad

theorem handleDiskMap_eq_of_mul {ρ : ℝ → ℝ} {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0)
    (h : ‖z‖ * P (‖z‖ ^ 2) = ρ (8 * (‖z‖ - 1))) :
    handleDiskMap A P z = (ρ (8 * (‖z‖ - 1)) / ‖z‖) • A z := by
  rw [handleDiskMap, map_smul, ← h]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hz]

end HandleDisk

/-- The rounded side of a neck at scale `1/8`, read through the compressions `f` and `g`. -/
theorem neckRounding_compress_nonpos_iff {f g : ℝ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (hf0 : ∀ x ∈ Icc (0 : ℝ) (3 / 4), f x = x) (hg0 : ∀ y ∈ Icc (0 : ℝ) (3 / 4), g y = y)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} :
    standardRimRounding (f (8 * (‖q.1‖ - 1)), g (8 * q.2)) ≤ 0 ↔
      neckRounding (1 / 8) q ≤ 0 := by
  rw [standardRimRounding_comp_nonpos_iff hf hg hf0 hg0, neckRounding]
  have h1 : (‖q.1‖ - 1) / (1 / 8 : ℝ) = 8 * (‖q.1‖ - 1) := by ring
  have h2 : q.2 / (1 / 8 : ℝ) = 8 * q.2 := by ring
  rw [h1, h2]

end GC.GraphManifold.Assembly
