import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornCommonArms
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornTwoArmSubsequence

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem exists_finiteHorn_approximate_pair_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ outer : ℕ, ∃ (target middle : ℕ) (D : ℝ),
        0 < D ∧ closure (H.subend target) ⊆ H.subend middle ∧
        closure (H.subend middle) ⊆ H.subend outer ∧
        (∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < D → x ∈ H.subend target) ∧
        ∀ (a : Fin 2 → EndRay H.endpoint) (r : Fin 2 → ℝ),
          (∀ k, 0 < r k) → (∀ k, r k < min (a k).length D) → ∀ eps : ℝ, 0 < eps →
          ∃ (p : W) (arm : Fin 2 → ℝ → W) (length : Fin 2 → ℝ),
            dist (p : UniformSpace.Completion W) H.endpoint < eps ∧ p ∈ H.subend target ∧
            (∀ k, 0 < length k) ∧ (∀ k, ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (arm k)) ∧
            (∀ k, arm k 0 = p) ∧ (∀ k, arm k (length k) = (a k).point (r k)) ∧
            (∀ k s, s ∈ Icc 0 (length k) → arm k s ∈ H.subend middle) ∧
            (∀ k s, s ∈ Icc 0 (length k) → ∀ t ∈ Icc 0 (length k),
              dist (arm k s) (arm k t) = |s - t|) ∧
            (∀ k, |length k - r k| < eps) ∧
            (∀ k s, s ∈ Ioc 0 (r k) → dist (arm k (length k * (s / r k))) ((a k).point s) < eps) ∧
            ∀ s ∈ Icc 0 (length 0), ∀ t ∈ Icc 0 (length 1),
              ∃ c : ℝ → W, c 0 = arm 0 s ∧ c 1 = arm 1 t ∧
                ContMDiff 𝓘(ℝ, ℝ) I3 ∞ c ∧
                (∀ u ∈ Icc (0 : ℝ) 1, c u ∈ H.subend outer) ∧
                ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
                  dist (c u) (c v) = |u - v| * dist (arm 0 s) (arm 1 t) := by
  obtain ⟨H₀, hH₀, harmpairs⟩ := exists_finiteHorn_common_arms_depth (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth outer
  obtain ⟨target, middle, htarget, hmiddle, harmpair⟩ := harmpairs g H hdepth outer
  obtain ⟨d, hd, hsub⟩ := finiteHorn_two_arm_subsequence_eq_endRay g H
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H target
  let D : ℝ := min d delta
  have hD : 0 < D := lt_min hd hdelta
  have hcapture (x : W) (hx : dist (x : UniformSpace.Completion W) H.endpoint < D) :
      x ∈ H.subend target := hball x (hx.trans_le (min_le_right _ _))
  refine ⟨target, middle, D, hD, htarget, hmiddle, hcapture, ?_⟩
  intro a r hr hrd eps heps
  have hrlen (k : Fin 2) : r k < (a k).length := (hrd k).trans_le (min_le_left _ _)
  have hrD (k : Fin 2) : r k < D := (hrd k).trans_le (min_le_right _ _)
  have hrd' (k : Fin 2) : r k < min (a k).length d :=
    lt_min (hrlen k) ((hrD k).trans_le (min_le_left _ _))
  have hp (k : Fin 2) : (a k).point (r k) ∈ H.subend target := by
    apply hcapture
    rw [(a k).radial (r k) ⟨hr k, (hrlen k).le⟩]
    exact hrD k
  obtain ⟨base, arm, length, hbaseT, hbaseMem, hlength, hsmooth, hstart, hend,
      harmMem, harmDist, hlengthT, hconnect⟩ := harmpair (fun k => (a k).point (r k)) hp
  let C (k : Fin 2) (n : ℕ) (s : Icc (0 : ℝ) 1) : W := arm k n (length k n * s)
  have hparam (k : Fin 2) (n : ℕ) (s : Icc (0 : ℝ) 1) :
      length k n * s ∈ Icc (0 : ℝ) (length k n) :=
    ⟨mul_nonneg (hlength k n).le s.property.1,
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left s.property.2 (hlength k n).le⟩
  have hCMem (k : Fin 2) (n : ℕ) (s : Icc (0 : ℝ) 1) : C k n s ∈ H.subend middle :=
    harmMem k n _ (hparam k n s)
  have hCDist (k : Fin 2) (n : ℕ) (s t : Icc (0 : ℝ) 1) :
      dist (C k n s) (C k n t) = length k n * dist s t := by
    change dist (arm k n (length k n * s)) (arm k n (length k n * t)) = length k n * dist s t
    rw [harmDist k n _ (hparam k n s) _ (hparam k n t)]
    change |length k n * (s : ℝ) - length k n * (t : ℝ)| = length k n * |(s : ℝ) - t|
    rw [← mul_sub, abs_mul, abs_of_pos (hlength k n)]
  have hlengthR (k : Fin 2) : Tendsto (length k) atTop (𝓝 (r k)) := by
    simpa only [(a k).radial (r k) ⟨hr k, (hrlen k).le⟩] using hlengthT k
  have hCbase (k : Fin 2) : Tendsto
      (fun n => (C k n ⟨0, by norm_num⟩ : UniformSpace.Completion W)) atTop (𝓝 H.endpoint) := by
    simpa only [C, mul_zero, hstart] using hbaseT
  have hCend (k : Fin 2) (n : ℕ) : C k n ⟨1, by norm_num⟩ = (a k).point (r k) := by
    simpa only [C, mul_one] using hend k n
  obtain ⟨phi, hphi, huniform⟩ := hsub a r hr hrd' middle length C
    (fun k n => (hlength k n).le) hlengthR hCMem hCDist hCbase hCend
  have hbaseSmall : ∀ᶠ n in atTop,
      dist (base (phi n) : UniformSpace.Completion W) H.endpoint < eps :=
    (hbaseT.comp hphi.tendsto_atTop).eventually (Metric.ball_mem_nhds H.endpoint heps)
  have hlengthSmall : ∀ᶠ n in atTop, ∀ k : Fin 2, |length k (phi n) - r k| < eps := by
    rw [Filter.eventually_all]
    intro k
    simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using
      ((hlengthR k).comp hphi.tendsto_atTop).eventually (Metric.ball_mem_nhds (r k) heps)
  have hclose : ∀ᶠ n in atTop, ∀ k : Fin 2, ∀ s : Icc (0 : ℝ) 1,
      dist (if (s : ℝ) = 0 then H.endpoint else ((a k).point (r k * s) : UniformSpace.Completion W))
        (C k (phi n) s : UniformSpace.Completion W) < eps := by
    rw [Filter.eventually_all]
    intro k
    exact Metric.tendstoUniformly_iff.mp (huniform k) eps heps
  obtain ⟨n, hbaseSmall, hlengthSmall, hclose⟩ := (hbaseSmall.and (hlengthSmall.and hclose)).exists
  refine ⟨base (phi n), fun k => arm k (phi n), fun k => length k (phi n),
    hbaseSmall, hbaseMem (phi n), fun k => hlength k (phi n), fun k => hsmooth k (phi n),
    fun k => hstart k (phi n), fun k => hend k (phi n),
    fun k s hs => harmMem k (phi n) s hs, fun k s hs t ht => harmDist k (phi n) s hs t ht,
    hlengthSmall, ?_, hconnect (phi n)⟩
  intro k s hs
  let z : Icc (0 : ℝ) 1 := ⟨s / r k,
    ⟨div_nonneg hs.1.le (hr k).le, (div_le_one (hr k)).mpr hs.2⟩⟩
  have hz : (z : ℝ) ≠ 0 := (div_pos hs.1 (hr k)).ne'
  have h := hclose k z
  rw [if_neg hz] at h
  simpa only [C, z, mul_div_cancel₀ _ (hr k).ne', UniformSpace.Completion.dist_eq, dist_comm] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
