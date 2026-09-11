import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDeepMinimizers

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem exists_finiteHorn_common_arms_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ outer : ℕ, ∃ target middle : ℕ,
        closure (H.subend target) ⊆ H.subend middle ∧
        closure (H.subend middle) ⊆ H.subend outer ∧
        ∀ p : Fin 2 → W, (∀ k, p k ∈ H.subend target) →
        ∃ (base : ℕ → W) (arm : Fin 2 → ℕ → ℝ → W) (length : Fin 2 → ℕ → ℝ),
          Tendsto (fun n => (base n : UniformSpace.Completion W)) atTop (𝓝 H.endpoint) ∧
          (∀ n, base n ∈ H.subend target) ∧
          (∀ k n, 0 < length k n) ∧
          (∀ k n, ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (arm k n)) ∧
          (∀ k n, arm k n 0 = base n) ∧ (∀ k n, arm k n (length k n) = p k) ∧
          (∀ k n s, s ∈ Icc 0 (length k n) → arm k n s ∈ H.subend middle) ∧
          (∀ k n s, s ∈ Icc 0 (length k n) → ∀ t ∈ Icc 0 (length k n),
            dist (arm k n s) (arm k n t) = |s - t|) ∧
          (∀ k, Tendsto (length k) atTop
            (𝓝 (dist (p k : UniformSpace.Completion W) H.endpoint))) ∧
          ∀ n s, s ∈ Icc 0 (length 0 n) → ∀ t ∈ Icc 0 (length 1 n),
            ∃ c : ℝ → W, c 0 = arm 0 n s ∧ c 1 = arm 1 n t ∧
              ContMDiff 𝓘(ℝ, ℝ) I3 ∞ c ∧
              (∀ u ∈ Icc (0 : ℝ) 1, c u ∈ H.subend outer) ∧
              ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
                dist (c u) (c v) = |u - v| * dist (arm 0 n s) (arm 1 n t) := by
  classical
  obtain ⟨H₀, hH₀, hmin⟩ := exists_finiteHorn_deep_minimizer_depth (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth outer
  obtain ⟨middle, hmiddle, hconnect⟩ := hmin g H hdepth outer
  obtain ⟨target, htarget, harmpair⟩ := hmin g H hdepth middle
  refine ⟨target, middle, htarget, hmiddle, ?_⟩
  intro p hp
  obtain ⟨d, hd, hdL, htail⟩ := H.cofinal_axial target
  let r (k : Fin 2) : ℝ := dist (p k : UniformSpace.Completion W) H.endpoint
  have hr (k : Fin 2) : 0 < r k := dist_pos.mpr (H.endpoint_missing (p k))
  let m : ℝ := min (r 0) (r 1)
  have hm : 0 < m := lt_min (hr 0) (hr 1)
  have hmk (k : Fin 2) : m ≤ r k := by
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _
  let radius : ℝ := min d m / 2
  have hrad : 0 < radius := half_pos (lt_min hd hm)
  have hradd : radius ≤ d := by
    have h := min_le_left d m
    dsimp [radius]
    linarith
  have hradr (k : Fin 2) : radius < r k := by
    have h := min_le_right d m
    have h' := hmk k
    dsimp [radius]
    linarith
  let rho (n : ℕ) : ℝ := radius / ((n : ℝ) + 1)
  have hrho (n : ℕ) : 0 < rho n := by positivity
  have hrho_le (n : ℕ) : rho n ≤ radius := by
    have hden : 0 < (n : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hden).mpr
    nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hdom (n : ℕ) : rho n ∈ Ioc (0 : ℝ) H.axial.length :=
    ⟨hrho n, ((hrho_le n).trans hradd).trans hdL⟩
  let base (n : ℕ) : W := H.axial.point (rho n)
  have hbaseMem (n : ℕ) : base n ∈ H.subend target :=
    htail (rho n) ⟨hrho n, (hrho_le n).trans hradd⟩
  have hbaseRad (n : ℕ) : dist (base n : UniformSpace.Completion W) H.endpoint = rho n :=
    H.axial.radial (rho n) (hdom n)
  have hrhoT : Tendsto rho atTop (𝓝 (0 : ℝ)) := by
    simpa only [rho, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul radius
  have hbaseT : Tendsto (fun n => (base n : UniformSpace.Completion W)) atTop (𝓝 H.endpoint) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [hbaseRad] using hrhoT
  have hbaseNe (k : Fin 2) (n : ℕ) : base n ≠ p k := by
    intro heq
    have h := hbaseRad n
    rw [heq] at h
    have hlt := (hrho_le n).trans_lt (hradr k)
    change rho n < dist (p k : UniformSpace.Completion W) H.endpoint at hlt
    exact (ne_of_lt hlt) h.symm
  have hcurves (k : Fin 2) (n : ℕ) := harmpair (base n) (hbaseMem n) (p k) (hp k)
  choose gamma hg0 hg1 hgSmooth hgMem hgDist using hcurves
  let length (k : Fin 2) (n : ℕ) : ℝ := dist (base n) (p k)
  have hlength (k : Fin 2) (n : ℕ) : 0 < length k n := dist_pos.mpr (hbaseNe k n)
  let arm (k : Fin 2) (n : ℕ) (s : ℝ) : W := gamma k n (s / length k n)
  have hparam (k : Fin 2) (n : ℕ) {s : ℝ} (hs : s ∈ Icc 0 (length k n)) :
      s / length k n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 (hlength k n).le, (div_le_one (hlength k n)).mpr hs.2⟩
  have harmMem (k : Fin 2) (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 (length k n)) :
      arm k n s ∈ H.subend middle := hgMem k n _ (hparam k n hs)
  have harmSmooth (k : Fin 2) (n : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (arm k n) :=
    (hgSmooth k n).comp (contMDiff_id.div_const (length k n))
  have harm0 (k : Fin 2) (n : ℕ) : arm k n 0 = base n := by
    simpa only [arm, zero_div] using hg0 k n
  have harmEnd (k : Fin 2) (n : ℕ) : arm k n (length k n) = p k := by
    simpa only [arm, div_self (hlength k n).ne'] using hg1 k n
  have harmDist (k : Fin 2) (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 (length k n))
      (t : ℝ) (ht : t ∈ Icc 0 (length k n)) : dist (arm k n s) (arm k n t) = |s - t| := by
    change dist (gamma k n (s / length k n)) (gamma k n (t / length k n)) = |s - t|
    rw [hgDist k n _ (hparam k n hs) _ (hparam k n ht), ← sub_div]
    change |(s - t) / length k n| * length k n = |s - t|
    rw [abs_div, abs_of_pos (hlength k n), div_mul_cancel₀ _ (hlength k n).ne']
  have hlengthT (k : Fin 2) : Tendsto (length k) atTop
      (𝓝 (dist (p k : UniformSpace.Completion W) H.endpoint)) := by
    simpa only [length, UniformSpace.Completion.dist_eq, dist_comm H.endpoint] using
      hbaseT.dist (tendsto_const_nhds (x := (p k : UniformSpace.Completion W)))
  refine ⟨base, arm, length, hbaseT, hbaseMem, hlength, harmSmooth, harm0,
    harmEnd, harmMem, harmDist, hlengthT, ?_⟩
  intro n s hs t ht
  exact hconnect (arm 0 n s) (harmMem 0 n s hs) (arm 1 n t) (harmMem 1 n t ht)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
