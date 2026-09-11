import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornApproximatePair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RayClampedParameter

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem exists_finiteHorn_ray_approximation_in_subend_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ outer : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
          hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
          ∃ A : RayApproximation H a b lo hi, A.connector_index = outer := by
  classical
  obtain ⟨H₀, hH₀, hpairs⟩ := exists_finiteHorn_approximate_pair_depth (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth outer
  obtain ⟨target, middle, D, hD, htarget, hmiddle, hcapture, hpair⟩ := hpairs g H hdepth outer
  refine ⟨D / 4, by positivity, ?_⟩
  intro a b lo hi hlo _hlohi hia hib hid
  let ray : Fin 2 → EndRay H.endpoint := ![a, b]
  have hilength (k : Fin 2) : hi k ≤ (ray k).length := by
    fin_cases k
    · exact hia
    · exact hib
  let R (k : Fin 2) : ℝ := min (ray k).length (D / 2)
  have hR (k : Fin 2) : 0 < R k := lt_min (ray k).length_pos (half_pos hD)
  have hRlength (k : Fin 2) : R k ≤ (ray k).length := min_le_left _ _
  have hRD (k : Fin 2) : R k < D :=
    (min_le_right _ _).trans_lt (half_lt_self hD)
  have hiR (k : Fin 2) : hi k ≤ R k :=
    le_min (hilength k) ((hid k).trans (by linarith : D / 4 ≤ D / 2))
  have htargetMem (k : Fin 2) (s : ℝ) (hs : s ∈ Icc (lo k) (hi k)) :
      (ray k).point s ∈ H.subend target := by
    apply hcapture
    rw [(ray k).radial s ⟨(hlo k).trans_le hs.1, hs.2.trans (hilength k)⟩]
    exact (hs.2.trans (hid k)).trans_lt (by linarith : D / 4 < D)
  let eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have heps (n : ℕ) : 0 < eps n := by positivity
  have heps1 (n : ℕ) : eps n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hepsT : Tendsto eps atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let rho (k : Fin 2) (n : ℕ) : ℝ := R k * (1 - eps n / 2)
  have hrho (k : Fin 2) (n : ℕ) : 0 < rho k n :=
    mul_pos (hR k) (by linarith [heps1 n])
  have hrhoR (k : Fin 2) (n : ℕ) : rho k n < R k := by
    have h := mul_lt_mul_of_pos_left (by linarith [heps n] : 1 - eps n / 2 < 1) (hR k)
    simpa only [mul_one] using h
  have hrhoSmall (k : Fin 2) (n : ℕ) : rho k n < min (ray k).length D :=
    lt_min ((hrhoR k n).trans_le (hRlength k)) ((hrhoR k n).trans (hRD k))
  have hrhoT (k : Fin 2) : Tendsto (rho k) atTop (𝓝 (R k)) := by
    simpa only [rho, zero_div, sub_zero, mul_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hepsT.div_const 2)).const_mul (R k)
  have hdata (n : ℕ) := hpair ray (fun k => rho k n) (fun k => hrho k n)
    (fun k => hrhoSmall k n) (eps n) (heps n)
  choose base arm length hbase hbaseMem hlength hsmooth hstarts hends hmem hmin hlenError hpoint hconnect
    using hdata
  let parameter (k : Fin 2) (n : ℕ) (s : ℝ) : ℝ :=
    length n k * (min s (rho k n) / rho k n)
  let error (k : Fin 2) (n : ℕ) : ℝ := eps n + (R k - rho k n)
  have herrorT (k : Fin 2) : Tendsto (error k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [error, sub_self, add_zero] using
      hepsT.add ((tendsto_const_nhds (x := R k)).sub (hrhoT k))
  have hparameterError (k : Fin 2) (n : ℕ) (s : ℝ) (hs : s ∈ Icc (lo k) (hi k)) :
      |parameter k n s - s| < error k n :=
    (clamped_ray_parameter_error (hrho k n) (hrhoR k n).le
      ⟨((hlo k).trans_le hs.1).le, hs.2.trans (hiR k)⟩).trans_lt
        (by
          simpa only [error, add_comm] using
            add_lt_add_right (hlenError n k) (R k - rho k n))
  have hpointError (k : Fin 2) (n : ℕ) (s : ℝ) (hs : s ∈ Icc (lo k) (hi k)) :
      dist (arm n k (parameter k n s)) ((ray k).point s) < error k n :=
    (ray k).dist_lt_of_clamped_approximation (hrho k n) (hrhoR k n).le (hRlength k)
      (arm n k) (hpoint n k) ⟨(hlo k).trans_le hs.1, hs.2.trans (hiR k)⟩
  refine ⟨{
    target_index := target
    arm_index := middle
    connector_index := outer
    target_buffer := htarget
    arm_buffer := hmiddle
    target_mem := ⟨htargetMem 0, htargetMem 1⟩
    base := base
    arm := fun k n => arm n k
    length := fun k n => length n k
    length_pos := fun k n => hlength n k
    arm_smooth := fun k n => (hsmooth n k).contMDiffOn
    arm_mem := fun k n s hs => hmem n k s hs
    parameter := parameter
    starts := fun k n => hstarts n k
    minimizing := fun k n s hs t ht => hmin n k s hs t ht
    parameter_mono := fun k n => by
      change MonotoneOn
        (fun s : ℝ => length n k * (min s (rho k n) / rho k n)) (Icc (lo k) (hi k))
      exact (clamped_ray_parameter_monotone (hlength n k).le (hrho k n)).monotoneOn _
    parameter_mem := fun k n s hs => clamped_ray_parameter_mem (hlength n k).le (hrho k n)
      ((hlo k).trans_le hs.1).le
    connectors := fun n s hs t ht => by
      obtain ⟨c, hc0, hc1, hcSmooth, hcMem, hcDist⟩ := hconnect n s hs t ht
      exact ⟨c, hc0, hc1, hcSmooth.contMDiffOn, hcMem, hcDist⟩
    uniform := by
      intro eta heta
      have hepsEta : ∀ᶠ n in atTop, eps n < eta := hepsT.eventually_lt_const heta
      have herrorEta : ∀ᶠ n in atTop, ∀ k : Fin 2, error k n < eta / 4 := by
        rw [Filter.eventually_all]
        intro k
        exact (herrorT k).eventually_lt_const (by positivity)
      filter_upwards [hepsEta, herrorEta] with n hn herror
      refine ⟨(hbase n).trans hn, ?_⟩
      intro s hs t ht
      have hpa := (hparameterError 0 n s hs).trans (herror 0)
      have hpb := (hparameterError 1 n t ht).trans (herror 1)
      have hxa := (hpointError 0 n s hs).trans (herror 0)
      have hxb := (hpointError 1 n t ht).trans (herror 1)
      have hquarter : eta / 4 < eta := by linarith
      refine ⟨hpa.trans hquarter, hpb.trans hquarter, hxa.trans hquarter, hxb.trans hquarter, ?_⟩
      have htri₁ := dist_triangle (arm n 0 (parameter 0 n s)) (a.point s)
        (arm n 1 (parameter 1 n t))
      have htri₂ := dist_triangle (a.point s) (b.point t) (arm n 1 (parameter 1 n t))
      have htri₃ := dist_triangle (a.point s) (arm n 0 (parameter 0 n s)) (b.point t)
      have htri₄ := dist_triangle (arm n 0 (parameter 0 n s)) (arm n 1 (parameter 1 n t)) (b.point t)
      rw [dist_comm (b.point t) (arm n 1 (parameter 1 n t))] at htri₂
      rw [dist_comm (a.point s) (arm n 0 (parameter 0 n s))] at htri₃
      change dist (arm n 0 (parameter 0 n s)) (a.point s) < eta / 4 at hxa
      change dist (arm n 1 (parameter 1 n t)) (b.point t) < eta / 4 at hxb
      apply abs_lt.mpr
      constructor <;> linarith
  }, rfl⟩

theorem exists_finiteHorn_ray_approximation_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) → (∀ k, lo k ≤ hi k) →
          hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
          Nonempty (RayApproximation H a b lo hi) := by
  obtain ⟨H₀, hH₀, happ⟩ := exists_finiteHorn_ray_approximation_in_subend_depth (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth
  obtain ⟨d, hd, hlocal⟩ := happ g H hdepth 0
  refine ⟨d, hd, ?_⟩
  intro a b lo hi hlo hlohi hia hib hid
  obtain ⟨A, _hA⟩ := hlocal a b lo hi hlo hlohi hia hib hid
  exact ⟨A⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
