import DifferentialGeometry.Analysis.Calculus.Inverse.DerivativePerturbation
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem MapCPConvergenceOn.eventually_injOn
    {K : Set E} {F : ℕ → E → E} (hF : MapCPConvergenceOn K 1 F id)
    (hconvex : Convex ℝ K)
    (hdiff : ∀ᶠ n in atTop, ∀ z ∈ K, DifferentiableAt ℝ (F n) z) :
    ∀ᶠ n in atTop, InjOn (F n) K := by
  obtain ⟨N, hN⟩ := hF (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop N, hdiff] with n hn hdn
  exact Coordinates.injOn_of_fderiv_near_id hconvex (by norm_num) hdn
    (fun z hz => neumannOfDerivNorm (hdn z hz) (hN n hn 1 le_rfl z hz))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eventually_lipschitzOnWith_of_mapCPConvergenceOn_compacts
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℕ → E → F}
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ U →
      MapCPConvergenceOn S 1 f (fun _ ↦ 0))
    (hf : ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, ∀ x ∈ S, DifferentiableAt ℝ (f n) x)
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ n in atTop, LipschitzOnWith ε (f n) K := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let P : Set (E × E) := (K ×ˢ K) ∩ {z | dist z.1 z.2 ≤ δ}
  let c : (E × E) × ℝ → E := fun z ↦ (1 - z.2) • z.1.1 + z.2 • z.1.2
  let S : Set E := c '' (P ×ˢ Icc (0 : ℝ) 1)
  have hP : IsCompact P :=
    (hK.prod hK).inter_right (isClosed_le continuous_dist continuous_const)
  have hc : Continuous c :=
    ((continuous_const.sub continuous_snd).smul continuous_fst.fst).add
      (continuous_snd.smul continuous_fst.snd)
  have hS : IsCompact S := (hP.prod isCompact_Icc).image hc
  have hseg {x y : E} (hx : x ∈ K) (hy : y ∈ K) (hxy : dist x y ≤ δ) :
      segment ℝ x y ⊆ S := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨((x, y), t), ⟨⟨⟨hx, hy⟩, hxy⟩, ht⟩, rfl⟩
  have hSU : S ⊆ U := by
    rintro z ⟨⟨⟨x, y⟩, t⟩, ⟨⟨⟨hx, _hy⟩, hxy⟩, ht⟩, rfl⟩
    change dist x y ≤ δ at hxy
    apply hδU
    apply Metric.closedBall_subset_cthickening hx δ
    exact (convex_closedBall x δ).segment_subset (Metric.mem_closedBall_self hδ.le)
      (by simpa only [Metric.mem_closedBall, dist_comm] using hxy)
      (by rw [segment_eq_image]; exact ⟨t, ht, rfl⟩)
  have hεR : 0 < (ε : ℝ) := hε
  obtain ⟨N₁, hN₁⟩ := hconv S hS hSU ε hεR
  obtain ⟨N₀, hN₀⟩ := hconv K hK hKU (ε * δ / 2) (by positivity)
  filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop N₀, hf S hS hSU]
    with n hn₁ hn₀ hfn
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  by_cases hxy : dist x y ≤ δ
  · have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ (f n) z‖ ≤ ε := by
      intro z hz
      have h := hN₁ n hn₁ 1 le_rfl z (hseg hx hy hxy hz)
      simpa only [mapDerivNorm, sub_zero, norm_iteratedFDeriv_one] using h
    exact (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hfn z (hseg hx hy hxy hz)) hbound
      (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
  · have hx0 : ‖f n x‖ ≤ ε * δ / 2 := by
      simpa only [mapDerivNorm, sub_zero, norm_iteratedFDeriv_zero] using
        hN₀ n hn₀ 0 (by omega) x hx
    have hy0 : ‖f n y‖ ≤ ε * δ / 2 := by
      simpa only [mapDerivNorm, sub_zero, norm_iteratedFDeriv_zero] using
        hN₀ n hn₀ 0 (by omega) y hy
    have hdist : δ ≤ ‖x - y‖ := by
      simpa only [dist_eq_norm] using le_of_lt (lt_of_not_ge hxy)
    calc
      ‖f n x - f n y‖ ≤ ‖f n x‖ + ‖f n y‖ := norm_sub_le _ _
      _ ≤ (ε : ℝ) * δ := by linarith
      _ ≤ (ε : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_left hdist ε.coe_nonneg

private theorem eventually_differentiableAt_on_compacts
    [LocallyCompactSpace E] {U : Set E} (hU : IsOpen U) {f : ℕ → E → F}
    (hf : ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, DifferentiableOn ℝ (f n) S) :
    ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, ∀ x ∈ S, DifferentiableAt ℝ (f n) x := by
  intro S hS hSU
  obtain ⟨V, hV, hSV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hS hU hSU
  filter_upwards [hf (closure V) hVc hVU] with n hn x hx
  exact (hn x (subset_closure (hSV hx))).differentiableAt
    (mem_of_superset (hV.mem_nhds (hSV hx)) subset_closure)

theorem eventually_lipschitzOnWith_of_mapCPConvergenceOn_compacts_of_differentiableOn
    [LocallyCompactSpace E]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℕ → E → F}
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ U →
      MapCPConvergenceOn S 1 f (fun _ ↦ 0))
    (hf : ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, DifferentiableOn ℝ (f n) S)
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ n in atTop, LipschitzOnWith ε (f n) K :=
  eventually_lipschitzOnWith_of_mapCPConvergenceOn_compacts hU hK hKU hconv
    (eventually_differentiableAt_on_compacts hU hf) hε

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem eventually_injOn_of_mapCPConvergenceOn_compacts
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℕ → E → E}
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 1 f id)
    (hf : ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, ∀ x ∈ S, DifferentiableAt ℝ (f n) x) :
    ∀ᶠ n in atTop, InjOn (f n) K := by
  have hδconv : ∀ S : Set E, IsCompact S → S ⊆ U →
      MapCPConvergenceOn S 1 (fun n x ↦ f n x - x) (fun _ ↦ 0) := by
    intro S hS hSU
    simpa only [MapCPConvergenceOn, mapDerivNorm, sub_zero, id_eq] using hconv S hS hSU
  have hδdiff : ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, ∀ x ∈ S, DifferentiableAt ℝ (fun x ↦ f n x - x) x := by
    intro S hS hSU
    exact (hf S hS hSU).mono fun _ hn x hx ↦ (hn x hx).sub differentiableAt_id
  have h := eventually_lipschitzOnWith_of_mapCPConvergenceOn_compacts
    hU hK hKU hδconv hδdiff (ε := (1 / 2 : ℝ≥0)) (by norm_num)
  filter_upwards [h] with n hn
  apply injOn_iff_injective.mpr
  exact ((isometry_subtype_coe : Isometry (fun x : K ↦ (x : E))).antilipschitzWith
    |>.add_sub_lipschitzWith (g := fun x : K ↦ f n x) hn.to_restrict (by norm_num)).injective

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem eventually_injOn_of_mapCPConvergenceOn_compacts_of_differentiableOn
    [LocallyCompactSpace E]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℕ → E → E}
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S 1 f id)
    (hf : ∀ S : Set E, IsCompact S → S ⊆ U →
      ∀ᶠ n in atTop, DifferentiableOn ℝ (f n) S) :
    ∀ᶠ n in atTop, InjOn (f n) K :=
  eventually_injOn_of_mapCPConvergenceOn_compacts hU hK hKU hconv
    (eventually_differentiableAt_on_compacts hU hf)

end DifferentialGeometry.CheegerGromovCompactness
