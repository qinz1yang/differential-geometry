import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRowsSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G6 part 2: the frontier of `M₂` and the end disks

* `frontier_M2_STR`: `frontier M₂ = {u = κ} ∪ {h = -1/4}` (`M₂ = {u ≤ κ, h ≤ -1/4}` is closed; a
  point with `u < κ` and `h < -1/4` is interior, and the two zero functions are regular at the
  points of their zero sets, so such a point takes values above the level arbitrarily near).
* `t_zero_or_one_iff_STR`: on the edge parent, `t ∈ {0, 1}` iff `u = κ`.
* `frequently_sphere_above_level_STR`: near a point of `{u = κ, h = -7/8}` there are points of
  `{u = κ}` above the level (the radial dilation of the disk coordinate in the edge chart keeps
  `t`, hence `u = κ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_FrontierSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_FrontierSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The frontier of `M₂` -/

theorem M1set_isClosed_STR : IsClosed M1set_STR :=
  (isClosed_le continuous_uW_STR continuous_const).inter
    (isClosed_le X135Radial.height_continuous continuous_const)

theorem frontier_M2_STR : frontier (cutChoice_STR ballZeroDomainsL_STR).M₂ =
    {p | uW_STR p = 4 / 5} ∪ {p | X135Radial.height p = -(1 / 4 : ℝ)} := by
  rw [M2_eq_STR, M1set_isClosed_STR.frontier_eq]
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or] at hc
    apply hn
    refine mem_interior.2 ⟨{y | uW_STR y < 4 / 5 ∧ X135Radial.height y < -(1 / 4 : ℝ)}, ?_, ?_,
      ⟨lt_of_le_of_ne hp.1 hc.1, lt_of_le_of_ne hp.2 hc.2⟩⟩
    · intro y hy
      exact ⟨hy.1.le, hy.2.le⟩
    · exact (isOpen_lt continuous_uW_STR continuous_const).inter
        (isOpen_lt X135Radial.height_continuous continuous_const)
  · rintro (hp | hp)
    · have hh : X135Radial.height p < -(1 / 4 : ℝ) := height_lt_of_uW_STR hp
      refine ⟨⟨hp.le, hh.le⟩, fun hint => ?_⟩
      have hr : ratioBall_STI p = 0 := ratioBall_eq_zero_iff_STI.2 hp
      have hip : (𝓡∂ 3).IsInteriorPoint p :=
        isInteriorPoint_of_height_STR (by linarith)
      have hfreq := frequently_lt_of_mfderiv_STR hip (ratioBall_regular_STI p hr)
      have hnb : interior M1set_STR ∈ nhds p := isOpen_interior.mem_nhds hint
      obtain ⟨y, hy, hyM⟩ := (hfreq.and_eventually hnb).exists
      have h1 : uW_STR y ≤ 4 / 5 := (interior_subset hyM).1
      have h2 : ratioBall_STI y < 0 := by rw [hr] at hy; exact hy
      have h3 : (4 / 5 : ℝ) < uW_STR y := by
        have : ratioBall_STI y = 4 / 5 - uW_STR y := rfl
        linarith
      linarith
    · have hu : uW_STR p < 4 / 5 := uW_lt_kap_of_height_STR hp
      refine ⟨⟨hu.le, hp.le⟩, fun hint => ?_⟩
      have hip : (𝓡∂ 3).IsInteriorPoint p :=
        isInteriorPoint_of_height_STR (by rw [hp]; norm_num)
      have hreg := X135Radial.carrier_height_regular p ⟨by rw [hp]; norm_num, by rw [hp]; norm_num⟩
      have hfreq := frequently_gt_of_mfderiv_STR hip hreg
      have hnb : interior M1set_STR ∈ nhds p := isOpen_interior.mem_nhds hint
      obtain ⟨y, hy, hyM⟩ := (hfreq.and_eventually hnb).exists
      have h1 : X135Radial.height y ≤ -(1 / 4 : ℝ) := (interior_subset hyM).2
      rw [hp] at hy
      linarith

/-! ## The end disks lie on `{u = κ}` -/

theorem t_zero_or_one_iff_STR {w : Wc.Carrier} (hw : w ∈ edgeParent_STR) :
    (tOf_STR (sphereSecond w.val) = 0 ∨ tOf_STR (sphereSecond w.val) = 1) ↔
      uW_STR w = 4 / 5 := by
  have hk := kap_lt_norm_of_edgeParent_STR hw
  have hre : (sphereSecond w.val).re < ‖sphereSecond w.val‖ := hw.2
  have hid := four_t_STR hk hre
  have hl := lam1_pos_of_STR hre hk
  set t := tOf_STR (sphereSecond w.val) with ht
  have hkap : kap_STR = 4 / 5 := rfl
  have hu : uW_STR w = (sphereSecond w.val).re := rfl
  rw [hu]
  constructor
  · intro h
    have h0 : 4 * t * (1 - t) = 0 := by rcases h with h | h <;> rw [h] <;> ring
    rw [h0] at hid
    have : kap_STR - (sphereSecond w.val).re = 0 := by
      rcases mul_eq_zero.1 hid.symm with h1 | h1
      · exact absurd h1 hl.ne'
      · exact h1
    linarith
  · intro h
    have h0 : kap_STR - (sphereSecond w.val).re = 0 := by linarith
    rw [h0, mul_zero] at hid
    have h1 : t * (1 - t) = 0 := by linarith
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by linarith)

/-- Near a point of `{u = κ, h = -7/8}` there are points of the sphere `{u = κ}` above the level
(the radial dilation of the disk coordinate in the edge chart keeps `t`, hence `u = κ`). -/
theorem frequently_sphere_above_level_STR {p : Wc.Carrier} (hpu : uW_STR p = 4 / 5)
    (hh : X135Radial.height p = -(7 / 8 : ℝ)) :
    ∃ᶠ y in nhds p, uW_STR y = 4 / 5 ∧ -(7 / 8 : ℝ) < X135Radial.height y := by
  have hs : ‖sphereFirst p.val‖ ^ 2 = 1 / 16 := by
    rw [height_eq_of_first_STR] at hh
    linarith
  have hn := norm_sphereFirst_sq_add p.val
  have hk : kap_STR < ‖sphereSecond p.val‖ := by
    have h0 := norm_nonneg (sphereSecond p.val)
    norm_num [kap_STR]
    nlinarith
  have hy : p ∈ edgeParent_STR := by
    refine ⟨by linarith, ?_⟩
    have : (sphereSecond p.val).re = 4 / 5 := hpu
    norm_num [kap_STR] at hk
    linarith
  set x₀ := edgeInv_STR p.val with hx₀
  have hρ : rho2_STR x₀ = 1 := by
    rw [hx₀, rho2_edgeInv_STR, hs]
    norm_num
  have hsrc : rho2_STR x₀ < 4 := by rw [hρ]; norm_num
  have ht0 : tOf_STR (sphereSecond p.val) = 0 ∨ tOf_STR (sphereSecond p.val) = 1 :=
    (t_zero_or_one_iff_STR hy).2 hpu
  have hpt : edgeToW_STR x₀ = p := Subtype.ext (edgeMap_edgeInv_STR hy)
  have hcont : ContinuousAt (fun ε => edgeToW_STR (radPath_STR x₀ ε)) 0 := by
    have h1 : ContinuousAt edgeToW_STR (radPath_STR x₀ 0) := by
      rw [radPath_zero_STR]
      exact continuousOn_edgeToW_STR.continuousAt (isOpen_edgeSource_STR.mem_nhds hsrc)
    exact h1.comp (continuous_radPath_STR x₀).continuousAt
  have htend : Filter.Tendsto (fun ε => edgeToW_STR (radPath_STR x₀ ε)) (nhdsWithin 0 (Ioi 0))
      (nhds p) := by
    have h0 : edgeToW_STR (radPath_STR x₀ 0) = p := by rw [radPath_zero_STR]; exact hpt
    have := hcont.tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine htend.frequently ?_
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  have hρε : rho2_STR (radPath_STR x₀ ε) = (1 + ε) ^ 2 := by
    rw [rho2_radPath_STR, hρ]
    ring
  have hlt : rho2_STR (radPath_STR x₀ ε) < 4 := by
    rw [hρε]
    nlinarith [hε.1, hε.2]
  have hpar := edgeToW_mem_parent_STR hlt
  have hseq := sphereFirst_sq_edgeToW_STR hlt
  rw [hρε] at hseq
  have hheight : X135Radial.height (edgeToW_STR (radPath_STR x₀ ε)) = (1 + ε) ^ 2 / 8 - 1 := by
    rw [height_eq_of_first_STR]
    simp only [edgeToW_STR] at hseq ⊢
    rw [hseq]
    ring
  refine ⟨?_, ?_⟩
  · refine (t_zero_or_one_iff_STR hpar).1 ?_
    rw [tOf_edgeToW_STR hlt, radPath_two_STR]
    have : x₀ 2 = tOf_STR (sphereSecond p.val) := by rw [hx₀, edgeInv_two_STR]
    rw [this]
    exact ht0
  · rw [hheight]
    nlinarith [hε.1, hε.2]

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
