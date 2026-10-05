import DifferentialGeometry.Geometry.Fibration.ActualSlimRank
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphModelApplications
import DifferentialGeometry.Geometry.Fibration.ActualCloudPlaneCoherence

/-!
# SGP06: the actual third cloudy packet

Blueprint `master207B.tex`, SGP06 (`thm:fibration-actual-third-cloud`, B:4711–4786), bound to the
actual slim projection `π₃𝓔⁰ = cgpProjMap … cgpQ3Tags` of CGP01's map, FC27's original slim core
`S₃ = π₃𝓔⁰(A₃)` (`fc27SlimSet 7`) and enlargement `S̃₃ = π₃𝓔⁰(Ã₃)` (`fc27SlimSet 8`), and the
radius `r(x) = Σρ(select x)` for ANY selection of preimages. The cloud test is stated exactly as
the hypothesis `hcloud` of `cfs08_slim_cloud` (CFS08/FC27): open balls of radius `r/Γ`, bound `Γr`.

* Generic: `exists_dist_lt_of_hausdorffDist_closedBall_lt_SGP5` (closed-ball Hausdorff closeness
  of a set and a line through its centre gives witnesses both ways),
  `hausdorffEDist_ball_le_of_scaled_coverage_SGP5` (the open-ball test at scale `c` from the
  closed-ball coverage in reference units at radii `R` and `tR`, with radial contraction by `t`),
  `sgp06_radius_SGP5`, `sgp06_parameters_SGP5` ((CP) bookkeeping, `t = 1 − Γ²/2`).
* `sgp06_own_coordinate_SGP5`: the `1`-Lipschitz own coordinate `P` with `P ∘ Φ_i = id` and
  `P(ρ(i)⁻¹π₃𝓔⁰(q)) = η_i(q)` at full markers.
* `sgp06_scaled_coverage_SGP5`: FC25 (`hausdorffDist_coordinate_graph_coverage_le`) in reference
  units with FC03's localization `sgp06_localization`, (SG), exact coordinate coverage
  `sgp06_coordinate_coverage` and the model inputs `sgp06_model_inputs`.
* `sgp06_point_SGP5`: at a core witness, the plane `im DΦ_i(η_i p)` is a line and the cloud test
  holds for every selection (radius comparison by `fc27_slim_cloud_scale`'s (AS)).
* `sgp06_row`: on `LocalChartPacketsRVZ`, planes over `S₃` with dimension one, the cloud test for
  every selection, and SGP05's rank conclusion for the same planes at every preimage.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Closed-ball Hausdorff closeness of a set and a line through its centre yields pointwise
witnesses in both directions (the Hausdorff distance is finite: both sets contain the centre and
lie in the closed ball). -/
theorem exists_dist_lt_of_hausdorffDist_closedBall_lt_SGP5 (S : Set H) (x : H) (hx : x ∈ S)
    (T : E →L[ℝ] H) {R d : ℝ} (hR : 0 ≤ R)
    (hH : hausdorffDist (S ∩ closedBall x R)
      ((fun v => x + T v) '' (univ : Set E) ∩ closedBall x R) < d) :
    (∀ y ∈ S ∩ closedBall x R, ∃ v, ‖T v‖ ≤ R ∧ dist y (x + T v) < d) ∧
      ∀ v, ‖T v‖ ≤ R → ∃ y ∈ S ∩ closedBall x R, dist (x + T v) y < d := by
  have hxS : x ∈ S ∩ closedBall x R := ⟨hx, mem_closedBall_self hR⟩
  have hxL : x ∈ (fun v => x + T v) '' (univ : Set E) ∩ closedBall x R :=
    ⟨⟨0, mem_univ _, by simp⟩, mem_closedBall_self hR⟩
  have hfin : hausdorffEDist (S ∩ closedBall x R)
      ((fun v => x + T v) '' (univ : Set E) ∩ closedBall x R) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨x, hxS⟩ ⟨x, hxL⟩
      (isBounded_closedBall.subset inter_subset_right)
      (isBounded_closedBall.subset inter_subset_right)
  refine ⟨fun y hy => ?_, fun v hv => ?_⟩
  · obtain ⟨z, ⟨⟨v, -, rfl⟩, hz⟩, hyz⟩ := exists_dist_lt_of_hausdorffDist_lt hy hH hfin
    refine ⟨v, ?_, hyz⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hz
    exact hz
  · have hmem : x + T v ∈ (fun v => x + T v) '' (univ : Set E) ∩ closedBall x R := by
      refine ⟨⟨v, mem_univ _, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hv
    obtain ⟨y, hy, hdy⟩ := exists_dist_lt_of_hausdorffDist_lt' hmem hH hfin
    exact ⟨y, hy, by rw [dist_comm]; exact hdy⟩

/-- **The open-ball cloud test from closed-ball coverage in reference units.** Let `Ŝ = c⁻¹S`
(`c > 0`), `x ∈ S`, `T : E →L H`, `0 < R`, `0 < t < 1`. If the closed-ball Hausdorff distance
between `Ŝ` and the line `c⁻¹x + im T` is `< δ/2` at the radii `R` and `tR`, and the radial slack
`(1 − t)R ≤ δ/2`, then the open-ball test holds at the actual scale:
`hausdorffEDist (S ∩ B(x, cR)) ((x + im T) ∩ B(x, cR)) ≤ cδ`. -/
theorem hausdorffEDist_ball_le_of_scaled_coverage_SGP5 (S Sh : Set H) (x : H) (hx : x ∈ S)
    {c : ℝ} (hc : 0 < c) (hSh : Sh = (fun y => c⁻¹ • y) '' S) (T : E →L[ℝ] H)
    {R t δ r d : ℝ} (hR : 0 < R) (ht0 : 0 < t) (ht1 : t < 1)
    (hcovR : hausdorffDist (Sh ∩ closedBall (c⁻¹ • x) R)
      ((fun v => c⁻¹ • x + T v) '' (univ : Set E) ∩ closedBall (c⁻¹ • x) R) < δ / 2)
    (hcovt : hausdorffDist (Sh ∩ closedBall (c⁻¹ • x) (t * R))
      ((fun v => c⁻¹ • x + T v) '' (univ : Set E) ∩ closedBall (c⁻¹ • x) (t * R)) < δ / 2)
    (hslack : (1 - t) * R ≤ δ / 2) (hr : c * R = r) (hd : c * δ = d) :
    hausdorffEDist (S ∩ ball x r) ((AffineSubspace.mk' x T.range : Set H) ∩ ball x r) ≤
      ENNReal.ofReal d := by
  have hxh : c⁻¹ • x ∈ Sh := by rw [hSh]; exact ⟨x, hx, rfl⟩
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  obtain ⟨hA, -⟩ := exists_dist_lt_of_hausdorffDist_closedBall_lt_SGP5 Sh (c⁻¹ • x) hxh T
    hR.le hcovR
  obtain ⟨-, hB⟩ := exists_dist_lt_of_hausdorffDist_closedBall_lt_SGP5 Sh (c⁻¹ • x) hxh T
    (mul_pos ht0 hR).le hcovt
  have hscale : ∀ y z : H, dist y z = c * dist (c⁻¹ • y) (c⁻¹ • z) := by
    intro y z
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hci, ← mul_assoc, mul_inv_cancel₀ hc.ne',
      one_mul]
  refine hausdorffEDist_le_of_mem_edist (fun y hy => ?_) (fun z hz => ?_)
  · -- set → plane: the scaled witness, contracted radially by `t`
    have hyS : c⁻¹ • y ∈ Sh ∩ closedBall (c⁻¹ • x) R := by
      refine ⟨by rw [hSh]; exact ⟨y, hy.1, rfl⟩, ?_⟩
      rw [mem_closedBall]
      have h1 := hy.2
      rw [mem_ball, hscale, ← hr] at h1
      exact (lt_of_mul_lt_mul_left h1 hc.le).le
    obtain ⟨v, hv, hdv⟩ := hA _ hyS
    refine ⟨x + T ((c * t) • v), ⟨?_, ?_⟩, ?_⟩
    · rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
      exact LinearMap.mem_range.mpr ⟨_, rfl⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (mul_pos hc ht0), ← hr]
      have hpos := mul_pos (mul_pos hc hR) (sub_pos.mpr ht1)
      calc c * t * ‖T v‖ ≤ c * t * R := mul_le_mul_of_nonneg_left hv (mul_pos hc ht0).le
        _ < c * R := by nlinarith
    · rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : dist y (x + c • T v) = c * dist (c⁻¹ • y) (c⁻¹ • x + T v) := by
        rw [hscale, smul_add, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      have h2 : dist (x + c • T v) (x + T ((c * t) • v)) = c * (1 - t) * ‖T v‖ := by
        rw [dist_add_left, map_smul, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs,
          show c - c * t = c * (1 - t) by ring, abs_of_pos (mul_pos hc (by linarith))]
      have h3 : c * (1 - t) * ‖T v‖ ≤ c * (δ / 2) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc.le
        exact (mul_le_mul_of_nonneg_left hv (by linarith)).trans hslack
      calc dist y (x + T ((c * t) • v)) ≤ dist y (x + c • T v) +
            dist (x + c • T v) (x + T ((c * t) • v)) := dist_triangle _ _ _
        _ ≤ c * (δ / 2) + c * (δ / 2) := by
          rw [h1, h2]
          exact add_le_add (mul_le_mul_of_nonneg_left hdv.le hc.le) h3
        _ = d := by rw [← hd]; ring
  · -- plane → set: contract first, then use the coverage at radius `tR`
    obtain ⟨hzA, hzr⟩ := hz
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub] at hzA
    obtain ⟨v, hv⟩ := hzA
    have hzv : z = x + T v := by
      have h : T v = z - x := hv
      rw [h]
      abel
    have hTv : ‖T v‖ < c * R := by
      rw [mem_ball, hzv, dist_eq_norm, add_sub_cancel_left, ← hr] at hzr
      exact hzr
    have hTv' : ‖T ((c⁻¹ * t) • v)‖ ≤ t * R := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hci ht0)]
      have : c⁻¹ * ‖T v‖ < R := by
        rw [inv_mul_lt_iff₀ hc]
        exact hTv
      nlinarith
    obtain ⟨yh, ⟨hyh, hyhB⟩, hdy⟩ := hB _ hTv'
    rw [hSh] at hyh
    obtain ⟨y, hyS, rfl⟩ := hyh
    refine ⟨y, ⟨hyS, ?_⟩, ?_⟩
    · rw [mem_ball, ← hr, hscale]
      rw [mem_closedBall] at hyhB
      have hpos := mul_pos (mul_pos hc hR) (sub_pos.mpr ht1)
      calc c * dist (c⁻¹ • y) (c⁻¹ • x) ≤ c * (t * R) := mul_le_mul_of_nonneg_left hyhB hc.le
        _ < c * R := by nlinarith
    · rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : dist (x + c • T ((c⁻¹ * t) • v)) y =
          c * dist (c⁻¹ • x + T ((c⁻¹ * t) • v)) (c⁻¹ • y) := by
        rw [hscale, smul_add, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      have h2 : dist z (x + c • T ((c⁻¹ * t) • v)) = (1 - t) * ‖T v‖ := by
        rw [hzv, dist_add_left, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
          dist_eq_norm]
        have h : T v - t • T v = (1 - t) • T v := by rw [sub_smul, one_smul]
        rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have h3 : (1 - t) * ‖T v‖ ≤ c * (δ / 2) := by
        calc (1 - t) * ‖T v‖ ≤ (1 - t) * (c * R) :=
              mul_le_mul_of_nonneg_left hTv.le (by linarith)
          _ = c * ((1 - t) * R) := by ring
          _ ≤ c * (δ / 2) := mul_le_mul_of_nonneg_left hslack hc.le
      calc dist z y ≤ dist z (x + c • T ((c⁻¹ * t) • v)) +
            dist (x + c • T ((c⁻¹ * t) • v)) y := dist_triangle _ _ _
        _ ≤ c * (δ / 2) + c * (δ / 2) := by
          rw [h1, h2]
          exact add_le_add h3 (mul_le_mul_of_nonneg_left hdy.le hc.le)
        _ = d := by rw [← hd]; ring

/-- SGP06's radius in reference units: `3ρ_i/4 ≤ ρ_s ≤ 5ρ_i/4` gives
`3Σ/4 ≤ Σρ_s/ρ_i ≤ 5Σ/4`, and the scale identities `ρ_i(r̂/Γ) = Σρ_s/Γ`, `ρ_i(Γr̂) = Γ(Σρ_s)`. -/
theorem sgp06_radius_SGP5 {sg ri rs Γ : ℝ} (hsg : 0 ≤ sg) (hri : 0 < ri) (hΓ : 0 < Γ)
    (h1 : 3 * ri / 4 ≤ rs) (h2 : rs ≤ 5 * ri / 4) :
    3 * sg / 4 ≤ sg * rs / ri ∧ sg * rs / ri ≤ 5 * sg / 4 ∧
      ri * (sg * rs / ri / Γ) = sg * rs / Γ ∧ ri * (Γ * (sg * rs / ri)) = Γ * (sg * rs) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hri]
    nlinarith
  · rw [div_le_iff₀ hri]
    nlinarith
  · field_simp
  · field_simp

/-- SGP06's parameter bookkeeping under (CP): with `3Σ/4 ≤ r̂ ≤ 5Σ/4`, `R = r̂/Γ` and
`t = 1 − Γ²/2`, both test radii `R, tR` lie in `(0, 1/100)`, both coverage budgets are below
`Γr̂/2`, and the radial slack `(1 − t)R` is `≤ Γr̂/2`. -/
theorem sgp06_parameters_SGP5 {Γ sg eg C rh : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hC : 0 < C) (hsgC : sg < Γ ^ 3 / (100 * C))
    (hegΓ : eg < Γ * sg / 100) (hrlo : 3 * sg / 4 ≤ rh) (hrhi : rh ≤ 5 * sg / 4) :
    0 < rh / Γ ∧ rh / Γ < 1 / 100 ∧ 0 < 1 - Γ ^ 2 / 2 ∧ 1 - Γ ^ 2 / 2 < 1 ∧
      0 < (1 - Γ ^ 2 / 2) * (rh / Γ) ∧ (1 - Γ ^ 2 / 2) * (rh / Γ) < 1 / 100 ∧
      3 * (2 * eg + C * (rh / Γ) ^ 2 / 2) < Γ * rh / 2 ∧
      3 * (2 * eg + C * ((1 - Γ ^ 2 / 2) * (rh / Γ)) ^ 2 / 2) < Γ * rh / 2 ∧
      (1 - (1 - Γ ^ 2 / 2)) * (rh / Γ) ≤ Γ * rh / 2 := by
  have hRh : rh / Γ < 1 / 100 := test_radius_lt_of_parameters hΓ hsgΓ hrhi
  have hRh0 : 0 < rh / Γ := div_pos (by linarith) hΓ
  have hSC : C * sg < Γ ^ 3 / 100 := by
    rw [lt_div_iff₀ (by positivity)] at hsgC
    nlinarith
  have hbud := coverage_budget_lt_half hΓ hsg hC hSC hegΓ (by linarith) (by linarith) (r := rh)
  have ht0 : 0 < 1 - Γ ^ 2 / 2 := by nlinarith
  have ht1 : 1 - Γ ^ 2 / 2 < 1 := by nlinarith
  have hsq : ((1 - Γ ^ 2 / 2) * (rh / Γ)) ^ 2 ≤ (rh / Γ) ^ 2 := by
    rw [mul_pow]
    have h1 : (1 - Γ ^ 2 / 2) ^ 2 ≤ 1 := by nlinarith
    have h2 := sq_nonneg (rh / Γ)
    nlinarith
  have hslack : Γ ^ 2 / 2 * (rh / Γ) = Γ * rh / 2 := by field_simp
  refine ⟨hRh0, hRh, ht0, ht1, mul_pos ht0 hRh0, ?_, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [sub_sub_cancel]
    exact hslack.le

end Generic

section Pointwise

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- **SGP06, the own coordinate.** A `1`-Lipschitz linear functional `P` on the block space (the
first axis coordinate of the own block of `i`) with `P ∘ Φ_i = id` and `P(ρ(i)⁻¹π₃𝓔⁰(q)) = η_i(q)`
wherever the slim cutoff of `i` is `1`. -/
theorem sgp06_own_coordinate_SGP5 (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) :
    ∃ Pc : BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ, (∀ z, ‖Pc z‖ ≤ ‖z‖) ∧
      (∀ u, Pc (sgpFullGraph L Z i sgn c zsgn zc u) = u) ∧
      ∀ q, L.slim.cutoff i.1 q = 1 →
        Pc ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) =
          (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q := by
  let f : BlockSpace (fun _ : CGPTag L Z => ℝ²) →ₗ[ℝ] ℝ :=
    { toFun := fun z => (z (.inr (.inl i))).fst 0
      map_add' := fun z w => by simp
      map_smul' := fun a z => by simp }
  have hf : ∀ z, ‖f z‖ ≤ 1 * ‖z‖ := by
    intro z
    rw [one_mul]
    calc ‖f z‖ = ‖(z (.inr (.inl i))).fst 0‖ := rfl
      _ ≤ ‖(z (.inr (.inl i))).fst‖ := PiLp.norm_apply_le _ 0
      _ ≤ ‖z (.inr (.inl i))‖ := WithLp.norm_fst_le _ _
      _ ≤ ‖z‖ := PiLp.norm_apply_le _ _
  refine ⟨f.mkContinuous 1 hf, fun z => ?_, fun u => ?_, fun q hq => ?_⟩
  · rw [LinearMap.mkContinuous_apply]
    simpa using hf z
  · rw [LinearMap.mkContinuous_apply]
    change (sgpFullGraph L Z i sgn c zsgn zc u (.inr (.inl i))).fst 0 = u
    rw [sgpFullGraph_own]
    simp [planeAxis_apply]
  · rw [LinearMap.mkContinuous_apply]
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have h1 : cgpProjMap L Z (cgpQ3Tags L Z) q (.inr (.inl i)) =
        cgpGlobalMap L Z q (.inr (.inl i)) :=
      cgpProjMap_apply_of_mem L Z (slim_mem_cgpQ3Tags L Z i) q
    have h2 : cgpGlobalMap L Z q (.inr (.inl i)) =
        WithLp.toLp 2 ((ρ i.1 * L.slim.cutoff i.1 q) • planeAxis ((L.slim.centre i.1 hi).coord q),
          ρ i.1 * L.slim.cutoff i.1 q) := rfl
    change (((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) (.inr (.inl i))).fst 0 = _
    rw [PiLp.smul_apply, h1, h2, hq, mul_one]
    have hc : (ρ i.1)⁻¹ * (ρ i.1 * (L.slim.centre i.1 hi).coord q) =
        (L.slim.centre i.1 hi).coord q := by
      rw [← mul_assoc, inv_mul_cancel₀ (hρ i.1).ne', one_mul]
    simpa [planeAxis_apply] using hc

/-- **SGP06, FC25 in reference units** (`hausdorffDist_coordinate_graph_coverage_le` with
`F = ρ(i)⁻¹π₃𝓔⁰`, `η = η_i`, `D = {B(i, Lρ(i)), |η_i| ≤ 8ℓ}`, `Φ = Φ_i`, the own coordinate,
`X = F(Ã₃)`, centre `F(p)`): for a core witness `p` and `0 < R < 1/100`, the closed-ball Hausdorff
distance between `F(Ã₃)` and the tangent line `F(p) + im DΦ_i(η_i p)` is at most
`3(2e + C_*R²/2)`. -/
theorem sgp06_scaled_coverage_SGP5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hs0 : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) {eg : ℝ} (heg : 0 ≤ eg)
    (hSG : ∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
      |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) x - sgpFullGraph L Z i sgn c zsgn zc
        ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg)
    {p : X} (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      7 * (10 ^ 5 * Δ))
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1 / 100) :
    hausdorffDist ((fun q => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) '' fc27SlimSet L 8 ∩
        closedBall ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p) R)
      ((fun v => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p +
          fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)
            ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p) v) ''
          (univ : Set ℝ) ∩
        closedBall ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p) R) ≤
      3 * (2 * eg + sgpGraphBound * R ^ 2 / 2) := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hΔ0 : 0 < Δ := by linarith
  have hG := four_le_sgpGraphBound_SGP4
  obtain ⟨Pc, hP, hgraph, hPq⟩ := sgp06_own_coordinate_SGP5 L Z i sgn c zsgn zc
  have h78 : 7 * (10 ^ 5 * Δ) ≤ 8 * 10 ^ 5 * Δ := by nlinarith
  have hη8 : |(L.slim.centre i.1 hi).coord p| ≤ 8 * 10 ^ 5 * Δ := hη.trans h78
  have hcutp : L.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 L hi]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hp hη8
  have hPx := hPq p hcutp
  obtain ⟨hreg, hsecond⟩ := sgp06_model_inputs L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq
    (Pc ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p)) R
  have hlocal : ∀ y ∈ (fun q => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) '' fc27SlimSet L 8 ∩
      closedBall ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p) R,
      ∃ q ∈ {q | q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(L.slim.centre i.1 hi).coord q| ≤ 8 * 10 ^ 5 * Δ},
        (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q = y ∧
          Pc y = (L.slim.centre i.1 hi).coord q := by
    rintro y ⟨⟨q, -, rfl⟩, hy⟩
    have hdist : dist (cgpProjMap L Z (cgpQ3Tags L Z) q) (cgpProjMap L Z (cgpQ3Tags L Z) p) ≤
        R * ρ i.1 := by
      rw [mem_closedBall, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hri),
        inv_mul_le_iff₀ hri] at hy
      linarith
    obtain ⟨hqb, hcutq, -, hηq⟩ := sgp06_localization L Z hΔ i hp hη hR0.le hR1 hdist
    exact ⟨q, ⟨hqb, hηq.le⟩, rfl, hPq q hcutq⟩
  have happrox : ∀ q ∈ {q | q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
      |(L.slim.centre i.1 hi).coord q| ≤ 8 * 10 ^ 5 * Δ},
      dist ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q)
        (sgpFullGraph L Z i sgn c zsgn zc ((L.slim.centre i.1 hi).coord q)) ≤ eg := by
    intro q hq
    rw [dist_eq_norm]
    exact (hSG q hq.1 hq.2).le
  have hcover : ∀ u ∈ closedBall (Pc ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p)) R,
      ∃ q ∈ {q | q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
        |(L.slim.centre i.1 hi).coord q| ≤ 8 * 10 ^ 5 * Δ},
        (L.slim.centre i.1 hi).coord q = u ∧
          (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q ∈
            (fun q => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) '' fc27SlimSet L 8 := by
    intro u hu
    rw [hPx, mem_closedBall, Real.dist_eq] at hu
    have hu8 : |u| ≤ 8 * 10 ^ 5 * Δ := by
      have h1 := abs_sub_abs_le_abs_sub u ((L.slim.centre i.1 hi).coord p)
      have h2 : (1 : ℝ) / 100 ≤ 10 ^ 5 * Δ := by nlinarith
      nlinarith
    obtain ⟨q, hq8, hqb, hqu, -⟩ := sgp06_coordinate_coverage L hΔ0.le i hu8
    exact ⟨q, ⟨hqb, by rw [hqu]; exact hu8⟩, hqu, ⟨q, hq8, rfl⟩⟩
  have hk := hausdorffDist_coordinate_graph_coverage_le
    (fun q => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) (L.slim.centre i.1 hi).coord
    {q | q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧ |(L.slim.centre i.1 hi).coord q| ≤ 8 * 10 ^ 5 * Δ}
    (sgpFullGraph L Z i sgn c zsgn zc) Pc hP hgraph
    ((fun q => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) '' fc27SlimSet L 8)
    ((ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) p) ⟨p, ⟨i, hp, hη8⟩, rfl⟩ hR0
    (by linarith) heg hreg hsecond hlocal happrox hcover
  rw [hPx] at hk
  exact hk

/-- **SGP06 at one core witness.** For a slim reference `i` with (SG)'s value clause for `Φ_i`, a
core witness `p` (`|η_i(p)| ≤ 7ℓ`) and (CP) (`0 < Σ < min(Γ/200, Γ³/(100C_*))`,
`0 < e < ΓΣ/100`): the plane `im DΦ_i(η_i p)` is a line, and for ANY selection of preimages over
`S̃₃` the open-ball cloud test at `x = π₃𝓔⁰(p)` with radius `r(x) = Σρ(select x)` holds:
`hausdorffEDist (S̃₃ ∩ B(x, r/Γ)) ((x + im DΦ_i(η_i p)) ∩ B(x, r/Γ)) ≤ Γr`. -/
theorem sgp06_point_SGP5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hs0 : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (hegΓ : eg < Γ * sg / 100)
    (hSG : ∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
      |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤ 8 * 10 ^ 5 * Δ →
      ‖(ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) x - sgpFullGraph L Z i sgn c zsgn zc
        ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg)
    {p : X} (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      7 * (10 ^ 5 * Δ)) :
    Module.finrank ℝ (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)
        ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)).range = 1 ∧
      ∀ select : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X,
        (∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8,
          cgpProjMap L Z (cgpQ3Tags L Z) (select x) = x) →
        hausdorffEDist (cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 ∩
            ball (cgpProjMap L Z (cgpQ3Tags L Z) p)
              (sg * ρ (select (cgpProjMap L Z (cgpQ3Tags L Z) p)) / Γ))
          ((AffineSubspace.mk' (cgpProjMap L Z (cgpQ3Tags L Z) p)
              (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)
                ((L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)).range :
                Set (BlockSpace (fun _ : CGPTag L Z => ℝ²))) ∩
            ball (cgpProjMap L Z (cgpQ3Tags L Z) p)
              (sg * ρ (select (cgpProjMap L Z (cgpQ3Tags L Z) p)) / Γ)) ≤
          ENNReal.ofReal (Γ * (sg * ρ (select (cgpProjMap L Z (cgpQ3Tags L Z) p)))) := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hΔ0 : 0 < Δ := by linarith
  have hG := four_le_sgpGraphBound_SGP4
  obtain ⟨hTlow, -⟩ := sgp05_model_reference L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq
    ((L.slim.centre i.1 hi).coord p)
  refine ⟨?_, fun select hselect => ?_⟩
  · have hinj : Function.Injective (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)
        ((L.slim.centre i.1 hi).coord p)) := by
      intro z w hzw
      have h := hTlow (z - w)
      rw [map_sub, hzw, sub_self, norm_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have hinj' : Function.Injective (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc)
        ((L.slim.centre i.1 hi).coord p) : ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²)) := hinj
    have h := LinearMap.finrank_range_of_inj hinj'
    rw [Module.finrank_self] at h
    exact h
  have h78 : 7 * (10 ^ 5 * Δ) ≤ 8 * 10 ^ 5 * Δ := by nlinarith
  have hη8 : |(L.slim.centre i.1 hi).coord p| ≤ 8 * 10 ^ 5 * Δ := hη.trans h78
  have hcutp : L.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 L hi]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hp hη8
  have hp8 : p ∈ fc27SlimSet L 8 := ⟨i, hp, hη8⟩
  have hsel := hselect _ ⟨p, hp8, rfl⟩
  have hmark : 0 < cgpMarker L Z (.inr (.inl i))
      (cgpProjMap L Z (cgpQ3Tags L Z) (select (cgpProjMap L Z (cgpQ3Tags L Z) p))) := by
    rw [hsel]
    have h1 : cgpProjMap L Z (cgpQ3Tags L Z) p (.inr (.inl i)) =
        cgpGlobalMap L Z p (.inr (.inl i)) :=
      cgpProjMap_apply_of_mem L Z (slim_mem_cgpQ3Tags L Z i) p
    change 0 < (cgpProjMap L Z (cgpQ3Tags L Z) p (.inr (.inl i))).snd
    rw [h1]
    change 0 < ρ i.1 * L.slim.cutoff i.1 p
    rw [hcutp, mul_one]
    exact hri
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  obtain ⟨hAS1, hAS2⟩ := (fc27_slim_cloud_scale L Z hΔ hΛ hsmall).1 i _ hmark
  have hrad := sgp06_radius_SGP5 hsg.le hri hΓ hAS1 hAS2
  obtain ⟨hrlo, hrhi, hr, hd⟩ := hrad
  have hpar := sgp06_parameters_SGP5 hΓ hΓ1 hsg hsgΓ (by linarith) hsgC hegΓ hrlo hrhi
  obtain ⟨hRh0, hRh, ht0, ht1, htR0, htR, hbud, hbudt, hslack⟩ := hpar
  have hcovR := sgp06_scaled_coverage_SGP5 L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq
    heg.le hSG hp hη hRh0 hRh
  have hcovt := sgp06_scaled_coverage_SGP5 L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0 huniq
    heg.le hSG hp hη htR0 htR
  exact hausdorffEDist_ball_le_of_scaled_coverage_SGP5
    (cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8)
    ((fun q => (ρ i.1)⁻¹ • cgpProjMap L Z (cgpQ3Tags L Z) q) '' fc27SlimSet L 8)
    (cgpProjMap L Z (cgpQ3Tags L Z) p) ⟨p, hp8, rfl⟩ hri (Set.image_image _ _ _).symm
    (fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) ((L.slim.centre i.1 hi).coord p))
    hRh0 ht0 ht1 (lt_of_le_of_lt hcovR hbud) (lt_of_le_of_lt hcovt hbudt) hslack hr hd

end Pointwise

section Row

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_SGP5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_SGP5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_SGP5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **SGP06, the actual third cloudy packet** (cloud test in the form CFS08/FC27 consume). For
`0 < Γ < 1` and (CP) `0 < Σ < min(Γ/200, Γ³/(100C_*))`, `0 < e < min(1/100, ΓΣ/100)` there are
SGP04/SGP05's thresholds such that on every actual RVZ family with their hypotheses there are planes
`plane x` over `S₃ = π₃𝓔⁰(A₃)` (those of SGP05: `im DΦ_i(η_i p)` at a core witness) with
(1) `dim plane x = 1`; (2) for ANY selection of preimages over `S̃₃ = π₃𝓔⁰(Ã₃)`, the open-ball
cloud test at radius `r(x) = Σρ(select x)`:
`hausdorffEDist (S̃₃ ∩ B(x, r/Γ)) ((x + plane x) ∩ B(x, r/Γ)) ≤ Γr` (exactly `cfs08_slim_cloud`'s
`hcloud`); (3) SGP05's rank conclusion for `plane x` at EVERY preimage `q` of `x`, in the units of
a reference `i`: the projection is onto, its normal error is `≤ eν` (`< Γν`), and
`ν/2 ≤ ‖P_q v‖` on the `g`-orthogonal complement of the kernel, `‖P_q v‖ ≤ 3C_*ν`. -/
theorem sgp06_row {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hΓ : 0 < Γ)
    (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
              fc27SlimSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1) ∧
          (∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 8,
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
                (select x) = x) →
            ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
                fc27SlimSet P.toLocalChartFamily 7,
              hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 8 ∩
                  ball x (sg * ρ (select x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (select x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (select x)))) ∧
          ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
              fc27SlimSet P.toLocalChartFamily 7,
            ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              x →
            let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, hrow⟩ := sgp05_row hΔ hβ₂ hβ₂1 heg heg1
  have hθ2 : θ ^ 2 / 10 ^ 6 < 1 / 100 := by
    have : θ ^ 2 < 1 := by nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hrowP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ2 hβ1 hLmax hΛ hLΛ he hT
    hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hσ1 : σs < 1 / 100 := hσθ.trans hθ2
  have hpt : ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
      fc27SlimSet P.toLocalChartFamily 7,
      ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        Module.finrank ℝ W = 1 ∧
        (∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
              fc27SlimSet P.toLocalChartFamily 8,
            cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
              (select x) = x) →
          hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 8 ∩
              ball x (sg * ρ (select x) / Γ))
            ((AffineSubspace.mk' x W :
                Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
              ball x (sg * ρ (select x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (select x)))) ∧
        ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
          x →
        let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
    rintro x ⟨p, ⟨i, hp, hηp⟩, rfl⟩
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have hηp' : |(P.slim.centre i.1 hi).coord p| ≤ 7 * (10 ^ 5 * Δ) := by
      rw [← mul_assoc]
      exact hηp
    have hrowi := hrowP i
    obtain ⟨sgn, c, zsgn, zc, hsgn, hzsgn, hSG, hrk⟩ := hrowi
    have hs01 := sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hσs.le hσ1.le hi
    obtain ⟨-, -, -, huniq, hzero01, -⟩ := hs01
    have hs0 : ∀ k (hk : k ∈ P.zero.centres),
        sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk → 1 ≤ (P.zero.zero k hk).radius / ρ i.1 :=
      fun k hk hm => (one_le_div_twenty_SGP4 hΔ hT).trans (hzero01 k hk hm).1
    have hpoint := sgp06_point_SGP5 P.toLocalChartFamily P.zero hΔ hΛ hLΛ i sgn c zsgn zc hsgn
      hzsgn hs0 huniq hΓ hΓ1 hsg hsgΓ hsgC heg hegΓ (fun y hy hyη => (hSG y hy hyη).1) hp hηp'
    obtain ⟨hfin, hcl⟩ := hpoint
    have hrkp := hrk p hp hηp'
    exact ⟨_, hfin, hcl, i, hrkp⟩
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun select hselect x hx =>
    (hplane x hx).2.1 select hselect, fun x hx => (hplane x hx).2.2⟩

end Row

end DifferentialGeometry.Geometry.Collapse
