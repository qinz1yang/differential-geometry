import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTestPP
import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphScale

/-!
# FC27's first-cloud test with (PP) AND the scale clause

Blueprint `master207B.tex`, FC27 (B:1658) / CFS27 (B:3626–3686) / EDP01's scale coordinate: the
first-cloud planes built from CFS27-pruned TCP05 graphs whose scale block is constant
(`tcp05_row_scale_GAF5`) lie in the kernel of the scale marker `v_s = (·)_{scale}.snd`, besides
the small-marker rule (PP).

* `tcp05_pruned_scale_GAF5`: pruning keeps the zero scale derivative.
* `tcp06_centre_pps_GAF5`, `tcp06_point_of_mem_pps_GAF5`, `tcp06_planes_pps_GAF5`: TCP06 with (PP)
  and `plane x ≤ ker v_s`.
* `fc27_first_test_pps_GAF5`: `fc27_first_test_pp_GAF5` with a further conjunct
  `∀ x ∈ S₁, plane x ≤ ker v_s` (placed before the (PP) conjunct).
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

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF5u
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5u
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5u
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP05 with CFS27's pruning, keeping the scale clause** (`tcp05_pruned_GAF5` for data whose
derivative has zero scale block; the pruned derivative has zero scale marker). With `1 ≤ Δ`,
`0 ≤ Λ`, `Λ·10⁶Δ ≤ 1/4`, `Λ·200 ≤ 1/4`: TCP05's
data at every circle centre `i` (a smooth `Φ_i` with own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` and
(TG) on `{‖η_i‖ ≤ 8} ∩ B(i, 200ρ(i))` with error `e`) gives data with the same clauses whose
derivative is annihilated by the marker of every retained block with `ρ(c_a) ≤ ρ(i)/2`
(`Φ_i' = π_{keep_i} ∘ Φ_i`). -/
theorem tcp05_pruned_scale_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4)
    {eg : ℝ}
    (hTCP : ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ a h, fderiv ℝ Φ a h (cgpScaleTag P.toLocalChartFamily P.zero) = 0) :
    ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ i / 2 → ∀ u v,
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0) ∧
        ∀ u v, blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) (fderiv ℝ Φ u v) = 0 := by
  classical
  intro i hi
  refine Exists.elim (hTCP i hi) (fun Φ hΦ => ?_)
  have hsm : ContDiff ℝ ∞ Φ := hΦ.1
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hd : Differentiable ℝ Φ := hsm.differentiable (by simp)
  let Kp := blockRestrict (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
  have hD : ∀ u, fderiv ℝ (Kp ∘ Φ) u = Kp.comp (fderiv ℝ Φ u) := fun u => by
    rw [fderiv_comp u Kp.differentiableAt (hd u), Kp.fderiv]
  refine ⟨Kp ∘ Φ, Kp.contDiff.comp hsm, fun j hj a => ?_,
    fun a => clm_comp_bounds_GAF5 Kp (norm_blockRestrict_le _) hsm2 (fun y => (hΦ.2.2.1 y).1)
      (fun y => (hΦ.2.2.1 y).2) a, fun x hx hx8 => ⟨?_, fun w => ?_⟩, fun a ha u v => ?_,
    fun u v => ?_⟩
  · change blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i)) (Φ a) (.inl j) = _
    have hk : (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈
        firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i) := by
      rw [← hj]
      exact firstKeep_own_GAF5 P.toLocalChartFamily P.zero j
    rw [blockRestrict_apply, ite_eq_left hk]
    exact hΦ.2.1 j hj a
  · have hfix := firstPrune_globalMap_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall hΛ200 hx
    have h1 : (ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
        (Kp ∘ Φ) (cgpCircleCoord P.toLocalChartFamily i hi x) =
        Kp ((ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
          Φ (cgpCircleCoord P.toLocalChartFamily i hi x)) := by
      rw [map_sub, map_smul]
      change _ = (ρ i)⁻¹ • blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
        (cgpGlobalMap P.toLocalChartFamily P.zero x) - _
      rw [hfix]
      rfl
    rw [h1]
    exact lt_of_le_of_lt (norm_blockRestrict_apply_le _ _) (hΦ.2.2.2.1 x hx hx8).1
  · have hfix := firstPrune_mvfderiv_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall hΛ200 hx w
    have h1 : (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
        fderiv ℝ (Kp ∘ Φ) (cgpCircleCoord P.toLocalChartFamily i hi x)
          (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w) =
        Kp ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
          fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)) := by
      rw [hD, map_sub, map_smul]
      change _ = (ρ i)⁻¹ • blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
        (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w) - _
      rw [hfix]
      rfl
    rw [h1]
    exact (norm_blockRestrict_apply_le _ _).trans ((hΦ.2.2.2.1 x hx hx8).2 w)
  · rw [hD]
    exact firstPrune_marker_GAF5 P.toLocalChartFamily P.zero a ha _
  · rw [hD]
    change blockMarkerCLM _ (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ i))
      (fderiv ℝ Φ u v)) = 0
    rw [blockMarkerCLM_apply, blockRestrict_apply]
    split_ifs
    · rw [hΦ.2.2.2.2 u v]
      rfl
    · rfl


/-- **TCP06 at one circle centre, with (PP).** As `tcp06_centre_KA8`, for a model `Φ` whose
derivative is annihilated by every retained marker with `ρ(c_a) ≤ ρ(j)/2`: the plane
`W = im DΦ(η_j p)` has in addition `W ≤ ker v_a` for every preimage `q` of `x` and every retained
marker with `ρ(c_a) < ρ(q)/5`. -/
theorem tcp06_centre_pps_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm : ContDiff ℝ ∞ Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1))
    (hb : ∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst)
    (hTG : ∀ x ∈ ball j.1 (200 * ρ j.1),
      ‖cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) x‖ ≤ 8 →
      ‖(ρ j.1)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
          Φ (cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) x)‖ <
        eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
            fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily j.1
              ((Set.Finite.mem_toFinset _).mp j.2) x)
              (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j.1
                ((Set.Finite.mem_toFinset _).mp j.2)) x w)‖ ≤
          eg * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner x w w))
    (hprune : ∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ j.1 / 2 → ∀ u v,
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0)
    (hscale : ∀ u v,
      blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) (fderiv ℝ Φ u v) = 0)
    {p : X} (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hηp : ‖cgpCircleCoord P.toLocalChartFamily j.1 ((Set.Finite.mem_toFinset _).mp j.2) p‖ ≤
      7) {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpGlobalMap P.toLocalChartFamily P.zero p = x) :
    ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      Module.finrank ℝ W = 2 ∧
      hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
          fc04Set P.toLocalChartFamily P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
        ((AffineSubspace.mk' x W :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) ∧
      (∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      W ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpScaleTag P.toLocalChartFamily P.zero) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) ∧
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          W ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  subst hpx
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hC : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hpoint := tcp06_point_KA8 P hΛ hΛ200 hj j rfl Φ hsm2 hown (fun a => (hb a).2) hΓ hΓ1 hsg
    hsgΓ hC hsgC heg hegΓ (fun y hy hyη => (hTG y hy hyη).1) hp hηp
  have hrank := fun q (hq : cgpGlobalMap P.toLocalChartFamily P.zero q =
      cgpGlobalMap P.toLocalChartFamily P.zero p) =>
    tcp06_rank_point_KA8 P hβ hγβ hj j rfl Φ hsm2 hown (fun a => (hb a).1) heg1
      (fun y hy hyη => (hTG y hy hyη).2) hp hηp hq
  refine ⟨_, hpoint.1, hpoint.2, ⟨j, hrank⟩, ?_, fun q hq a ha => ?_⟩
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
    rw [LinearMap.mem_ker]
    exact hscale _ u
  have hfm := tcp06_full_marker_KA8 P hj j rfl hp (le_trans hηp (by norm_num)) hq
  have hsc := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ j.1) (mem_ball.mp hfm.1) hΛ200
  have hrj := hρ j.1
  have hsa : ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ j.1 / 2 := by linarith [hsc.2]
  intro w hw
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
  rw [LinearMap.mem_ker]
  exact hprune a hsa _ u

/-- **TCP06 at one point of the core image, with (PP)**, from pruned TCP05 data at every circle
centre (`tcp05_pruned_GAF5`'s conclusion). -/
theorem tcp06_point_of_mem_pps_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100)
    (hTCP : ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ i / 2 → ∀ u v,
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0) ∧
        ∀ u v, blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) (fderiv ℝ Φ u v) = 0)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7) :
    ∃ W : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      Module.finrank ℝ W = 2 ∧
      hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
          fc04Set P.toLocalChartFamily P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
        ((AffineSubspace.mk' x W :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x) ∧
      (∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := W.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      W ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpScaleTag P.toLocalChartFamily P.zero) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) ∧
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          W ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  refine Exists.elim hx (fun p hp => ?_)
  refine Exists.elim hp.1 (fun j hj' => ?_)
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  refine Exists.elim (hTCP j.1 hj) (fun Φ hΦ => ?_)
  exact tcp06_centre_pps_GAF5 P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ j Φ hΦ.1
    (hΦ.2.1 j rfl) hΦ.2.2.1 hΦ.2.2.2.1 hΦ.2.2.2.2.1 hΦ.2.2.2.2.2 hj'.1 hj'.2
    hp.2

/-- **TCP06 on the whole core image, with (PP)**: the planes of `tcp06_point_of_mem_pps_GAF5`,
chosen over `S₁`. -/
theorem tcp06_planes_pps_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100)
    (hTCP : ∀ i (hi : i ∈ P.circle.centres),
      ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiff ℝ ∞ Φ ∧
        (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
          Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
        (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
        (∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
              Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ i / 2 → ∀ u v,
          blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (fderiv ℝ Φ u v) = 0) ∧
        ∀ u v, blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) (fderiv ℝ Φ u v) = 0) :
    ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
        Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        Module.finrank ℝ (plane x) = 2) ∧
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
            fc04Set P.toLocalChartFamily P.zero 8 ∩
            ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
          ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) ∧
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (cgpGlobalMap P.toLocalChartFamily P.zero) q)
        Function.Surjective Pq ∧
        (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
          1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
        ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpScaleTag P.toLocalChartFamily P.zero) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
      ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
        ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
        ∀ a : CGPMarkerIndex P.toLocalChartFamily,
          ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
          plane x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpMarkerTag P.toLocalChartFamily P.zero a) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  have hpt := fun x (hx : x ∈ cgpGlobalMap P.toLocalChartFamily P.zero ''
      fc04Set P.toLocalChartFamily P.zero 7) =>
    tcp06_point_of_mem_pps_GAF5 P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hTCP hx
  choose! plane hplane using hpt
  exact ⟨plane, fun x hx => (hplane x hx).1, fun x hx => (hplane x hx).2.1,
    fun x hx => (hplane x hx).2.2.1, fun x hx => (hplane x hx).2.2.2.1,
    fun x hx => (hplane x hx).2.2.2.2⟩

end Packets

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF5u {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF5u {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF5u {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27's first-cloud test with (PP)** (stage `0`): `fc27_first_test_GAF4` (TCP06's thresholds
and hypotheses verbatim) with the planes built from CFS27-pruned TCP05 graphs, and in addition the
small-marker rule (PP): for every `x ∈ S₁`, preimage `q` of `x` and retained marker with
`ρ(c_a) < ρ(q)/5`, `plane x ≤ ker v_a`. -/
theorem fc27_first_test_pps_GAF5 {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          Module.finrank ℝ (plane x) = gafStageDim 0 ∧
            plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
        (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 0) (sel x) = x) →
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
            hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
                ball x (sg * ρ (sel x) / Γ))
              ((AffineSubspace.mk' x (plane x) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
          ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
          let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (cgpGlobalMap P.toLocalChartFamily P.zero) q)
          Function.Surjective Pq ∧
          (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
              (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
            1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
          ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
          plane x ≤ LinearMap.ker ((blockMarkerCLM
            (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (cgpScaleTag P.toLocalChartFamily P.zero) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
        ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
            x →
          ∀ a : CGPMarkerIndex P.toLocalChartFamily,
            ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
            plane x ≤ LinearMap.ker ((blockMarkerCLM
              (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, hrow⟩ :=
    tcp05_row_scale_GAF5 heg heg1 hν hν1
  refine ⟨σ, hσ, hσ1, min η₂ (1 / 10000000), min γ₀ (1 / 20), ηc, θ, lt_min hη₂ (by norm_num),
    lt_min hγ₀ (by norm_num), hηc, hθ, hθ1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, h⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31
  have hTCP := h P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    (h16.trans (min_le_left _ _)) (h17.trans (min_le_left _ _)) h18
    (h19.trans (min_le_left _ _)) h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hnum := tcp06_numbers_KA8 hΔ h1 h4 (h17.trans (min_le_right _ _))
    (h16.trans (min_le_right _ _))
  have hΔ1 : 1 ≤ Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hTCP' := tcp05_pruned_scale_GAF5 P.toLocalChartPackets hΔ1 h1 hsmall hnum.1 hTCP
  have hT := tcp06_planes_pps_GAF5 P.toLocalChartPackets h1 hnum.1 (h16.trans (min_le_right _ _))
    hnum.2 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hTCP'
  refine hT.elim fun plane hp => ?_
  have hconv := fc27_first_of_tcp06_GAF4 P.toLocalChartFamily P.zero plane hsg.le hp.1 hp.2.1
  refine ⟨plane, hconv.1, hconv.2, fun x hx => ?_, fun x hx => ?_, fun x hx q hq a ha => ?_⟩
  · rw [gafCloud_zero_GAF4] at hx
    exact hp.2.2.1 x hx
  · rw [gafCloud_zero_GAF4] at hx
    exact hp.2.2.2.1 x hx
  · rw [gafCloud_zero_GAF4] at hx
    have hq' : cgpGlobalMap P.toLocalChartFamily P.zero q = x := by
      rw [← cgpProjMap_univ_GAF P.toLocalChartFamily P.zero]
      exact hq
    exact hp.2.2.2.2 x hx q hq' a ha

end DifferentialGeometry.Geometry.Collapse
