import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07LevelSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreStandardTypeGaf07
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle

/-!
# GAF07 fibre types: `j = 3` standard smooth `S²` / `T²` (review 70), `j = 1` circles

Blueprint `master207B.tex`, GAF07 (B:6049–6063): "For `j = 3` they are smooth `S²` or `T²` fibers";
review 70 (D70-2..4, lane C14-SLIM-STD). The weak theorem (`Gaf02Chain.gaf07_slim_level_GAFC`,
homeomorphism to the original slim level) stays. Here the whole adjusted level
`{p ∈ Y_i | g_i(p) = a}`, `|a| < 4·10⁵Δ`, of the chain's adjusted axis coordinate is the exact image
of a smooth embedding (`IsSmoothEmbedding`) of the STANDARD `ClosureSphere` or of the standard
`Torus`.

Route: FC34's straight-line family `h_τ = (1 − τ)η_i + τg_i` on the slab of the centre's STORED
packet (radius `r = 5·10⁵Δ`, normalized instances), regular along the level by the gauge estimates
(`Gaf02Chain.gaf07_slim_gauge_GAFC`: LFR20.1's right inverse of gauge `≤ 4/3`,
`‖Dg_i − Dη_i‖ < c₃`), with its whole trace in the compact slab `{|η_i| ≤ 4.01·10⁵Δ}`;
C14-SLIM-STD's `SlimCentre.gaf07_slim_fibre_standard_type_SSTD` (for the manifold orientation `oM`,
`K ≥ 5`) makes the end level `{h_1 = a}` diffeomorphic to `ClosureSphere` or `Torus`; the
regular-fibre inclusion into `M` is a smooth embedding.

* `Gaf02Chain.gaf07_slim_gauge_GAFC` (BASES-free): ONE `H ∈ [0, 1/1000)` with the right inverse and
  the derivative comparison at every point of every `Y_i`.
* `Gaf02Chain.gaf07_slim_level_standard_GAFC`: GAF07 `j = 3`, standard smooth type.
* `surjective_mfderiv_straightLine_restrict_GAFC`: the gauge submersion criterion at one point of an
  open set (generic).
* `nonempty_homeomorph_circleLevel_circle_GAFC`, `Gaf02ChainE.gaf07_circle_whole_fibre_circle_GAFC`
  (`j = 1`): every WHOLE circle fibre over `B₁` is homeomorphic to `Circle`.
* Consumer `gaf07_slim_level_standard_C14Z_GAFC`: on the final family `LocalChartPacketsC14Z` (its
  OWN orientation parameter `oM`), for a chain with (JA) on its `LocalChartPacketsC14` projection.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- A straight-line slice `(1 − τ)η + τg`, restricted to an open set, is a submersion at `y` when
`dη` has a right inverse of gauge `≤ K` and `|dg − dη| ≤ cν`, `cK < 1` (gauge form at one point). -/
theorem surjective_mfderiv_straightLine_restrict_GAFC {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] (U : TopologicalSpace.Opens M) (η f : M → ℝ) (y : U) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) (hη : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) η y)
    (hf : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f y) (ν : E3 → ℝ) {c K : ℝ} (hc : 0 ≤ c)
    (hcK : c * K < 1)
    (hR : ∃ R : ℝ →L[ℝ] E3, (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) η y).comp R =
      ContinuousLinearMap.id ℝ ℝ ∧ ∀ w, ν (R w) ≤ K * ‖w‖)
    (hD : ∀ v : E3, ‖(show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f y) v -
      (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) η y) v‖ ≤ c * ν v) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z : U => (1 - τ) • η z + τ • f z) y) := by
  rw [DifferentialGeometry.mfderiv_restrict_open (fun x => (1 - τ) • η x + τ • f x) U y]
  have hd := (hη.hasMFDerivAt.const_smul (1 - τ)).add (hf.hasMFDerivAt.const_smul τ)
  rw [show (fun x => (1 - τ) • η x + τ • f x) = (1 - τ) • η + τ • f from rfl, hd.mfderiv]
  obtain ⟨R, hRid, hRn⟩ := hR
  set Dη : E3 →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) η y
  set Df : E3 →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f y
  refine surjective_of_right_inverse_perturbation_nu_GAFC Dη ((1 - τ) • Dη + τ • Df) R hRid ν
    hRn (fun v => ?_) hc hcK
  have hdiff : ((1 - τ) • Dη + τ • Df) v - Dη v = τ • (Df v - Dη v) := by
    have hap : ((1 - τ) • Dη + τ • Df) v = (1 - τ) • Dη v + τ • Df v := rfl
    rw [hap, sub_smul, one_smul, smul_sub]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  have h1 := hD v
  have h0 : 0 ≤ ‖Df v - Dη v‖ := norm_nonneg _
  calc τ * ‖Df v - Dη v‖ ≤ 1 * ‖Df v - Dη v‖ := mul_le_mul_of_nonneg_right hτ.2 h0
    _ ≤ c * ν v := by rw [one_mul]; exact h1

/-- **The original circle level is a topological circle** (LFR07's fibres are `S¹`,
`CircleChart.nonempty_circle_diffeomorph`): for `‖a‖ < 100`,
`{p ∈ B(c_i, 200ρ(c_i)) | η_i(p) = a} ≃ₜ Circle`. -/
theorem nonempty_homeomorph_circleLevel_circle_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs
    K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    {a : ℝ²} (ha : ‖a‖ < 100) :
    Nonempty ({p | p ∈ ball i.1 (200 * ρ i.1) ∧
      cgpCoord P.toLocalChartFamily P.zero (.inl i) p = a} ≃ₜ Circle) := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hr := hρ i.1
  have hc0 := P.circle.chart_center i.1 hj
  let c := P.circle.chart i.1 hj
  let mR : MetricSpace X := mX.rescale (ρ i.1)⁻¹ (inv_pos.mpr hr)
  have hc : c.center = i.1 := hc0
  have hz : a ∈ planeBallOpens 100 := mem_planeBallOpens_iff.mpr ha
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  have hmem : ∀ x : X, x ∈ @ball X mX.toPseudoMetricSpace i.1 (200 * ρ i.1) ↔
      x ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    intro x
    rw [hc]
    exact (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).symm
  let _ := regularFiberChartedSpace (diskPreimageMap (ball c.center 200) isOpen_ball c.coord
      c.contMDiffOn_coord.continuousOn 100) ⟨a, hz⟩
    (contMDiff_diskPreimageMap isOpen_ball c.contMDiffOn_coord 100)
    (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball c.contMDiffOn_coord c.rank 100 x)
  obtain ⟨φ⟩ := c.nonempty_circle_diffeomorph hdim ⟨a, hz⟩
  refine ⟨Homeomorph.trans ?_ φ.toHomeomorph.symm⟩
  exact
    { toFun := fun p => ⟨⟨p.1, (hmem p.1).mp p.2.1, by
          change c.coord p.1 ∈ ball (0 : ℝ²) 100
          have h2 : c.coord p.1 = a := p.2.2
          rw [h2, mem_ball_zero_iff]
          exact ha⟩, Subtype.ext p.2.2⟩
      invFun := fun y => ⟨y.1.1, (hmem y.1.1).mpr y.1.2.1, congrArg Subtype.val y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _)
      continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) }


namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07's slim gauge estimates** (BASES-free): with `c₃ < 1/1000` there is ONE `H ∈ [0, 1/1000)`
such that at every point `y` of every slim domain `Y_i`, `dη_i` has a right inverse `R` with
`√(R_i⁻²g(R w, R w)) ≤ (4/3)|w|` (LFR20.1) and `|dg_i(v) − dη_i(v)| ≤ H √(R_i⁻²g(v, v))`. -/
theorem gaf07_slim_gauge_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000) :
    ∃ H : ℝ, 0 ≤ H ∧ H < 1 / 1000 ∧
      ∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset), ∀ y ∈ gaf07SlimY_GAFC P i,
        (∃ R : ℝ →L[ℝ] E3,
          (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
            (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord y).comp R =
              ContinuousLinearMap.id ℝ ℝ ∧
            ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (R w) (R w)) ≤ 4 / 3 * ‖w‖) ∧
        ∀ v : E3, ‖(show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.gaf07SlimCoord_GAFC i) y) v -
          (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
            (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord y) v‖ ≤
          H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v) := by
  obtain ⟨-, hΔ1, -⟩ := C.std
  obtain ⟨H, hH, hder⟩ := C.gaf07_slim_derivative_GAFC
  refine ⟨max H 0, le_max_right _ _, max_lt (hH.trans hc) (by norm_num), fun i y hy => ⟨?_, ?_⟩⟩
  · have hj := (Set.Finite.mem_toFinset _).mp i.2
    set cc := P.slim.centre i.1 hj with hcc
    have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
    have hyd : dist y i.1 < 91 / 100 * (10 ^ 6 * Δ) * ρ i.1 :=
      cc.dist_lt_of_abs_coord_le_ZERO (hball ▸ hy.1) (by nlinarith [hy.2, abs_nonneg (cc.coord y)])
    obtain ⟨w, hw1, hw⟩ := cc.derivative_GAFC hyd
    set d : ℝ := mvfderiv 𝓘(ℝ, E3) cc.coord y w with hd
    have hd0 : 0 < d := by linarith
    refine ⟨ContinuousLinearMap.toSpanSingleton ℝ (d⁻¹ • w), ?_, fun t => ?_⟩
    · refine ContinuousLinearMap.ext fun t => ?_
      change (mvfderiv 𝓘(ℝ, E3) cc.coord y) (t • d⁻¹ • w) = t
      rw [map_smul, map_smul, ← hd, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hd0.ne', mul_one]
    · change Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (t • d⁻¹ • w) (t • d⁻¹ • w)) ≤ 4 / 3 * ‖t‖
      have hsc : g.inner y (t • d⁻¹ • w) (t • d⁻¹ • w) = (t * d⁻¹) ^ 2 * g.inner y w w := by
        rw [smul_smul, map_smul, map_smul]
        simp only [smul_apply, smul_eq_mul]
        ring
      rw [hsc, show (ρ i.1)⁻¹ ^ 2 * ((t * d⁻¹) ^ 2 * g.inner y w w) =
        (t * d⁻¹) ^ 2 * ((ρ i.1)⁻¹ ^ 2 * g.inner y w w) by ring, hw1, mul_one,
        Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hd0), Real.norm_eq_abs]
      have h43 : d⁻¹ ≤ 4 / 3 := by
        rw [inv_le_comm₀ hd0 (by norm_num)]
        linarith
      calc |t| * d⁻¹ ≤ |t| * (4 / 3) := mul_le_mul_of_nonneg_left h43 (abs_nonneg t)
        _ = 4 / 3 * |t| := by ring
  · intro v
    rw [Real.norm_eq_abs]
    refine (hder i y hy.1 (by nlinarith [hy.2]) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-- **GAF07, `j = 3`, standard smooth type** (B:6049–6063; review 70): for a manifold orientation
`oM`, packet jet order `K ≥ 5` and `c₃ < 1/1000`, for every slim index `i` and `|a| < 4·10⁵Δ` the
WHOLE adjusted level `{p ∈ Y_i | g_i(p) = a}` is the exact image of a smooth embedding of the
standard `ClosureSphere` or of the standard `Torus`. -/
theorem gaf07_slim_level_standard_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hK : 5 ≤ K) (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    (∃ f : ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC P i ∧ C.gaf07SlimCoord_GAFC i p = a}) ∨
      (∃ f : Torus → X, IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC P i ∧ C.gaf07SlimCoord_GAFC i p = a}) := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  set cc := P.slim.centre i.1 hj with hcc
  have hri := hρ i.1
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨H, hH0, hH, hgauge⟩ := C.gaf07_slim_gauge_GAFC hc
  have hgsm := (C.gaf07_slim_smooth_GAFC i).2
  set Yi := gaf07SlimY_GAFC P i with hYi
  set gi := C.gaf07SlimCoord_GAFC i with hgi
  have hval : ∀ y ∈ Yi, |gi y - cc.coord y| < 1 / 800 :=
    fun y hy => C.gaf07_slim_axis_value_GAFC hc i hy.1 hy.2
  -- the slab of the stored packet is `Y_i` (radius `r = 5·10⁵Δ`)
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  have hYmem : ∀ x : X, (ρ i.1)⁻¹ * dist x i.1 < 10 ^ 6 * Δ → |cc.coord x| < 5 * (10 ^ 5 * Δ) →
      x ∈ gaf07SlimY_GAFC P i := by
    intro x hx hη
    refine ⟨?_, hη⟩
    rw [inv_mul_lt_iff₀ hri] at hx
    change dist x i.1 < 1000000 * Δ * ρ i.1
    linarith
  have hYmem' : ∀ x ∈ gaf07SlimY_GAFC P i, (ρ i.1)⁻¹ * dist x i.1 < 10 ^ 6 * Δ := by
    intro x hx
    have hx' : dist x i.1 < 1000000 * Δ * ρ i.1 := hx.1
    rw [inv_mul_lt_iff₀ hri]
    linarith
  have hYball : ∀ x ∈ gaf07SlimY_GAFC P i, x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) :=
    fun x hx => hball ▸ hx.1
  have hcoordsm := cc.contMDiffOn_coord
  set ηc := cc.coord with hηc
  have hr : 5 * (10 ^ 5 * Δ) ≤ 905 * 10 ^ 3 * Δ := by nlinarith
  have key0 := cc.gaf07_slim_fibre_standard_type_SSTD hK hΔ1 oM hr
  have hηd : ∀ y ∈ Yi, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ηc y := fun y hy =>
    ((hcoordsm.contMDiffAt (isOpen_ball.mem_nhds (hball ▸ hy.1))).mdifferentiableAt (by simp))
  have hgd : ∀ y, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) gi y := fun y =>
    (hgsm y).mdifferentiableAt (by simp)
  have hgi : ∀ y ∈ Yi, (∃ R : ℝ →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ηc y).comp R = ContinuousLinearMap.id ℝ ℝ ∧
        ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y (R w) (R w)) ≤ 4 / 3 * ‖w‖) ∧
      ∀ v : E3, ‖(show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) gi y) v -
        (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ηc y) v‖ ≤
        H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y v v) := fun y hy => hgauge i y hy
  let P' := cc.packet
  let iZ := cc.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ i.1)⁻¹ (inv_pos.mpr hri)
  let bR := radialScaledBundle g (ρ i.1)⁻¹ (inv_pos.mpr hri)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ i.1)⁻¹ (inv_pos.mpr hri)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ i.1)⁻¹ (inv_pos.mpr hri)
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ i.1)⁻¹ (inv_pos.mpr hri)).mpr hMc
  have hcoordeq : ηc = P'.coord := rfl
  let a' : lineBallOpens (5 * (10 ^ 5 * Δ)) := ⟨a, mem_lineBallOpens_iff.mpr (by linarith)⟩
  have hSl : ∀ y : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)), y.1 ∈ Yi := by
    intro y
    have hy := mem_realSlabOpens_iff.mp y.2
    exact hYmem y.1 hy.1 hy.2
  have hηS : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y : realSlabOpens (ball i.1 (10 ^ 6 * Δ))
      isOpen_ball P'.coord P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)) =>
        P'.coord y.1) :=
    hcoordsm.comp_contMDiff (contMDiff_subtype_val (I := 𝓘(ℝ, E3))) (fun y => hYball _ (hSl y))
  have hgS : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y : realSlabOpens (ball i.1 (10 ^ 6 * Δ))
      isOpen_ball P'.coord P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)) =>
        gi y.1) :=
    hgsm.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E3)))
  let h : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)) × ℝ → ℝ :=
    fun x => (1 - x.2) • P'.coord x.1.1 + x.2 • gi x.1.1
  have hh : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ) ∞ h := contMDiff_straightLine hηS hgS
  have h0 : ∀ y, h (y, 0) = P'.coord y.1 := fun y => by
    simp only [h, sub_zero, one_smul, zero_smul, add_zero]
  have hcK : H * (4 / 3) < 1 := by linarith
  have hDS : ∀ (y : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ))) (v : E3),
      ‖(show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) gi y.1) v -
        (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) P'.coord y.1) v‖ ≤
        H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y.1 v v) := by
    intro y v
    have hD := (hgi y.1 (hSl y)).2 v
    rw [hcoordeq] at hD
    exact hD
  have hRS : ∀ (y : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ))), ∃ R : ℝ →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) P'.coord y.1).comp R =
        ContinuousLinearMap.id ℝ ℝ ∧
        ∀ w, Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y.1 (R w) (R w)) ≤ 4 / 3 * ‖w‖ := by
    intro y
    have hR := (hgi y.1 (hSl y)).1
    rw [hcoordeq] at hR
    exact hR
  have hηdS : ∀ (y : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ))),
      MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) P'.coord y.1 := by
    intro y
    have hd := hηd y.1 (hSl y)
    rw [hcoordeq] at hd
    exact hd
  have hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a'.1 →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => h (z, τ)) y) := fun τ hτ y _ =>
    surjective_mfderiv_straightLine_restrict_GAFC _ P'.coord gi y hτ (hηdS y) (hgd y.1)
      (fun v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner y.1 v v)) hH0 hcK (hRS y) (hDS y)
  have hQ : IsCompact {y : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)) |
        |P'.coord y.1| ≤ 401 / 100 * (10 ^ 5 * Δ)} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert P'.toSlimChart.isCompact_closedSlab_FPRE (a := 401 / 100 * (10 ^ 5 * Δ))
      (by nlinarith) using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_realSlabOpens_iff.mp y.2).1, hy⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨x, mem_realSlabOpens_iff.mpr ⟨hx, by nlinarith⟩⟩, hxa, rfl⟩
  have hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a'.1 → y ∈ {y : realSlabOpens
      (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord P'.lipschitz.continuous.continuousOn
        (5 * (10 ^ 5 * Δ)) | |P'.coord y.1| ≤ 401 / 100 * (10 ^ 5 * Δ)} := by
    intro τ hτ y hy
    have hv := hval y.1 (hSl y)
    have hl := norm_lt_of_level_of_straight_line (V := ℝ) hτ hℓ
      (by rw [Real.norm_eq_abs]; exact ha) (by rw [Real.norm_eq_abs]; exact hv) hy
    rw [Real.norm_eq_abs] at hl
    exact hl.le
  have key := key0 a' h hh h0 hreg hQ hloc
  have hh1 := contMDiff_familySlice hh 1
  have hreg1 := hreg 1 (right_mem_Icc.mpr zero_le_one)
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a'.1 hh1 hreg1
  have hinc := contMDiff_regularFiberInclusion (fun y => h (y, 1)) a'.1 hh1 hreg1
  let ι := (Subtype.val : realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
      P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)) → X) ∘
    (Subtype.val : {y // h (y, 1) = a'.1} → _)
  have hι : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) 𝓘(ℝ, E3) ∞ ι :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, E3))).comp hinc
  have hemb : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hinj : ∀ y : {y // h (y, 1) = a'.1}, Injective (mfderiv
      𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) 𝓘(ℝ, E3) ι y) := by
    intro y
    have hFd := (hinc y).mdifferentiableAt (by simp)
    have h2 := (DifferentialGeometry.hasMFDerivAt_subtype_val (I := 𝓘(ℝ, E3)) _ y.1).comp y
      hFd.hasMFDerivAt
    rw [h2.mfderiv]
    have hi := mfderiv_regularFiberInclusion_injective (fun y => h (y, 1)) a'.1 hh1 hreg1 y
    intro u v huv
    exact hi huv
  have hrange : range ι =
      {p | p ∈ Yi ∧ gi p = a} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨hSl y.1, ?_⟩
      have hy := y.2
      simp only [h, sub_self, zero_smul, one_smul, zero_add] at hy
      exact hy
    · rintro ⟨hx, hxa⟩
      have hxS : x ∈ realSlabOpens (ball i.1 (10 ^ 6 * Δ)) isOpen_ball P'.coord
          P'.lipschitz.continuous.continuousOn (5 * (10 ^ 5 * Δ)) := by
        rw [mem_realSlabOpens_iff]
        refine ⟨hYmem' x hx, ?_⟩
        have h2 : |ηc x| < 5 * (10 ^ 5 * Δ) := hx.2
        rw [hcoordeq] at h2
        exact h2
      refine ⟨⟨⟨x, hxS⟩, ?_⟩, rfl⟩
      simp only [h, sub_self, zero_smul, one_smul, zero_add]
      exact hxa
  rcases key with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD _ hι hemb hinj d
    exact Or.inl ⟨_, h1, h2.trans hrange⟩
  · obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD _ hι hemb hinj d
    exact Or.inr ⟨_, h1, h2.trans hrange⟩

end Gaf02Chain

namespace Gaf02ChainE

variable {vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, `j = 1`: the whole circle fibres are circles** (B:6053–6055, topological type): for
`w ∈ W₁` in the ratio piece of `i` (TCP01 range of the packet, `c₃ < 1/1000`), the WHOLE fibre
`(π₁E)⁻¹(w)` is homeomorphic to `Circle`. -/
theorem gaf07_circle_whole_fibre_circle_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 0)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w) :
    Nonempty ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (C.toChain.E p)) ⁻¹' {w} ≃ₜ Circle) := by
  obtain ⟨ha, -, ⟨φ⟩, -⟩ := C.gaf07_circle_whole_fibre_GAFC hc hβ hd w hW i hm hr
  obtain ⟨ψ⟩ := nonempty_homeomorph_circleLevel_circle_GAFC P.toLocalChartPackets i
    (a := (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w) (by linarith)
  have hset : {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
      cgpCoord P.toLocalChartFamily P.zero (.inl i) p =
        (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl i) w} =
      {p | p ∈ ball i.1 (200 * ρ i.1) ∧ cgpCoord P.toLocalChartFamily P.zero (.inl i) p =
        (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl i) w} := by
    ext p
    constructor
    · rintro ⟨⟨hp, -⟩, hpa⟩
      exact ⟨hp, hpa⟩
    · rintro ⟨hp, hpa⟩
      exact ⟨⟨hp, by rw [hpa]; linarith⟩, hpa⟩
  exact ⟨(φ.trans (Homeomorph.setCongr hset)).trans ψ⟩

end Gaf02ChainE

/-- **Consumer: GAF07 `j = 3` on the final family, standard smooth type** (review 70): for the final
family `LocalChartPacketsC14Z` with its OWN orientation `oM` (`K ≥ 5`) and a chain with (JA) on its
`LocalChartPacketsC14` projection, every whole adjusted slim level `{p ∈ Y_i | g_i(p) = a}`,
`|a| < 4·10⁵Δ`, is the image of a smooth embedding of the standard `ClosureSphere` or `Torus`. -/
theorem gaf07_slim_level_standard_C14Z_GAFC {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    (∃ f : ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
          C.toChain.gaf07SlimCoord_GAFC i p = a}) ∨
      (∃ f : Torus → X, IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
          C.toChain.gaf07SlimCoord_GAFC i p = a}) :=
  C.toChain.gaf07_slim_level_standard_GAFC C.c_two_lt hK oM i ha

end DifferentialGeometry.Geometry.Collapse
