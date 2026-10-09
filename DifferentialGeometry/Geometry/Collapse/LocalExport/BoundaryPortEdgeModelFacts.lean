import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimClausesB

/-!
# Facts on EGP06's model on a boundary supply (lane S-PORT-EDGE)

Block facts of `edgeModelOf_BPE S a sgn c` (EGP06's model graph `egpModelGraph_BAUGP` of the `edgeB`
reference `a` in the interior tag space) and the plateau step of (FM\*) for an edge marker, for the
clauses (SB-int), (PP-int), (FM\*-int), (ZB\*-int) of `port_edge_interior_table_BAUGP`:

* `marker_fderiv_of_close_edge_BPE` (generic over the tag type and the model, closed
  `EdgeStagePlanes_PLN.full_marker`, last step): a model block `blockLift (graphPacketModelBlock …)`
  whose argument is `8Δ`-plateau-close to a full block has a locally constant marker, hence the
  marker of the derivative vanishes;
* `edgeModelOf_slim_eq_zero_of_small_BPE`, `edgeModelOf_edge_eq_zero_of_small_BPE` — the whole block
  of a slim / edge marker with `ρ(j) ≤ .99ρ(a)` is zero (listed charts have `ρ(j) > .99ρ(a)`);
* `edgeModelOf_edge_listed_BPE`, `edgeModelOf_edge_unlisted_BPE` — the blocks of the other edge
  charts;
* `edgeModelOf_zero_eq_zero_BPE` — the zero block of a zero support missing `D_a`.
Twin of `BoundaryPortSlimModelFacts` (model-graph facts) and the generic part of
`BoundaryPortSlimClausesB`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section GenericModel

variable {τ : Type*} [Fintype τ]

/-- **The plateau step of (FM\*) for an edge marker**, for ANY finite tag type and ANY model `Φ`
(closed `EdgeStagePlanes_PLN.full_marker`, last step): if `‖r_a⁻¹y − Φ(u)‖ < e` (`e < 1/100`), the
`t`-block of `y` is the full block `(r_i·1 η, r_i·1)` with `|η| ≤ (351/49)ℓ`, `r_i/r_a ≥ 99/100`,
and the `t`-block of `Φ` is EGP06's listed block
`blockLift (graphPacketModelBlock ℓ (r_i/r_a) (σw+c))`, then the marker of `t` annihilates
`DΦ(u)`. -/
theorem marker_fderiv_of_close_edge_BPE {Φ : ℝ → BlockSpace (fun _ : τ => ℝ²)}
    (hΦ : Differentiable ℝ Φ) (t : τ) {y : BlockSpace (fun _ : τ => ℝ²)}
    {u η eg ra ri ℓ sg cc : ℝ} (hra : 0 < ra) (hri : 0 < ri) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100)
    (hs : 99 / 100 ≤ ri / ra) (hη : |η| ≤ 351 / 49 * ℓ) (hℓ : 1 ≤ ℓ)
    (hTG : ‖ra⁻¹ • y - Φ u‖ < eg)
    (hy : y t = WithLp.toLp 2 ((ri * 1) • planeAxis η, ri * 1))
    (hmt : ∀ w, Φ w t = blockLift_KC3 (graphPacketModelBlock ℓ (ri / ra) (sg * w + cc))) (v : ℝ) :
    ((fderiv ℝ Φ u v) t).snd = 0 := by
  have hnum := plateau_numbers_PLN hℓ (s := ri / ra) hs heg0 heg
  have hcl := lift_block_close_PLN t hTG hy (hmt u)
  have harg := scaledCutoffBlock_arg_lt_of_close_PLN (div_pos hri hra) hnum.1
    (by rw [Real.norm_eq_abs]; exact hη) hcl hnum.2
  have hℓ0 : 0 < ℓ := by linarith
  have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ri / ra) (r := 8 * ℓ)
    (φ := scaledEdgeCoordinateProfile ℓ)
    (fun z hz => by
      rw [Real.norm_eq_abs] at hz
      have hz' : |z / ℓ| ≤ 8 := by
        rw [abs_div, abs_of_pos hℓ0, div_le_iff₀ hℓ0]
        exact hz
      exact intervalPlateauProfile_one (by norm_num) (by norm_num)
        ⟨by linarith [neg_abs_le (z / ℓ)], by linarith [le_abs_self (z / ℓ)]⟩)
    (u := fun w => sg * w + cc)
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt harg
  have hloc : (fun w => (Φ w t).snd) =ᶠ[𝓝 u] fun _ => ri / ra := by
    filter_upwards [hev] with w hw
    rw [hmt w]
    exact hw
  exact blockMarkerCLM_fderiv_eq_zero_GAFS t (hΦ u) hloc v

end GenericModel

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM) (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)

/-- The slim blocks of EGP06's model of a small slim chart (`ρ(j) ≤ .99ρ(a)`) are zero: the chart
is neither listed (listed charts have `ρ(j) > .99ρ(a)`) nor the own tag. -/
theorem edgeModelOf_slim_eq_zero_of_small_BPE (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (j : S.SlimIdx_BAUGD)
    (hj : S.rho j.1 ≤ 99 / 100 * S.rho a.1) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (.inr (.inl j)) = 0 := by
  classical
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hS : j.1 ∉ egpSlimList_BAUGP S.family.toLocalPacketsOnB a.1 := fun hS => by
    have h1 := egpSlimList_ratio_GAF4_BAUGP S.family.toLocalPacketsOnB hΔ hΛ hLΛ hS
    linarith only [h1, hj]
  change egpModelComponent_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c
    (.inr (.inl j)) u = 0
  simp only [egpModelComponent_BAUGP, hS, ite_false]
  rfl

/-- The edge blocks of EGP06's model of a small edge chart (`ρ(j) ≤ .99ρ(a)`) are zero. -/
theorem edgeModelOf_edge_eq_zero_of_small_BPE (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (j : S.EdgeIdx_BAUGD)
    (hj : S.rho j.1 ≤ 99 / 100 * S.rho a.1) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (.inr (.inr (.inl j))) = 0 := by
  classical
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hri := S.rho_pos a.1
  have hji : j.1 ≠ a.1 := fun h => by
    rw [h] at hj
    linarith only [hj, hri]
  have hE : j.1 ∉ egpEdgeList_BAUGP S.family.toLocalPacketsOnB a.1 := fun hE => by
    have h1 := egpEdgeList_ratio_GAF4_BAUGP S.family.toLocalPacketsOnB hΔ hΛ hLΛ hE
    linarith only [h1, hj]
  change egpModelComponent_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c
    (.inr (.inr (.inl j))) u = 0
  simp only [egpModelComponent_BAUGP, hji, hE, ite_false]
  rfl

/-- The block of a LISTED edge chart `j ≠ a` of EGP06's model. -/
theorem edgeModelOf_edge_listed_BPE (j : S.EdgeIdx_BAUGD) (hne : j.1 ≠ a.1)
    (hl : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      j.1 ∈ egpEdgeList_BAUGP S.family.toLocalPacketsOnB a.1) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (.inr (.inr (.inl j))) =
      blockLift_KC3 (graphPacketModelBlock Δ (S.rho j.1 / S.rho a.1)
        (sgn (.inr (.inr (.inl j))) * u + c (.inr (.inr (.inl j))))) := by
  classical
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  change egpModelComponent_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c
    (.inr (.inr (.inl j))) u = _
  simp only [egpModelComponent_BAUGP, hne, hl, ite_true, ite_false]

/-- The block of an UNLISTED edge chart `j ≠ a` of EGP06's model is zero. -/
theorem edgeModelOf_edge_unlisted_BPE (j : S.EdgeIdx_BAUGD) (hne : j.1 ≠ a.1)
    (hl : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      j.1 ∉ egpEdgeList_BAUGP S.family.toLocalPacketsOnB a.1) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (.inr (.inr (.inl j))) = 0 := by
  classical
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  change egpModelComponent_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c
    (.inr (.inr (.inl j))) u = 0
  simp only [egpModelComponent_BAUGP, hne, hl, ite_false]
  rfl

/-- The zero block of EGP06's model of a zero support missing `D_a = B(a, 20Δρ(a))` is zero. -/
theorem edgeModelOf_zero_eq_zero_BPE (k : S.ZeroIdx_BAUGC)
    (hk : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      k.1 ∉ zeroMeetingList_BPE S.family.zero a.1 (20 * Δ)) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (S.zeroTag_BAUGC k) = 0 := by
  classical
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  change egpModelComponent_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c
    (.inr (.inr (.inr (.inl k)))) u = 0
  simp only [egpModelComponent_BAUGP, hk, ite_false]
  rfl

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
