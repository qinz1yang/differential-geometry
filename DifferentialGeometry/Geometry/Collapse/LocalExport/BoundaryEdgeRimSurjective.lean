import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimBlocks
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimKernel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCollarConormOn
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentAssembly
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEScaleB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightTransport

/-!
# G12 / G16 (part b): the rim surjectivity of `(f₂, T)` on the enhanced boundary chain

Closed twin `Gaf02Chain.edge_vertical_rank_EDPE` (`Fibration/ActualStageChainEdpHeight.lean`),
at the final time `θ = 1` of EDP04's homotopy.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

omit [ConnectedSpace W.Carrier] in
/-- The chain rule through `val` for a continuous linear functional of a differentiable map. -/
theorem mvfderiv_clm_comp_val_BAUGD {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ℓ : H →L[ℝ] ℝ) (f : W.Carrier → H) (q : W.pieceInterior ⊤)
    (hf : MDifferentiableAt W.model 𝓘(ℝ, H) f q.val) (u : TangentSpace (𝓡 3) q) :
    mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => ℓ (f z.val)) q u =
      ℓ (mvfderiv W.model f q.val (mfderiv (𝓡 3) W.model Subtype.val q u)) := by
  have hl : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => ℓ (f y)) q.val :=
    ℓ.differentiableAt.mdifferentiableAt.comp q.val hf
  rw [mvfderiv_comp_val_BCG7 W (fun y => ℓ (f y)) q hl u, mvfderiv_clm_comp_BDFB ℓ hf]


namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- `g(dval u, dval u) = ĝ(u, u)` at a point with `D ≥ 4` (`ĝ = g°` on `{D ≥ 4}`). -/
theorem inner_dval_BAUGD (q : W.pieceInterior ⊤)
    (hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val) (u : TangentSpace (𝓡 3) q) :
    g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
        (mfderiv (𝓡 3) W.model Subtype.val q u) = S.completion.metric.inner q u u :=
  inner_mfderiv_val_BCG7 W g S.completion.metric
    (fun x hx => S.completion.inner_eq_on_agree x (S.completion.far_subset_agree hx)) q hD u u

/-- The height coordinate `u_{E'}` of `H^∂` as a continuous linear functional. -/
def heightFun_BAUGD :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).comp
    (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl S.edgeTag_BAUGA))

theorem heightFun_apply_BAUGD
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.heightFun_BAUGD z = S.heightCoord_BIF z :=
  rfl

theorem abs_heightFun_le_BAUGD
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    |S.heightFun_BAUGD z| ≤ ‖z‖ :=
  abs_proj_blockVector_le_BAUGD (Sum.inl S.edgeTag_BAUGA) z

/-- **EDP03's collar co-norm at `q` in kernel form**: at a point `q` of the chart ball of the
`edgeB` centre `j` with `|η_j(q)| ≤ 10Δ`, `Δ/10 ≤ t(q) ≤ 10Δ`, every unit `ξ` has a vector `u` of
the `ĝ`-sphere of radius `ρ_j` with `D(η_j)(u) ξ₀ + D(F/ρ)(u) ξ₁ > 9/10`. -/
theorem edge_conorm_BAUGD (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 10 * Δ) (h1 : Δ / 10 ≤ S.edgeHeightRaw q)
    (h2 : S.edgeHeightRaw q ≤ 10 * Δ) :
    ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ u : TangentSpace (𝓡 3) q,
      S.completion.metric.inner q u u = S.rho j.1 ^ 2 ∧
      9 / 10 < mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q u * ξ 0 +
        mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeSmoothing_BAUGD z / S.rho z.val) q u *
          ξ 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.edgeB.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hx : q ∈ ball j.1 (100 * Δ * S.rho j.1) := mem_ball.mpr hd
  have hηfun : S.edgeEta_BIF j.1 = S.family.edgeB.coord_BAUGA j.1 :=
    funext fun z => S.edgeEta_eq_coord_BAUGP2 j z
  have hη' : |S.family.edgeB.coord_BAUGA j.1 q| ≤ 10 * Δ := by
    rw [← hηfun]
    exact hη
  obtain ⟨-, hco⟩ := S.family.edgeB.collar_conorm_BAUGD hγc hγc1 hβc1 hj hx hη' h1 h2
  have hηc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (S.family.edgeB.coord_BAUGA j.1) q :=
    (S.family.edgeB.contMDiffOn_coord_BAUGA hj).contMDiffAt (isOpen_ball.mem_nhds hx)
  have htc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => S.family.edgeB.smoothing y / S.rho y.val) q :=
    S.family.edgeB.contMDiffAt_height_of_collar_BAUGA hj hx hη' h1 h2
  have hFc : ∀ k, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (![S.family.edgeB.coord_BAUGA j.1,
      fun y => S.family.edgeB.smoothing y / S.rho y.val] k) q := fun k => by
    fin_cases k
    · exact hηc
    · exact htc
  intro ξ hξ
  obtain ⟨u, hu, h9⟩ := hco ξ hξ
  refine ⟨u, hu, ?_⟩
  rw [inner_two_BAUGD, edgeReferenceCoordinates_derivative hFc u 0,
    edgeReferenceCoordinates_derivative hFc u 1] at h9
  rw [hηfun]
  exact h9

theorem edgeSmoothing_nonneg_BAUGD (z : W.pieceInterior ⊤) : 0 ≤ S.edgeSmoothing_BAUGD z := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  exact S.family.edgeB.smoothing_nonneg z

/-- The smoothing `F = t ρ` is differentiable at a collar point (`t` smooth there, LFR38). -/
theorem mdifferentiableAt_edgeSmoothing_BAUGD (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 10 * Δ) (h1 : Δ / 10 ≤ S.edgeHeightRaw q)
    (h2 : S.edgeHeightRaw q ≤ 10 * Δ) :
    MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) S.edgeSmoothing_BAUGD q := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.edgeB.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hx : q ∈ ball j.1 (100 * Δ * S.rho j.1) := mem_ball.mpr hd
  have hη' : |S.family.edgeB.coord_BAUGA j.1 q| ≤ 10 * Δ := by
    rw [← S.edgeEta_eq_coord_BAUGP2 j q]
    exact hη
  have htc : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => S.family.edgeB.smoothing y / S.rho y.val) q :=
    S.family.edgeB.contMDiffAt_height_of_collar_BAUGA hj hx hη' h1 h2
  have hρd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun z : W.pieceInterior ⊤ => S.rho z.val) q :=
    ((S.scale_spec.1 q.val).mdifferentiableAt (by simp)).comp q (mdifferentiableAt_val_BCG7 W q)
  have hfun : S.edgeSmoothing_BAUGD = fun y : W.pieceInterior ⊤ =>
      (S.family.edgeB.smoothing y / S.rho y.val) * S.rho y.val := funext fun y => by
    have := S.rho_pos y.val
    change S.family.edgeB.smoothing y = _
    field_simp
  rw [hfun]
  exact (htc.mdifferentiableAt (by simp)).mul hρd

/-- **The quotient rule for `t = F/ρ` on `W°`** at a collar point. -/
theorem dt_quotient_BAUGD (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 10 * Δ) (h1 : Δ / 10 ≤ S.edgeHeightRaw q)
    (h2 : S.edgeHeightRaw q ≤ 10 * Δ) (u : TangentSpace (𝓡 3) q) :
    mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeSmoothing_BAUGD z / S.rho z.val) q u =
      (S.rho q.val)⁻¹ * mvfderiv (𝓡 3) S.edgeSmoothing_BAUGD q u -
        S.edgeSmoothing_BAUGD q * (S.rho q.val ^ 2)⁻¹ *
          mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.rho z.val) q u := by
  let _ := inducedMetricSpace S.completion.metric
  have hFd := S.mdifferentiableAt_edgeSmoothing_BAUGD j hd hη h1 h2
  have hρd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun z : W.pieceInterior ⊤ => S.rho z.val) q :=
    ((S.scale_spec.1 q.val).mdifferentiableAt (by simp)).comp q (mdifferentiableAt_val_BCG7 W q)
  exact mvfderiv_div_apply (F := S.edgeSmoothing_BAUGD)
    (ρ := fun z : W.pieceInterior ⊤ => S.rho z.val) hFd hρd (S.rho_pos q.val).ne' u

/-- **`|dF| ≤ (1 + ε)|u|_ĝ`**: the smoothing is `(1 + ε)`-Lipschitz for `d_ĝ`. -/
theorem abs_dedgeSmoothing_le_BAUGD (hε0 : 0 ≤ ε) (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 10 * Δ) (h1 : Δ / 10 ≤ S.edgeHeightRaw q)
    (h2 : S.edgeHeightRaw q ≤ 10 * Δ) (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) S.edgeSmoothing_BAUGD q u| ≤
      (1 + ε) * Real.sqrt (S.completion.metric.inner q u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hFd := S.mdifferentiableAt_edgeSmoothing_BAUGD j hd hη h1 h2
  have hlip : LipschitzWith (Real.toNNReal (1 + ε)) S.edgeSmoothing_BAUGD :=
    S.family.edgeB.lipschitz_smoothing
  exact Geodesic.abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf S.completion.metric
    (inducedMetricSpace_hmetric S.completion.metric) (by linarith) hlip hFd u

/-- **The scale varies by at most `Λ r ρ_j` on the `d_ĝ`-ball `B(j, rρ_j)`** around a centre with
`D(j) > 10` (T3B's transport; the sharp form of `rho_comparable_of_dist_lt_BAUGP2`). -/
theorem abs_rho_sub_le_of_dist_lt_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) {j q : W.pieceInterior ⊤}
    (hj : ENNReal.ofReal 10 < distanceToBoundary W g j) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 2000000 * Δ)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j < r * S.rho j) :
    |S.rho q - S.rho j| ≤ Λ * (r * S.rho j) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have htr := (S.transport_spec.2.1 j hj).2
  have hK0 := consumerConstant_ge_BAUGA hΔ hV hβ1 hb
  have hrj := S.rho_pos j
  have hqK : q ∈ ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j) := by
    rw [mem_ball]
    refine hq.trans_le (mul_le_mul_of_nonneg_right ?_ hrj.le)
    linarith
  have hjK : j ∈ ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j) :=
    mem_ball_self (mul_pos (by nlinarith) hrj)
  have hdist : riemannianEDistOf g q.val j.val = edist q j := htr q hqK j hjK
  have hedist : edist q j < ENNReal.ofReal (r * S.rho j) := edist_lt_ofReal.mpr hq
  have hlip := S.scale_spec.2.1 q.val j.val
  have h1 : ENNReal.ofReal |S.rho q.val - S.rho j.val| ≤ ENNReal.ofReal (Λ * (r * S.rho j)) := by
    refine hlip.trans ?_
    rw [hdist, ENNReal.ofReal_mul hΛ]
    exact mul_le_mul_right hedist.le _
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1

end BoundarySupplyCore

omit [ConnectedSpace W.Carrier] in
/-- **Germ transfer of a derivative bound** (abstract form of A3c through `val`): for a continuous
linear functional `ℓ` with `|ℓ w| ≤ M‖w‖`, two maps `E`, `F` of `W` with
`‖DE v − DF v‖ ≤ H_d |v|_g`, and a function `φ` on `W°` which is the germ of `ℓ ∘ F ∘ val` at `q`:
`|D(ℓ ∘ E ∘ val)(u) − Dφ(u)| ≤ M H_d |u|_ĝ` for a metric `ĝ` with `g(dval u, dval u) = ĝ(u, u)`. -/
theorem abs_dclm_sub_germ_BAUGD {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ℓ : H →L[ℝ] ℝ) {M Hd : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w, |ℓ w| ≤ M * ‖w‖)
    (E F : W.Carrier → H) (q : W.pieceInterior ⊤)
    (hE : MDifferentiableAt W.model 𝓘(ℝ, H) E q.val)
    (hF : MDifferentiableAt W.model 𝓘(ℝ, H) F q.val) (φ : W.pieceInterior ⊤ → ℝ)
    (hev : (fun z : W.pieceInterior ⊤ => ℓ (F z.val)) =ᶠ[𝓝 q] φ)
    (hder : ∀ v : TangentSpace W.model q.val,
      ‖mvfderiv W.model E q.val v - mvfderiv W.model F q.val v‖ ≤
        Hd * Real.sqrt (g.inner q.val v v))
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hnorm : ∀ u : TangentSpace (𝓡 3) q, g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
      (mfderiv (𝓡 3) W.model Subtype.val q u) = ĝ.inner q u u)
    (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => ℓ (E z.val)) q u - mvfderiv (𝓡 3) φ q u| ≤
      M * (Hd * Real.sqrt (ĝ.inner q u u)) := by
  have e1 := mvfderiv_clm_comp_val_BAUGD ℓ E q hE u
  have e2 : mvfderiv (𝓡 3) φ q u = ℓ (mvfderiv W.model F q.val
      (mfderiv (𝓡 3) W.model Subtype.val q u)) := by
    rw [← mvfderiv_congr_BDFB hev u]
    exact mvfderiv_clm_comp_val_BAUGD ℓ F q hF u
  have h4 := hder (mfderiv (𝓡 3) W.model Subtype.val q u)
  rw [hnorm u] at h4
  rw [e1, e2, ← map_sub]
  exact (hM _).trans (mul_le_mul_of_nonneg_left h4 hM0)

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- The stage-`1` projection keeps the `edgeB` blocks: `λ_j ∘ π₁ = λ_j`. -/
theorem edgeRatio_stageProj_one_BAUGD (j : S.EdgeIdx_BAUGD)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeRatio_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 x) = S.edgeRatio_BAUGD j x := by
  have hmem : (Sum.inl (.inr (.inr (.inl j))) : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈
      (actualSlotsV2_BAUGD S).stageTagsAug 1 := by
    unfold BoundaryInteriorSlots_BIF.stageTagsAug
    rw [Finset.mem_disjSum]
    exact Or.inl ⟨.inr (.inr (.inl j)), BoundarySupplyCore.mem_stageTagsV2_one_BAUGD.mpr rfl, rfl⟩
  have h : S.edgeVector_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 1 x) =
      S.edgeVector_BAUGD j x := by
    unfold BoundarySupplyCore.edgeVector_BAUGD BoundaryInteriorSlots_BIF.stageProj
    simp only [blockVectorCLM_apply, blockRestrict_apply, hmem, ite_true]
  unfold BoundarySupplyCore.edgeRatio_BAUGD
  simp only [smul_apply, ContinuousLinearMap.comp_apply, h]

end BoundarySupply

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **`dA` is close to `dF` on the plateau region**: `A = u_{E'} ∘ E`, `|d(A ∘ val)(u) −
d(F)(u)| ≤ H_d |u|_ĝ` where `F` is the `edgeB` smoothing (A3c and `u_{E'}(F_∂) = F` there). -/
theorem abs_dheight_sub_dsmoothing_BAUGD (hΔ : 0 < Δ) {Hd : ℝ}
    (hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤} (hq : q ∈ S.edgeRegion_BAUGD j)
    (hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val) (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.height z.val) q u -
        mvfderiv (𝓡 3) S.edgeSmoothing_BAUGD q u| ≤
      Hd * Real.sqrt (S.completion.metric.inner q u u) := by
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) C.toChain.E q.val :=
    ((C.stage_smooth_BAUGD 3) _).mdifferentiableAt (by simp)
  have hF := C.mdifferentiableAt_boundaryOriginalMap_BAUGD q.val
  have hev : (fun z : W.pieceInterior ⊤ => S.heightFun_BAUGD (S.boundaryOriginalMap z.val)) =ᶠ[𝓝 q]
      S.edgeSmoothing_BAUGD := by
    filter_upwards [(S.isOpen_edgeRegion_BAUGD j).mem_nhds hq] with z hz
    exact S.heightCoord_boundaryOriginalMap_eq_BAUGD hΔ j hz
  have h := abs_dclm_sub_germ_BAUGD S.heightFun_BAUGD zero_le_one
    (fun w => (one_mul ‖w‖).symm ▸ S.abs_heightFun_le_BAUGD w) C.toChain.E S.boundaryOriginalMap q
    hE hF _ hev (fun v => hder _ v) S.completion.metric (S.inner_dval_BAUGD q hD) u
  rw [one_mul] at h
  exact h

include C in
/-- **`dgq` is close to `dη` on the plateau region**: `gq = λ_j ∘ E`, `λ_j(F_∂) = η_j` there, so
`|d(gq ∘ val)(u) − dη_j(u)| ≤ H_d |u|_ĝ / ρ_j` (A3c). -/
theorem abs_dedge_sub_deta_BAUGD (hΔ : 0 < Δ) {Hd : ℝ}
    (hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤} (hq : q ∈ S.edgeRegion_BAUGD j)
    (hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val) (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val)) q u -
        mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q u| ≤
      (S.rho j.1)⁻¹ * (Hd * Real.sqrt (S.completion.metric.inner q u u)) := by
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) C.toChain.E q.val :=
    ((C.stage_smooth_BAUGD 3) _).mdifferentiableAt (by simp)
  have hF := C.mdifferentiableAt_boundaryOriginalMap_BAUGD q.val
  have hev : (fun z : W.pieceInterior ⊤ =>
      S.edgeRatio_BAUGD j (S.boundaryOriginalMap z.val)) =ᶠ[𝓝 q] S.edgeEta_BIF j.1 := by
    filter_upwards [(S.isOpen_edgeRegion_BAUGD j).mem_nhds hq] with z hz
    exact S.edgeRatio_boundaryOriginalMap_eq_BAUGD hΔ j hz
  exact abs_dclm_sub_germ_BAUGD (S.edgeRatio_BAUGD j) (inv_nonneg.mpr (S.rho_pos j.1).le)
    (fun w => by rw [← div_eq_inv_mul]; exact S.abs_edgeRatio_le_BAUGD j w) C.toChain.E
    S.boundaryOriginalMap q hE hF _ hev (fun v => hder _ v) S.completion.metric
    (S.inner_dval_BAUGD q hD) u

include C in
/-- **The rim point lies in the plateau region** (EDP04's `T = 4Δ` with EDP03's (EH)): at an
interior point `q` of the chart ball of an `edgeB` centre `j` with `|η_j| < 4.01Δ`, `t < 4.01Δ` and
`T = 4Δ`: `D(q) ≥ 4`, `q` lies in the plateau region, `3.9Δ < t < 4.1Δ`, `|A − F| < c₃ρ` and
`ρ(q)/ρ_j > 99/100`. Numerical premises (parameters only): `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`. -/
theorem rim_region_BAUGD (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ) (ht : S.edgeHeightRaw q < 401 / 100 * Δ)
    (hT : C.toChain.heightRatio q.val = 4 * Δ) :
    ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val ∧ q ∈ S.edgeRegion_BAUGD j ∧
      39 / 10 * Δ < S.edgeHeightRaw q ∧ S.edgeHeightRaw q < 41 / 10 * Δ ∧
      |C.toChain.height q.val - S.edgeSmoothing_BAUGD q| < c 2 * S.rho q.val ∧
      99 / 100 < S.rho q.val / S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨hΛ, hΔ0, -, -, hΔΛ, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  have hj : j.1 ∈ S.family.edgeB.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hj10 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
    lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩)
      (S.family.edgeB.centres_subset hj)
  have hD4 := S.four_lt_distanceToBoundary_of_dist_lt_BAUGC hV hβ1 hb hΔ0.le hj10
    (C := 100 * Δ) (by positivity) (by linarith) hd
  have hrj := S.rho_pos j.1
  have hρ99 : 99 / 100 < S.rho q.val / S.rho j.1 := by
    have h := S.abs_rho_sub_le_of_dist_lt_BAUGD hΛ hΔ1 hV hβ1 hb hj10 (r := 100 * Δ)
      (by positivity) (by linarith) hd
    have h1 := (abs_le.mp h).1
    rw [lt_div_iff₀ hrj]
    nlinarith [mul_pos hΔ0 hrj, mul_nonneg hΛ (mul_pos hΔ0 hrj).le]
  have hs := (C.scale_edp01_BAUGD.2 q.val).2.1
  have hκ : 0 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ :=
    mul_nonneg (by linarith [C.scale_edp01_BAUGD.1]) hΛ
  have hAF := C.stage_error_lt_BAUGD 2 q.val
  have hAerr : |C.toChain.height q.val - S.heightCoord_BIF (S.boundaryOriginalMap q.val)| <
      c 2 * S.rho q.val := by
    have h1 := S.abs_heightFun_le_BAUGD (C.toChain.E q.val - S.boundaryOriginalMap q.val)
    rw [map_sub] at h1
    exact h1.trans_lt hAF
  have hAP := S.heightCoord_boundaryOriginalMap_le_BAUGD q
  have hη8 : |S.edgeEta_BIF j.1 q| < 8 * Δ := by linarith
  have hAFeq : 3 / 10 * Δ ≤ S.edgeSmoothing_BAUGD q / S.rho q.val →
      S.heightCoord_BIF (S.boundaryOriginalMap q.val) = S.edgeSmoothing_BAUGD q := fun h3 => by
    have hm := S.edgeBMarker_eq_one_BAUGD hΔ0 j q hd hη8 h3 (by linarith)
    rw [S.heightCoord_boundaryOriginalMap_BAUGD, hm, one_mul]
    rfl
  have hPnn : 0 ≤ S.edgeSmoothing_BAUGD q := S.family.edgeB.smoothing_nonneg q
  obtain ⟨h39, h41, hAP'⟩ := rim_t_bounds_BAUGD hrj hρ99 hs hAP hAerr hAFeq hPnn ht hΔ1 hκ hC hc hT
  rw [← S.edgeHeightRaw_eq_BAUGD] at h39 h41
  have hreg : q ∈ S.edgeRegion_BAUGD j :=
    ⟨mem_ball.mpr hd, hη8, by linarith, by linarith⟩
  exact ⟨hD4.le, hreg, h39, h41, hAP', hρ99⟩

include C in
/-- `A ∘ val`, `s ∘ val` and `ρ ∘ val` are differentiable on `W°` (A3a). -/
theorem mdifferentiableAt_height_BAUGD (q : W.pieceInterior ⊤) :
    MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun z : W.pieceInterior ⊤ => C.toChain.height z.val) q := by
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) C.toChain.E q.val :=
    ((C.stage_smooth_BAUGD 3) _).mdifferentiableAt (by simp)
  have h : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.height q.val :=
    S.heightFun_BAUGD.differentiableAt.mdifferentiableAt.comp q.val hE
  exact h.comp q (mdifferentiableAt_val_BCG7 W q)

include C in
theorem mdifferentiableAt_scale_BAUGD (q : W.pieceInterior ⊤) :
    MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun z : W.pieceInterior ⊤ => C.toChain.scale z.val) q :=
  ((C.scale_edp01_BAUGD.2 q.val).1).comp q (mdifferentiableAt_val_BCG7 W q)

omit C in
theorem mdifferentiableAt_rho_BAUGD (q : W.pieceInterior ⊤) :
    MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun z : W.pieceInterior ⊤ => S.rho z.val) q :=
  ((S.scale_spec.1 q.val).mdifferentiableAt (by simp)).comp q (mdifferentiableAt_val_BCG7 W q)

include C in
/-- **The quotient rule for `T = A/s` on `W°`.** -/
theorem dT_quotient_BAUGD (q : W.pieceInterior ⊤) (u : TangentSpace (𝓡 3) q) :
    mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.heightRatio z.val) q u =
      (C.toChain.scale q.val)⁻¹ *
          mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.height z.val) q u -
        C.toChain.height q.val * ((C.toChain.scale q.val) ^ 2)⁻¹ *
          mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.scale z.val) q u := by
  let _ := inducedMetricSpace S.completion.metric
  exact mvfderiv_div_apply (F := fun z : W.pieceInterior ⊤ => C.toChain.height z.val)
    (ρ := fun z : W.pieceInterior ⊤ => C.toChain.scale z.val)
    (C.mdifferentiableAt_height_BAUGD q) (C.mdifferentiableAt_scale_BAUGD q)
    (C.scale_pos_BAUGD q.val).2.2.ne' u

include C in
/-- **A3f' through `val`**: `|d(s ∘ val)(u)| ≤ C_ρΛ |dval u|_g`. -/
theorem abs_dscale_le_BAUGD (q : W.pieceInterior ⊤) (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.scale z.val) q u| ≤
      100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ *
        Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
          (mfderiv (𝓡 3) W.model Subtype.val q u)) := by
  rw [mvfderiv_comp_val_BCG7 W C.toChain.scale q (C.scale_edp01_BAUGD.2 q.val).1 u]
  exact (C.scale_edp01_BAUGD.2 q.val).2.2.1 _

omit C in
/-- `|d(ρ ∘ val)(u)| ≤ Λ |dval u|_g` (`ρ` is `Λ`-Lipschitz). -/
theorem abs_drho_le_BAUGD (hΛ : 0 ≤ Λ) (q : W.pieceInterior ⊤) (u : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.rho z.val) q u| ≤
      Λ * Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
        (mfderiv (𝓡 3) W.model Subtype.val q u)) := by
  have hρ : MDifferentiableAt W.model 𝓘(ℝ, ℝ) S.rho q.val :=
    (S.scale_spec.1 q.val).mdifferentiableAt (by simp)
  rw [mvfderiv_comp_val_BCG7 W S.rho q hρ u]
  exact abs_mvfderiv_le_of_lipschitz_riemannianEDistOf_BDFB g
    ((S.scale_spec.1 q.val).of_le (by exact_mod_cast le_top)) hΛ Filter.univ_mem
    (fun x _ y _ => S.scale_spec.2.1 x y) _

include C in
/-- **The rim surjectivity on `W°`**: at an interior point `q` of the chart ball of an `edgeB`
centre `j` with `|η_j| < 4.01Δ`, `t < 4.01Δ` and `T = 4Δ`, the pair
`(d(λ_j ∘ E ∘ val), d(T ∘ val))` is onto `ℝ × ℝ` (closed twin: `edge_vertical_rank_EDPE`, final
time of EDP04's homotopy). Numerical premises (parameters only): `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`
(N76-9), `0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`. -/
theorem rim_surjective_wdeg_BAUGD (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ) (ht : S.edgeHeightRaw q < 401 / 100 * Δ)
    (hT : C.toChain.heightRatio q.val = 4 * Δ) :
    Function.Surjective (fun u : TangentSpace (𝓡 3) q =>
      (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val)) q u,
        mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.heightRatio z.val) q u)) := by
  obtain ⟨hΛ, hΔ0, -, -, -, -, -, -, -, hΔ1, -, -⟩ := C.std
  obtain ⟨hD4, hreg, h39, h41, hAP, hρ99⟩ := C.rim_region_BAUGD hc hC j hd hη ht hT
  obtain ⟨Hd, hHd, hder0⟩ := C.stage_derivative_lt_BAUGD 2
  have hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v) := hder0
  have hrj := S.rho_pos j.1
  have hρq := S.rho_pos q.val
  have hκ : 0 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ :=
    mul_nonneg (by linarith [C.scale_edp01_BAUGD.1]) hΛ
  have hΛκ : Λ ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ := by
    have := mul_le_mul_of_nonneg_right (C.scale_edp01_BAUGD.1) hΛ
    linarith
  have hηle : |S.edgeEta_BIF j.1 q| ≤ 10 * Δ := by linarith
  have h1' : Δ / 10 ≤ S.edgeHeightRaw q := by linarith
  have h2' : S.edgeHeightRaw q ≤ 10 * Δ := by linarith
  have hsph : ∀ u : TangentSpace (𝓡 3) q, S.completion.metric.inner q u u = S.rho j.1 ^ 2 →
      Real.sqrt (S.completion.metric.inner q u u) = S.rho j.1 := fun u hu => by
    rw [hu, Real.sqrt_sq hrj.le]
  have hsg : ∀ u : TangentSpace (𝓡 3) q, S.completion.metric.inner q u u = S.rho j.1 ^ 2 →
      Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
        (mfderiv (𝓡 3) W.model Subtype.val q u)) = S.rho j.1 := fun u hu => by
    rw [S.inner_dval_BAUGD q hD4 u, hsph u hu]
  have hs := (C.scale_edp01_BAUGD.2 q.val).2.1
  have hS : |C.toChain.scale q.val / S.rho j.1 - S.rho q.val / S.rho j.1| ≤
      100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * (S.rho q.val / S.rho j.1) := by
    rw [← sub_div, abs_div, abs_of_pos hrj, div_le_iff₀ hrj]
    calc |C.toChain.scale q.val - S.rho q.val| ≤
          100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * S.rho q.val := hs
      _ = 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * (S.rho q.val / S.rho j.1) *
          S.rho j.1 := by field_simp
  have hB : |C.toChain.height q.val / S.rho j.1 - S.edgeSmoothing_BAUGD q / S.rho j.1| <
      c 2 * (S.rho q.val / S.rho j.1) := by
    rw [← sub_div, abs_div, abs_of_pos hrj, div_lt_iff₀ hrj]
    calc |C.toChain.height q.val - S.edgeSmoothing_BAUGD q| < c 2 * S.rho q.val := hAP
      _ = c 2 * (S.rho q.val / S.rho j.1) * S.rho j.1 := by field_simp
  have hnorm : S.edgeSmoothing_BAUGD q / S.rho j.1 / (S.rho q.val / S.rho j.1) =
      S.edgeHeightRaw q := by
    rw [S.edgeHeightRaw_eq_BAUGD]
    field_simp
  have ht0 : 0 ≤ S.edgeSmoothing_BAUGD q / S.rho j.1 / (S.rho q.val / S.rho j.1) := by
    rw [hnorm, S.edgeHeightRaw_eq_BAUGD]
    exact div_nonneg (S.edgeSmoothing_nonneg_BAUGD q) hρq.le
  have hco := S.edge_conorm_BAUGD hγc hγc1 hβc1 j hd hηle h1' h2'
  have hker := rim_pair_surjective_kernel_BAUGD
    {u : TangentSpace (𝓡 3) q | S.completion.metric.inner q u u = S.rho j.1 ^ 2}
    (mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) S.edgeSmoothing_BAUGD q : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.rho z.val) q : TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.height z.val) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.scale z.val) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeRatio_BAUGD j (C.toChain.E z.val)) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => S.edgeSmoothing_BAUGD z / S.rho z.val) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    (mvfderiv (𝓡 3) (fun z : W.pieceInterior ⊤ => C.toChain.heightRatio z.val) q :
      TangentSpace (𝓡 3) q →ₗ[ℝ] ℝ)
    hrj hρ99 hS hB ht0 (by rw [hnorm]; linarith) hΔ1 hκ hC hc
    (fun u => S.dt_quotient_BAUGD j hd hηle h1' h2' u)
    (fun u => C.dT_quotient_BAUGD q u)
    (fun u hu => by
      have h := C.abs_dscale_le_BAUGD q u
      rw [hsg u hu] at h
      exact h.trans_eq (by ring))
    (fun u hu => by
      have h := abs_drho_le_BAUGD (S := S) hΛ q u
      rw [hsg u hu] at h
      exact h.trans (by nlinarith [hrj]))
    (fun u hu => by
      have h := C.abs_dheight_sub_dsmoothing_BAUGD hΔ0 hder j hreg hD4 u
      rw [hsph u hu] at h
      exact h.trans_lt (mul_lt_mul_of_pos_right hHd hrj))
    (fun u hu => by
      have h := S.abs_dedgeSmoothing_le_BAUGD hε0 j hd hηle h1' h2' u
      rw [hsph u hu] at h
      exact h.trans_lt (mul_lt_mul_of_pos_right (by linarith) hrj))
    (fun u hu => by
      have h := C.abs_dedge_sub_deta_BAUGD hΔ0 hder j hreg hD4 u
      rw [hsph u hu] at h
      refine h.trans_lt ?_
      calc (S.rho j.1)⁻¹ * (Hd * S.rho j.1) = Hd := by field_simp
        _ < c 2 := hHd)
    hco
  exact hker

include C in
/-- **The rim surjectivity at an interior point** (the `hrim` input of
`BoundaryGaf02ChainE.edgeParentOfRim_BAUGD`): under the localization `d(q, j) < 100Δρ_j`,
`|η_j| < 4.01Δ`, `t < 4.01Δ` and at `T = 4Δ`, the functional `ℓ = λ_j` of `f₂` has
`(d(ℓ ∘ f₂), dT)` onto `ℝ × ℝ` at `q`. Numerical premises as in `rim_surjective_wdeg_BAUGD`. -/
theorem rim_surjective_BAUGD (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 401 / 100 * Δ) (ht : S.edgeHeightRaw q < 401 / 100 * Δ)
    (hT : C.toChain.heightRatio q.val = 4 * Δ) :
    ∃ ℓ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ,
      Function.Surjective (fun v : TangentSpace W.model q.val =>
        (mvfderiv W.model (fun z => ℓ (C.toChain.stageMap 1 z)) q.val v,
          mvfderiv W.model C.toChain.heightRatio q.val v)) := by
  refine ⟨S.edgeRatio_BAUGD j, ?_⟩
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) C.toChain.E q.val :=
    ((C.stage_smooth_BAUGD 3) _).mdifferentiableAt (by simp)
  have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio q.val :=
    (C.heightRatio_contMDiff_BAUGD q.val).mdifferentiableAt (by simp)
  have hfun : (fun z => S.edgeRatio_BAUGD j (C.toChain.stageMap 1 z)) =
      fun z => S.edgeRatio_BAUGD j (C.toChain.E z) :=
    funext fun z => S.edgeRatio_stageProj_one_BAUGD j (C.toChain.E z)
  rw [hfun]
  have hsurj := C.rim_surjective_wdeg_BAUGD hc hC hε0 hε hγc hγc1 hβc1 j hd hη ht hT
  intro y
  obtain ⟨u, hu⟩ := hsurj y
  refine ⟨mfderiv (𝓡 3) W.model Subtype.val q u, ?_⟩
  have e1 := mvfderiv_clm_comp_val_BAUGD (S.edgeRatio_BAUGD j) C.toChain.E q hE u
  have e1' := mvfderiv_clm_comp_BDFB (I := W.model) (S.edgeRatio_BAUGD j) hE
    (mfderiv (𝓡 3) W.model Subtype.val q u)
  have e2 := mvfderiv_comp_val_BCG7 W C.toChain.heightRatio q hTd u
  beta_reduce at hu ⊢
  rw [e1'] 
  rw [← e1, ← e2]
  exact hu

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
