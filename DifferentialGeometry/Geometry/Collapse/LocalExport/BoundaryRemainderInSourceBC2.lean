import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesRestBC2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFApplications

/-!
# BCF02 pieces, part 3: `R_c ⊆ X₁` (`hX1`) from the four-family cover (lane S-BCF02b, G1)

The first of the four atomic inputs of `bcf02_pieces_of_rest_BC2` (the conjunct `R_c ⊆ X₁` of
the frozen `bcf02_pieces_BCF02`, B:9805-9812 "all points of `R` are two-stratum and eligible for
the ORIGINAL selected circle cover, which puts them in `X_1`"), proved from the interface and the
register premises alone:

* `EdgeFamilyOn.abs_coord_le_BC2`: `|η_j| ≤ 3.5Δ` on the edge ball `B(j, 2Δρ_j)` (the actual edge
  coordinate is `(1 + σ_c)/ρ_j`-Lipschitz and vanishes at the centre);
* `EdgeFamilyOn.smoothing_div_le_BC2`: `smoothing/ρ ≤ 3.5Δ` on `B(j, 2Δρ_j)` (the centre is a
  point of the closed weak-edge set, `smoothing_value`, slow variation of `ρ`);
* `BoundarySupply.circleEta_norm_lt_BC2`: `‖η_j‖ < 2(1 + γ)` on the plateau ball `B(j, 2ρ_j)`
  (the adapted packet's `(1 + γ)`-Lipschitz chart), hence `≤ 7/2` for `γ ≤ 3/4`;
* `BoundaryGaf02BasesV2.edge_ball_subset_interior_BC2`: `B(j, 2Δρ_j) ⊆ int X₂` (EDP02's
  `edge_original_subset`);
* **`BoundaryCompactSlimChoiceV2.remainder_subset_source_BC2`**: `R_c ⊆ X₁` (`bcg01_cover_BCG3`:
  zero balls are excluded by `zero_exclusion_of_mem_M₂_BCF`, slim balls by
  `slim_exclusion_of_mem_M₂_BCF`, a point of an edge ball is interior to `P_e` in `M₂` hence not
  in `R_c`, and a point of a circle ball is in `X₁` by `circle_original_subset`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
  {U₁ U₂ : Set X}

/-- **The edge coordinate on the plateau ball**: on `B(j, 2Δρ_j)` of an edge centre `j`,
`|η_j| ≤ 3.5Δ` (the coordinate is `(1 + σc)/ρ_j`-Lipschitz and vanishes at `j`; `σc ≤ 1/1000`). -/
theorem EdgeFamilyOn.abs_coord_le_BC2
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hΔ : 0 < Δ)
    (hσc : σc ≤ 1 / 1000) {j : X} (hj : j ∈ F.centres) {x : X}
    (hx : dist x j < 2 * Δ * ρ j) : |F.coord_BAUGA j x| ≤ 7 / 2 * Δ := by
  have hrj := hρ j
  have h := F.coord_lipschitz_BCF2K hj x j
  rw [F.coord_self_BCF2K hj, sub_zero] at h
  have hM : max (1 + σc) 0 ≤ 1001 / 1000 := max_le (by linarith) (by norm_num)
  have hM0 : 0 ≤ max (1 + σc) 0 := le_max_right _ _
  have h1 : max (1 + σc) 0 / ρ j * dist x j ≤ max (1 + σc) 0 / ρ j * (2 * Δ * ρ j) :=
    mul_le_mul_of_nonneg_left hx.le (by positivity)
  have h2 : max (1 + σc) 0 / ρ j * (2 * Δ * ρ j) = 2 * max (1 + σc) 0 * Δ := by
    field_simp
  have h3 : 2 * max (1 + σc) 0 * Δ ≤ 2 * (1001 / 1000) * Δ := by
    have := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right this hΔ.le
  linarith

/-- **The weak-edge height on the plateau ball**: at an edge centre `j` (a point of the closed
weak-edge set), `smoothing x / ρ x ≤ 3.5Δ` for `d(x, j) < 2Δρ_j` (`μ ≤ 10⁻⁸`, the scale is
`Λ`-Lipschitz, `2ΔΛ ≤ 1/4`). -/
theorem EdgeFamilyOn.smoothing_div_le_BC2
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {Λ : ℝ} (hΔ : 0 < Δ)
    (hΛ : 0 ≤ Λ) (hlip : LipschitzWith (Real.toNNReal Λ) ρ) (hμ : μ ≤ 1 / 10 ^ 8)
    (hlam : 2 * Δ * Λ ≤ 1 / 4) {j : X} (hj : j ∈ F.centres) {x : X}
    (hx : dist x j < 2 * Δ * ρ j) : F.smoothing x / ρ x ≤ 7 / 2 * Δ := by
  have hrj := hρ j
  have hrx := hρ x
  have hjA := F.mem_closure_weakEdge_BDRY5 hj
  have hval := F.smoothing_value j hj x
  have hinf : infDist x (closure
      {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) ≤
      dist x j := infDist_le_dist_of_mem hjA
  have hμ0 : 0 ≤ μ := by
    by_contra h
    push Not at h
    have := abs_nonneg (F.smoothing x - infDist x (closure
      {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}))
    have h2 : μ * (Δ * ρ j) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  have hsm : F.smoothing x < (2 + 1 / 10 ^ 8) * (Δ * ρ j) := by
    have h1 := (abs_lt.mp hval).2
    have h2 : μ * (Δ * ρ j) ≤ 1 / 10 ^ 8 * (Δ * ρ j) :=
      mul_le_mul_of_nonneg_right hμ (by positivity)
    nlinarith
  have hρx : 3 / 4 * ρ j ≤ ρ x := by
    have h1 := hlip.dist_le_mul x j
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist x j ≤ Λ * (2 * Δ * ρ j) := mul_le_mul_of_nonneg_left hx.le hΛ
    have h3 : Λ * (2 * Δ * ρ j) = (2 * Δ * Λ) * ρ j := by ring
    have h4 : (2 * Δ * Λ) * ρ j ≤ 1 / 4 * ρ j := mul_le_mul_of_nonneg_right hlam hrj.le
    linarith [(abs_le.mp h1).1]
  rw [div_le_iff₀ hrx]
  nlinarith [mul_pos hΔ hrj]

end Generic

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **The circle chart coordinate on the plateau ball** (the adapted packet's `(1 + γ)`-Lipschitz
chart, centred): on `B(j, 2ρ_j)` the normalized coordinate `η_j` has norm `< 2(1 + γ)`. -/
theorem circleEta_norm_lt_BC2 {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 0)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j < 2 * S.rho j) :
    ‖S.circleEta_BIF j q‖ < 2 * (1 + γ) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.circle.centres := hj
  have hr := S.rho_pos j
  have hqd : (S.rho j)⁻¹ * dist q j < 2 := by
    rw [inv_mul_lt_iff₀ hr]
    linarith
  obtain ⟨Dq, hDq⟩ : ∃ D : ℝ, D = (S.rho j)⁻¹ * dist q j := ⟨_, rfl⟩
  rw [← hDq] at hqd
  have heta : S.circleEta_BIF j =
      (let c := S.family.circle.chart j hj'
       letI := (inducedMetricSpace S.completion.metric).rescale (S.rho j)⁻¹
         (inv_pos.mpr (S.rho_pos j))
       c.coord) := by
    unfold BoundarySupplyCore.circleEta_BIF
    rw [dite_eq_left hj']
  have ad := S.family.circleAdapted j hj'
  have hγ0 : 0 ≤ γ := by
    have h := ad.adapted j (by
      let _ := (inducedMetricSpace S.completion.metric).rescale (S.rho j)⁻¹
        (inv_pos.mpr (S.rho_pos j))
      exact mem_ball_self (by norm_num))
    exact (norm_nonneg _).trans h.le
  have hcc := S.family.circle.chart_center j hj'
  have hlip := ad.lipschitz
  let c := S.family.circle.chart j hj'
  let _ := (inducedMetricSpace S.completion.metric).rescale (S.rho j)⁻¹ (inv_pos.mpr hr)
  have hcc' : c.center = j := hcc
  have h0 : c.coord j = 0 := by
    have h := c.coord_center
    rwa [hcc'] at h
  have hqB : q ∈ ball j 200 := by
    rw [hDq] at hqd
    exact hqd.trans (by norm_num)
  have hjB : j ∈ ball j 200 := mem_ball_self (by norm_num)
  have hl : LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200) := hlip
  have hd := hl.dist_le_mul q hqB j hjB
  rw [h0, dist_zero_right, Real.coe_toNNReal _ (by linarith)] at hd
  have hd' : ‖c.coord q‖ ≤ (1 + γ) * Dq := by
    rw [hDq]
    exact hd
  rw [heta]
  change ‖c.coord q‖ < 2 * (1 + γ)
  have hpos : 0 < 1 + γ := by linarith
  calc ‖c.coord q‖ ≤ (1 + γ) * Dq := hd'
    _ < (1 + γ) * 2 := mul_lt_mul_of_pos_left hqd hpos
    _ = 2 * (1 + γ) := by ring

end BoundarySupply

section Assembly

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryGaf02BasesV2

/-- **An edge ball lies in the interior of `X₂`**: for a revised edge centre `j`, the ball
`B(j, 2Δρ_j)` lies in `int X₂` (EDP02's `edge_original_subset`, with `|η_j| ≤ 3.5Δ` and
`smoothing/ρ ≤ 3.5Δ` on the ball). -/
theorem edge_ball_subset_interior_BC2 (Bs : BoundaryGaf02BasesV2 C) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ)
    (hμ : μ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    {j : W.pieceInterior ⊤} (hj : j ∈ S.stageCentres_BIF 1) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j < 2 * Δ * S.rho j) :
    q.val ∈ interior (Bs.source 1) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj' : j ∈ S.family.edgeB.centres := hj
  have hr := S.rho_pos j
  have hΔΛ : 2 * Δ * Λ ≤ 1 / 4 := by nlinarith
  have heta : S.edgeEta_BIF j q = S.family.edgeB.coord_BAUGA j q := by
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left hj', S.family.edgeB.coord_BAUGA_of_mem hj']
  have hht : S.edgeHeightRaw q = S.family.edgeB.smoothing q / S.rho q := rfl
  refine Bs.edge_original_subset q j hj ?_ ?_ ?_
  · have : 2 * Δ * S.rho j ≤ 100 * Δ * S.rho j := by nlinarith
    linarith
  · rw [heta]
    exact S.family.edgeB.abs_coord_le_BC2 hΔ hσc hj' hq
  · rw [hht]
    exact S.family.edgeB.smoothing_div_le_BC2 hΔ hΛ S.family.lipschitz_scale hμ hΔΛ hj' hq

end BoundaryGaf02BasesV2

namespace BoundaryCompactSlimChoiceV2

/-- **`hX1`: `R_c ⊆ X₁`** (BCF02 clause "`R ⊂ X₁`", B:9805-9812). A point `p` of the circle
remainder lies in `M₂ ⊆ {D ≥ 35}`; the four-family cover of `{D ≥ 35}` puts it in a zero ball
(excluded by the zero exclusion of `M₂`), a slim ball (excluded by the slim exclusion), an edge
ball (then `p ∈ int X₂`, so `p` is interior to `P_e` in `M₂` and not in `R_c`), or a circle ball
(then `‖η_j(p)‖ < 2(1 + γ) ≤ 7/2` and `p ∈ X₁` by GAF07's `circle_original_subset`). -/
theorem remainder_subset_source_BC2 (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hγ34 : γ ≤ 3 / 4)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) :
    Kc.remainder ⊆ Bs.source 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro p hp
  obtain ⟨hpM, hpR⟩ := hp
  have h35 : ENNReal.ofReal 35 ≤ distanceToBoundary W g p := Kc.M₂_subset_D35_BCF hpM
  have hpos : 0 < distanceToBoundary W g p :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) h35
  have hpi := mem_interior_of_distanceToBoundary_pos_BDRY1 W g hpos
  rw [← coe_pieceInterior_top_BDRY1 W] at hpi
  let q : W.pieceInterior ⊤ := ⟨p, hpi⟩
  have hqM : q.val ∈ Kc.M₂ := hpM
  have hU : {x : W.pieceInterior ⊤ | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} ⊆
      {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x} := fun y hy =>
    lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)) hy
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hcov := S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.bcg01_cover_BCG3 hU q h35
  rcases hcov with ⟨z, hz, hqz⟩ | ⟨j, hj, hqj⟩ | ⟨j, hj, hqj⟩ | ⟨j, hj, hqj⟩
  · exfalso
    have hex := Kc.zero_exclusion_of_mem_M₂_BCF Z q hqM z hz
    have hqz' : dist q z < (S.family.zero.zero z hz).radius / 10 := mem_ball.mp hqz
    have hrad := (S.family.zero.zero z hz).radius_pos
    linarith
  · exact Bs.circle_original_subset q j hj
      (by
        have h2 : dist q j < 2 * S.rho j := mem_ball.mp hqj
        have hr := S.rho_pos j
        linarith)
      (by
        have h2 : dist q j < 2 * S.rho j := mem_ball.mp hqj
        have := S.circleEta_norm_lt_BC2 hj h2
        linarith)
  · exfalso
    have hr := S.rho_pos j
    have hj' : j ∈ S.family.slim.centres := hj
    have hqj' : dist q j < 2 * (Δ * S.rho j) := mem_ball.mp hqj
    have hd9 : dist q j < 9 * Δ * S.rho j := by nlinarith [mul_pos hΔ hr]
    have hex := Kc.slim_exclusion_of_mem_M₂_BCF hΔ.le hσs q hqM j hj' hd9
    have hcoord := (S.family.slim.centre j hj').abs_coord_sub_le_BCF2K hσs q j
    rw [(S.family.slim.centre j hj').coord_self_BCF2K, sub_zero] at hcoord
    have h1 : (1 + σs) * (S.rho j)⁻¹ * dist q j ≤ (1 + σs) * (S.rho j)⁻¹ * (2 * (Δ * S.rho j)) :=
      mul_le_mul_of_nonneg_left hqj'.le (by positivity)
    have h2 : (1 + σs) * (S.rho j)⁻¹ * (2 * (Δ * S.rho j)) = 2 * (1 + σs) * Δ := by
      field_simp
    nlinarith
  · exfalso
    have hint := Bs.edge_ball_subset_interior_BC2 hΔ hΛ hμ hσc hLΛ hj (q := q) hqj
    refine hpR ⟨⟨p, hpM⟩, ?_, rfl⟩
    refine mem_interior.mpr ⟨Subtype.val ⁻¹' interior (Bs.source 1), ?_, ?_, hint⟩
    · rintro ⟨y, hyM⟩ hy
      exact ⟨hyM, interior_subset hy⟩
    · exact isOpen_interior.preimage continuous_subtype_val

end BoundaryCompactSlimChoiceV2

end Assembly

end DifferentialGeometry.Geometry.Collapse
