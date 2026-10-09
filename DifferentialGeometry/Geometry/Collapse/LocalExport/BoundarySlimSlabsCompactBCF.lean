import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecomposition
import DifferentialGeometry.Geometry.Collapse.LocalExport.OriginalSlabCompactness

/-!
# BCF01 input (c): the original closed slim slabs of the boundary supply are compact
(lane S-BCF134c, suffix `_BCF`; blueprint BCF01 proof: "The original closed slim slabs are compact
by their original proper bundle")

`BoundarySupplyCore.slimSlabs_BIF` is the union over the (finitely many) slim centres `j` of
`{q | dist q j < 10⁶Δρ(j), |η_j q| ≤ 3.5·10⁵Δ}`. Each piece is the whole closed slab of the slim
chart of the regional slim centre (`SlimChart.isCompact_closedSlab_FPRE`: LFR20's proper
restriction, at the normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)` whose topology is that of `d`), so the
union is compact in `W°`.

* `ball_rescale_iff_BCF`: the physical ball `B(j, kρ(j))` is the normalized ball `B(j, k)`;
* `SlimCentreOn.isCompact_closedSlab_BCF`: the whole closed slab of ONE regional slim centre;
* `BoundarySupplyCore.isCompact_slimSlabs_BCF`: the union of the original closed slabs
  `{|η_j| ≤ 3.5·10⁵Δ}` is compact, and its image in `W` (`Subtype.val`) too
  (`isCompact_val_slimSlabs_BCF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The physical ball `B(j, kρ(j))` is the ball of radius `k` of the normalized metric at `j`. -/
theorem ball_rescale_iff_BCF {Z : Type*} {m : MetricSpace Z} {r : Z → ℝ} {j x : Z}
    (hj : 0 < r j) {k : ℝ} :
    x ∈ @ball Z (m.rescale (r j)⁻¹ (inv_pos.mpr hj)).toPseudoMetricSpace j k ↔
      x ∈ @ball Z m.toPseudoMetricSpace j (k * r j) := by
  change (r j)⁻¹ * @dist Z m.toDist x j < k ↔ @dist Z m.toDist x j < k * r j
  rw [inv_mul_lt_iff₀ hj]
  constructor <;> intro h <;> linarith

section Centre

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- **The whole closed slab of a regional slim centre is compact** (`a < 905·10³Δ`): the slab
`{x ∈ B(j, 10⁶Δρ(j)) | |η_j x| ≤ a}` of the slim coordinate `coord_BCG2`. -/
theorem SlimCentreOn.isCompact_closedSlab_BCF (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j)
    {a : ℝ} (ha : a < 905 * 10 ^ 3 * Δ) :
    IsCompact {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ |c.coord_BCG2 x| ≤ a} := by
  have hr := hρ j
  have hS : {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ |c.coord_BCG2 x| ≤ a} =
      {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace j (10 ^ 6 * Δ) ∧
        |c.coord_BCG2 x| ≤ a} := by
    ext x
    exact and_congr_left' (ball_rescale_iff_BCF (m := mX) hr (k := (10 ^ 6 * Δ))).symm
  rw [hS]
  let Pk := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact Pk.isCompact_closedSlab_FPRE ha

end Centre

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **The union of the original closed slim slabs is compact** (`0 < Δ`): the finite union over the
slim centres of the whole closed slabs `{|η_j| ≤ 3.5·10⁵Δ}` (BCF01's input (c); the blueprint's
"compact by their original proper bundle"). -/
theorem BoundarySupplyCore.isCompact_slimSlabs_BCF (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ
    b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM) (hΔ : 0 < Δ) :
    IsCompact S.slimSlabs_BIF := by
  let _m := inducedMetricSpace S.completion.metric
  let _c := S.completion.complete
  have hfin := S.family.slim.finite_centres
  have heq : S.slimSlabs_BIF = ⋃ j ∈ S.family.slim.centres,
      {x | x ∈ ball j (1000000 * Δ * S.rho j) ∧ |S.slimEta_BIF j x| ≤ 350000 * Δ} := by
    ext q
    constructor
    · rintro ⟨j, hj, h1, h2⟩
      exact mem_iUnion₂.mpr ⟨j, hj, mem_ball.mpr h1, h2⟩
    · intro hq
      obtain ⟨j, hj, h1, h2⟩ := mem_iUnion₂.mp hq
      exact ⟨j, hj, mem_ball.mp h1, h2⟩
  rw [heq]
  refine hfin.isCompact_biUnion fun j hj => ?_
  have hη : (fun x => |S.slimEta_BIF j x|) =
      fun x => |(S.family.slim.centre j hj).coord_BCG2 x| := by
    funext x
    unfold BoundarySupplyCore.slimEta_BIF
    rw [dite_eq_left hj]
  have hset : {x | x ∈ ball j (1000000 * Δ * S.rho j) ∧ |S.slimEta_BIF j x| ≤ 350000 * Δ} =
      {x | x ∈ ball j (10 ^ 6 * Δ * S.rho j) ∧ |(S.family.slim.centre j hj).coord_BCG2 x| ≤
        350000 * Δ} := by
    ext x
    simp only [mem_ofPred_eq]
    have h1 : (1000000 : ℝ) = 10 ^ 6 := by norm_num
    rw [h1, congrFun hη x]
  rw [hset]
  exact (S.family.slim.centre j hj).isCompact_closedSlab_BCF (by nlinarith)

/-- The image of the original closed slim slabs in `W` is compact. -/
theorem BoundarySupplyCore.isCompact_val_slimSlabs_BCF (S : BoundarySupplyCore K A β βd εN Λ w Δ
    σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W g δn n B oM) (hΔ : 0 < Δ) :
    IsCompact (Subtype.val '' S.slimSlabs_BIF) :=
  (S.isCompact_slimSlabs_BCF hΔ).image continuous_subtype_val

end DifferentialGeometry.Geometry.Collapse
