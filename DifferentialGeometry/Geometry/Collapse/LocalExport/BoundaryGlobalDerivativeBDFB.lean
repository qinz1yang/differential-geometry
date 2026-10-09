import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBlockBudgetsApplicationsBDFB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Fibration.ActualGlobalDerivative

/-!
# CGP02 on the complete final boundary family `(W°, ĝ)` (lane B-DFB, G2)

Blueprint `master207B.tex`, CGP02 (`prop:fibration-actual-global-derivative`, B:3956–4002) in the
boundary setting of BCG.0/BCG01 (B:8700–8790): the interior part of the augmented map keeps the
source formulas of the ACTIVE family, so CGP02's square-sum calculation applies on the completed
interior `(W°, d_ĝ)` with LPA06's boundary multiplicity.

* `cgp_active_tags_ncard_le_BDFB`: on `F : LocalPacketsOnBFRZ`, the circle, slim, `edgeB` and zero
  tags whose cutoff's closed support contains `x` number at most `N_TCP + 1`
  (`lpa06_pointwise_le_BFRZ` for circle, slim, `edgeB`; `zero_list_le_one_BFRZ` for the zero tags);
* `cgp_active_edge_card_le_BDFB`: the `edgeB` cutoffs whose closed support contains `x` number at
  most `N_TCP`;
* `cgp02_row_BDFB`: `‖d𝓔⁰(v)‖ ≤ 1000 (N_TCP + 2) P₀² √(g_x(v, v))` for the ported global map
  `cgpGlobalMap_BAUGP F.toLocalPacketsOnB F.zero` (FC02 `norm_mvfderiv_blockMap_apply_le_fc02`, the
  ported block budgets of G1, `early_derivative_constant`);
* `BoundarySupplyCore.norm_mvfderiv_interiorMapOn_le_BDFB`: the same for BAUG-A's interior formula
  `S.interiorMapOn_BAUGA` on `(W°, ĝ)` (through `interiorMapOn_eq_cgpGlobalMap_BAUGP`).

`N_TCP = tcp01SupportBound`, `P₀ = cgpProfileBound` are numerical (fixed before `Δ`, noncollapse,
the number of charts and the scale range). Parameter ranges: B-COUNT's (`Δ ≥ 1`,
`10⁶ΔΛ < 10⁻⁵`, `Lmax`, `e < 1/40`, `T`), FC18 (ii)'s `μ, τ ≤ 1/100`, and
`σ_s, σ_c, γ_c, ε_r ∈ [0, 1]` (CGP02's constant-radius budget).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Analysis DifferentialGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section BFRZ

attribute [local instance] LocalPacketsOn.instMetricN LocalPacketsOn.instChartedN
  LocalPacketsOn.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The active tags of the boundary `𝓔⁰` at `x`** (circle, slim, `edgeB`, zero tags whose
cutoff's closed support contains `x`) are at most `N_TCP + 1`: LPA06 bounds the circle, slim and
`edgeB` closed supports containing `x` by `N_TCP`, and at most one zero support meets
`B(x, 10ρ(x))`. -/
theorem cgp_active_tags_ncard_le_BDFB
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (x : X) :
    {i : CGPTag_BAUGP F.toLocalPacketsOnB F.zero |
        i ≠ cgpScaleTag_BAUGP F.toLocalPacketsOnB F.zero ∧
        i ≠ cgpEdgeTag_BAUGP F.toLocalPacketsOnB F.zero ∧
        x ∈ tsupport (cgpCutoff_BAUGP F.toLocalPacketsOnB F.zero i)}.ncard ≤
      tcp01SupportBound + 1 := by
  have hx : x ∈ ball x (10 * ρ x) := mem_ball_self (mul_pos (by norm_num) (hρ x))
  set L := F.toLocalPacketsOnB with hL
  set Z := F.zero with hZ
  let SC : Set L.circle.finite_centres.toFinset := {j | x ∈ tsupport (L.circle.cutoff j)}
  let SS : Set L.slim.finite_centres.toFinset := {j | x ∈ tsupport (L.slim.cutoff_BCNT j)}
  let SE : Set L.edgeB.finite_centres.toFinset := {j | x ∈ tsupport (L.edgeB.cutoff_BAUGA j)}
  let SZ : Set Z.finite_centres.toFinset := {i | x ∈ tsupport (fun y =>
    Calculus.annularCutoff Calculus.cutoffProfile
      ((Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial y))}
  let fC : L.circle.finite_centres.toFinset → CGPTag_BAUGP L Z := Sum.inl
  let fS : L.slim.finite_centres.toFinset → CGPTag_BAUGP L Z := fun j => Sum.inr (Sum.inl j)
  let fE : L.edgeB.finite_centres.toFinset → CGPTag_BAUGP L Z :=
    fun j => Sum.inr (Sum.inr (Sum.inl j))
  let fZ : Z.finite_centres.toFinset → CGPTag_BAUGP L Z :=
    fun i => Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
  have hsub : {i : CGPTag_BAUGP L Z | i ≠ cgpScaleTag_BAUGP L Z ∧ i ≠ cgpEdgeTag_BAUGP L Z ∧
      x ∈ tsupport (cgpCutoff_BAUGP L Z i)} ⊆ fC '' SC ∪ fS '' SS ∪ fE '' SE ∪ fZ '' SZ := by
    rintro (j | j | j | i | bb) ⟨h1, h2, h3⟩
    · exact Or.inl (Or.inl (Or.inl ⟨j, h3, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨j, h3, rfl⟩))
    · exact Or.inl (Or.inr ⟨j, h3, rfl⟩)
    · exact Or.inr ⟨i, h3, rfl⟩
    · cases bb
      · exact absurd rfl h1
      · exact absurd rfl h2
  have h1 := Set.ncard_le_ncard hsub
  have h2 := (Set.ncard_union_le (fC '' SC ∪ fS '' SS ∪ fE '' SE) (fZ '' SZ)).trans
    (Nat.add_le_add_right ((Set.ncard_union_le (fC '' SC ∪ fS '' SS) (fE '' SE)).trans
      (Nat.add_le_add_right (Set.ncard_union_le (fC '' SC) (fS '' SS)) _)) _)
  have hC : (fC '' SC).ncard ≤
      (F.circle.centres ∩ {j | x ∈ tsupport (F.circle.cutoff j)}).ncard :=
    (Set.ncard_image_le).trans (ncard_subtype_le_KA2 L.circle.finite_centres
      (p := fun y => x ∈ tsupport (L.circle.cutoff y))
      (q := fun y => x ∈ tsupport (L.circle.cutoff y)) fun _ _ hy => hy)
  have hS : (fS '' SS).ncard ≤
      (F.slim.centres ∩ {j | x ∈ tsupport (F.slim.cutoff_BCNT j)}).ncard :=
    (Set.ncard_image_le).trans (ncard_subtype_le_KA2 L.slim.finite_centres
      (p := fun y => x ∈ tsupport (L.slim.cutoff_BCNT y))
      (q := fun y => x ∈ tsupport (L.slim.cutoff_BCNT y)) fun _ _ hy => hy)
  have hE : (fE '' SE).ncard ≤
      (F.edgeB.centres ∩ {j | x ∈ tsupport (F.edgeB.cutoff_BAUGA j)}).ncard :=
    (Set.ncard_image_le).trans (ncard_subtype_le_KA2 L.edgeB.finite_centres
      (p := fun y => x ∈ tsupport (L.edgeB.cutoff_BAUGA y))
      (q := fun y => x ∈ tsupport (L.edgeB.cutoff_BAUGA y)) fun _ _ hy => hy)
  have hZc : (fZ '' SZ).ncard ≤ (zeroMeetingListOn_BCNT F.zero x 10).ncard := by
    refine (Set.ncard_image_le).trans ?_
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    refine Set.ncard_le_ncard ?_ (F.zero.finite_centres.subset fun _ hk => hk.choose)
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨(Set.Finite.mem_toFinset _).mp i.2, x, hi, hx⟩
  have hlpa := lpa06_pointwise_le_BFRZ F hΛ hΔ hLΛ hLmax x
  have hzero := zero_list_le_one_BFRZ F hΛ hΔ hLΛ he hT x (ℓ := 10) (by norm_num) (by nlinarith)
  omega

open Classical in
/-- The `edgeB` cutoffs whose closed support contains `x` number at most `N_TCP` (LPA06). -/
theorem cgp_active_edge_card_le_BDFB
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (x : X) :
    ((Finset.univ.filter fun i : F.edgeB.finite_centres.toFinset =>
        x ∈ tsupport (F.edgeB.cutoff_BAUGA i)).card : ℝ) ≤ tcp01SupportBound := by
  have hcard : (Finset.univ.filter fun i : F.edgeB.finite_centres.toFinset =>
      x ∈ tsupport (F.edgeB.cutoff_BAUGA i)).card ≤
        (F.edgeB.centres ∩ {j | x ∈ tsupport (F.edgeB.cutoff_BAUGA j)}).ncard := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp only [Finset.mem_univ, true_and]
    exact ncard_subtype_le_KA2 F.edgeB.finite_centres
      (p := fun y => x ∈ tsupport (F.edgeB.cutoff_BAUGA y))
      (q := fun y => x ∈ tsupport (F.edgeB.cutoff_BAUGA y)) fun _ _ hy => hy
  have hlpa := lpa06_pointwise_le_BFRZ F hΛ hΔ hLΛ hLmax x
  have h : (Finset.univ.filter fun i : F.edgeB.finite_centres.toFinset =>
      x ∈ tsupport (F.edgeB.cutoff_BAUGA i)).card ≤ tcp01SupportBound := by omega
  exact_mod_cast h

/-- **CGP02 on the complete final boundary family**: the ported global map
`𝓔⁰ = cgpGlobalMap_BAUGP F.toLocalPacketsOnB F.zero` (ACTIVE edge `edgeB`) satisfies
`‖d𝓔⁰(v)‖ ≤ 1000 (N_TCP + 2) P₀² √(g_x(v, v))` for every tangent vector; `N_TCP`, `P₀` numerical. -/
theorem cgp02_row_BDFB
    (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) (x : X)
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP F.toLocalPacketsOnB F.zero) x v‖ ≤
      1000 * ((tcp01SupportBound : ℝ) + 2) * cgpProfileBound ^ 2 * Real.sqrt (g.inner x v v) := by
  have hP1 := cgpProfileBound_spec.1
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hΛ1 : Λ ≤ 1 := by nlinarith
  set L := F.toLocalPacketsOnB with hL
  set Z := F.zero with hZ
  have hmargin : ∀ j ∈ L.edgeB.centres,
      tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j) := fun _ hj =>
    (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ hτ hΔΛ hj).2.2
  have hF : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))
      (blockMap (cgpRadius_BAUGP L Z) (cgpCutoff_BAUGP L Z) (cgpCoord_BAUGP L Z)) x :=
    (contMDiff_cgpGlobalMap_family_BAUGP L Z hΛ hΔ0 hμ hτ hΔΛ (by linarith) x).mdifferentiableAt
      (by simp)
  have hN0 : (0 : ℝ) ≤ tcp01SupportBound := Nat.cast_nonneg _
  have hρE : cgpScaleTag_BAUGP L Z ≠ cgpEdgeTag_BAUGP L Z := by simp
  have hscale := cgp02_scale_tag_budget_BDFB L Z hΛ x v
  have hEblock : x ∈ tsupport (cgpCutoff_BAUGP L Z (cgpEdgeTag_BAUGP L Z)) →
      ‖mvfderiv 𝓘(ℝ, E3) (fun y => blockMap (cgpRadius_BAUGP L Z) (cgpCutoff_BAUGP L Z)
        (cgpCoord_BAUGP L Z) y (cgpEdgeTag_BAUGP L Z)) x v‖ ≤
        500 * ((tcp01SupportBound : ℝ) + 1) * cgpProfileBound ^ 2 *
          Real.sqrt (g.inner x v v) := by
    intro hx
    refine (cgp02_edgeMarker_tag_budget_BDFB L Z hΔ hΛ hΔΛ hσc hγc hmargin hx v).trans
      (mul_le_mul_of_nonneg_right ?_ hν)
    have hn := cgp_active_edge_card_le_BDFB F hΛ hΔ hLΛ hLmax x
    have hP2 : 0 ≤ cgpProfileBound ^ 2 := sq_nonneg _
    gcongr
  have hblock : ∀ i, i ≠ cgpScaleTag_BAUGP L Z → i ≠ cgpEdgeTag_BAUGP L Z →
      x ∈ tsupport (cgpCutoff_BAUGP L Z i) →
      ‖mvfderiv 𝓘(ℝ, E3) (fun y => blockMap (cgpRadius_BAUGP L Z) (cgpCutoff_BAUGP L Z)
        (cgpCoord_BAUGP L Z) y i) x v‖ ≤
        (2 + 80 * cgpProfileBound) * Real.sqrt (g.inner x v v) := fun i h1 h2 hx =>
    cgp02_constant_radius_tag_budget_BDFB L Z hΔ hσs hσc hγc hεr (by linarith) hmargin i h1 h2
      hx v
  have hcount := cgp_active_tags_ncard_le_BDFB F hΛ hΔ hLΛ hLmax he hT x
  have h := norm_mvfderiv_blockMap_apply_le_fc02 (R := cgpRadius_BAUGP L Z)
    (ζ := cgpCutoff_BAUGP L Z) (η := cgpCoord_BAUGP L Z) hF v hν _ _ hρE hscale hEblock hblock
    hcount
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hν)
  have hB0 : (0 : ℝ) ≤ 2 + 80 * cgpProfileBound := by linarith
  have hcast : (((tcp01SupportBound + 1 : ℕ) : ℝ)) = (tcp01SupportBound : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact early_derivative_constant hN0 hP1 hΛ hΛ1 hB0 le_rfl (by positivity) le_rfl

end BFRZ

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundarySupplyCore

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    W g δn n B oM)

/-- **CGP02 for BAUG-A's interior formula on `(W°, ĝ)`**: `‖dF_int(u)‖ ≤ 1000 (N_TCP + 2) P₀² |u|_ĝ`
for `F_int = S.interiorMapOn_BAUGA` (the ACTIVE family's FC01 block map). -/
theorem norm_mvfderiv_interiorMapOn_le_BDFB (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1)
    (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) (x : W.pieceInterior ⊤)
    (u : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) S.interiorMapOn_BAUGA x u‖ ≤
      1000 * ((tcp01SupportBound : ℝ) + 2) * cgpProfileBound ^ 2 *
        Real.sqrt (S.completion.metric.inner x u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rw [S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  exact cgp02_row_BDFB S.family hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr x u

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
