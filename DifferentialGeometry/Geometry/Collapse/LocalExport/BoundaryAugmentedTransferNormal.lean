import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferTable
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityContributorBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedModelCircle

/-!
# The transfer layer, field `normal` (lane BAUG-C)

The spec field `normal` of `BoundaryEnhancedPlaneSpecV3` for the port table `portTable_BAUGC`
(transfer of the port clauses (PRE) and (TG derivative), `PortTargets v3.1`), uniform in the stage:
at every preimage `q ∈ W°` of a cloud point, the component of `π_j DF_∂(v)` normal to the plane is
at most `e|v|_g` in the ORIGINAL metric of `W`.

* generic kernel `norm_starProjection_le_of_augDeriv_BAUGC` (interior error `e₁`, one boundary slot
  error `e₂` ⟹ normal component `≤ e₁ + e₂`) and the derivative slot calculus of augmented maps
  (`augIntProj_blockRestrict_mvfderiv_BAUGC`, `mvfderiv_boundaryAugmentedMap_inr_BAUGC`);
* boundary geometry on the stored supply: `exists_pos_scale_lipschitz_BAUGC` (`Λ ≥ 0` replaced by a
  positive constant for BCG-8b), `four_lt_distanceToBoundary_of_dist_lt_BAUGC` (`D_a ⊆ {D > 4}`, so
  `ĝ = g°` there; T3B's consumer balls), `notMem_tsupport_block_of_notMem_BAUGC`,
  `mvfderiv_block_eq_zero_of_notMem_BAUGC` (unlisted components vanish on `D_a`),
  `boundaryList_facts_BAUGC` (`J_∂(a)` a subsingleton, `ρ(a) ≤ 1`, `D_a` in the collar band);
* the pointwise estimate `normal_at_preimage_BAUGC` / `normal_at_preimage_original_BAUGC`
  (interior part from (TG derivative), listed slot from BCG-8b's differential error, abstract plane);
* **`portTable_normal_BAUGC`**: the field `normal` of the port table;
* consumer `stage_normal_inputs_BAUGC`: the supply-side hypotheses of `portTable_normal_BAUGC`
  (centres in `{D > 10}`, rows of norm `≤ 1`, BCG02's (BA) on `D_a`) at the three stages with the
  stored coordinates and rows.

Heartbeat discipline (protocol: no `set_option`): every declaration that destructs or rewrites works
with an abstract plane `K` and the membership lemma `portTable_mem_plane_BAUGC`.
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

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]
  [Fintype κ] [DecidableEq κ]

/-- **The normal kernel** (transfer of `normal`): if `y` is `e₁`-close to `c • T_int z` in the
interior part and every boundary slot is `e₂`-close to `c • slot_b(T_b z)`, with at most one slot
error nonzero, then the component of `y` normal to any plane containing `c • D z`
(`D = augDeriv T_int T_b`) is at most `e₁ + e₂`. -/
theorem norm_starProjection_le_of_augDeriv_BAUGC
    (Tint : E →L[ℝ] BlockSpace (fun _ : ι => ℝ²)) (Tb : κ → E →L[ℝ] ℝ × ℝ)
    (K : Submodule ℝ (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) [K.HasOrthogonalProjection]
    (y : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (c : ℝ) (z : E)
    (hK : c • augDeriv_BAUGC Tint Tb z ∈ K) {e₁ e₂ : ℝ} (he₂ : 0 ≤ e₂)
    (hint : ‖augIntProjCLM_BAUGC y - c • Tint z‖ ≤ e₁)
    (hslot : ∀ b, ‖y (Sum.inr b) - c • planeBlockEmbed_BAUGA (Tb b z)‖ ≤ e₂)
    (huniq : ∀ b₁ b₂, y (Sum.inr b₁) - c • planeBlockEmbed_BAUGA (Tb b₁ z) ≠ 0 →
      y (Sum.inr b₂) - c • planeBlockEmbed_BAUGA (Tb b₂ z) ≠ 0 → b₁ = b₂) :
    ‖Kᗮ.starProjection y‖ ≤ e₁ + e₂ := by
  refine (norm_orthogonal_starProjection_le_BAUGC K y _ hK).trans ?_
  set d := y - c • augDeriv_BAUGC Tint Tb z with hd
  have hdint : augIntProjCLM_BAUGC d = augIntProjCLM_BAUGC y - c • Tint z := by
    rw [hd, map_sub, map_smul, ← ContinuousLinearMap.comp_apply augIntProjCLM_BAUGC,
      augIntProj_comp_augDeriv_BAUGC]
  have hdslot : ∀ b, d (Sum.inr b) = y (Sum.inr b) - c • planeBlockEmbed_BAUGA (Tb b z) := by
    intro b
    rw [hd, PiLp.sub_apply, PiLp.smul_apply, augDeriv_apply_inr_BAUGC]
  by_cases hex : ∃ b₀, d (Sum.inr b₀) ≠ 0
  · obtain ⟨b₀, hb₀⟩ := hex
    have h1 := norm_le_proj_add_slot_BAUGC d b₀ fun b hb => by
      by_contra hne
      exact hb (huniq b b₀ ((hdslot b) ▸ hne) ((hdslot b₀) ▸ hb₀))
    rw [hdint, hdslot b₀] at h1
    linarith [hint, hslot b₀]
  · push Not at hex
    rw [norm_eq_proj_of_slots_zero_BAUGC d hex, hdint]
    linarith

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- `‖ρ⁻¹D − T‖ ≤ e ρ⁻¹N ⟹ ‖D − ρT‖ ≤ eN` (`ρ > 0`). -/
theorem norm_sub_smul_le_of_inv_smul_BAUGC {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ e N : ℝ} (hρ : 0 < ρ) (D T : F) (h : ‖ρ⁻¹ • D - T‖ ≤ e * (ρ⁻¹ * N)) :
    ‖D - ρ • T‖ ≤ e * N := by
  have hsplit : D - ρ • T = ρ • (ρ⁻¹ • D - T) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  rw [hsplit, norm_smul, Real.norm_of_nonneg hρ.le]
  calc ρ * ‖ρ⁻¹ • D - T‖ ≤ ρ * (e * (ρ⁻¹ * N)) := mul_le_mul_of_nonneg_left h hρ.le
    _ = e * N := by field_simp

end Kernel

section Deriv

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
/-- `pr_int ∘ π_{s ⊕ κ} = π_s ∘ pr_int`. -/
theorem augIntProj_blockRestrict_disjSum_BAUGC [DecidableEq ι] [DecidableEq κ] (s : Finset ι)
    (v : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    augIntProjCLM_BAUGC (blockRestrict (s.disjSum Finset.univ) v) =
      blockRestrict s (augIntProjCLM_BAUGC v) := by
  refine PiLp.ext fun i => ?_
  rw [augIntProjCLM_apply_BAUGC, blockRestrict_apply, blockRestrict_apply,
    augIntProjCLM_apply_BAUGC]
  by_cases hi : i ∈ s
  · rw [ite_eq_left (Finset.inl_mem_disjSum.mpr hi), ite_eq_left hi]
  · rw [ite_eq_right (fun h => hi (Finset.inl_mem_disjSum.mp h)), ite_eq_right hi]

/-- **The interior part of the stage-projected derivative**: `pr_int π_{s ⊕ κ} DF(v) =
D(π_s ∘ pr_int ∘ F)(v)`. -/
theorem augIntProj_blockRestrict_mvfderiv_BAUGC [DecidableEq ι] [DecidableEq κ]
    {F : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²)} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²)) F x) (s : Finset ι)
    (v : TangentSpace I x) :
    augIntProjCLM_BAUGC (blockRestrict (s.disjSum Finset.univ) (mvfderiv I F x v)) =
      mvfderiv I (fun y => blockRestrict s (augIntProjCLM_BAUGC (F y))) x v := by
  have h := mvfderiv_clm_comp hF ((blockRestrict s).comp augIntProjCLM_BAUGC) v
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, augIntProj_blockRestrict_disjSum_BAUGC]

/-- **A boundary slot of the derivative of an augmented map**: `(DF(v))_b = slot(DB_b(v))`. -/
theorem mvfderiv_boundaryAugmentedMap_inr_BAUGC (Fint : M → BlockSpace (fun _ : ι => ℝ²))
    (Bl : κ → M → ℝ × ℝ) {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²))
      (boundaryAugmentedMap_BAUGA Fint Bl) x)
    (b : κ) (hB : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (Bl b) x) (v : TangentSpace I x) :
    mvfderiv I (boundaryAugmentedMap_BAUGA Fint Bl) x v (Sum.inr b) =
      planeBlockEmbed_BAUGA (mvfderiv I (Bl b) x v) := by
  have h1 := mvfderiv_clm_comp hF
    (blockProjCLM_PLN (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inr b)) v
  have h2 := mvfderiv_clm_comp hB planeBlockEmbed_BAUGA v
  have he : (fun y => blockProjCLM_PLN (V := fun _ : ι ⊕ κ => ℝ²) (Sum.inr b)
      (boundaryAugmentedMap_BAUGA Fint Bl y)) = fun y => planeBlockEmbed_BAUGA (Bl b y) :=
    funext fun _ => rfl
  rw [he, h2] at h1
  exact h1.symm

end Deriv

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- The three reference-domain constants `C_a = 10, 20Δ, 950000Δ` lie in `[0, 950000Δ]` for
`Δ ≥ 1`. -/
theorem stageDomain_BIF_bounds_BAUGC {Δ : ℝ} (hΔ : 1 ≤ Δ) (st : Fin 3) :
    0 ≤ stageDomain_BIF Δ st ∧ stageDomain_BIF Δ st ≤ 950000 * Δ := by
  fin_cases st
  · change (0 : ℝ) ≤ 10 ∧ (10 : ℝ) ≤ 950000 * Δ
    constructor <;> linarith
  · change (0 : ℝ) ≤ 20 * Δ ∧ 20 * Δ ≤ 950000 * Δ
    constructor <;> linarith
  · change (0 : ℝ) ≤ 950000 * Δ ∧ 950000 * Δ ≤ 950000 * Δ
    constructor <;> linarith

/-- A `ĝ`-ball of `W°` whose image is the `g`-ball of the same radius forces `D(j) ≥ R`. -/
theorem ofReal_le_distanceToBoundary_of_image_ball_BAUGC
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) {j : W.pieceInterior ⊤} {R : ℝ} :
    letI := inducedMetricSpace ĝ
    Subtype.val '' Metric.ball j R = riemannianBallOf g j.val R →
    ENNReal.ofReal R ≤ distanceToBoundary W g j.val := by
  let _ := inducedMetricSpace ĝ
  intro hball
  unfold distanceToBoundary
  refine le_iInf fun q => ?_
  by_contra hlt
  push Not at hlt
  have hq : (q : W.Carrier) ∈ riemannianBallOf g j.val R := hlt
  rw [← hball] at hq
  obtain ⟨y, -, hy⟩ := hq
  have hyI : (y : W.Carrier) ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1]
    exact y.2
  rw [hy, ← W.model.compl_boundary] at hyI
  exact hyI q.2

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- `d_g ≤ d_ĝ` on `W°`, in the `dist` of `ĝ`. -/
theorem riemannianEDistOf_le_ofReal_dist_BAUGC (q a : W.pieceInterior ⊤) :
    riemannianEDistOf g q.val a.val ≤
      ENNReal.ofReal (letI := inducedMetricSpace S.completion.metric; dist q a) := by
  let _ := inducedMetricSpace S.completion.metric
  have h1 := riemannianEDistOf_val_le_completion_BDRY1 W g S.completion.metric
    S.completion.inner_le q a
  rwa [inducedMetricSpace_hmetric S.completion.metric q a] at h1

/-- **A positive Lipschitz constant of the scale** with BCG-8b's `100ΔΛ' ≤ 10⁻⁶` (replaces
`Λ ≥ 0` by `Λ' = Λ + 10⁻¹²/Δ > 0`). -/
theorem exists_pos_scale_lipschitz_BAUGC (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∃ Λ' : ℝ, 0 < Λ' ∧ 100 * Δ * Λ' ≤ 1 / 1000000 ∧ Λ' * (950000 * Δ) ≤ 1 / 4 ∧
      ∀ x y, ENNReal.ofReal |S.rho x - S.rho y| ≤
        ENNReal.ofReal Λ' * riemannianEDistOf g x y := by
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Λ + 1 / (1000000000000 * Δ), by positivity, ?_, ?_, fun x y => ?_⟩
  · have h1 : 100 * Δ * (1 / (1000000000000 * Δ)) = 1 / 10000000000 := by field_simp; norm_num
    nlinarith
  · have h1 : 1 / (1000000000000 * Δ) * (950000 * Δ) = 95 / 100000000 := by
      field_simp; norm_num
    nlinarith
  · refine (S.scale_spec.2.1 x y).trans ?_
    gcongr
    linarith [show 0 < 1 / (1000000000000 * Δ) by positivity]

/-- **Reference domains stay in `{D > 4}`**: a point of `B_ĝ(a, Cρ(a))`, `C ≤ 950000Δ`, around a
centre with `D(a) > 10` has `D > 4` (T3B's consumer balls). -/
theorem four_lt_distanceToBoundary_of_dist_lt_BAUGC (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (hΔ : 0 ≤ Δ) {a q : W.pieceInterior ⊤} (ha : ENNReal.ofReal 10 < distanceToBoundary W g a.val)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 950000 * Δ)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q a < C * S.rho a) :
    ENNReal.ofReal 4 < distanceToBoundary W g q.val := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  set K₀ := 2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹ with hK₀
  have hρa := S.rho_pos a
  have hK₀C : C ≤ K₀ := by
    have : 0 ≤ (β 1)⁻¹ := inv_nonneg.mpr hβ1.le
    have : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
    nlinarith
  have hball := (S.transport_spec.2.1 a ha).1
  have hR := ofReal_le_distanceToBoundary_of_image_ball_BAUGC (g := g) S.completion.metric hball
  have hadd := distanceToBoundary_le_add W g a.val q.val
  have hdg : riemannianEDistOf g a.val q.val < ENNReal.ofReal (C * S.rho a) := by
    refine lt_of_le_of_lt (S.riemannianEDistOf_le_ofReal_dist_BAUGC a q) ?_
    rw [dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hq)).mpr hq
  by_contra h4
  push Not at h4
  have hlt : distanceToBoundary W g a.val < ENNReal.ofReal (4 + C * S.rho a) := by
    calc distanceToBoundary W g a.val ≤ distanceToBoundary W g q.val +
          riemannianEDistOf g a.val q.val := hadd
      _ < ENNReal.ofReal 4 + ENNReal.ofReal (C * S.rho a) :=
          ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h4) h4 hdg
      _ = ENNReal.ofReal (4 + C * S.rho a) := (ENNReal.ofReal_add (by norm_num)
          (by positivity)).symm
  have h1 : (10 : ℝ) < 4 + C * S.rho a :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp (ha.trans hlt)
  have h2 : 4 * K₀ * S.rho a < 4 + C * S.rho a :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp (lt_of_le_of_lt hR hlt)
  have h3 : C * S.rho a ≤ K₀ * S.rho a := mul_le_mul_of_nonneg_right hK₀C hρa.le
  nlinarith

/-- **Unlisted components vanish near the reference domain**: `i ∉ J_∂(a)` and
`d_ĝ(q, a) < C_aρ(a)` give `q ∉ tsupport F_i`. -/
theorem notMem_tsupport_block_of_notMem_BAUGC {st : Fin 3} {a q : W.pieceInterior ⊤}
    {i : Fin S.packet.cusp.count} (hi : i ∉ S.boundaryList_BIF st a)
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a) :
    q.val ∉ tsupport (S.packet.toBoundaryCollarPacket.block i) := by
  intro hmem
  refine hi (BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mpr ⟨q.val, hmem, ?_⟩)
  let _ := inducedMetricSpace S.completion.metric
  refine lt_of_le_of_lt (S.riemannianEDistOf_le_ofReal_dist_BAUGC a q) ?_
  rw [dist_comm]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hq)).mpr hq

/-- **BCG01 at a stage reference domain** (nonproduct branch; `0 ≤ Λ` through
`exists_pos_scale_lipschitz_BAUGC`): `J_∂(a)` is a subsingleton, and a member `i` has `ρ(a) ≤ 1` and
the whole `ĝ`-domain `B(a, C_aρ(a))` in the collar band `e_i{19 < z < 91}`. -/
theorem boundaryList_facts_BAUGC (hsep : S.SeparatedCollarZero_BIF) (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hβ1 : 0 < β 1) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) (st : Fin 3) (a : W.pieceInterior ⊤) :
    (S.boundaryList_BIF st a).Subsingleton ∧
      ∀ i ∈ S.boundaryList_BIF st a, S.rho a ≤ 1 ∧
        ∀ q : W.pieceInterior ⊤, (letI := inducedMetricSpace S.completion.metric;
          dist q a < stageDomain_BIF Δ st * S.rho a) →
          ∃ q' ∈ cuspDomain, (S.packet.toBoundaryCollarPacket.cusp.collar i).toFun q' = q.val ∧
            2 < q'.2.val 0 ∧ q'.2.val 0 < 98 := by
  obtain ⟨Λ', hΛ'0, hΛ'Δ, -, hlip'⟩ := S.exists_pos_scale_lipschitz_BAUGC hΛ hΔ hΛΔ
  have hε : cuspTolerance_BCUSP1 (β 1) βd εN ≤ 1 / 4 :=
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _).trans (by norm_num)
  have hΔ0 : 0 < Δ := by linarith
  have hC : stageDomain_BIF Δ st ≤ 95 / 100 * (1000000 * Δ) :=
    (stageDomain_BIF_bounds_BAUGC hΔ st).2.trans (by linarith)
  have hdisj : ∀ i j : Fin S.packet.toBoundaryCollarPacket.cusp.count, i ≠ j →
      Disjoint ((S.packet.toBoundaryCollarPacket.cusp.collar i).toFun ''
          {q : CuspHalfSpace | q.2.val 0 < 92})
        ((S.packet.toBoundaryCollarPacket.cusp.collar j).toFun ''
          {q : CuspHalfSpace | q.2.val 0 < 92}) := fun i j hij => (hsep.1 i j hij).1
  refine ⟨S.packet.toBoundaryCollarPacket.boundarySupportList_subsingleton_BCG8b hε hdisj
      S.rho_pos hΛ'0 hΔ0 hβ1 hlip' S.scale_spec.2.2.2.1 hΛ'Δ hreq hC a.val, fun i hi => ?_⟩
  obtain ⟨hρp, hband, -⟩ := S.packet.toBoundaryCollarPacket.bcg03_mem_boundarySupportList_BCG8b
    hε S.rho_pos hΛ'0 hΔ0 hβ1 hlip' S.scale_spec.2.2.2.1 hΛ'Δ hreq hC
    (Empty.elim : Empty → W.Carrier) (Empty.elim : Empty → ℝ) (fun k => k.elim) hi
  refine ⟨?_, fun q hq => ?_⟩
  · have h1 : β 1 ^ 3 < 1 := by nlinarith [pow_pos hβ1 3]
    linarith
  · have hqg : q.val ∈ riemannianBallOf g a.val (stageDomain_BIF Δ st * S.rho a) := by
      let _ := inducedMetricSpace S.completion.metric
      change riemannianEDistOf g a.val q.val < ENNReal.ofReal (stageDomain_BIF Δ st * S.rho a)
      refine lt_of_le_of_lt (S.riemannianEDistOf_le_ofReal_dist_BAUGC a q) ?_
      rw [dist_comm]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hq)).mpr hq
    obtain ⟨q', hq', hqx, h19, h91, -, -⟩ := hband q.val hqg
    exact ⟨q', hq', hqx, by linarith, by linarith⟩

/-- An unlisted component has zero derivative on the reference domain. -/
theorem mvfderiv_block_eq_zero_of_notMem_BAUGC {st : Fin 3} {a q : W.pieceInterior ⊤}
    {i : Fin S.packet.cusp.count} (hi : i ∉ S.boundaryList_BIF st a)
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a) (v : TangentSpace W.model q.val) :
    mvfderiv W.model (S.packet.toBoundaryCollarPacket.block i) q.val v = 0 := by
  have hev : S.packet.toBoundaryCollarPacket.block i =ᶠ[𝓝 q.val] fun _ => (0 : ℝ × ℝ) :=
    (notMem_tsupport_iff_eventuallyEq).mp (S.notMem_tsupport_block_of_notMem_BAUGC hi hq)
  rw [mvfderiv_apply_LC, hev.mfderiv_eq, mfderiv_const]
  rfl

end BoundarySupply

section NormalParts

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM}

omit [ConnectedSpace W.Carrier] in
/-- Every tangent vector of `W` at an interior point is `dval` of a tangent vector of `W°`. -/
theorem exists_mfderiv_val_eq_BAUGC (q : W.pieceInterior ⊤) (v : TangentSpace W.model q.val) :
    ∃ w : TangentSpace 𝓘(ℝ, E3) q, mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w = v :=
  ((isLocalDiffeomorph_pieceInterior_val W ⊤).mfderivToContinuousLinearEquiv (by simp) q).surjective v

/-- On `{D ≥ 4}`: `g(dval w, dval w) = ĝ(w, w)` for the stored completion. -/
theorem inner_mfderiv_val_completion_BAUGC (q : W.pieceInterior ⊤)
    (hq : ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val) (w : TangentSpace 𝓘(ℝ, E3) q) :
    g.inner q.val (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w) = S.completion.metric.inner q w w :=
  inner_mfderiv_val_BCG7 W g S.completion.metric (fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)) q hq w w

/-- `F_∂ ∘ val` is differentiable on `W°` (BAUG-A's smoothness). -/
theorem mdifferentiableAt_boundaryOriginalMap_val_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (q : W.pieceInterior ⊤) :
    MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (fun y : W.pieceInterior ⊤ => S.boundaryOriginalMap y.val) q :=
  ((S.boundaryOriginalMap_smooth hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he q.val).mdifferentiableAt
    (by simp)).comp q (mdifferentiableAt_val_BCG7 W q)

/-- `D(F_∂ ∘ val)(w) = DF_∂(dval w)`. -/
theorem mvfderiv_boundaryOriginalMap_val_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (q : W.pieceInterior ⊤)
    (w : TangentSpace 𝓘(ℝ, E3) q) :
    mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => S.boundaryOriginalMap y.val) q w =
      mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w) :=
  mvfderiv_comp_val_BCG7 W S.boundaryOriginalMap q
    ((S.boundaryOriginalMap_smooth hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he q.val).mdifferentiableAt
      (by simp)) w

/-- **The interior part of the stage-projected derivative** through `val`:
`pr_int π_j DF_∂(dval w) = D(π_{Q_j} ∘ F_int)(w)` on `W°`. -/
theorem augIntProj_stageProj_mvfderiv_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (q : W.pieceInterior ⊤) (w : TangentSpace 𝓘(ℝ, E3) q) :
    augIntProjCLM_BAUGC (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w))) =
      mvfderiv 𝓘(ℝ, E3)
        (fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) q w := by
  rw [← mvfderiv_boundaryOriginalMap_val_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he q w]
  have h := augIntProj_blockRestrict_mvfderiv_BAUGC
    (mdifferentiableAt_boundaryOriginalMap_val_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he q)
    (Φ.stageTags st) w
  have hfun : (fun y : W.pieceInterior ⊤ => blockRestrict (Φ.stageTags st)
      (augIntProjCLM_BAUGC (S.boundaryOriginalMap y.val))) =
      fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y) :=
    funext fun y => by
      rw [augIntProjCLM_eq_BAUGC, S.boundaryOriginalMap_interior_projection,
        S.interiorMapW_val_BAUGA]
  exact h.trans (congrArg (fun f => mvfderiv 𝓘(ℝ, E3) f q w) hfun)

/-- **Interior part of the normal estimate at one preimage**: (TG derivative) at `q` with error
`e'` against `T` gives `‖pr_int π_j DF_∂(dval w) − ρ T‖ ≤ e'|w|_ĝ`. -/
theorem normal_interior_part_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) (q : W.pieceInterior ⊤)
    (w : TangentSpace 𝓘(ℝ, E3) q) {ρa e' : ℝ} (hρa : 0 < ρa)
    (T : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
    (hTG : ‖ρa⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) q w - T‖ ≤
      e' * Real.sqrt (ρa⁻¹ ^ 2 * S.completion.metric.inner q w w)) :
    ‖augIntProjCLM_BAUGC (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w))) - ρa • T‖ ≤
      e' * Real.sqrt (S.completion.metric.inner q w w) := by
  rw [augIntProj_stageProj_mvfderiv_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st q w]
  have hsq : Real.sqrt (ρa⁻¹ ^ 2 * S.completion.metric.inner q w w) =
      ρa⁻¹ * Real.sqrt (S.completion.metric.inner q w w) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hTG' := hTG.trans_eq (congrArg (fun t => e' * t) hsq)
  have hsplit : ∀ D : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²),
      D - ρa • T = ρa • (ρa⁻¹ • D - T) := fun D => by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hρa.ne', one_smul]
  rw [hsplit, norm_smul, Real.norm_of_nonneg hρa.le]
  calc ρa * ‖ρa⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) q w - T‖
      ≤ ρa * (e' * (ρa⁻¹ * Real.sqrt (S.completion.metric.inner q w w))) :=
        mul_le_mul_of_nonneg_left hTG' hρa.le
    _ = e' * Real.sqrt (S.completion.metric.inner q w w) := by field_simp

/-- A boundary slot of the stage-projected derivative of `F_∂` is the plane encoding of the
derivative of the collar block. -/
theorem stageProj_mvfderiv_inr_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    (p : W.Carrier) (v : TangentSpace W.model p) (i : Fin S.packet.cusp.count) :
    Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap p v) (Sum.inr i) =
      planeBlockEmbed_BAUGA (mvfderiv W.model (S.packet.toBoundaryCollarPacket.block i) p v) := by
  rw [BoundaryInteriorSlots_BIF.stageProj_inr_BGR]
  exact mvfderiv_boundaryAugmentedMap_inr_BAUGC S.interiorMapW_BAUGA
    S.packet.toBoundaryCollarPacket.block
    ((S.boundaryOriginalMap_smooth hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he p).mdifferentiableAt (by simp)) i
    ((S.packet.toBoundaryCollarPacket.contMDiff_block i p).mdifferentiableAt (by simp)) v

/-- `D(R⁻¹F_b ∘ val)(w) = R⁻¹ DF_b(dval w)`. -/
theorem mvfderiv_smul_block_val_BAUGC (i : Fin S.packet.cusp.count) (R : ℝ)
    (q : W.pieceInterior ⊤) (w : TangentSpace 𝓘(ℝ, E3) q) :
    mvfderiv 𝓘(ℝ, E3) (fun y : W.pieceInterior ⊤ => R • S.packet.toBoundaryCollarPacket.block i y)
        q w =
      R • mvfderiv W.model (S.packet.toBoundaryCollarPacket.block i) q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w) := by
  have hB : MDifferentiableAt W.model 𝓘(ℝ, ℝ × ℝ) (S.packet.toBoundaryCollarPacket.block i)
      q.val := (S.packet.toBoundaryCollarPacket.contMDiff_block i q.val).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt W.model 𝓘(ℝ, ℝ × ℝ)
      (fun p => (R • ContinuousLinearMap.id ℝ (ℝ × ℝ)) (S.packet.toBoundaryCollarPacket.block i p))
      q.val :=
    (((R • ContinuousLinearMap.id ℝ (ℝ × ℝ)).contMDiff (n := ∞)).contMDiffAt.mdifferentiableAt
      (by simp)).comp q.val hB
  have h1 := mvfderiv_comp_val_BCG7 W
    (fun p => (R • ContinuousLinearMap.id ℝ (ℝ × ℝ)) (S.packet.toBoundaryCollarPacket.block i p))
    q hf w
  have h2 := mvfderiv_clm_comp hB (R • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)
  simp only [smul_apply, ContinuousLinearMap.id_apply] at h1 h2
  exact h1.trans h2

/-- **The listed slot of the normal estimate** (BCG-8b's differential error at one preimage `q`
in the band, `ρ(a) ≤ 1`, (BA) on `D_a`, `|Dη_a| ≤ 2|·|`): `‖(π_j DF_∂(dval w))_b − ρ(a) slot(DΦ^∂_b(Dη_a w))‖
≤ 6P_*θ|w|_ĝ`. -/
theorem normal_listed_slot_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → E)
    (Ar : E →L[ℝ] ℝ) (hA : ‖Ar‖ ≤ 1) (a q : W.pieceInterior ⊤) (i : Fin S.packet.cusp.count)
    (hρ1 : S.rho a ≤ 1)
    (hband : ∃ q' ∈ cuspDomain, (S.packet.toBoundaryCollarPacket.cusp.collar i).toFun q' = q.val ∧
      2 < q'.2.val 0 ∧ q'.2.val 0 < 98)
    (hval : |(S.packet.height i q - S.packet.height i a) / S.rho a - Ar (eta q - eta a)| < θ)
    (hdiff : ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3)
          (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
          q u - Ar (mvfderiv 𝓘(ℝ, E3) eta q u)| ≤
        θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
          S.completion.metric).inner q u u))
    (hη : ∀ u : TangentSpace 𝓘(ℝ, E3) q, ‖mvfderiv 𝓘(ℝ, E3) eta q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u))
    (w : TangentSpace 𝓘(ℝ, E3) q) :
    ‖Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)) (Sum.inr i) -
      S.rho a • planeBlockEmbed_BAUGA (fderiv ℝ
        (boundaryModel_BCG8b (S.packet.height i a) (S.rho a) Ar (eta a)) (eta q)
        (mvfderiv 𝓘(ℝ, E3) eta q w))‖ ≤
      6 * bmConst_BAUGC * θ * Real.sqrt (S.completion.metric.inner q w w) := by
  have hρa := S.rho_pos a
  have err := (bcg03_model_errors_row_BCG8b W g S.packet.toBoundaryCollarPacket i
    S.completion.metric S.rho S.rho_pos norm_fderiv_boundaryBlock_le_bmConst_BAUGC
    norm_fderiv_fderiv_boundaryBlock_le_bmConst_BAUGC a q hρ1 hband eta hA hval hdiff hη).2 w
  rw [mvfderiv_smul_block_val_BAUGC (S := S) i (S.rho a)⁻¹ q w] at err
  have hsc : Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
      S.completion.metric).inner q w w) =
      (S.rho a)⁻¹ * Real.sqrt (S.completion.metric.inner q w w) := by
    rw [scaleMetric_inner, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsc] at err
  rw [stageProj_mvfderiv_inr_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st, ← map_smul, ← map_sub]
  refine (norm_planeBlockEmbed_le_BAUGC _).trans ?_
  have hsplit : ∀ D X : ℝ × ℝ, D - S.rho a • X = S.rho a • ((S.rho a)⁻¹ • D - X) := fun D X => by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hρa.ne', one_smul]
  rw [hsplit, norm_smul, Real.norm_of_nonneg hρa.le]
  have h3 : S.rho a * ‖(S.rho a)⁻¹ • mvfderiv W.model (S.packet.toBoundaryCollarPacket.block i)
        q.val (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w) -
      fderiv ℝ (boundaryModel_BCG8b (S.packet.height i a) (S.rho a) Ar (eta a)) (eta q)
        (mvfderiv 𝓘(ℝ, E3) eta q w)‖ ≤
      S.rho a * (3 * bmConst_BAUGC * θ * ((S.rho a)⁻¹ *
        Real.sqrt (S.completion.metric.inner q w w))) :=
    mul_le_mul_of_nonneg_left err hρa.le
  have h4 : S.rho a * (3 * bmConst_BAUGC * θ * ((S.rho a)⁻¹ *
      Real.sqrt (S.completion.metric.inner q w w))) =
      3 * bmConst_BAUGC * θ * Real.sqrt (S.completion.metric.inner q w w) := by
    field_simp
  linarith

/-- An unlisted slot of the normal estimate vanishes exactly. -/
theorem normal_unlisted_slot_BAUGC (hΛ : 0 ≤ Λ) (hΔ0 : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Db : Fin S.packet.cusp.count → E →L[ℝ] ℝ × ℝ)
    (a q : W.pieceInterior ⊤)
    (hqa : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a)
    (w : TangentSpace 𝓘(ℝ, E3) q) (u : E) {i : Fin S.packet.cusp.count}
    (hi : i ∉ S.boundaryList_BIF st a) :
    Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)) (Sum.inr i) -
      S.rho a • planeBlockEmbed_BAUGA
        (augmentedBlockDeriv_BAUGC (S.boundaryList_BIF st a) Db i u) = 0 := by
  rw [stageProj_mvfderiv_inr_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st,
    S.mvfderiv_block_eq_zero_of_notMem_BAUGC hi hqa, augmentedBlockDeriv_BAUGC, ite_eq_right hi]
  simp

/-- **Every boundary slot of the normal estimate** at a preimage `q ∈ D_a` with `η_a q = z`:
error `≤ 6P_*θ|w|_ĝ`. -/
theorem normal_slot_BAUGC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hsep : S.SeparatedCollarZero_BIF) (hθ : 0 ≤ θ) (Φ : BoundaryInteriorSlots_BIF S)
    (st : Fin 3) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
    (hrow : ∀ a i, ‖row a i‖ ≤ 1) (a q : W.pieceInterior ⊤) (z : E) (hηe : eta a q = z)
    (hqa : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a)
    (hBAv : ∀ i ∈ S.boundaryList_BIF st a,
      |(S.packet.height i q - S.packet.height i a) / S.rho a - row a i (eta a q - eta a a)| < θ)
    (hBAd : ∀ i ∈ S.boundaryList_BIF st a, ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3)
          (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
          q u - row a i (mvfderiv 𝓘(ℝ, E3) (eta a) q u)| ≤
        θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
          S.completion.metric).inner q u u))
    (hη : ∀ u : TangentSpace 𝓘(ℝ, E3) q, ‖mvfderiv 𝓘(ℝ, E3) (eta a) q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u))
    (w : TangentSpace 𝓘(ℝ, E3) q) (i : Fin S.packet.cusp.count) :
    ‖Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)) (Sum.inr i) -
      S.rho a • planeBlockEmbed_BAUGA (augmentedBlockDeriv_BAUGC (S.boundaryList_BIF st a)
        (fun i => fderiv ℝ (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a)
          (eta a a) i) z) i (mvfderiv 𝓘(ℝ, E3) (eta a) q w))‖ ≤
      6 * bmConst_BAUGC * θ * Real.sqrt (S.completion.metric.inner q w w) := by
  have hΔ0 : 0 < Δ := by linarith
  by_cases hi : i ∈ S.boundaryList_BIF st a
  · have hfacts := (S.boundaryList_facts_BAUGC hsep hΛ hΔ1 hβ1 hΛΔ hreq st a).2 i hi
    have h := normal_listed_slot_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st (eta a) (row a i)
      (hrow a i) a q i hfacts.1 (hfacts.2 q hqa) (hBAv i hi) (hBAd i hi) hη w
    rw [hηe] at h
    rw [augmentedBlockDeriv_BAUGC, ite_eq_left hi]
    exact h
  · rw [normal_unlisted_slot_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st _ a q hqa w _ hi, norm_zero]
    have := one_le_bmConst_BAUGC
    positivity

/-- **The normal estimate at one preimage** (abstract plane `K` containing
`ρ(a) D(K^∂Φ^∂)(z)(Dη_a w)`): `‖Kᗮ π_j DF_∂(dval w)‖ ≤ (e' + 6P_*θ)|w|_ĝ`. -/
theorem normal_at_preimage_BAUGC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) (hsep : S.SeparatedCollarZero_BIF) (hθ : 0 ≤ θ)
    (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
    (hrow : ∀ a i, ‖row a i‖ ≤ 1) (Tm : E →L[ℝ] BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
    (K : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    [K.HasOrthogonalProjection] (a q : W.pieceInterior ⊤) (z : E) (hηe : eta a q = z)
    (hK : ∀ (c : ℝ) (u : E), c • augDeriv_BAUGC Tm (augmentedBlockDeriv_BAUGC (S.boundaryList_BIF st a)
        fun i => fderiv ℝ (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a)
          (eta a a) i) z) u ∈ K)
    (hqa : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a)
    (hBAv : ∀ i ∈ S.boundaryList_BIF st a,
      |(S.packet.height i q - S.packet.height i a) / S.rho a - row a i (eta a q - eta a a)| < θ)
    (hBAd : ∀ i ∈ S.boundaryList_BIF st a, ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3)
          (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
          q u - row a i (mvfderiv 𝓘(ℝ, E3) (eta a) q u)| ≤
        θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
          S.completion.metric).inner q u u))
    (hη : ∀ u : TangentSpace 𝓘(ℝ, E3) q, ‖mvfderiv 𝓘(ℝ, E3) (eta a) q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u))
    {e' : ℝ} (w : TangentSpace 𝓘(ℝ, E3) q)
    (hTG : ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) q w -
        Tm (mvfderiv 𝓘(ℝ, E3) (eta a) q w)‖ ≤
      e' * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner q w w)) :
    ‖Kᗮ.starProjection (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)))‖ ≤
      e' * Real.sqrt (S.completion.metric.inner q w w) +
        6 * bmConst_BAUGC * θ * Real.sqrt (S.completion.metric.inner q w w) := by
  have hΔ0 : 0 < Δ := by linarith
  refine norm_starProjection_le_of_augDeriv_BAUGC Tm _ K _ (S.rho a)
    (mvfderiv 𝓘(ℝ, E3) (eta a) q w) (hK _ _)
    (by have := one_le_bmConst_BAUGC; positivity)
    (normal_interior_part_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st q w (S.rho_pos a) _ hTG)
    (normal_slot_BAUGC hΛ hΔ1 hμ hτ hΔΛ hV hβ1 hb he hΛΔ hreq hsep hθ Φ st eta row hrow a q z hηe
      hqa hBAv hBAd hη w) fun i₁ i₂ h₁ h₂ => ?_
  have hsub := (S.boundaryList_facts_BAUGC hsep hΛ hΔ1 hβ1 hΛΔ hreq st a).1
  have hm : ∀ i, Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)) (Sum.inr i) -
      S.rho a • planeBlockEmbed_BAUGA (augmentedBlockDeriv_BAUGC (S.boundaryList_BIF st a)
        (fun i => fderiv ℝ (bmBlocks_BAUGC (fun i => S.packet.height i a) (S.rho a) (row a)
          (eta a a) i) z) i (mvfderiv 𝓘(ℝ, E3) (eta a) q w)) ≠ 0 →
      i ∈ S.boundaryList_BIF st a := fun i h => by
    by_contra hi
    exact h (normal_unlisted_slot_BAUGC hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb he Φ st _ a q hqa w _ hi)
  exact hsub (hm i₁ h₁) (hm i₂ h₂)

/-- **The normal estimate at one preimage, in the original metric** (abstract plane `K`): with
`D(q) ≥ 4` (`ĝ = g°` at `q`) and `e' + 6P_*θ ≤ e`, `‖Kᗮ π_j DF_∂(v)‖ ≤ e|v|_g` for every
`v ∈ T_qW`. -/
theorem normal_at_preimage_original_BAUGC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) (hsep : S.SeparatedCollarZero_BIF) (hθ : 0 ≤ θ)
    (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
    (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
    (hrow : ∀ a i, ‖row a i‖ ≤ 1) (Tm : E →L[ℝ] BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
    (K : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    [K.HasOrthogonalProjection] (a q : W.pieceInterior ⊤) (z : E) (hηe : eta a q = z)
    (hK : ∀ (c : ℝ) (u : E), c • augDeriv_BAUGC Tm (augmentedBlockDeriv_BAUGC
        (S.boundaryList_BIF st a) fun i => fderiv ℝ (bmBlocks_BAUGC (fun i => S.packet.height i a)
          (S.rho a) (row a) (eta a a) i) z) u ∈ K)
    (hqa : letI := inducedMetricSpace S.completion.metric;
      dist q a < stageDomain_BIF Δ st * S.rho a)
    (h4 : ENNReal.ofReal 4 ≤ distanceToBoundary W g q.val)
    (hBAv : ∀ i ∈ S.boundaryList_BIF st a,
      |(S.packet.height i q - S.packet.height i a) / S.rho a - row a i (eta a q - eta a a)| < θ)
    (hBAd : ∀ i ∈ S.boundaryList_BIF st a, ∃ θ' < θ, ∀ u : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3)
          (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
          q u - row a i (mvfderiv 𝓘(ℝ, E3) (eta a) q u)| ≤
        θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
          S.completion.metric).inner q u u))
    (hη : ∀ u : TangentSpace 𝓘(ℝ, E3) q, ‖mvfderiv 𝓘(ℝ, E3) (eta a) q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u))
    {e' eg : ℝ} (heg : e' + 6 * bmConst_BAUGC * θ ≤ eg)
    (hTG : ∀ w : TangentSpace 𝓘(ℝ, E3) q, ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) q w -
        Tm (mvfderiv 𝓘(ℝ, E3) (eta a) q w)‖ ≤
      e' * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner q w w))
    (v : TangentSpace W.model q.val) :
    ‖Kᗮ.starProjection (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤
      eg * Real.sqrt (g.inner q.val v v) := by
  refine (exists_mfderiv_val_eq_BAUGC q v).elim fun w hw => ?_
  have h1 := normal_at_preimage_BAUGC hΛ hΔ1 hμ hτ hΔΛ hV hβ1 hb he hΛΔ hreq hsep hθ Φ st eta row
    hrow Tm K a q z hηe hK hqa hBAv hBAd hη w (hTG w)
  have h2 : ‖Kᗮ.starProjection (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ =
      ‖Kᗮ.starProjection (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val
        (mfderiv 𝓘(ℝ, E3) W.model Subtype.val q w)))‖ :=
    congrArg (fun v' => ‖Kᗮ.starProjection (Φ.stageProj st
      (mvfderiv W.model S.boundaryOriginalMap q.val v'))‖) hw.symm
  have h3 : g.inner q.val v v = S.completion.metric.inner q w w :=
    (congrArg (fun v' => g.inner q.val v' v') hw.symm).trans
      (inner_mfderiv_val_completion_BAUGC (S := S) q h4 w)
  have h5 : e' * Real.sqrt (S.completion.metric.inner q w w) +
      6 * bmConst_BAUGC * θ * Real.sqrt (S.completion.metric.inner q w w) ≤
      eg * Real.sqrt (g.inner q.val v v) := by
    rw [h3]
    have := Real.sqrt_nonneg (S.completion.metric.inner q w w)
    nlinarith
  exact h2.trans_le (h1.trans h5)

end NormalParts

section Normal

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S) (st : Fin 3) {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E)
  (row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ)
  (Ψ : W.pieceInterior ⊤ → E → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
  (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
    BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
  (rpre : Φ.stageCloudEnlarged st → W.pieceInterior ⊤)
  (pre ref : Φ.stageCloud st → W.pieceInterior ⊤)
  (href : ∀ x, ref x ∈ S.stageCentres_BIF st)
  (hrpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (rpre x).val) = x.1)
  (hpre : ∀ x, Φ.stageProj st (S.boundaryOriginalMap (pre x).val) = x.1 ∧
    (letI := inducedMetricSpace S.completion.metric
     dist (pre x) (ref x) < stageDomain_BIF Δ st * S.rho (ref x)))

/-- Every vector `c • D(K^∂Φ^∂)(η_a(pre x))(u)` lies in the plane of the port table at `x`. -/
theorem portTable_mem_plane_BAUGC
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hx : x ∈ Φ.stageCloud st)
    (c : ℝ) (u : E) :
    c • augDeriv_BAUGC (fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
        (eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)))
      (augmentedBlockDeriv_BAUGC (S.boundaryList_BIF st (ref ⟨x, hx⟩)) fun i =>
        fderiv ℝ (bmBlocks_BAUGC (fun i => S.packet.height i (ref ⟨x, hx⟩))
          (S.rho (ref ⟨x, hx⟩)) (row (ref ⟨x, hx⟩)) (eta (ref ⟨x, hx⟩) (ref ⟨x, hx⟩)) i)
          (eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩))) u ∈
      (portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x := by
  rw [portTable_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hx]
  simp only [portModel_BAUGC]
  rw [fderiv_augmented_pruned_BAUGC (Kint (ref ⟨x, hx⟩))
    ((hM _ (href ⟨x, hx⟩)).differentiable (by norm_num) _)
    (portModel_blocks_differentiableAt_BAUGC st eta row _ _)]
  exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

/-- **Field `normal` of the port table** (TCP06 / EGP07 / SGP05 normal estimate, boundary
version): from (PRE) (every preimage `q` of a cloud point lies in `D_a` with `η_a q = η_a(pre x)`),
(TG derivative) at `q` with error `e'`, `|Dη_a| ≤ 2|·|_{ρ(a)⁻²ĝ}` at `q`, BCG02's (BA) on `D_a` and
the stage centres in `{D > 10}`: at every preimage the component of `π_j DF_∂(v)` normal to `L_x` is
at most `(e' + 6P_*θ)|v|_g ≤ e|v|_g` (`ĝ = g°` on `D_a ⊆ {D > 4}`; `J_∂(a)` a subsingleton; the
listed slot by BCG-8b's differential error, unlisted slots vanish near `D_a`). -/
theorem portTable_normal_BAUGC (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1)
    (hsep : S.SeparatedCollarZero_BIF) {eg eg' : ℝ} (hθ : 0 ≤ θ)
    (heg : eg' + 6 * bmConst_BAUGC * θ ≤ eg)
    (hcent : ∀ a ∈ S.stageCentres_BIF st, ENNReal.ofReal 10 < distanceToBoundary W g a.val)
    (hrow : ∀ a i, ‖row a i‖ ≤ 1)
    (hBAv : ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a,
      letI := inducedMetricSpace S.completion.metric
      ∀ y : W.pieceInterior ⊤, dist y a < stageDomain_BIF Δ st * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a -
          row a i (eta a y - eta a a)| < θ)
    (hBAd : ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a,
      letI := inducedMetricSpace S.completion.metric
      ∀ x : W.pieceInterior ⊤, dist x a < stageDomain_BIF Δ st * S.rho a → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
              x u - row a i (mvfderiv 𝓘(ℝ, E3) (eta a) x u)| ≤
            θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (S.rho_pos a)) 2) S.completion.metric).inner x u u))
    (hM : ∀ a ∈ S.stageCentres_BIF st, ContDiff ℝ 2 (Kint a ∘ Ψ a))
    (hPREq : ∀ x (hx : x ∈ Φ.stageCloud st) (q : W.pieceInterior ⊤),
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
        (letI := inducedMetricSpace S.completion.metric
         dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ st * S.rho (ref ⟨x, hx⟩)) ∧
        eta (ref ⟨x, hx⟩) q = eta (ref ⟨x, hx⟩) (pre ⟨x, hx⟩))
    (hTGq : ∀ x (hx : x ∈ Φ.stageCloud st) (q : W.pieceInterior ⊤),
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x → ∀ w : TangentSpace 𝓘(ℝ, E3) q,
        ‖(S.rho (ref ⟨x, hx⟩))⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (fun y => blockRestrict (Φ.stageTags st) (S.interiorMapOn_BAUGA y)) q w -
          fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩)) (eta (ref ⟨x, hx⟩) q)
            (mvfderiv 𝓘(ℝ, E3) (eta (ref ⟨x, hx⟩)) q w)‖ ≤
          eg' * Real.sqrt ((S.rho (ref ⟨x, hx⟩))⁻¹ ^ 2 * S.completion.metric.inner q w w))
    (hηq : ∀ x (hx : x ∈ Φ.stageCloud st) (q : W.pieceInterior ⊤),
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x → ∀ u : TangentSpace 𝓘(ℝ, E3) q,
        ‖mvfderiv 𝓘(ℝ, E3) (eta (ref ⟨x, hx⟩)) q u‖ ≤ 2 * Real.sqrt ((scaleMetric
          ((S.rho (ref ⟨x, hx⟩))⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos (ref ⟨x, hx⟩))) 2)
            S.completion.metric).inner q u u)) :
    ∀ x ∈ Φ.stageCloud st, ∀ q : W.pieceInterior ⊤,
      Φ.stageProj st (S.boundaryOriginalMap q.val) = x →
      ∀ v : TangentSpace W.model q.val,
        ‖((portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x)ᗮ.starProjection
            (Φ.stageProj st (mvfderiv W.model S.boundaryOriginalMap q.val v))‖ ≤
          eg * Real.sqrt (g.inner q.val v v) := by
  intro x hx q hq v
  have ha : ref ⟨x, hx⟩ ∈ S.stageCentres_BIF st := href ⟨x, hx⟩
  have hPq := hPREq x hx q hq
  have hΔ0 : 0 < Δ := by linarith
  have hC0 := (stageDomain_BIF_bounds_BAUGC hΔ1 st).1
  have hC := (stageDomain_BIF_bounds_BAUGC hΔ1 st).2
  have h4 := S.four_lt_distanceToBoundary_of_dist_lt_BAUGC hV hβ1 hb hΔ0.le (hcent _ ha) hC0 hC
    hPq.1
  have hTG := fun w => (hTGq x hx q hq w).trans_eq' (by rw [hPq.2])
  exact normal_at_preimage_original_BAUGC hΛ hΔ1 hμ hτ hΔΛ hV hβ1 hb he hΛΔ hreq hsep hθ Φ st eta
    row hrow _ ((portTable_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre).planes.plane x)
    (ref ⟨x, hx⟩) q _ hPq.2
    (portTable_mem_plane_BAUGC Φ st eta row Ψ Kint rpre pre ref href hrpre hpre hM hx)
    hPq.1 h4.le (fun i hi => hBAv _ ha i hi q hPq.1) (fun i hi => hBAd _ ha i hi q hPq.1)
    (hηq x hx q hq) heg hTG v

end Normal

/-! ### Consumer: the supply-side inputs at the three stages -/

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **The supply-side inputs of `portTable_normal_BAUGC` at the circle stage**: circle centres in
`{D > 10}`, stored rows of norm `≤ 1`, BCG02's (BA) value and differential clauses on
`D_a = B(a, 10ρ(a))` for the listed components. -/
theorem circle_normal_inputs_BAUGC :
    (∀ a ∈ S.stageCentres_BIF 0, ENNReal.ofReal 10 < distanceToBoundary W g a.val) ∧
    (∀ a i, ‖S.circleRow_BIF a i‖ ≤ 1) ∧
    (∀ a ∈ S.stageCentres_BIF 0, ∀ i ∈ S.boundaryList_BIF 0 a,
      letI := inducedMetricSpace S.completion.metric
      ∀ y : W.pieceInterior ⊤, dist y a < stageDomain_BIF Δ 0 * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a -
          S.circleRow_BIF a i (S.circleEta_BIF a y - S.circleEta_BIF a a)| < θ) ∧
    (∀ a ∈ S.stageCentres_BIF 0, ∀ i ∈ S.boundaryList_BIF 0 a,
      letI := inducedMetricSpace S.completion.metric
      ∀ x : W.pieceInterior ⊤, dist x a < stageDomain_BIF Δ 0 * S.rho a → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
              x u - S.circleRow_BIF a i (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a) x u)| ≤
            θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (S.rho_pos a)) 2) S.completion.metric).inner x u u)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  exact ⟨fun a ha => (S.family.circle.centres_subset ha).1, S.norm_circleRow_BIF_le_BAUGC,
    fun a ha i hi => S.circleRow_BIF_value_BAUGC ha hi,
    fun a ha i hi => S.circleRow_BIF_deriv_BAUGC ha hi⟩

/-- **The supply-side inputs at the revised-edge stage** (`D_a = B(a, 20Δρ(a))`; `edgeB` centres in
`{D > 20}`). -/
theorem edge_normal_inputs_BAUGC :
    (∀ a ∈ S.stageCentres_BIF 1, ENNReal.ofReal 10 < distanceToBoundary W g a.val) ∧
    (∀ a i, ‖S.edgeRow_BIF a i‖ ≤ 1) ∧
    (∀ a ∈ S.stageCentres_BIF 1, ∀ i ∈ S.boundaryList_BIF 1 a,
      letI := inducedMetricSpace S.completion.metric
      ∀ y : W.pieceInterior ⊤, dist y a < stageDomain_BIF Δ 1 * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a -
          S.edgeRow_BIF a i (S.edgeEta_BIF a y - S.edgeEta_BIF a a)| < θ) ∧
    (∀ a ∈ S.stageCentres_BIF 1, ∀ i ∈ S.boundaryList_BIF 1 a,
      letI := inducedMetricSpace S.completion.metric
      ∀ x : W.pieceInterior ⊤, dist x a < stageDomain_BIF Δ 1 * S.rho a → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
              x u - S.edgeRow_BIF a i (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) x u)| ≤
            θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (S.rho_pos a)) 2) S.completion.metric).inner x u u)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  refine ⟨fun a ha => lt_trans (ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num))
      (S.family.edgeB.centres_subset ha), S.norm_edgeRow_BIF_le_BAUGC,
    fun a ha i hi => (S.edgeRow_BIF_value_deriv_BAUGC ha hi).1,
    fun a ha i hi => (S.edgeRow_BIF_value_deriv_BAUGC ha hi).2⟩

/-- **The supply-side inputs at the slim stage** (`D_a = B(a, 950000Δρ(a))`). -/
theorem slim_normal_inputs_BAUGC :
    (∀ a ∈ S.stageCentres_BIF 2, ENNReal.ofReal 10 < distanceToBoundary W g a.val) ∧
    (∀ a i, ‖S.slimRow_BIF a i‖ ≤ 1) ∧
    (∀ a ∈ S.stageCentres_BIF 2, ∀ i ∈ S.boundaryList_BIF 2 a,
      letI := inducedMetricSpace S.completion.metric
      ∀ y : W.pieceInterior ⊤, dist y a < stageDomain_BIF Δ 2 * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a -
          S.slimRow_BIF a i (S.slimEta_BIF a y - S.slimEta_BIF a a)| < θ) ∧
    (∀ a ∈ S.stageCentres_BIF 2, ∀ i ∈ S.boundaryList_BIF 2 a,
      letI := inducedMetricSpace S.completion.metric
      ∀ x : W.pieceInterior ⊤, dist x a < stageDomain_BIF Δ 2 * S.rho a → ∃ θ' < θ,
        ∀ u : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3)
              (fun y : W.pieceInterior ⊤ => (S.packet.height i y - S.packet.height i a) / S.rho a)
              x u - S.slimRow_BIF a i (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF a) x u)| ≤
            θ' * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (S.rho_pos a)) 2) S.completion.metric).inner x u u)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  exact ⟨fun a ha => (S.family.slim.centres_subset ha).1, S.norm_slimRow_BIF_le_BAUGC,
    fun a ha i hi => (S.slimRow_BIF_value_deriv_BAUGC ha hi).1,
    fun a ha i hi => (S.slimRow_BIF_value_deriv_BAUGC ha hi).2⟩

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
