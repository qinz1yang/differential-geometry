import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferCloud

/-!
# The transfer layer, the three stages (lane BAUG-C)

For ONE stored supply `S`: the port output of a stage (the conclusion of
`port_{circle,edge,slim}_interior_table_BAUGP`, `PortTargets v3.1`, called at `(Γ, 5Σ/4, e/2)`;
for edge / slim also the supplementary (PRE~) target) gives a stage table of the actual slot v2
with `BoundaryEnhancedPlaneSpecV3` at `(Γ, Σ, e)` — the port table `portTable_BAUGC` with the
twelve field lemmas of G3b–G3d.

* `exists_boundaryCircleSpec_of_port_BAUGC`, `exists_boundaryEdgeSpec_of_port_BAUGC`,
  `exists_boundarySlimSpec_of_port_BAUGC` (hypothesis `hport` = the port conclusion verbatim up to
  `sg ↦ 5/4·sg`, `eg ↦ eg/2`; numbers = ProducerDP v3's; extra numeric premises
  `β₁³·10⁶Δ < 1`, chart quality `≤ 1`, `0 ≤ θ`, `16P_*θ ≤ e`);
* stage coordinates `circleEta_deriv_le_BAUGC`, `edgeEta_deriv_le_BAUGC`, `slimEta_deriv_le_BAUGC`
  (`|Dη_a| ≤ 2|·|_{ρ(a)⁻²ĝ}` on the cores);
* `egpGraphConst_pos_BAUGC`, `sgpGraphBound_pos_BAUGC` (local copies of KC4 / GAF8, avoiding the
  imports of the edge / slim graph rows).

Heartbeat pitfall: the port clauses mention `S.stageTagsV2_BAUGD`, the field lemmas
`(actualSlotsV2_BAUGD S).stageTags`; unifying them inside a norm costs ~300k heartbeats, so every
stage proof first rewrites the port hypotheses with `actualSlotsV2_stageTags_BAUGD`.
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

/-- EGP06's early constant `C†` is positive (local copy of the KC4 argument: both LC87
multiplicity constants are ratios of positive model volumes). -/
theorem egpGraphConst_pos_BAUGC : 0 < egpGraphConst := by
  have hV : ∀ K r : ℝ, K < 0 → 0 < r → 0 < VolumeComparison.modelVolume K 3 r := fun K r hK hr =>
    VolumeComparison.modelVolume_pos (by norm_num) hr ⟨hr.le, fun h => absurd h (not_lt.mpr hK.le)⟩
  have h1 : 0 < egp02ListBound := by
    unfold egp02ListBound egp02EdgeCount egp02SlimCount
    exact add_pos (div_pos (hV _ _ (by norm_num) (by norm_num)) (hV _ _ (by norm_num) (by norm_num)))
      (div_pos (hV _ _ (by norm_num) (by norm_num)) (hV _ _ (by norm_num) (by norm_num)))
  have h2 := one_le_egpProfileConst
  unfold egpGraphConst
  have h3 : 0 < egp02ListBound + 2 := by linarith
  have h4 : 0 < egpProfileConst + 1 := by linarith
  positivity

/-- The slim graph modulus is positive (local copy of the GAF8 argument). -/
theorem sgpGraphBound_pos_BAUGC : 0 < sgpGraphBound := by
  have hV : ∀ K r : ℝ, K < 0 → 0 < r → 0 < VolumeComparison.modelVolume K 3 r := fun K r hK hr =>
    VolumeComparison.modelVolume_pos (by norm_num) hr ⟨hr.le, fun h => absurd h (not_lt.mpr hK.le)⟩
  have hs : 0 < egp02SlimCount := by
    unfold egp02SlimCount
    exact div_pos (hV _ _ (by norm_num) (by norm_num)) (hV _ _ (by norm_num) (by norm_num))
  have h1 : 0 < max sgpProfileBound zeroProfileBound + 1 := by
    linarith [le_max_left sgpProfileBound zeroProfileBound, sgpProfileBound_spec.1]
  have h2 : 0 < egp02SlimCount + 2 := by linarith
  rw [sgpGraphBound]
  exact mul_pos (mul_pos (by norm_num) h2) h1

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- **The circle reference coordinate is `2`-Lipschitz in the units of `ρ(a)⁻²ĝ` on the core**
(the adapted packet's `(1 + γ)`-Lipschitz chart, `γ ≤ 1`; `γ ≥ 0` from the adapted clause at the
centre). -/
theorem circleEta_deriv_le_BAUGC (hγ1 : γ ≤ 1) {a : W.pieceInterior ⊤}
    (ha : a ∈ S.stageCentres_BIF 0) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q a < 200 * S.rho a)
    (u : TangentSpace 𝓘(ℝ, E3) q) :
    ‖mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a) q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have ha' : a ∈ S.family.circle.centres := ha
  have heta : S.circleEta_BIF a =
      (let c := S.family.circle.chart a ha'
       letI := (inducedMetricSpace S.completion.metric).rescale (S.rho a)⁻¹
         (inv_pos.mpr (S.rho_pos a))
       c.coord) := by
    unfold BoundarySupplyCore.circleEta_BIF
    rw [dite_eq_left ha']
  have ad := S.family.circleAdapted a ha'
  have hγ0 : 0 ≤ γ := by
    have h := ad.adapted a (by
      let _ := (inducedMetricSpace S.completion.metric).rescale (S.rho a)⁻¹
        (inv_pos.mpr (S.rho_pos a))
      exact mem_ball_self (by norm_num))
    exact (norm_nonneg _).trans h.le
  rw [heta]
  refine (norm_mvfderiv_circle_coord_le_BCG8b S.family.circle ha' ad hγ0 hq u).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)


/-- **The revised-edge reference coordinate is `2`-Lipschitz in the units of `ρ(a)⁻²ĝ` on the core**
(`σ_c ≤ 1`). -/
theorem edgeEta_deriv_le_BAUGC (hσc0 : 0 ≤ σc) (hσc1 : σc ≤ 1) {a : W.pieceInterior ⊤}
    (ha : a ∈ S.stageCentres_BIF 1) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q a < 100 * Δ * S.rho a)
    (u : TangentSpace 𝓘(ℝ, E3) q) :
    ‖mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have ha' : a ∈ S.family.edgeB.centres := ha
  have heta : S.edgeEta_BIF a = S.family.edgeB.coord_BCG1 a ha' := by
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left ha']
  rw [heta, Real.norm_eq_abs]
  refine (abs_mvfderiv_edge_coord_le_BCG8b S.family.edgeB ha' hσc0 hq u).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- **The slim reference coordinate is `2`-Lipschitz in the units of `ρ(a)⁻²ĝ` on the core**
(`σ_s ≤ 1`). -/
theorem slimEta_deriv_le_BAUGC (hσs0 : 0 ≤ σs) (hσs1 : σs ≤ 1) {a : W.pieceInterior ⊤}
    (ha : a ∈ S.stageCentres_BIF 2) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q a < 1000000 * Δ * S.rho a)
    (u : TangentSpace 𝓘(ℝ, E3) q) :
    ‖mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF a) q u‖ ≤
      2 * Real.sqrt ((scaleMetric ((S.rho a)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (S.rho_pos a)) 2)
        S.completion.metric).inner q u u) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have ha' : a ∈ S.family.slim.centres := ha
  have heta : S.slimEta_BIF a = (S.family.slim.centre a ha').coord_BCG2 := by
    unfold BoundarySupplyCore.slimEta_BIF
    rw [dite_eq_left ha']
  have hq' : dist q a < 10 ^ 6 * Δ * S.rho a := by norm_num; exact hq
  rw [heta, Real.norm_eq_abs]
  refine (abs_mvfderiv_slim_coord_le_BCG8b (S.family.slim.centre a ha') hσs0 hq' u).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

open Classical in
/-- **The circle stage of the actual slot v2 with its spec V3, from the circle port output** (the
transfer of `port_circle_interior_table_BAUGP` called at `(Γ, 5Σ/4, e/2)`; its conclusion is the
hypothesis `hport`, verbatim up to that substitution): with ProducerDP v3's numbers, the register
smoothness premises, `β₁³·10⁶Δ < 1`, `γ ≤ 1`, the budget `16P_*θ ≤ e` and the separated branch,
the port table of the output carries `BoundaryEnhancedPlaneSpecV3` at `(Γ, Σ, e)`. -/
theorem exists_boundaryCircleSpec_of_port_BAUGC {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC))) (heg : 0 < eg)
    (hegΓ : eg < Γ * sg / 100) (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) (hγ1 : γ ≤ 1)
    (hθ : 0 ≤ θ) (h16 : 16 * bmConst_BAUGC * θ ≤ eg) (hsep : S.SeparatedCollarZero_BIF)
    (hport :
      letI := inducedMetricSpace S.completion.metric
      ∃ (Ψ : W.pieceInterior ⊤ → ℝ² → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
          BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ²)
        (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 0 → W.pieceInterior ⊤)
        (pre : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤)
        (ref : (actualSlotsV2_BAUGD S).stageCloud 0 → W.pieceInterior ⊤),
      (∀ a ∈ S.stageCentres_BIF 0, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
        ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤ tcpGraphConst) ∧
      (∀ a ∈ S.stageCentres_BIF 0, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
        ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧ ‖S.circleEta_BIF a x‖ ≤ 8) →
          Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x)) =
            S.circleEta_BIF a x) ∧
      (∀ a ∈ S.stageCentres_BIF 0, ∀ u,
        blockRestrict (S.stageTagsV2_BAUGD 0) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
      (∀ a ∈ S.stageCentres_BIF 0, ∀ x : W.pieceInterior ⊤, (dist x a < 200 * S.rho a ∧ ‖S.circleEta_BIF a x‖ ≤ 8) →
        ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA x) -
            (Kint a ∘ Ψ a) (S.circleEta_BIF a x)‖ < eg / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 0) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.circleEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a) x w)‖ ≤
            eg / 2 * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 0 ∧ (dist (pre x) (ref x) < 200 * S.rho (ref x) ∧ ‖S.circleEta_BIF (ref x) (pre x)‖ ≤ 7) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 0 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ 5 / 4 * sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = y) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ u : ℝ²,
        ‖u - S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * (5 / 4 * sg) / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
          S.circleEta_BIF (ref ⟨x, hx⟩) q = u ∧
          (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 0) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
        (dist q (ref ⟨x, hx⟩) < 200 * S.rho (ref ⟨x, hx⟩) ∧ ‖S.circleEta_BIF (ref ⟨x, hx⟩) q‖ ≤ 8) ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 0 * S.rho (ref ⟨x, hx⟩) ∧
          S.circleEta_BIF (ref ⟨x, hx⟩) q = S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 0), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
          ∀ v : ℝ², ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
            (S.circleEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      (∀ a ∈ S.stageCentres_BIF 0, ∀ m : S.MarkerIdx_BAUGC,
        S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 0 * S.rho a →
        ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
      (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 0 → ∀ p ∈ S.markerCore7_BAUGC m,
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          ∀ v : ℝ², ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.circleEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val) ∈
          (actualSlotsV2_BAUGD S).stageCloud 0 →
        200 * S.zeroRadius_BAUGC k / T < S.rho p →
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 0),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 0
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 0
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.zeroBlockCLM_BAUGC k y = 0 ∧
          ∀ v : ℝ², (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.circleEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0) ∧
      (∀ a ∈ S.stageCentres_BIF 0, ∀ u v : ℝ²,
        ((fderiv ℝ (Kint a ∘ Ψ a) u v) S.scaleTag_BAUGA).snd = 0)) :
    ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 0 ℝ² S.circleEta_BIF
      S.circleRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  obtain ⟨Ψ, Kint, Pc, rpre, pre, ref, hM, hOWN, hQ, hTG, hSEL1, hSEL2, hLOC, hCOV, hPRE, hPP, hSB,
    hFM, hZB, hSCL⟩ := hport
  rw [← actualSlotsV2_stageTags_BAUGD] at hOWN hQ hTG
  have href : ∀ x, ref x ∈ S.stageCentres_BIF 0 := fun x => (hSEL2 x).1
  have hpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap (pre x).val) = x.1 ∧
      (letI := inducedMetricSpace S.completion.metric
       dist (pre x) (ref x) < stageDomain_BIF Δ 0 * S.rho (ref x)) :=
    fun x => ⟨(hSEL2 x).2.2.2, (hSEL2 x).2.2.1⟩
  have hnum := transfer_numbers_BAUGC hΓ (lt_of_lt_of_le one_pos one_le_tcpGraphConst) hsgΓ hsgC
    heg hegΓ h16
  have hM' : ∀ a ∈ S.stageCentres_BIF 0, ContDiff ℝ 2 (Kint a ∘ Ψ a) := fun a ha => (hM a ha).1
  have hin := S.circle_normal_inputs_BAUGC
  refine ⟨portTable_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre
    pre ref href hSEL1 hpre, ?_⟩
  refine
    { prune_slot := ?_
      cloud_subset := ?_
      radius_mcb := ?_
      preimage_comparable := ?_
      dimension := ?_
      cloudy := ?_
      normal := ?_
      small_pp := ?_
      scale_zero := ?_
      small_block := ?_
      full_marker := ?_
      zero_block := ?_ }
  · exact portTable_prune_slot_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
  · exact actualSlotsV2_cloud_subset_BAUGD S (by linarith) 0
  · exact radius_mcb_of_scale_kept_BAUGC (actualSlotsV2_scale_kept_BAUGD S) hsg
  · exact preimage_comparable_of_scale_kept_BAUGC (actualSlotsV2_scale_kept_BAUGD S)
  · exact portTable_dimension_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre finrank_euclideanSpace_fin Pc hM' (fun a ha => (hOWN a ha).2.1) hQ
  · exact portTable_cloudy_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hΛ hΔ1 hβ1 hΛΔ hreq hsep hθ (lt_of_lt_of_le one_pos one_le_tcpGraphConst) hΓ hΓ1 hsg hsgΓ hsgC hnum.2.2.2.2.2 hnum.2.2.2.1 (fun a y => (letI := inducedMetricSpace S.completion.metric; dist y a < 200 * S.rho a) ∧ ‖S.circleEta_BIF a y‖ ≤ 8) Pc (fun a ha => ⟨(hM a ha).1, fun u => ((hM a ha).2 u).2⟩) hOWN (fun a ha y hy => (hTG a ha y hy).1) (fun x => ⟨(hSEL2 x).2.1.1, (hSEL2 x).2.1.2.trans (by norm_num)⟩) hLOC hCOV (fun x hx q hq => (hPRE x hx q hq).2.1) (actualSlotsV2_stageCloud_subset_BAUGD S (by linarith) 0) hin.2.1 hin.2.2.1
  · exact portTable_normal_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hΛ hΔ1 hμ hτ hΔΛ hV hβ1 hb he hΛΔ hreq hsep hθ hnum.2.2.2.2.1 hin.1 hin.2.1 hin.2.2.1 hin.2.2.2 hM' (fun x hx q hq => ⟨(hPRE x hx q hq).2.1, (hPRE x hx q hq).2.2⟩) (fun x hx q hq w => (hTG _ (href _) q (hPRE x hx q hq).1).2 w) (fun x hx q hq u => S.circleEta_deriv_le_BAUGC hγ1 (href _) (hPRE x hx q hq).1.1 u)
  · exact portTable_small_pp_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hPP
  · exact portTable_scale_zero_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' (fun _ => hSCL)
  · exact portTable_small_block_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hSB
  · exact portTable_full_marker_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hFM
  · exact portTable_zero_block_BAUGC (actualSlotsV2_BAUGD S) 0 S.circleEta_BIF S.circleRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hZB

open Classical in
/-- **The revised-edge stage of the actual slot v2 with its spec V3, from the revised-edge port output** (the
transfer of the port table called at `(Γ, 5Σ/4, e/2)` — hypothesis `hport`, verbatim up to that
substitution — and of the supplementary (PRE~) target `hPREt`): with ProducerDP v3's numbers, the
register smoothness premises, `β₁³·10⁶Δ < 1`, the chart quality `≤ 1`, the budget `16P_*θ ≤ e` and
the separated branch, the port table of the output carries `BoundaryEnhancedPlaneSpecV3`. -/
theorem exists_boundaryEdgeSpec_of_port_BAUGC {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC))) (heg : 0 < eg)
    (hegΓ : eg < Γ * sg / 100) (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) (hσc0 : 0 ≤ σc) (hσc1 : σc ≤ 1)
    (hθ : 0 ≤ θ) (h16 : 16 * bmConst_BAUGC * θ ≤ eg) (hsep : S.SeparatedCollarZero_BIF)
    (hport :
      letI := inducedMetricSpace S.completion.metric
      ∃ (Ψ : W.pieceInterior ⊤ → ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
          BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ)
        (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 → W.pieceInterior ⊤)
        (pre : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤)
        (ref : (actualSlotsV2_BAUGD S).stageCloud 1 → W.pieceInterior ⊤),
      (∀ a ∈ S.stageCentres_BIF 1, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
        ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ egpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤ egpGraphConst) ∧
      (∀ a ∈ S.stageCentres_BIF 1, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
        ∀ x : W.pieceInterior ⊤, (dist x a < 100 * Δ * S.rho a ∧ |S.edgeEta_BIF a x| ≤ 8 * Δ ∧ S.edgeHeightRaw x ≤ 8 * Δ) →
          Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x)) =
            S.edgeEta_BIF a x) ∧
      (∀ a ∈ S.stageCentres_BIF 1, ∀ u,
        blockRestrict (S.stageTagsV2_BAUGD 1) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
      (∀ a ∈ S.stageCentres_BIF 1, ∀ x : W.pieceInterior ⊤, (dist x a < 100 * Δ * S.rho a ∧ |S.edgeEta_BIF a x| ≤ 8 * Δ ∧ S.edgeHeightRaw x ≤ 8 * Δ) →
        ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
            (Kint a ∘ Ψ a) (S.edgeEta_BIF a x)‖ < eg / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.edgeEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF a) x w)‖ ≤
            eg / 2 * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 1 ∧ (dist (pre x) (ref x) < 100 * Δ * S.rho (ref x) ∧ |S.edgeEta_BIF (ref x) (pre x)| ≤ 7 * Δ ∧ S.edgeHeightRaw (pre x) ≤ 7 * Δ) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 1 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ 5 / 4 * sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = y) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ u : ℝ,
        ‖u - S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * (5 / 4 * sg) / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
          S.edgeEta_BIF (ref ⟨x, hx⟩) q = u ∧
          (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 1) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = x →
        (dist q (ref ⟨x, hx⟩) < 100 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.edgeEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * Δ ∧ S.edgeHeightRaw q ≤ 8 * Δ) ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 1 * S.rho (ref ⟨x, hx⟩) ∧
          S.edgeEta_BIF (ref ⟨x, hx⟩) q = S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
      (∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
        (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (sel x).val) = x) →
        ∀ L' : ℝ, 0 ≤ L' → L' * (5 / 4 * sg) ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1,
          dist y x ≤ L' * max (5 / 4 * sg * S.rho (sel y)) (5 / 4 * sg * S.rho (sel x)) →
          5 / 4 * sg * S.rho (sel x) / (5 / 3) ≤ 5 / 4 * sg * S.rho (sel y) ∧
            5 / 4 * sg * S.rho (sel y) ≤ 5 / 3 * (5 / 4 * sg * S.rho (sel x))) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 1), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
            (S.edgeEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      (∀ a ∈ S.stageCentres_BIF 1, ∀ m : S.MarkerIdx_BAUGC,
        S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 1 * S.rho a →
        ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
      (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 1 → ∀ p ∈ S.markerCore7_BAUGC m,
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 1
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.edgeEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val) ∈
          (actualSlotsV2_BAUGD S).stageCloud 1 →
        200 * S.zeroRadius_BAUGC k / T < S.rho p →
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 1),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 1
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.zeroBlockCLM_BAUGC k y = 0 ∧
          ∀ v : ℝ, (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.edgeEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0))
    (hPREt : ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 1, ∀ q₁ q₂ : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₁.val) = x →
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q₂.val) = x →
      S.rho q₁ ≤ 5 / 3 * S.rho q₂) :
    ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 1 ℝ S.edgeEta_BIF
      S.edgeRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  obtain ⟨Ψ, Kint, Pc, rpre, pre, ref, hM, hOWN, hQ, hTG, hSEL1, hSEL2, hLOC, hCOV, hPRE, hMCb, hPP,
    hSB, hFM, hZB⟩ := hport
  rw [← actualSlotsV2_stageTags_BAUGD] at hOWN hQ hTG
  have href : ∀ x, ref x ∈ S.stageCentres_BIF 1 := fun x => (hSEL2 x).1
  have hpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap (pre x).val) = x.1 ∧
      (letI := inducedMetricSpace S.completion.metric
       dist (pre x) (ref x) < stageDomain_BIF Δ 1 * S.rho (ref x)) :=
    fun x => ⟨(hSEL2 x).2.2.2, (hSEL2 x).2.2.1⟩
  have hnum := transfer_numbers_BAUGC hΓ egpGraphConst_pos_BAUGC hsgΓ hsgC heg hegΓ h16
  have hM' : ∀ a ∈ S.stageCentres_BIF 1, ContDiff ℝ 2 (Kint a ∘ Ψ a) := fun a ha => (hM a ha).1
  have hin := S.edge_normal_inputs_BAUGC
  have hΔ0 : (0 : ℝ) ≤ Δ := by linarith
  refine ⟨portTable_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre
    pre ref href hSEL1 hpre, ?_⟩
  refine
    { prune_slot := ?_
      cloud_subset := ?_
      radius_mcb := ?_
      preimage_comparable := ?_
      dimension := ?_
      cloudy := ?_
      normal := ?_
      small_pp := ?_
      scale_zero := ?_
      small_block := ?_
      full_marker := ?_
      zero_block := ?_ }
  · exact portTable_prune_slot_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
  · exact actualSlotsV2_cloud_subset_BAUGD S hΔ0 1
  · exact radius_mcb_of_port_BAUGC hMCb
  · exact hPREt
  · exact portTable_dimension_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
      (by rw [Module.finrank_self]; rfl) Pc hM' (fun a ha => (hOWN a ha).2.1) hQ
  · exact portTable_cloudy_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
      hΛ hΔ1 hβ1 hΛΔ hreq hsep hθ egpGraphConst_pos_BAUGC hΓ hΓ1 hsg hsgΓ hsgC hnum.2.2.2.2.2 hnum.2.2.2.1
      (fun a y => (letI := inducedMetricSpace S.completion.metric; dist y a < 100 * Δ * S.rho a) ∧
          |S.edgeEta_BIF a y| ≤ 8 * Δ ∧ S.edgeHeightRaw y ≤ 8 * Δ) Pc
      (fun a ha => ⟨(hM a ha).1, fun u => ((hM a ha).2 u).2⟩) hOWN
      (fun a ha y hy => (hTG a ha y hy).1)
      (fun x => ⟨(hSEL2 x).2.1.1, (hSEL2 x).2.1.2.1.trans (by linarith), (hSEL2 x).2.1.2.2.trans (by linarith)⟩) hLOC hCOV
      (fun x hx q hq => (hPRE x hx q hq).2.1)
      (actualSlotsV2_stageCloud_subset_BAUGD S hΔ0 1) hin.2.1 hin.2.2.1
  · exact portTable_normal_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
      hΛ hΔ1 hμ hτ hΔΛ hV hβ1 hb he hΛΔ hreq hsep hθ hnum.2.2.2.2.1 hin.1 hin.2.1 hin.2.2.1
      hin.2.2.2 hM' (fun x hx q hq => ⟨(hPRE x hx q hq).2.1, (hPRE x hx q hq).2.2⟩)
      (fun x hx q hq w => (hTG _ (href _) q (hPRE x hx q hq).1).2 w)
      (fun x hx q hq u => S.edgeEta_deriv_le_BAUGC hσc0 hσc1 (href _) (hPRE x hx q hq).1.1 u)
  · exact portTable_small_pp_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hPP
  · exact portTable_scale_zero_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM'
      (fun h => absurd h (by decide))
  · exact portTable_small_block_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hSB
  · exact portTable_full_marker_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hFM
  · exact portTable_zero_block_BAUGC (actualSlotsV2_BAUGD S) 1 S.edgeEta_BIF S.edgeRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hZB

open Classical in
/-- **The slim stage of the actual slot v2 with its spec V3, from the slim port output** (the
transfer of the port table called at `(Γ, 5Σ/4, e/2)` — hypothesis `hport`, verbatim up to that
substitution — and of the supplementary (PRE~) target `hPREt`): with ProducerDP v3's numbers, the
register smoothness premises, `β₁³·10⁶Δ < 1`, the chart quality `≤ 1`, the budget `16P_*θ ≤ e` and
the separated branch, the port table of the output carries `BoundaryEnhancedPlaneSpecV3`. -/
theorem exists_boundarySlimSpec_of_port_BAUGC {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC))) (heg : 0 < eg)
    (hegΓ : eg < Γ * sg / 100) (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hreq : β 1 ^ 3 * (1000000 * Δ) < 1) (hσs0 : 0 ≤ σs) (hσs1 : σs ≤ 1)
    (hθ : 0 ≤ θ) (h16 : 16 * bmConst_BAUGC * θ ≤ eg) (hsep : S.SeparatedCollarZero_BIF)
    (hport :
      letI := inducedMetricSpace S.completion.metric
      ∃ (Ψ : W.pieceInterior ⊤ → ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Kint : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ]
          BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
        (Pc : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) →L[ℝ] ℝ)
        (rpre : (actualSlotsV2_BAUGD S).stageCloudEnlarged 2 → W.pieceInterior ⊤)
        (pre : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤)
        (ref : (actualSlotsV2_BAUGD S).stageCloud 2 → W.pieceInterior ⊤),
      (∀ a ∈ S.stageCentres_BIF 2, ContDiff ℝ 2 (Kint a ∘ Ψ a) ∧ ∀ u,
        ‖fderiv ℝ (Kint a ∘ Ψ a) u‖ ≤ sgpGraphBound ∧ ‖fderiv ℝ (fderiv ℝ (Kint a ∘ Ψ a)) u‖ ≤ sgpGraphBound) ∧
      (∀ a ∈ S.stageCentres_BIF 2, (∀ z, ‖Pc a z‖ ≤ ‖z‖) ∧ (∀ u, Pc a ((Kint a ∘ Ψ a) u) = u) ∧
        ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧ |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
          Pc a ((S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x)) =
            S.slimEta_BIF a x) ∧
      (∀ a ∈ S.stageCentres_BIF 2, ∀ u,
        blockRestrict (S.stageTagsV2_BAUGD 2) ((Kint a ∘ Ψ a) u) = (Kint a ∘ Ψ a) u) ∧
      (∀ a ∈ S.stageCentres_BIF 2, ∀ x : W.pieceInterior ⊤, (dist x a < 1000000 * Δ * S.rho a ∧ |S.slimEta_BIF a x| ≤ 8 * (100000 * Δ)) →
        ‖(S.rho a)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
            (Kint a ∘ Ψ a) (S.slimEta_BIF a x)‖ < eg / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(S.rho a)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (fun y => blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA y)) x w -
              fderiv ℝ (Kint a ∘ Ψ a) (S.slimEta_BIF a x) (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF a) x w)‖ ≤
            eg / 2 * Real.sqrt ((S.rho a)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
      (∀ x, (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (rpre x).val) = x.1) ∧
      (∀ x, ref x ∈ S.stageCentres_BIF 2 ∧ (dist (pre x) (ref x) < 1000000 * Δ * S.rho (ref x) ∧ |S.slimEta_BIF (ref x) (pre x)| ≤ 7 * (100000 * Δ)) ∧
        dist (pre x) (ref x) < stageDomain_BIF Δ 2 * S.rho (ref x) ∧
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          ‖augIntProjCLM_BAUGC (y - x)‖ ≤ 5 / 4 * sg * S.rho (ref ⟨x, hx⟩) / Γ →
          ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
            dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
            (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = y) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ u : ℝ,
        ‖u - S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)‖ ≤ 2 * (5 / 4 * sg) / Γ →
        ∃ q : W.pieceInterior ⊤, (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧
          dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
          S.slimEta_BIF (ref ⟨x, hx⟩) q = u ∧
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloudEnlarged 2) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
        (dist q (ref ⟨x, hx⟩) < 1000000 * Δ * S.rho (ref ⟨x, hx⟩) ∧ |S.slimEta_BIF (ref ⟨x, hx⟩) q| ≤ 8 * (100000 * Δ)) ∧ dist q (ref ⟨x, hx⟩) < stageDomain_BIF Δ 2 * S.rho (ref ⟨x, hx⟩) ∧
          S.slimEta_BIF (ref ⟨x, hx⟩) q = S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) ∧
      (∀ sel : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → W.pieceInterior ⊤,
        (∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (sel x).val) = x) →
        ∀ L' : ℝ, 0 ≤ L' → L' * (5 / 4 * sg) ≤ 1 / 5 →
        ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
        ∀ y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2,
          dist y x ≤ L' * max (5 / 4 * sg * S.rho (sel y)) (5 / 4 * sg * S.rho (sel x)) →
          5 / 4 * sg * S.rho (sel x) / (5 / 3) ≤ 5 / 4 * sg * S.rho (sel y) ∧
            5 / 4 * sg * S.rho (sel y) ≤ 5 / 3 * (5 / 4 * sg * S.rho (sel x))) ∧
      (∀ x (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud 2), ∀ q : W.pieceInterior ⊤,
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) = x →
        ∀ m : S.MarkerIdx_BAUGC, S.rho (S.markerCentre_BAUGC m) < S.rho q / 5 →
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨x, hx⟩) ∘ Ψ (ref ⟨x, hx⟩))
            (S.slimEta_BIF (ref ⟨x, hx⟩) (pre ⟨x, hx⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      (∀ a ∈ S.stageCentres_BIF 2, ∀ m : S.MarkerIdx_BAUGC,
        S.rho (S.markerCentre_BAUGC m) ≤ smallBlockFactor_BAUGC 2 * S.rho a →
        ∀ u, (Kint a ∘ Ψ a) u (S.markerTag_BAUGC m) = 0) ∧
      (∀ εc σ' : ℝ, 0 < εc → 0 ≤ σ' → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (m : S.MarkerIdx_BAUGC), S.markerStage_BAUGC m = 2 → ∀ p ∈ S.markerCore7_BAUGC m,
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.markerCLM_BAUGC m y = S.rho (S.markerCentre_BAUGC m) ∧
          ∀ v : ℝ, ((fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.slimEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.markerTag_BAUGC m)).snd = 0) ∧
      (∀ εc σ' : ℝ, 0 < εc → σ' ≤ εc / 10000 → ∀ (x₀ : W.pieceInterior ⊤)
        (k : S.ZeroIdx_BAUGC) (p : W.pieceInterior ⊤),
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val) ∈
          (actualSlotsV2_BAUGD S).stageCloud 2 →
        200 * S.zeroRadius_BAUGC k / T < S.rho p →
        ∀ y (hy : y ∈ (actualSlotsV2_BAUGD S).stageCloud 2),
          (closedBall y (80 * εc⁻¹ * (σ' * S.rho (if hyT : y ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
              then rpre ⟨y, hyT⟩ else x₀))) ∩
            ball ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap p.val))
              (8 * εc⁻¹ * (σ' * S.rho (if hpT : (actualSlotsV2_BAUGD S).stageProj 2
                  (S.boundaryOriginalMap p.val) ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2
                then rpre ⟨_, hpT⟩ else x₀)))).Nonempty →
          S.zeroBlockCLM_BAUGC k y = 0 ∧
          ∀ v : ℝ, (fderiv ℝ (Kint (ref ⟨y, hy⟩) ∘ Ψ (ref ⟨y, hy⟩))
            (S.slimEta_BIF (ref ⟨y, hy⟩) (pre ⟨y, hy⟩)) v) (S.zeroTag_BAUGC k) = 0))
    (hPREt : ∀ x ∈ (actualSlotsV2_BAUGD S).stageCloudEnlarged 2, ∀ q₁ q₂ : W.pieceInterior ⊤,
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₁.val) = x →
      (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q₂.val) = x →
      S.rho q₁ ≤ 5 / 3 * S.rho q₂) :
    ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 2 ℝ S.slimEta_BIF
      S.slimRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  obtain ⟨Ψ, Kint, Pc, rpre, pre, ref, hM, hOWN, hQ, hTG, hSEL1, hSEL2, hLOC, hCOV, hPRE, hMCb, hPP,
    hSB, hFM, hZB⟩ := hport
  rw [← actualSlotsV2_stageTags_BAUGD] at hOWN hQ hTG
  have href : ∀ x, ref x ∈ S.stageCentres_BIF 2 := fun x => (hSEL2 x).1
  have hpre : ∀ x, (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap (pre x).val) = x.1 ∧
      (letI := inducedMetricSpace S.completion.metric
       dist (pre x) (ref x) < stageDomain_BIF Δ 2 * S.rho (ref x)) :=
    fun x => ⟨(hSEL2 x).2.2.2, (hSEL2 x).2.2.1⟩
  have hnum := transfer_numbers_BAUGC hΓ sgpGraphBound_pos_BAUGC hsgΓ hsgC heg hegΓ h16
  have hM' : ∀ a ∈ S.stageCentres_BIF 2, ContDiff ℝ 2 (Kint a ∘ Ψ a) := fun a ha => (hM a ha).1
  have hin := S.slim_normal_inputs_BAUGC
  have hΔ0 : (0 : ℝ) ≤ Δ := by linarith
  refine ⟨portTable_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre
    pre ref href hSEL1 hpre, ?_⟩
  refine
    { prune_slot := ?_
      cloud_subset := ?_
      radius_mcb := ?_
      preimage_comparable := ?_
      dimension := ?_
      cloudy := ?_
      normal := ?_
      small_pp := ?_
      scale_zero := ?_
      small_block := ?_
      full_marker := ?_
      zero_block := ?_ }
  · exact portTable_prune_slot_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
  · exact actualSlotsV2_cloud_subset_BAUGD S hΔ0 2
  · exact radius_mcb_of_port_BAUGC hMCb
  · exact hPREt
  · exact portTable_dimension_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
      (by rw [Module.finrank_self]; rfl) Pc hM' (fun a ha => (hOWN a ha).2.1) hQ
  · exact portTable_cloudy_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
      hΛ hΔ1 hβ1 hΛΔ hreq hsep hθ sgpGraphBound_pos_BAUGC hΓ hΓ1 hsg hsgΓ hsgC hnum.2.2.2.2.2 hnum.2.2.2.1
      (fun a y => (letI := inducedMetricSpace S.completion.metric; dist y a < 1000000 * Δ * S.rho a) ∧
          |S.slimEta_BIF a y| ≤ 8 * (100000 * Δ)) Pc
      (fun a ha => ⟨(hM a ha).1, fun u => ((hM a ha).2 u).2⟩) hOWN
      (fun a ha y hy => (hTG a ha y hy).1)
      (fun x => ⟨(hSEL2 x).2.1.1, (hSEL2 x).2.1.2.trans (by linarith)⟩) hLOC hCOV
      (fun x hx q hq => (hPRE x hx q hq).2.1)
      (actualSlotsV2_stageCloud_subset_BAUGD S hΔ0 2) hin.2.1 hin.2.2.1
  · exact portTable_normal_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre
      hΛ hΔ1 hμ hτ hΔΛ hV hβ1 hb he hΛΔ hreq hsep hθ hnum.2.2.2.2.1 hin.1 hin.2.1 hin.2.2.1
      hin.2.2.2 hM' (fun x hx q hq => ⟨(hPRE x hx q hq).2.1, (hPRE x hx q hq).2.2⟩)
      (fun x hx q hq w => (hTG _ (href _) q (hPRE x hx q hq).1).2 w)
      (fun x hx q hq u => S.slimEta_deriv_le_BAUGC hσs0 hσs1 (href _) (hPRE x hx q hq).1.1 u)
  · exact portTable_small_pp_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hPP
  · exact portTable_scale_zero_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM'
      (fun h => absurd h (by decide))
  · exact portTable_small_block_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hSB
  · exact portTable_full_marker_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hFM
  · exact portTable_zero_block_BAUGC (actualSlotsV2_BAUGD S) 2 S.slimEta_BIF S.slimRow_BIF Ψ Kint rpre pre ref href hSEL1 hpre hM' hZB

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
