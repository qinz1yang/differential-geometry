import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc33
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesKernel

/-!
# FC33 as ONE row on the bases object: `fc33_row_BAS`

Blueprint `master207B.tex`, FC33 (`found:fibration-final-bases`, B:2873–2905), equal to the second
paragraph of GAF02 (B:5816–5824). Lane S-BASES-KER, group G11.

FC33 delivers (i) KL 13.1 with `𝓔 = Ψ₃Ψ₂Ψ₁𝓔⁰`, `|𝓔 − 𝓔⁰| < c_adjust ρ`, `‖D𝓔 − D𝓔⁰‖ < c_adjust`
(`Gaf02Chain.fc33_adjusted_RFC`, lane C14-ROWS-FC); (ii) embedded bases `W_j ⊂ Q_j` of dimensions
`2, 1, 1`, the appropriately restricted later images of the smoothed bases (marker `> .9R_i`,
coordinate thresholds `5.5`, `5.5Δ`, `5.5·10⁵Δ`); (iii) `π_j𝓔 : U_j → W_j` a submersion on the
EXACT original thresholds `5`, `5Δ` (including `η_{E'} < 5Δ`), `5·10⁵Δ`; and requires that KL 13.46
be implemented (four tasks: local coordinate projection proper onto local diffeomorphism; finite
covering of a Euclidean ball; connected local coordinate fibres; path lifting in the original
bundle ruling out two sheets; FC03 rules out remote preimages).

`Gaf02Bases.fc33_row_BAS` takes the bases object `B : Gaf02Bases C R` (lane C14-BASES, G8) and
the chain's `c₃ < c_adjust`, and concludes the clauses below (clause table in the delivery block):

* `finalBase_subset_stageQ_BAS`: `W_st ⊆ Q_st` (exhaustion: every `w ∈ V_st⁰` is `f_st p`, and
  `Θ_st (f_st p) = π_st E p ∈ Q_st`);
* `exists_plateau_preimage_BAS`: `V_st⁰ ⊆ f_st(B⁶_st)` (CGP07's threshold-6 exhaustion, all stages);
* `kl1346_patch_BAS` (generic) and `kl1346_circle/edge/slim_BAS` (per patch): KL 13.46 tasks 1–2
  as the CGP07 patch statement — `κ_j|V_j⁰` is a proper bijection onto `B(0, 5.5ℓ)` with smooth
  inverse (a proper diffeomorphism onto the ball), one sheet over every point (the covering of
  the ball has degree one);
* `final_eq_iff_BAS`: KL 13.46 task 4 (two sheets ruled out): on `U_st`, `π_st E p = π_st E p'`
  iff `f_st p = f_st p'` (CGP08, `Θ_st` injective on the whole marked base);
* `fc33_row_BAS`: the row.
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

/-- **KL 13.46, tasks 1–2, for one marked patch** (kernel form): if the linear coordinate
`κ = R⁻¹u` is a bijection of the patch `V` onto the ball `B(0, r)` with smooth inverse `φ` and
compact preimages of compact subsets of the ball, then `κ|V` is a proper map onto the ball with
smooth inverse (a proper diffeomorphism), and the covering of the ball by `V` has exactly one
sheet over every point. -/
theorem kl1346_patch_BAS {H E' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (V : Set H) (u : H →L[ℝ] E') (R : ℝ)
    (φ : E' → H) (r : ℝ) (hbij : BijOn (R⁻¹ • u) V (ball (0 : E') r))
    (hφ : ContDiffOn ℝ ∞ φ (ball (0 : E') r)) (hinv : InvOn φ (R⁻¹ • u) V (ball (0 : E') r))
    (hproper : ∀ K ⊆ ball (0 : E') r, IsCompact K → IsCompact (V ∩ (R⁻¹ • u) ⁻¹' K)) :
    ((R⁻¹ • u) '' V = ball (0 : E') r ∧
      (∀ K ⊆ ball (0 : E') r, IsCompact K → IsCompact (V ∩ (R⁻¹ • u) ⁻¹' K)) ∧
      ContDiffOn ℝ ∞ φ (ball (0 : E') r) ∧ InvOn φ (R⁻¹ • u) V (ball (0 : E') r)) ∧
    ∀ b ∈ ball (0 : E') r, ∃! w, w ∈ V ∧ (R⁻¹ • u) w = b :=
  ⟨⟨hbij.image_eq, hproper, hφ, hinv⟩, fun _ hb =>
    (hbij.surjOn hb).elim fun w hw => ⟨w, ⟨hw.1, hw.2⟩, fun _ hw' =>
      hbij.injOn hw'.1 hw.1 (hw'.2.trans hw.2.symm)⟩⟩

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Bases

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {R : Gaf02RoughData C}

/-- `V_st⁰ ⊆ f_st(B⁶_st)`: every point of the marked base is the stage value of a point of the
ORIGINAL threshold-6 plateau (CGP07's exhaustion, every stage). -/
theorem exists_plateau_preimage_BAS (B : Gaf02Bases C R) (st : Fin 3)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.markedBase_BAS st) :
    ∃ p, p ∈ gafStagePlateau_BAS P.toLocalChartPackets st ∧ C.stageMap_BAS st p = w := by
  rcases (by decide : ∀ s : Fin 3, s = 0 ∨ s = 1 ∨ s = 2) st with rfl | rfl | rfl
  · have hm : w ∈ ⋃ j, C.circlePatch_BAS j := hw
    exact (mem_iUnion.mp hm).elim fun j hj =>
      (B.circle.spec.exhaust j w hj).elim fun p hp => ⟨p, ⟨j, hp.1⟩, hp.2⟩
  · have hm : w ∈ ⋃ j, C.edgePatch_BAS j := hw
    exact (mem_iUnion.mp hm).elim fun j hj =>
      (B.edge.spec.exhaust j w hj).elim fun p hp => ⟨p, ⟨j, hp.1⟩, hp.2⟩
  · have hm : w ∈ ⋃ j, C.slimPatch_BAS j := hw
    exact (mem_iUnion.mp hm).elim fun j hj =>
      (B.slim.spec.exhaust j w hj).elim fun p hp => ⟨p, ⟨j, hp.1⟩, hp.2⟩

/-- **`W_st ⊆ Q_st`** (FC33's embedded bases lie in `Q_j`): a point of `W_st = Θ_st(V_st⁰)` is
`Θ_st (f_st p) = π_st E p` for a point `p` of the plateau (exhaustion). -/
theorem finalBase_subset_stageQ_BAS (B : Gaf02Bases C R) (st : Fin 3) :
    C.finalBase_BAS st ⊆ (gafStageQ P.toLocalChartFamily P.zero st : Set
      (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨p, -, rfl⟩ := B.exists_plateau_preimage_BAS st hw
  rw [← C.final_factor_BAS st p]
  exact Submodule.starProjection_apply_mem _ _

/-- **KL 13.46 tasks 1–2, circle patch `j`** (BASES' CGP07 chart): `κ_j|V_j⁰` is a proper map onto
`B(0, 5.5)` with smooth inverse, one sheet over every point. -/
theorem kl1346_circle_BAS (B : Gaf02Bases C R)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) '' C.circlePatch_BAS j =
        ball (0 : ℝ²) (11 / 2 * 1) ∧
      (∀ K ⊆ ball (0 : ℝ²) (11 / 2 * 1), IsCompact K → IsCompact (C.circlePatch_BAS j ∩
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) ⁻¹' K)) ∧
      ContDiffOn ℝ ∞ (B.circle.chart j) (ball (0 : ℝ²) (11 / 2 * 1)) ∧
      InvOn (B.circle.chart j) ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
        (C.circlePatch_BAS j) (ball (0 : ℝ²) (11 / 2 * 1))) ∧
    ∀ y ∈ ball (0 : ℝ²) (11 / 2 * 1), ∃! w, w ∈ C.circlePatch_BAS j ∧
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) w = y :=
  kl1346_patch_BAS _ _ _ _ _ (B.circle.spec.patch j).1 (B.circle.spec.patch j).2.1
    (B.circle.spec.patch j).2.2.1 (B.circle.spec.proper j)

/-- **KL 13.46 tasks 1–2, edge patch `j`** (axis coordinate; `ℓ = Δ`). -/
theorem kl1346_edge_BAS (B : Gaf02Bases C R) (j : P.edge.finite_centres.toFinset) :
    (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ''
        C.edgePatch_BAS j = ball (0 : ℝ) (11 / 2 * Δ) ∧
      (∀ K ⊆ ball (0 : ℝ) (11 / 2 * Δ), IsCompact K → IsCompact (C.edgePatch_BAS j ∩
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ⁻¹' K)) ∧
      ContDiffOn ℝ ∞ (B.edge.chart j) (ball (0 : ℝ) (11 / 2 * Δ)) ∧
      InvOn (B.edge.chart j)
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (C.edgePatch_BAS j) (ball (0 : ℝ) (11 / 2 * Δ))) ∧
    ∀ y ∈ ball (0 : ℝ) (11 / 2 * Δ), ∃! w, w ∈ C.edgePatch_BAS j ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) w = y :=
  kl1346_patch_BAS _ _ _ _ _ (B.edge.spec.patch j).1 (B.edge.spec.patch j).2.1
    (B.edge.spec.patch j).2.2.1 (B.edge.spec.proper j)

/-- **KL 13.46 tasks 1–2, slim patch `j`** (axis coordinate; `ℓ = 10⁵Δ`). -/
theorem kl1346_slim_BAS (B : Gaf02Bases C R) (j : P.slim.finite_centres.toFinset) :
    (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) ''
        C.slimPatch_BAS j = ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
      (∀ K ⊆ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), IsCompact K → IsCompact (C.slimPatch_BAS j ∩
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) ⁻¹' K)) ∧
      ContDiffOn ℝ ∞ (B.slim.chart j) (ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ))) ∧
      InvOn (B.slim.chart j)
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.slimPatch_BAS j) (ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)))) ∧
    ∀ y ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)), ∃! w, w ∈ C.slimPatch_BAS j ∧
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) w = y :=
  kl1346_patch_BAS _ _ _ _ _ (B.slim.spec.patch j).1 (B.slim.spec.patch j).2.1
    (B.slim.spec.patch j).2.2.1 (B.slim.spec.proper j)

/-- **KL 13.46 task 4 (two sheets ruled out), on FC33's exact `U_st`**: two points of `U_st` have
the same final value `π_st E` iff they have the same native value `f_st` (CGP08: `Θ_st` is
injective on the whole marked base, and `f_st(U_st) ⊆ V_st⁰`). -/
theorem final_eq_iff_BAS (B : Gaf02Bases C R) {st : Fin 3} {p p' : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st)
    (hp' : p' ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p') ↔
      C.stageMap_BAS st p = C.stageMap_BAS st p' := by
  rw [B.later.final_factor st p, B.later.final_factor st p']
  exact ⟨fun h => B.later.later_injOn st (C.stageMap_mem_markedBase_R74 st hp)
    (C.stageMap_mem_markedBase_R74 st hp') h, fun h => by rw [h]⟩

/-- **FC33, embedded bases `W_j ⊂ Q_j`** (restricted later images of the marked bases, marker
`> .9R_i`, coordinate thresholds `5.5`, `5.5Δ`, `5.5·10⁵Δ`, chart form of dimensions `2, 1, 1`):
`W_st ⊆ Q_st`, `W_st = Θ_st(V_st⁰)` with `V_st⁰` the union of the marked patches (explicit
thresholds), `Θ_st ∘ chart_j` smooth onto the open piece `W_st ∩ {marked j}` with the linear left
inverse `κ_j`, and the pieces cover `W_st`. -/
theorem fc33_bases_embedded_BAS (B : Gaf02Bases C R) :
    (∀ st, C.finalBase_BAS st ⊆ (gafStageQ P.toLocalChartFamily P.zero st : Set
      (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) ∧
    (∀ st, C.finalBase_BAS st = C.Θ_BAS st '' C.markedBase_BAS st) ∧
    (∀ j : P.toLocalChartFamily.circle.finite_centres.toFinset, C.circlePatch_BAS j =
      {w | w ∈ (C.slot 0).zeroSet ∧ 9 / 10 * ρ j.1 < gafCircleMarker P.toLocalChartPackets j w ∧
        ‖gafCircleVector P.toLocalChartPackets j w‖ < 11 / 2 * 1 * ρ j.1}) ∧
    (∀ j : P.edge.finite_centres.toFinset, C.edgePatch_BAS j =
      {w | w ∈ (C.slot 1).zeroSet ∧
        9 / 10 * ρ j.1 < gafEdgeMarker P.toLocalChartFamily P.zero j w ∧
        ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) w‖ <
          11 / 2 * Δ * ρ j.1}) ∧
    (∀ j : P.slim.finite_centres.toFinset, C.slimPatch_BAS j =
      {w | w ∈ (C.slot 2).zeroSet ∧
        9 / 10 * ρ j.1 < gafSlimMarker P.toLocalChartFamily P.zero j w ∧
        ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) w‖ <
          11 / 2 * (10 ^ 5 * Δ) * ρ j.1}) ∧
    (∀ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
      type_of% (B.circle.spec.base_chart j)) ∧
    (∀ j : P.edge.finite_centres.toFinset, type_of% (B.edge.spec.base_chart j)) ∧
    (∀ j : P.slim.finite_centres.toFinset, type_of% (B.slim.spec.base_chart j)) ∧
    type_of% B.circle.spec.cover ∧ type_of% B.edge.spec.cover ∧ type_of% B.slim.spec.cover :=
  ⟨B.finalBase_subset_stageQ_BAS, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun j => B.circle.spec.base_chart j, fun j => B.edge.spec.base_chart j,
    fun j => B.slim.spec.base_chart j, B.circle.spec.cover, B.edge.spec.cover,
    B.slim.spec.cover⟩

/-- **FC33, the bases are smooth manifolds of dimensions `2, 1, 1`**, embedded in the block space:
the chart-form manifold structures of the adapter `Gaf02Bases.toSmoothStageBases74` (models `ℝ²`,
`ℝ`, `ℝ`), with smooth inclusion of injective differential (an immersion; with the subspace
topology, a smooth embedding). -/
theorem fc33_bases_manifolds_BAS (B : Gaf02Bases C R) :
    type_of% B.toSmoothStageBases74.circle_isManifold ∧
      type_of% B.toSmoothStageBases74.edge_isManifold ∧
      type_of% B.toSmoothStageBases74.slim_isManifold :=
  ⟨B.toSmoothStageBases74.circle_isManifold, B.toSmoothStageBases74.edge_isManifold,
    B.toSmoothStageBases74.slim_isManifold⟩

/-- **FC33, `π_jE : U_j → W_j` is a submersion on the EXACT original thresholds**: `U_j` are open,
exactly `{‖η_j‖ < 5}` (circle), `{|η_j| < 5Δ, t < 5Δ}` (edge, including `η_{E'} < 5Δ`) and
`{|η_j| < 5·10⁵Δ}` (slim) on the charts' domains, `π_stE(U_st) ⊆ W_st`, and in the chart `κ_j` of
`W_st` the derivative of `π_stE` is onto at every point of `U_st` in chart `j`. -/
theorem fc33_submersions_BAS (B : Gaf02Bases C R) :
    (∀ st, IsOpen (gafStageDomain5_BAS P.toLocalChartPackets st)) ∧
    gafStageDomain5_BAS P.toLocalChartPackets 0 =
      {p | ∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
        p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5} ∧
    gafStageDomain5_BAS P.toLocalChartPackets 1 =
      {p | ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 5 * Δ ∧ cgpHeight P.toLocalChartFamily p < 5 * Δ} ∧
    gafStageDomain5_BAS P.toLocalChartPackets 2 =
      {p | ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
          5 * (10 ^ 5 * Δ)} ∧
    (∀ st, MapsTo (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p))
      (gafStageDomain5_BAS P.toLocalChartPackets st) (C.finalBase_BAS st)) ∧
    type_of% B.circle.spec.submersion ∧ type_of% B.edge.spec.submersion ∧
    type_of% B.slim.spec.submersion :=
  ⟨fun st => isOpen_gafStageDomain5_R74 P.toLocalChartPackets st, rfl, rfl, rfl,
    B.later.mapsTo_final, B.circle.spec.submersion, B.edge.spec.submersion,
    B.slim.spec.submersion⟩

/-- **FC33, KL 13.46 implemented**: tasks 1–2 for every marked patch (proper bijective local
coordinate onto the ball with smooth inverse, one sheet), exhaustion of the marked base by the
original threshold-6 plateau (preimages localized in the buffered chart), task 4 (no two sheets:
final values agree iff native values agree on `U_st`, `Θ_st` injective on the whole marked base). -/
theorem fc33_kl1346_BAS (B : Gaf02Bases C R) :
    (∀ j : P.toLocalChartFamily.circle.finite_centres.toFinset, type_of% (B.kl1346_circle_BAS j)) ∧
    (∀ j : P.edge.finite_centres.toFinset, type_of% (B.kl1346_edge_BAS j)) ∧
    (∀ j : P.slim.finite_centres.toFinset, type_of% (B.kl1346_slim_BAS j)) ∧
    (∀ (st : Fin 3) (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      w ∈ C.markedBase_BAS st → ∃ p, p ∈ gafStagePlateau_BAS P.toLocalChartPackets st ∧
        C.stageMap_BAS st p = w) ∧
    (∀ (st : Fin 3) (p p' : X), p ∈ gafStageDomain5_BAS P.toLocalChartPackets st →
      p' ∈ gafStageDomain5_BAS P.toLocalChartPackets st →
      ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p') ↔
          C.stageMap_BAS st p = C.stageMap_BAS st p')) ∧
    (∀ st, InjOn (C.Θ_BAS st) (C.markedBase_BAS st)) :=
  ⟨fun j => B.kl1346_circle_BAS j, fun j => B.kl1346_edge_BAS j, fun j => B.kl1346_slim_BAS j,
    fun st _ hw => B.exists_plateau_preimage_BAS st hw,
    fun _ _ _ hp hp' => B.final_eq_iff_BAS hp hp', B.later.later_injOn⟩

/-- **FC33, the later maps preserve kernels on CGP08's carriers** (GAF02's BASES sentence): the
kernel identification of G9 at every carrier point. -/
theorem fc33_kernels_BAS (B : Gaf02Bases C R) :
    ∀ (st : Fin 3) (p : X) (hp : p ∈ C.carrier_BAS st), type_of% (B.ker_final_eq_BAS st hp) :=
  fun st _ hp => B.ker_final_eq_BAS st hp

/-- **The FC33 row** on the bases object: with `c₃ < c_adjust`, the chain `C` and its bases object
`B` carry, on ONE chain and ONE rough datum, (1) FC33's first clause, (2) the embedded bases
`W_j ⊂ Q_j` of dimensions `2, 1, 1`, (3) the submersions `π_jE : U_j → W_j` on the exact original
thresholds, (4) KL 13.46's tasks (see `fc33_kl1346_BAS`), (5) the kernel identification. -/
theorem fc33_row_BAS (B : Gaf02Bases C R) {cadj : ℝ} (hc : c 2 < cadj) :
    type_of% (C.fc33_adjusted_RFC hc) ∧ type_of% B.fc33_bases_embedded_BAS ∧
      type_of% B.fc33_bases_manifolds_BAS ∧ type_of% B.fc33_submersions_BAS ∧
      type_of% B.fc33_kl1346_BAS ∧ type_of% B.fc33_kernels_BAS :=
  ⟨C.fc33_adjusted_RFC hc, B.fc33_bases_embedded_BAS, B.fc33_bases_manifolds_BAS,
    B.fc33_submersions_BAS, B.fc33_kl1346_BAS, B.fc33_kernels_BAS⟩

end Gaf02Bases

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The FC33 row on `(C, R)`**: the row at the producer's bases object `C.gaf02Bases_BAS R`
(hypotheses: the chain, its rough data and `c₃ < c_adjust`). -/
theorem fc33_row_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) {cadj : ℝ} (hc : c 2 < cadj) :
    type_of% ((C.gaf02Bases_BAS R).fc33_row_BAS hc) :=
  (C.gaf02Bases_BAS R).fc33_row_BAS hc

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
