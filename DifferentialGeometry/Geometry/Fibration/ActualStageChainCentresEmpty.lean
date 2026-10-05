import DifferentialGeometry.Geometry.Fibration.ActualStageChainLater

/-!
# GAF02 BASES on an empty stage, independent of the slot's constructor (review 71, D71-11)

Review 71 (D71-11, binding): `.active` on an empty family is allowed; the adjustment is the identity
by the CUTOFF / empty-family theorem (not by "`Z = ∅`"), the native zero set is empty because the
stage cloud is; BASES indexes patches and charts by ACTUAL centre membership and has
`B⁶_st = U_st = V⁰_st = W_st = ∅` on an empty stage. No statement below mentions the slot's
constructor; consumers never branch on it.

For `gafStageCentres P st = ∅` (the stage's centre family is empty), on any chain `C`:

* `stageCutoff_eq_zero_of_centres_empty_BASP`: `ψ_{st+1}(g_st p) = 0` for every `p` (CFS16: a
  nonzero cutoff puts `π_st𝓔⁰ p` in the stage cloud, which is empty);
* **`stageOut_eq_stageIn_of_centres_empty_BASP`**: `g_{st+1} = g_st`;
  `stageMap_of_centres_empty_BASP`: `f_st = π_st ∘ g_st`;
* `zeroSet_subset_tube_BASP` (every stage): each point of the slot's zero set lies in a selected
  ball `B(y, 20Ξ⁻¹r_y)` of a cloud point `y`; hence `zeroSet_eq_empty_of_centres_empty_BASP`;
* `markedPatch_eq_empty_of_centres_empty_BASP` (every marked patch on the zero set, any coordinate,
  marker, scale and range: `V⁰ = ∅`), `markedBase_subset_zeroSet_BASP`,
  `markedBase_eq_empty_of_centres_empty_BASP` (`V⁰_st = ⋃_j V_j⁰ = ∅`),
  `finalBase_eq_empty_of_centres_empty_BASP` (`W_st = Θ_st(V⁰_st) = ∅`);
* `plateau_eq_empty_of_centres_empty_BASP` (`B⁶_st = ∅`), `domain5_eq_empty_of_centres_empty_BASP`
  (`U_st = ∅`), `rfDomain_eq_empty_of_centres_empty_BASP` (`D_st = B⁶_st ∩ f_st⁻¹(V⁰_st) = ∅`).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **`B⁶_st = ∅` on an empty stage** (the original threshold-6 plateau is indexed by the stage's
actual centres). -/
theorem plateau_eq_empty_of_centres_empty_BASP (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K
    σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) {st : Fin 3} (h : gafStageCentres P st = ∅) :
    gafStagePlateau_BAS P st = ∅ :=
  Gaf02Chain.plateau_eq_empty_of_inactive_BAS h

/-- **`U_st = ∅` on an empty stage** (FC33's threshold-5 domains are indexed by the stage's actual
centres). -/
theorem domain5_eq_empty_of_centres_empty_BASP (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K
    σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) {st : Fin 3} (h : gafStageCentres P st = ∅) :
    gafStageDomain5_BAS P st = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  fin_cases st
  · obtain ⟨j, -⟩ := hp
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h' : P.circle.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj
  · obtain ⟨j, -⟩ := hp
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h' : P.edge.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj
  · obtain ⟨j, -⟩ := hp
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h' : P.slim.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The stage cutoff vanishes on an empty stage** (CFS16 contrapositive: a nonzero cutoff
`ψ_{st+1}(g_st p)` puts `π_st𝓔⁰ p` in the stage cloud, which is empty). -/
theorem stageCutoff_eq_zero_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    {st : Fin 3} (h : gafStageCentres P st = ∅) (p : X) :
    gafStageCutoff_BAS P st (C.stageIn_BAS st p) = 0 := by
  by_contra hne
  have hx := (C.stage_input_mem_omega_BAS hne).1
  rw [gafCloud_eq_empty_GAF8 P h] at hx
  exact hx

/-- **An empty stage is an identity stage** (D71-11, by the cutoff, for ANY slot):
`g_{st+1} = g_st`. -/
theorem stageOut_eq_stageIn_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    {st : Fin 3} (h : gafStageCentres P st = ∅) : C.stageOut_BAS st = C.stageIn_BAS st := by
  funext p
  rw [C.stageOut_eq_adjust_BAS st p, adjustmentMap_apply,
    C.stageCutoff_eq_zero_of_centres_empty_BASP h p, zero_smul, add_zero]

/-- On an empty stage the stage map is the projected stage input: `f_st = π_st ∘ g_st`. -/
theorem stageMap_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (h : gafStageCentres P st = ∅) (p : X) :
    C.stageMap_BAS st p =
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.stageIn_BAS st p) := by
  unfold stageMap_BAS
  rw [C.stageOut_eq_stageIn_of_centres_empty_BASP h]

/-- **The native zero set lies in the selected balls over the stage cloud** (every stage, every
slot): `w ∈ Z_st ⇒ w ∈ B(y, 20Ξ_st⁻¹r_y)` for a cloud point `y`. -/
theorem zeroSet_subset_tube_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ (C.slot st).zeroSet) :
    ∃ y ∈ gafCloud P.toLocalChartFamily P.zero st,
      w ∈ ball y (20 * (Ξ st)⁻¹ * (S st * ρ (C.sel st y))) := by
  cases hO : C.slot st with
  | active O =>
    rw [hO, Gaf02StageSlot.zeroSet_active] at hw
    obtain ⟨y, hy, hwy⟩ := exists_selected_mem_ball_BAS O hw
    exact ⟨y, O.I_subset hy, hwy⟩
  | inactive h =>
    rw [hO] at hw
    exact absurd hw (Set.notMem_empty w)

/-- **The native zero set of an empty stage is empty** (C2's reading of D71-11: empty stage cloud
⇒ empty zero set, for any slot). -/
theorem zeroSet_eq_empty_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    (h : gafStageCentres P st = ∅) : (C.slot st).zeroSet = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
  obtain ⟨y, hy, -⟩ := C.zeroSet_subset_tube_BASP st hw
  rw [gafCloud_eq_empty_GAF8 P h] at hy
  exact hy

/-- **Every marked patch of an empty stage is empty** (`V⁰ = ∅` for any coordinate, marker, scale
and range). -/
theorem markedPatch_eq_empty_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    {st : Fin 3} (h : gafStageCentres P st = ∅) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (u : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] E)
    (v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) (R ℓ : ℝ) :
    markedPatch_BPRE (C.slot st).zeroSet u v R ℓ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
  have hw' : w ∈ (C.slot st).zeroSet := hw.1
  rw [C.zeroSet_eq_empty_of_centres_empty_BASP h] at hw'
  exact hw'

/-- The marked base `V⁰_st = ⋃_j V_j⁰` lies in the stage's native zero set (every stage). -/
theorem markedBase_subset_zeroSet_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    C.markedBase_BAS st ⊆ (C.slot st).zeroSet := by
  fin_cases st
  · change (⋃ j, C.circlePatch_BAS j) ⊆ (C.slot 0).zeroSet
    exact Set.iUnion_subset fun j w hw => hw.1
  · change (⋃ j, C.edgePatch_BAS j) ⊆ (C.slot 1).zeroSet
    exact Set.iUnion_subset fun j w hw => hw.1
  · change (⋃ j, C.slimPatch_BAS j) ⊆ (C.slot 2).zeroSet
    exact Set.iUnion_subset fun j w hw => hw.1

/-- **`V⁰_st = ∅` on an empty stage.** -/
theorem markedBase_eq_empty_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    {st : Fin 3} (h : gafStageCentres P st = ∅) : C.markedBase_BAS st = ∅ :=
  Set.eq_empty_of_subset_empty
    ((C.markedBase_subset_zeroSet_BASP st).trans (C.zeroSet_eq_empty_of_centres_empty_BASP h).le)

/-- **`W_st = Θ_st(V⁰_st) = ∅` on an empty stage.** -/
theorem finalBase_eq_empty_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    {st : Fin 3} (h : gafStageCentres P st = ∅) : C.finalBase_BAS st = ∅ := by
  unfold finalBase_BAS
  rw [C.markedBase_eq_empty_of_centres_empty_BASP h, Set.image_empty]

/-- **The RF domain `D_st = B⁶_st ∩ f_st⁻¹(V⁰_st)` is empty on an empty stage.** -/
theorem rfDomain_eq_empty_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    {st : Fin 3} (h : gafStageCentres P st = ∅) :
    gafStagePlateau_BAS P st ∩ C.stageMap_BAS st ⁻¹' C.markedBase_BAS st = ∅ := by
  rw [plateau_eq_empty_of_centres_empty_BASP P h, Set.empty_inter]

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
