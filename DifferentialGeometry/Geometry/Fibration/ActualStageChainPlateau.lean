import DifferentialGeometry.Geometry.Fibration.ActualStageChain

/-!
# GAF02 BASES, first step: native landing (PLAT) on the chain object

Blueprint `master207B.tex`, GAF02 (B:5797–5870) and CGP07/CGP08 (B:4176–4316); external draft 59
§4 "第一步" (disposition D59-5). Everything is indexed by ONE chain `C : Gaf02Chain P …`; no
plane, nearest map, cutoff or `E` is chosen again.

Stage `st ∈ {0, 1, 2}` (circle, edge, slim) of the chain has input `g_{st}` (`g₀ = 𝓔⁰`), output
`g_{st+1} = Ψ_{st+1} ∘ g_{st}` (`g₃ = E`), cutoff `ψ_{st+1}` (CFS31: source, CFS23, CFS22), target
`Q_st` and stage map `f_st = π_{Q_st} ∘ g_{st+1}`.

* `Gaf02StageSlot.zeroSet`: the native zero set `Z_st` of an active slot, `∅` for an inactive one.
* `gafStageCutoff_BAS`, `Gaf02Chain.stageIn_BAS`, `Gaf02Chain.stageOut_BAS`,
  `Gaf02Chain.stageMap_BAS` (`f_st`), `gafStagePlateau_BAS` (the ORIGINAL threshold-6 plateau
  `B⁶_st` of CFS31: `|η_j| < 6` on circles, `|η_j| < 6Δ` and `t < 6Δ` on edges,
  `|η_j| < 6·10⁵Δ` on slims), `gafStagePlateauAt_BAS` (one reference).
* `Gaf02Chain.stageOut_eq_adjust_BAS` (ADJ, CHAIN in stage form),
  `Gaf02Chain.cutoff_eq_one_of_plateau_BAS`, `Gaf02Chain.stage_input_mem_omega_BAS`
  (CFS16: the stage input lies in `Ω_st`), `Gaf02Chain.cloud_subset_stageQ_BAS`,
  `Gaf02Chain.plane_le_stageQ_BAS`.
* **(PLAT)** `Gaf02Chain.plat_BAS`: on `B⁶_st`, for an active slot `O`,
  `f_st(p) = P_st(π_st g_st p) = ι_st p_st(π_st g_st p) ∈ Z_st` (PNATIVE of the SAME output);
  `Gaf02Chain.plat_mem_zeroSet_BAS`.
* `Gaf02Chain.stageMap_contMDiff_BAS`; inactive branch: `Gaf02Chain.plateau_eq_empty_of_inactive_BAS`
  (empty source domain), `Gaf02Chain.stageOut_eq_stageIn_of_inactive_BAS` (`Ψ = id`).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02StageSlot

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {st : Fin 3} {Kj : ℕ} {sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X}
  {plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
    Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
  {Ξ sg cw : ℝ}

/-- The native zero set `Z_st` of a slot: the output's zero set (active), `∅` (inactive). -/
def zeroSet : Gaf02StageSlot P st Kj sel plane Ξ sg cw →
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
  | .active O => O.Z
  | .inactive _ => ∅

theorem zeroSet_active (O : Cfs15StageOutput (gafStageDim st) Kj Ξ cw
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    (fun x => sg * ρ (sel x)) plane) :
    (Gaf02StageSlot.active O : Gaf02StageSlot P st Kj sel plane Ξ sg cw).zeroSet = O.Z := rfl

end Gaf02StageSlot

/-- The three actual CFS31 cutoffs `ψ₁` (source), `ψ₂` (CFS23), `ψ₃` (CFS22), by stage. -/
def gafStageCutoff_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) (st : Fin 3) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ :=
  ![markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P),
    gafStageTwoCutoff P.toLocalChartFamily P.zero, gafStageThreeCutoff P.toLocalChartFamily P.zero]
    st

/-- The ORIGINAL threshold-6 plateaux `B⁶_st` of CFS31 (circle: `|η_j| < 6` on `B(c_j, 200ρ_j)`;
edge: `|η_j| < 6Δ`, `t < 6Δ` on `B(c_j, 100Δρ_j)`; slim: `|η_j| < 6·10⁵Δ` on `B(c_j, 10⁶Δρ_j)`). -/
def gafStagePlateau_BAS (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) (st : Fin 3) : Set X :=
  ![{p | ∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
        p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6},
    {p | ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ},
    {p | ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)}]
    st

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The stage inputs `g₀ = 𝓔⁰`, `g₁`, `g₂`. -/
def stageIn_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  ![cgpGlobalMap P.toLocalChartFamily P.zero, C.g₁, C.g₂] st

/-- The stage outputs `g₁`, `g₂`, `g₃ = E`. -/
def stageOut_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  ![C.g₁, C.g₂, C.E] st

/-- The stage maps `f_st = π_{Q_st} ∘ g_{st+1}` (never identified with `π_{Q_st} ∘ E`). -/
def stageMap_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.stageOut_BAS st p)

/-- (ADJ) and (CHAIN) in stage form: `g_{st+1} = Ψ_{st+1} ∘ g_st`,
`Ψ_{st+1} = adjustmentMap Q_st (π_{Q_st} ∘ a_st) ψ_{st+1}` with `a_st` the slot's map. -/
theorem stageOut_eq_adjust_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) (p : X) :
    C.stageOut_BAS st p = adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.slot st).map y))
      (gafStageCutoff_BAS P st) (C.stageIn_BAS st p) := by
  fin_cases st <;> rfl

/-- **The plateau** (CFS31 at the chain's own stage inputs): on `B⁶_st`, `ψ_{st+1}(g_st p) = 1`. -/
theorem cutoff_eq_one_of_plateau_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3} {p : X}
    (hp : p ∈ gafStagePlateau_BAS P st) : gafStageCutoff_BAS P st (C.stageIn_BAS st p) = 1 := by
  have cb := C.cutoff_bindings
  fin_cases st
  · exact cb.1.2.2.1 p hp
  · exact cb.2.1.2.2.1 p hp
  · exact cb.2.2.2.2.1 p hp

/-- **CFS16 at the chain** (`stage_input_mem_tube`): if `ψ_{st+1}(g_st p) ≠ 0` then
`x = π_st 𝓔⁰ p ∈ S_st` and `π_st g_st p ∈ B(x, Σ_st ρ(sel_st x))`, so `π_st g_st p ∈ Ω_st`. -/
theorem stage_input_mem_omega_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3} {p : X}
    (hp : gafStageCutoff_BAS P st (C.stageIn_BAS st p) ≠ 0) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st ∧
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.stageIn_BAS st p) ∈
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))
          (S st * ρ (C.sel st ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p)))) ∧
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.stageIn_BAS st p) ∈
        cfs15Omega_C15 (gafCloud P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x)) := by
  have hsupp : C.stageIn_BAS st p ∈ tsupport (gafStageCutoff_BAS P st) :=
    subset_tsupport _ (Function.mem_support.mpr hp)
  have key : (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st ∧
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.stageIn_BAS st p) ∈
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))
          (S st * ρ (C.sel st ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p)))) := by
    have tube := C.stage_input_mem_tube p
    fin_cases st
    · exact tube.1 hsupp
    · exact tube.2.1 hsupp
    · exact tube.2.2 hsupp
  exact ⟨key.1, key.2, mem_cfs15Omega_of_mem_C15 key.1 key.2⟩

/-- Every stage cloud point lies in `Q_st`. -/
theorem cloud_subset_stageQ_BAS (st : Fin 3) :
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, x ∈ gafStageQ P.toLocalChartFamily P.zero st := by
  rintro x ⟨q, -, rfl⟩
  rw [← gafStageQ_starProjection_globalMap]
  exact Submodule.starProjection_apply_mem _ _

/-- The chain's planes lie in `Q_st` (the stage tests' first clause). -/
theorem plane_le_stageQ_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
      C.plane st x ≤ gafStageQ P.toLocalChartFamily P.zero st := by
  intro x hx
  fin_cases st
  · exact (C.test0.1 x hx).2
  · exact (C.test1.1 x hx).2
  · exact (C.test2.1 x hx).2

/-- `π_Q(y + (π_Q a − π_Q y)) = π_Q a` (the plateau value of an adjustment). -/
theorem starProjection_adjust_of_one_BAS {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (a : H → H)
    (ψ : H → ℝ) {y : H} (hψ : ψ y = 1) :
    Q.starProjection (adjustmentMap Q (fun z => Q.starProjection (a z)) ψ y) =
      Q.starProjection (a (Q.starProjection y)) := by
  rw [adjustmentMap_apply, hψ, one_smul, map_add, map_sub,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem Q _),
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem Q _)]
  abel

/-- **(PLAT)** (draft 59 §4 first step): on the original threshold-6 plateau `B⁶_st`, for an
active slot `O`, `π_st g_st p ∈ Ω_st` and
`f_st(p) = P_st(π_st g_st p) = ι_st p_st(π_st g_st p) ∈ Z_st` (PNATIVE of the SAME output). -/
theorem plat_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    {O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st) (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x))
      (C.plane st)}
    (hO : C.slot st = .active O) {p : X} (hp : p ∈ gafStagePlateau_BAS P st) :
    ∃ hz : (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.stageIn_BAS st p) ∈
        cfs15Omega_C15 (gafCloud P.toLocalChartFamily P.zero st) (fun x => S st * ρ (C.sel st x)),
      C.stageMap_BAS st p = (O.p ⟨_, hz⟩ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily
        P.zero => ℝ²)) ∧ C.stageMap_BAS st p ∈ O.Z := by
  have h1 := C.cutoff_eq_one_of_plateau_BAS hp
  have hz := (C.stage_input_mem_omega_BAS (st := st) (p := p) (by rw [h1]; exact one_ne_zero)).2.2
  refine ⟨hz, ?_⟩
  have hval : C.stageMap_BAS st p = (O.p ⟨_, hz⟩ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²)) := by
    rw [stageMap_BAS, C.stageOut_eq_adjust_BAS st p,
      starProjection_adjust_of_one_BAS _ (C.slot st).map _ h1, hO]
    exact O.projected_nearest_eq_native _ (cloud_subset_stageQ_BAS st) (C.plane_le_stageQ_BAS st)
      _ hz
  refine ⟨hval, ?_⟩
  rw [hval]
  exact (O.p ⟨_, hz⟩).2

/-- (PLAT) in slot form: `f_st(B⁶_st) ⊆ Z_st` (an inactive slot has an empty plateau). -/
theorem plat_mem_zeroSet_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3} {p : X}
    (hp : p ∈ gafStagePlateau_BAS P st) : C.stageMap_BAS st p ∈ (C.slot st).zeroSet := by
  cases hO : C.slot st with
  | active O =>
    exact (C.plat_BAS hO hp).2.2
  | inactive h =>
    exfalso
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

/-- The stage maps are smooth (`g_{st+1}` smooth, CORE). -/
theorem stageMap_contMDiff_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (C.stageMap_BAS st) := by
  have hout : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
      ℝ²)) ∞ (C.stageOut_BAS st) := by
    have hs := C.stage_smooth
    fin_cases st
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2
  exact (gafStageQ P.toLocalChartFamily P.zero st).starProjection.contDiff.contMDiff.comp hout

/-- An inactive stage has an EMPTY original plateau (draft 59 §3.5: the submersion claim lives
only on this empty source domain). -/
theorem plateau_eq_empty_of_inactive_BAS {st : Fin 3} (h : gafStageCentres P st = ∅) :
    gafStagePlateau_BAS P st = ∅ := by
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

/-- An inactive slot is an identity stage: `g_{st+1} = g_st`. -/
theorem stageOut_eq_stageIn_of_inactive_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {st : Fin 3}
    {h : gafStageCentres P st = ∅} (hO : C.slot st = .inactive h) (p : X) :
    C.stageOut_BAS st p = C.stageIn_BAS st p := by
  have hid := C.inactive_stage_id
  fin_cases st
  · change C.Ψ₁ _ = _
    rw [hid.1 h hO]
    rfl
  · change C.Ψ₂ _ = _
    rw [hid.2.1 h hO]
    rfl
  · change C.Ψ₃ _ = _
    rw [hid.2.2 h hO]
    rfl

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
