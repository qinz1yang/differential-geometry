import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreSatBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSignedFunctionBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeTransverseBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspExitOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD

/-!
# BCF02 G4, group G3: the face function of a CUSP label (lane S-BCF02-G4)

For a cusp `i` of the boundary chain, a function `h : H → ℝ` on the ambient base space with

* `h` continuous on the edge base `B₂`;
* on `B₂`: `h y < 0 ⟺` the whole edge fibre lies in `int C_i` (the cusp core), `h y = 0 ⟺` it
  lies in the cusp front `H_i = ∂C_i`, `0 < h y ⟺` it lies in `C_iᶜ`;
* `h` is smooth on an open subset of `H` around every zero in `B₂` (it is the linear functional
  `φ_i = J_i¹ − 40 J_i²` of the base `H^∂` near the front, `cuspBaseCLM_OBD`);
* at every `p ∈ X₂` with `h (f₂ p) = 0`: `h ∘ f₂` is smooth, has non-zero differential, and
  `(d(h ∘ f₂), dT)` is onto `ℝ²` when `T = 4Δ`.

Route: `exists_signed_function_BG4` with `R = int C_i`, `P = H_i`, `O` the open `near` of
`cuspFnLink_OBD` (on which `F = u_i − 40 v_i` is smooth, regular at its zeros, the front is
`{F = 0}` and the core is `{F ≤ 0}`), `d = F`, `a = φ_i` (a continuous linear functional of `H`,
`φ_i ∘ f₂ = F` on all of `W` since every `π_j` keeps every boundary slot).
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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The face function of a cusp label** (see the module docstring). The numerics are those of
`frontier_M₁_BGR` / `cuspFnLink_OBD`. -/
theorem exists_cuspFaceFun_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    ∃ h : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
      ContinuousOn h (Bs.base 1) ∧
      (∀ y ∈ Bs.base 1,
        (h y < 0 ↔ Bs.fibre 1 y ⊆ interior (C.toChain.cuspCore_BIF i)) ∧
        (h y = 0 ↔ Bs.fibre 1 y ⊆ C.toChain.cuspFront_BIF i) ∧
        (0 < h y ↔ Bs.fibre 1 y ⊆ (C.toChain.cuspCore_BIF i)ᶜ)) ∧
      (∀ y ∈ Bs.base 1, h y = 0 → ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧ ContDiffOn ℝ ∞ h O) ∧
      (∀ p ∈ Bs.source 1, h (C.toChain.stageMap 1 p) = 0 →
        ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => h (C.toChain.stageMap 1 q)) p ∧
        mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 ∧
        (C.toChain.heightRatio p = 4 * Δ →
          Surjective fun v : TangentSpace W.model p =>
            (mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p v,
              mvfderiv W.model C.toChain.heightRatio p v))) := by
  classical
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  obtain ⟨near, -, hsm, hreg, hfront, hcore⟩ := C.cuspFnLink_OBD hrd hrd4 hrdc hprem hθ i
  let F : W.Carrier → ℝ := fun x =>
    chainBoundaryU_BCG6K C.toChain.E i x - 40 * chainBoundaryV_BCG6K C.toChain.E i x
  have hfront' : C.toChain.cuspFront_BIF i = {x | x ∈ near ∧ F x = 0} := hfront
  have hcore' : C.toChain.cuspCore_BIF i ∩ near = {x | x ∈ near ∧ F x ≤ 0} := hcore
  have hsm' : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ F near := hsm
  have hreg' : ∀ x ∈ near, F x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0 := hreg
  have hFa : ∀ p, cuspBaseCLM_OBD i (C.toChain.stageMap 1 p) = F p := fun p =>
    cuspBaseCLM_stageMap_OBD C.toChain 1 i p
  have hCc : IsClosed (C.toChain.cuspCore_BIF i) := (hcomp i).compact_core.isClosed
  have hF : frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i :=
    (hcomp i).relative_frontier_eq
  have hunion : interior (C.toChain.cuspCore_BIF i) ∪ C.toChain.cuspFront_BIF i =
      C.toChain.cuspCore_BIF i := by
    rw [← hF, ← closure_eq_interior_union_frontier, hCc.closure_eq]
  have hdisj : Disjoint (interior (C.toChain.cuspCore_BIF i)) (C.toChain.cuspFront_BIF i) := by
    rw [← hF]
    exact Set.disjoint_left.mpr fun x hx hxf => hxf.2 hx
  have hint_iff : ∀ p ∈ near, p ∈ interior (C.toChain.cuspCore_BIF i) ↔ F p < 0 := by
    intro p hpn
    constructor
    · intro hp
      have hpc : p ∈ C.toChain.cuspCore_BIF i ∩ near := ⟨interior_subset hp, hpn⟩
      rw [hcore'] at hpc
      have hle : F p ≤ 0 := hpc.2
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hpf : p ∈ C.toChain.cuspFront_BIF i := by
          rw [hfront']
          exact ⟨hpn, heq⟩
        rw [← hF] at hpf
        exact hpf.2 hp
    · intro hp
      have hopen : IsOpen {x | x ∈ near ∧ F x < 0} :=
        hsm'.continuousOn.isOpen_inter_preimage near.isOpen isOpen_Iio
      have hsub : {x | x ∈ near ∧ F x < 0} ⊆ C.toChain.cuspCore_BIF i := by
        intro x hx
        have : x ∈ C.toChain.cuspCore_BIF i ∩ near := by
          rw [hcore']
          exact ⟨hx.1, le_of_lt hx.2⟩
        exact this.1
      exact interior_maximal hsub hopen ⟨hpn, hp⟩
  have hface_iff : ∀ p ∈ near, p ∈ C.toChain.cuspFront_BIF i ↔ F p = 0 := by
    intro p hpn
    rw [hfront']
    exact ⟨fun h => h.2, fun h => ⟨hpn, h⟩⟩
  -- the dichotomy of the whole edge disks
  have hdich : ∀ y ∈ Bs.base 1,
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ interior (C.toChain.cuspCore_BIF i) ∨
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ C.toChain.cuspFront_BIF i ∨
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆
        (interior (C.toChain.cuspCore_BIF i) ∪ C.toChain.cuspFront_BIF i)ᶜ := by
    intro y hy
    by_cases hmeet : ∃ q ∈ Bs.fibre 1 y, q ∈ C.toChain.cuspFront_BIF i
    · obtain ⟨q, hq, hqf⟩ := hmeet
      refine Or.inr (Or.inl fun q' hq' => ?_)
      have hq1 : C.toChain.stageMap 1 q' = C.toChain.stageMap 1 q := by
        rw [show C.toChain.stageMap 1 q' = y from hq'.2, show C.toChain.stageMap 1 q = y from hq.2]
      exact C.toChain.cuspFront_saturated_BIF 1 i hqf hq1
    · push Not at hmeet
      have hpre := C.isPreconnected_edgeFibre_BG4 WF hy
      have hcov : Bs.fibre 1 y ⊆ interior (C.toChain.cuspCore_BIF i) ∪
          (C.toChain.cuspCore_BIF i)ᶜ := by
        intro q hq
        by_cases hqi : q ∈ interior (C.toChain.cuspCore_BIF i)
        · exact Or.inl hqi
        · refine Or.inr fun hqZ => ?_
          apply hmeet q hq
          rw [← hF]
          exact ⟨subset_closure hqZ, hqi⟩
      have hdj : Disjoint (interior (C.toChain.cuspCore_BIF i)) (C.toChain.cuspCore_BIF i)ᶜ :=
        Set.disjoint_left.mpr fun x hx hxc => hxc (interior_subset hx)
      rcases hpre.subset_or_subset isOpen_interior hCc.isOpen_compl hdj hcov with h | h
      · exact Or.inl h
      · refine Or.inr (Or.inr fun q hq hq' => ?_)
        rcases hq' with h1 | h1
        · exact h hq (interior_subset h1)
        · exact hmeet q hq h1
  have hf₂ : Continuous (C.toChain.stageMap 1) := (C.stageMap_contMDiff_BAUGD 1).continuous
  have hfrontnear : C.toChain.cuspFront_BIF i ⊆ near := fun p hp => (hfront' ▸ hp).1
  obtain ⟨h, hcont, hsign, hsm2⟩ := exists_signed_function_BG4 (X := Bs.source 1)
    (f := C.toChain.stageMap 1) (B := Bs.base 1) hf₂.continuousOn (Bs.image_eq 1) (Bs.proper 1)
    (R := interior (C.toChain.cuspCore_BIF i)) (P := C.toChain.cuspFront_BIF i)
    isOpen_interior (by rw [hunion]; exact hCc) hdisj hdich (O := (near : Set W.Carrier))
    near.isOpen (fun p hp => hfrontnear hp.1)
    (a := fun z => cuspBaseCLM_OBD i z) (d := F) (Ω := univ) isOpen_univ
    (cuspBaseCLM_OBD i).continuous.continuousOn (fun _ _ => mem_univ _)
    (fun p _ => hFa p) (fun p hp => hint_iff p hp.1) (fun p hp => hface_iff p hp.1)
  rw [hunion] at hsign
  refine ⟨h, hcont, hsign, ?_, ?_⟩
  · intro y hy h0
    obtain ⟨V, hVo, hyV, hVeq⟩ := hsm2 y hy ((hsign y hy).2.1.mp h0)
    exact ⟨V, hVo, hyV, (cuspBaseCLM_OBD i).contDiff.contDiffOn.congr fun z hz => hVeq z hz⟩
  · intro p hp h0
    have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp
    have hfib : Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {C.toChain.stageMap 1 p} ⊆
        C.toChain.cuspFront_BIF i := (hsign _ hy).2.1.mp h0
    have hpf : p ∈ C.toChain.cuspFront_BIF i := hfib ⟨hp, rfl⟩
    have hpn : p ∈ near := hfrontnear hpf
    obtain ⟨V, hVo, hyV, hVeq⟩ := hsm2 _ hy hfib
    have hheq : (fun q => h (C.toChain.stageMap 1 q)) =ᶠ[𝓝 p] F := by
      filter_upwards [(hVo.preimage hf₂).mem_nhds hyV] with q hqV
      rw [hVeq _ hqV]
      exact hFa q
    have hF0 : F p = 0 := (hface_iff p hpn).mp hpf
    have hreg2 : mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 := by
      rw [mvfderiv_congr_nhds_BG4 hheq]
      exact mvfderiv_ne_zero_iff_BCG6K.mpr (hreg' p hpn hF0)
    refine ⟨(hsm'.contMDiffAt (near.isOpen.mem_nhds hpn)).congr_of_eventuallyEq hheq, hreg2,
      fun hT => ?_⟩
    have hhd : DifferentiableAt ℝ h (C.toChain.stageMap 1 p) :=
      ((cuspBaseCLM_OBD i).differentiableAt).congr_of_eventuallyEq
        (Filter.mem_of_superset (hVo.mem_nhds hyV) fun z hz => hVeq z hz)
    exact C.surjective_comp_height_BG4 (Bs.source_one_subset_edgeParent_BIFc hp) hT hhd hreg2

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
