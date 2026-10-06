import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspExitOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityContributorBGR

/-!
# BCG07 clause 07.g3: the cusp equation of the base boundary (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3b. Blueprint BCG07 [B:9471–9580], clause g3: the
relative base domain `D_j` has smooth boundary "whose cusp equation is `u_b/v_b − 40 = 0`; near a
cusp frontier the base function pulls back to the BCG06 defining function, base differential
`≠ 0`" (S-BCG-ROWS3 clause table: no Lean target in v3.1 §F).

Every stage projection `π_j` keeps EVERY boundary slot (`stageProj_inr_BGR`), so the cusp
coordinates `(u_b, v_b) = J_b(E)` factor through every stage map `f_j = π_j ∘ E`. The BASE CUSP
FUNCTION is the continuous linear functional `φ_b = J_b¹ − 40 J_b²` on the ambient base `H^∂`:

* `cuspBaseCLM_stageMap_OBD`: `φ_b ∘ f_j = u_b − 40 v_b` on the WHOLE carrier, every stage;
* **`BoundaryGaf02ChainE.cuspBase_equation_OBD`** (E4b premises): at every point `p` of the cusp
  front `H_b`, `φ_b (f_j p) = 0`, the BASE differential is nonzero
  (`φ_b ∘ df_j(p) ≠ 0`, i.e. `φ_b` is nonzero on the tangent image of the base at `f_j p`), and
  near `p` the cusp equation reads `u_b/v_b − 40 = φ_b ∘ f_j` (`v_b ≡ 1` near the front, BCG06).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `J_b²` read as a continuous linear functional: the marker coordinate of the slot of `b`. -/
def chainBoundaryVCLM_OBD (b : κ) : BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ² ℝ).comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ : WithLp 2 (ℝ² × ℝ) ≃L[ℝ] ℝ² × ℝ) :
      WithLp 2 (ℝ² × ℝ) →L[ℝ] ℝ² × ℝ).comp
      (PiLp.proj 2 (fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)) (Sum.inr b)))

/-- **The base cusp function** `φ_b = J_b¹ − 40 J_b²` on the ambient base. -/
def cuspBaseCLM_OBD (b : κ) : BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] ℝ :=
  chainBoundaryUCLM_BCG6K b - (40 : ℝ) • chainBoundaryVCLM_OBD b

omit [Fintype ι] [Fintype κ] in
/-- `φ_b y = (J_b y).1 − 40 (J_b y).2`. -/
theorem cuspBaseCLM_apply_OBD (b : κ) (y : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    cuspBaseCLM_OBD b y =
      (augmentedBoundaryCoord_BC7C b y).1 - 40 * (augmentedBoundaryCoord_BC7C b y).2 :=
  rfl

/-- A linear functional composed with a map: if the composite has nonzero differential, the
functional is nonzero on the image of the differential. -/
theorem clm_comp_mfderiv_ne_zero_OBD {EM HM M F : Type*} [NormedAddCommGroup EM]
    [NormedSpace ℝ EM] [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M]
    [ChartedSpace HM M] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M → F} (L : F →L[ℝ] ℝ)
    {p : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f p) (h : mfderiv I 𝓘(ℝ, ℝ) (L ∘ f) p ≠ 0) :
    L.comp (mfderiv I 𝓘(ℝ, F) f p) ≠ 0 := by
  have h1 := mfderiv_comp p L.mdifferentiableAt hf
  rw [L.mfderiv_eq] at h1
  intro h0
  apply h
  rw [h1]
  exact h0

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The base cusp function pulls back to the BCG06 defining function** on the whole carrier,
through every stage map (`π_j` keeps every boundary slot). -/
theorem cuspBaseCLM_stageMap_OBD (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (st : Fin 3) (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    cuspBaseCLM_OBD i (C.stageMap st p) =
      chainBoundaryU_BCG6K C.E i p - 40 * chainBoundaryV_BCG6K C.E i p := by
  rw [cuspBaseCLM_apply_OBD]
  simp only [augmentedBoundaryCoord_BC7C, BoundaryGaf02Chain.stageMap, Φ.stageProj_inr_BGR]
  rfl

end Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Every stage map of the chain is smooth. -/
theorem contMDiff_stageMap_OBD (st : Fin 3) :
    ContMDiff W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      (C.toChain.stageMap st) :=
  ((actualSlotsV2_BAUGD S).stageProj st).contDiff.comp_contMDiff (C.stage_smooth_BAUGD 3)

/-- The base cusp function vanishes on the stage image of the front. -/
theorem cuspBase_front_zero_OBD (st : Fin 3) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) : cuspBaseCLM_OBD i (C.toChain.stageMap st p) = 0 := by
  have hfr : chainBoundaryU_BCG6K C.toChain.E i p = 40 * chainBoundaryV_BCG6K C.toChain.E i p :=
    hp.2
  rw [cuspBaseCLM_stageMap_OBD C.toChain st i p, hfr, sub_self]

/-- The composite `φ_b ∘ f_j` is the function `u_b − 40 v_b`. -/
theorem cuspBase_comp_stageMap_OBD (st : Fin 3) (i : Fin S.packet.cusp.count) :
    (cuspBaseCLM_OBD i ∘ C.toChain.stageMap st) =
      fun q => chainBoundaryU_BCG6K C.toChain.E i q - 40 * chainBoundaryV_BCG6K C.toChain.E i q :=
  funext (cuspBaseCLM_stageMap_OBD C.toChain st i)

/-- **The base differential is nonzero** at the front (E4b premises): `φ_b ∘ df_j(p) ≠ 0`. -/
theorem cuspBase_differential_ne_zero_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (st : Fin 3) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) :
    (cuspBaseCLM_OBD i).comp
        (mfderiv W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
          (C.toChain.stageMap st) p) ≠ 0 := by
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hne : mfderiv W.model 𝓘(ℝ, ℝ) (fun q => chainBoundaryU_BCG6K C.toChain.E i q -
      40 * chainBoundaryV_BCG6K C.toChain.E i q) p ≠ 0 :=
    hspec.defining_differential_ne_zero i p hp
  rw [← C.cuspBase_comp_stageMap_OBD st i] at hne
  exact clm_comp_mfderiv_ne_zero_OBD (cuspBaseCLM_OBD i)
    ((C.contMDiff_stageMap_OBD st).mdifferentiableAt (by simp)) hne

/-- **The cusp equation near the front** (E4b premises): `u_b/v_b − 40 = φ_b ∘ f_j` near `p`
(`v_b ≡ 1` near the front). -/
theorem cuspBase_ratio_near_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (st : Fin 3) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) :
    ∀ᶠ q in 𝓝 p, chainBoundaryU_BCG6K C.toChain.E i q / chainBoundaryV_BCG6K C.toChain.E i q -
      40 = cuspBaseCLM_OBD i (C.toChain.stageMap st q) := by
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  filter_upwards [hspec.marker_eq_one_near_front i p hp] with q hq
  rw [cuspBaseCLM_stageMap_OBD C.toChain st i q, hq, div_one, mul_one]

/-- **BCG07 07.g3, the cusp equation of the base boundary** (E4b premises): at every point `p`
of the cusp front `H_b` and every stage `j`, the base cusp function vanishes at `f_j p`, its
BASE differential is nonzero (`φ_b ∘ df_j(p) ≠ 0`), and near `p` the cusp equation
`u_b/v_b − 40` is `φ_b ∘ f_j`. -/
theorem cuspBase_equation_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (st : Fin 3) (i : Fin S.packet.cusp.count) :
    ∀ p ∈ C.toChain.cuspFront_BIF i, cuspBaseCLM_OBD i (C.toChain.stageMap st p) = 0 ∧
      (cuspBaseCLM_OBD i).comp
          (mfderiv W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
            (C.toChain.stageMap st) p) ≠ 0 ∧
      ∀ᶠ q in 𝓝 p, chainBoundaryU_BCG6K C.toChain.E i q / chainBoundaryV_BCG6K C.toChain.E i q -
          40 = cuspBaseCLM_OBD i (C.toChain.stageMap st q) := fun _ hp =>
  ⟨C.cuspBase_front_zero_OBD st i hp,
    C.cuspBase_differential_ne_zero_OBD hrd hrd4 hrdc hprem hθ st i hp,
    C.cuspBase_ratio_near_OBD hrd hrd4 hrdc hprem hθ st i hp⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
