import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsOfChainBGR

/-!
# BD0, defining-function part: `cuspFn` and `near` of the cusp cores (S-BCG-ROWS2 G26)

`CuspCores.cuspFn / near / near_interior / fn_smooth / fn_regular / internal_eq / near_eq` (draft 74
§3.2): on the enhanced chain `C` the global defining function of the core `C_b = {G ≤ 40}`
(`cuspCore_eq_BCG6K`) is `G − 40` with `G = coreLevel_BCG6K b (u_b)` smooth on `W` and REGULAR on
`{G ≤ 40}` (`mfderiv_coreLevel_ne_zero_BCG6K`); the open neighbourhood `near_b = {39 < G < 41} ∩ W°`
of the front (interior points: `mem_strip_of_mem_front_BCG6K`) carries
`front = {near ∧ G − 40 = 0}` and `core ∩ near = {near ∧ G − 40 ≤ 0}`.

* **`BoundaryGaf02ChainE.cuspFnData_BGR`** (premises of E4: the `r_∂` block and `θ < 1/100`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The defining function of a cusp core near its front** (`CuspCores.cuspFn / near`): an open
`near ⊆ W°`, a function smooth on `near` with nonzero differential at its zeros there, whose zero
set in `near` is exactly the front `H_b` and whose sublevel in `near` is exactly `C_b ∩ near`. -/
theorem cuspFnData_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    ∃ (near : TopologicalSpace.Opens W.Carrier) (fn : W.Carrier → ℝ),
      (near : Set W.Carrier) ⊆ W.interior ∧
      ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near ∧
      (∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      C.toChain.cuspFront_BIF i = {x | x ∈ near ∧ fn x = 0} ∧
      C.toChain.cuspCore_BIF i ∩ near = {x | x ∈ near ∧ fn x ≤ 0} := by
  have hεd := epsBoundary_lt_BGR hrd hrdc
  have hBI := (C.bcg04_row_BGR hrd hprem).2.1 3
  have hBFM := (C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3
  have hc₃ := C.validity.c_two_lt_E4
  have hR := BoundaryCollarPacket.register_R_BCG6K hεd hc₃
  have hu : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.toChain.E i) := fun i =>
    contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i
  let P := S.packet.toBoundaryCollarPacket
  let G : W.Carrier → ℝ := P.coreLevel_BCG6K i (chainBoundaryU_BCG6K C.toChain.E i)
  have hG : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ G := P.contMDiff_coreLevel_BCG6K i (hu i)
  have hreg : ∀ x, G x ≤ 40 → mfderiv W.model 𝓘(ℝ, ℝ) G x ≠ 0 := fun x hx =>
    P.mfderiv_coreLevel_ne_zero_BCG6K i (cuspTolerance_le_thousandth_BCUSP1 _ _ _) (hu i)
      C.toChain.c_two_pos_BCG6K.le hR (fun y _ => (hBI i y).1)
      (C.bcg04_derivative_on_boundary_chain_BGR i) hx
  have hcore : C.toChain.cuspCore_BIF i = {x | G x ≤ 40} := P.cuspCore_eq_BCG6K hεd (hBI i) (hBFM i)
  have hfront : C.toChain.cuspFront_BIF i = {x | G x = 40} :=
    P.cuspFront_eq_BCG6K hεd (hBI i) (hBFM i)
  let U : TopologicalSpace.Opens W.Carrier :=
    ⟨{x | 39 < G x ∧ G x < 41}, (isOpen_lt continuous_const hG.continuous).inter
      (isOpen_lt hG.continuous continuous_const)⟩
  refine ⟨U ⊓ W.interior, fun x => G x + (-40), fun x hx => hx.2, ?_, ?_, ?_, ?_⟩
  · exact (hG.add contMDiff_const).contMDiffOn
  · intro x hx hx0
    have hx40 : G x ≤ 40 := by linarith
    have hGd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) G x := (hG x).mdifferentiableAt (by simp)
    rw [← mvfderiv_ne_zero_iff_BCG6K, mvfderiv_fun_add hGd mdifferentiableAt_const,
      mvfderiv_const, add_zero, mvfderiv_ne_zero_iff_BCG6K]
    exact hreg x hx40
  · rw [hfront]
    ext x
    constructor
    · intro hx
      have hx' : x ∈ C.toChain.cuspFront_BIF i := by rw [hfront]; exact hx
      have hint := (P.mem_strip_of_mem_front_BCG6K hεd (hBI i) hx').2
      have hmem := mem_pieceInterior_of_isInteriorPoint_BCG6K hint
      have hx40 : G x = 40 := hx
      exact ⟨⟨⟨by linarith, by linarith⟩, hmem.2⟩, by simp [hx40]⟩
    · rintro ⟨-, h0⟩
      change G x = 40
      linarith
  · rw [hcore]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by change G x + (-40) ≤ 0; have : G x ≤ 40 := h1; linarith⟩
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      change G x ≤ 40
      change G x + (-40) ≤ 0 at h1
      linarith

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
