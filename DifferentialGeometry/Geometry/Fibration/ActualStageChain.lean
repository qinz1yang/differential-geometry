import DifferentialGeometry.Geometry.Fibration.ActualStageCoreExports
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# GAF02 CORE as a chain object: `Gaf02Chain`

Blueprint `master207B.tex`, GAF02 (B:5797); external draft 59 §3 (dispositions D59-4). The object
stores the data chosen by the proof — per-stage selections, the per-stage planes (until the enhanced
plane witnesses of lane C14-PLANES land: the conclusions of the present stage tests, FC27 first /
edge / slim with (PP), the first one with the scale clause), and per stage a smoothing slot
`Gaf02StageSlot`: `active` (a `Cfs15StageOutput` of lane C14-CFS15OUT on the stage cloud, radius
`Σρ ∘ sel`, accuracy `Ξ`, with the stage plane in its plane slot; the smoothing map is its OWN
ambient
nearest map `a = ι ∘ p`, whose smoothness, value / derivative bounds, GAF03 locality and (SMV) come
from the output) or `inactive` (the stage family is empty; smoothing map `id`, `Ψ_j = id`). The
cutoffs are the actual CFS31 formulas `ψ₁` (source), `ψ₂` (CFS23), `ψ₃` (CFS22).

DEFINITIONS (ADJ, CHAIN): `P_j = π_{Q_j} ∘ a_j`, `Ψ_j z = z + ψ_j z • (P_j (π_j z) − π_j z)`,
`g₁ = Ψ₁ ∘ 𝓔⁰`, `g₂ = Ψ₂ ∘ g₁`, `E = g₃ = Ψ₃ ∘ g₂`, `s = ℓ_ρ ∘ E`. The stage outputs `g₁, g₂, g₃`
are named apart from `E`'s projections `h_j = π_j E`; nothing here identifies `π₂ g₂` with `π₂ E`.

THEOREMS about `C.E` (the induction `g₀ → g₁ → ZM(g₁) → g₂ → ZM(g₂) → g₃` is the kernel's,
run on the object's own data in `stage_one_core`, `stage_two_core`, `stage_three_core`):
`core_analytic`, `stage_smooth`, `stage_error_lt`, `stage_derivative_lt`, `stage_small_markers`,
`prefix_am0`, `segment_am0`, `keeps_orthogonal_coordinates`, `keeps_earlier_family_blocks`,
`scale_eq_first_blend`, `scale_pos`, `stage_input_mem_tube`, `cutoff_bindings`, `stage_formula`,
`stage_id_off_support`, `inactive_stage_id`, `empty_family_stage_id`, and the summary `core`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF8c
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF8c
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF8c
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The centre sets of the three stage families (circle, edge, slim). -/
def gafStageCentres (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V) :
    Fin 3 → Set X :=
  ![P.circle.centres, P.edge.centres, P.slim.centres]

/-- An empty stage family has an empty stage core, hence an empty stage cloud. -/
theorem gafCloud_eq_empty_GAF8 (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V)
    {st : Fin 3} (h : gafStageCentres P st = ∅) : gafCloud P.toLocalChartFamily P.zero st = ∅ := by
  have hcore : gafStageCore P.toLocalChartFamily P.zero st = ∅ := by
    fin_cases st
    · refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨j, -⟩ := hp
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      simp only [gafStageCentres] at h
      simp_all
    · refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨j, -⟩ := hp
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      simp only [gafStageCentres] at h
      simp_all
    · refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨j, -⟩ := hp
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      simp only [gafStageCentres] at h
      simp_all
  simp [gafCloud, hcore]

/-- **GAF02's per-stage smoothing slot** (draft 59 §3.5, D59-4): `active` — CFS15's native stage
output (`Cfs15StageOutput`, model dimension `k_st`, jet order `Kj`, accuracy `Ξ`, weight constant
`c_w`, cloud `S_st ⊆ S̃_st`, radius `Σρ ∘ sel`, plane slot `plane`); `inactive` — the stage family
is empty. -/
inductive Gaf02StageSlot (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V)
    (st : Fin 3) (Kj : ℕ) (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Ξ sg cw : ℝ) : Type
  | active (O : Cfs15StageOutput (gafStageDim st) Kj Ξ cw (gafCloud P.toLocalChartFamily P.zero st)
        (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)) plane) :
      Gaf02StageSlot P st Kj sel plane Ξ sg cw
  | inactive (hempty : gafStageCentres P st = ∅) : Gaf02StageSlot P st Kj sel plane Ξ sg cw

namespace Gaf02StageSlot

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {st : Fin 3} {Kj : ℕ} {sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X}
  {plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
    Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
  {Ξ sg cw : ℝ}

/-- The smoothing map of a slot: the output's ambient nearest map `a = ι ∘ p` of an active slot,
the identity otherwise (so that `π_Q ∘ id` makes the stage adjustment the identity). -/
def map : Gaf02StageSlot P st Kj sel plane Ξ sg cw → BlockSpace (fun _ : CGPTag
    P.toLocalChartFamily P.zero => ℝ²) →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  | .active O => O.ambient
  | .inactive _ => fun y => y

/-- Smoothness of the slot's map on `Ω` (vacuous for an inactive slot: empty cloud). -/
theorem smooth (σ : Gaf02StageSlot P st Kj sel plane Ξ sg cw) :
    ContDiffOn ℝ ∞ σ.map (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (sg * ρ (sel x)))
        := by
  cases σ with
  | active O => exact O.ambient_contDiffOn
  | inactive h =>
    rw [gafCloud_eq_empty_GAF8 P h]
    simp

/-- CFS14 (3)'s value / derivative bounds and GAF03's locality for the slot's map. -/
theorem bounds (σ : Gaf02StageSlot P st Kj sel plane Ξ sg cw) :
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖σ.map z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)) ∧
      DifferentiableAt ℝ σ.map z ∧ ‖fderiv ℝ σ.map z - (plane x).starProjection‖ ≤ Ξ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
        Kk.starProjection (σ.map z) = c := by
  cases σ with
  | active O =>
    intro x hx z hz
    have hvd := O.ambient_value_deriv hx hz
    exact ⟨hvd.1, hvd.2.1, hvd.2.2, fun Kk c hc => (O.locality_of_cloud_C15 hx Kk c hc).2.2 z hz⟩
  | inactive h =>
    intro x hx
    rw [gafCloud_eq_empty_GAF8 P h] at hx
    exact absurd hx (Set.notMem_empty x)

/-- (SMV) for the slot's map (EDP01's mean-value input). -/
theorem mean (σ : Gaf02StageSlot P st Kj sel plane Ξ sg cw) :
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ∀ ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ,
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          plane i ≤ LinearMap.ker (ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
              ℝ²) →ₗ[ℝ] ℝ)) →
        ∀ R₀ βm : ℝ,
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          |ℓ i - R₀| ≤ βm) →
        |ℓ (σ.map z) - R₀| ≤ βm ∧ ‖ℓ.comp (fderiv ℝ σ.map z)‖ ≤ 2 * cw * βm / (sg * ρ (sel x)) := by
  cases σ with
  | active O =>
    intro x hx z hz ℓ hpl R₀ βm hβ
    exact O.smv_of_cloud_C15 hx ℓ hpl R₀ βm hβ z hz
  | inactive h =>
    intro x hx
    rw [gafCloud_eq_empty_GAF8 P h] at hx
    exact absurd hx (Set.notMem_empty x)

end Gaf02StageSlot

/-- **GAF02 CORE, the chain object** (draft 59 §3.1, the present-test version). Parameters: the
packet `P`, the jet order `Kj` of the stage outputs and the per-stage numbers `Ξ_j = Ξ_j(Γ_j)`,
`Γ_j`, `Σ_j = S j`, `e_j = eg j`, `c_j`,
`c_w`; fields: the packet hypotheses, the numbers inequalities of GAF01's CHOICE in the kernel's
form, the selections, the planes with the stage tests' conclusions, the smoothing slots. -/
structure Gaf02Chain (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V)
    (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) : Type where
  /-- The packet hypotheses (GAF01 / CFS31). -/
  std : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1
  /-- The numbers: positivity, `128Ξ⁻¹Σ ≤ 1/5`, and GAF01's CHOICE inequalities used by the stages.
  -/
  numbers : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2
  /-- The per-stage selections of original preimages over the enlarged clouds. -/
  sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X
  hsel : ∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
    cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
      (sel st x) = x
  /-- The per-stage planes. -/
  plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
    Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
  /-- FC27's first-cloud test with (PP) and the scale clause, at `(Γ 0, Σ 0, e 0)`. -/
  test0 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      Module.finrank ℝ (plane 0 x) = gafStageDim 0 ∧
        plane 0 x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
    (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 0) (sel' x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 0 ∩
            ball x (S 0 * ρ (sel' x) / Γ 0))
          ((AffineSubspace.mk' x (plane 0 x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (S 0 * ρ (sel' x) / Γ 0)) ≤ ENNReal.ofReal (Γ 0 * (S 0 * ρ (sel' x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := (plane 0 x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg 0 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane 0 x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpScaleTag P.toLocalChartFamily P.zero) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane 0 x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
  /-- FC27's edge test with (PP), at `(Γ 1, Σ 1, e 1)`. -/
  test1 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      Module.finrank ℝ (plane 1 x) = gafStageDim 1 ∧
        plane 1 x ≤ gafStageQ P.toLocalChartFamily P.zero 1) ∧
    (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 1) (sel' x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 1 ∩
            ball x (S 1 * ρ (sel' x) / Γ 1))
          ((AffineSubspace.mk' x (plane 1 x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (S 1 * ρ (sel' x) / Γ 1)) ≤ ENNReal.ofReal (Γ 1 * (S 1 * ρ (sel' x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane 1 x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg 1) ∧
        (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(plane 1 x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
        (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
          1 / 2 ≤ ‖(plane 1 x).starProjection ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
        (∀ k ∈ plane 1 x, ∃ w : TangentSpace 𝓘(ℝ, E3) q,
            (plane 1 x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane 1 x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
  /-- FC27's slim test with (PP), at `(Γ 2, Σ 2, e 2)`. -/
  test2 : (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      Module.finrank ℝ (plane 2 x) = gafStageDim 2 ∧
        plane 2 x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
    (∀ sel' : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
        cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 2) (sel' x) = x) →
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
            ball x (S 2 * ρ (sel' x) / Γ 2))
          ((AffineSubspace.mk' x (plane 2 x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (S 2 * ρ (sel' x) / Γ 2)) ≤ ENNReal.ofReal (Γ 2 * (S 2 * ρ (sel' x)))) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
        x →
      let Pq := (plane 2 x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
        eg 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
    (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane 2 x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
  /-- The per-stage smoothing slots. -/
  slot : ∀ st, Gaf02StageSlot P st Kj (sel st) (plane st) (Ξ st) (S st) (cw st)

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- (ADJ) stage one: `Ψ₁ = adjustmentMap Q₁ (π_{Q₁} ∘ a₀) ψ₁`. -/
def Ψ₁ (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map y))
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P))

/-- (ADJ) stage two: `Ψ₂ = adjustmentMap Q₂ (π_{Q₂} ∘ a₁) ψ₂`. -/
def Ψ₂ (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection ((C.slot 1).map y))
    (gafStageTwoCutoff P.toLocalChartFamily P.zero)

/-- (ADJ) stage three: `Ψ₃ = adjustmentMap Q₃ (π_{Q₃} ∘ a₂) ψ₃`. -/
def Ψ₃ (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ((C.slot 2).map y))
    (gafStageThreeCutoff P.toLocalChartFamily P.zero)

/-- (CHAIN) the first stage output `g₁ = Ψ₁ ∘ 𝓔⁰`. -/
def g₁ (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily
    P.zero => ℝ²) :=
  C.Ψ₁ ∘ cgpGlobalMap P.toLocalChartFamily P.zero

/-- (CHAIN) the second stage output `g₂ = Ψ₂ ∘ g₁`. -/
def g₂ (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily
    P.zero => ℝ²) :=
  C.Ψ₂ ∘ C.g₁

/-- (CHAIN) the final map `E = g₃ = Ψ₃ ∘ g₂`. -/
def E (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily
    P.zero => ℝ²) :=
  C.Ψ₃ ∘ C.g₂

/-- The scale exit `s = ℓ_ρ ∘ E`. -/
def scale (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : X → ℝ :=
  fun p => gafScaleMarker P.toLocalChartFamily P.zero (C.E p)


/-- `g₁` unfolded: `Ψ₁ ∘ 𝓔⁰` with `Ψ₁`'s formula (the kernel's form). -/
theorem g₁_eq (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : C.g₁ =
    adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero := rfl

/-- `g₂` unfolded (the kernel's form). -/
theorem g₂_eq (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : C.g₂ =
    adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection ((C.slot 1).map y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map y))
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) := rfl

/-- `E` unfolded (the kernel's form). -/
theorem E_eq (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : C.E =
    adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ((C.slot 2).map y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
      (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection ((C.slot 1).map y))
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero)) := rfl

/-- `Ψ₁`, `Ψ₂`, `Ψ₃` unfolded (the exports' form). -/
theorem Ψ_eq (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    C.Ψ₁ = adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map y))
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) ∧
    C.Ψ₂ = adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection ((C.slot 1).map y))
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∧
    C.Ψ₃ = adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ((C.slot 2).map y))
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) := ⟨rfl, rfl, rfl⟩

/-- (ADJ) and (CHAIN) pointwise: `Ψ_j z = z + ψ_j z • (P_j (π_j z) − π_j z)` with
`P_j = π_j ∘ a_j`, and `g₁ = Ψ₁ ∘ 𝓔⁰`, `g₂ = Ψ₂ ∘ g₁`, `E = Ψ₃ ∘ g₂`. -/
theorem stage_formula (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (z : BlockSpace (fun _ : CGPTag
    P.toLocalChartFamily P.zero => ℝ²)) (p : X) :
    C.Ψ₁ z = z + (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P)) z •
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map ((gafStageQ
          P.toLocalChartFamily P.zero 0).starProjection z)) -
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection z) ∧
    C.Ψ₂ z = z + (gafStageTwoCutoff P.toLocalChartFamily P.zero) z •
      ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection ((C.slot 1).map ((gafStageQ
          P.toLocalChartFamily P.zero 1).starProjection z)) -
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) ∧
    C.Ψ₃ z = z + (gafStageThreeCutoff P.toLocalChartFamily P.zero) z •
      ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection ((C.slot 2).map ((gafStageQ
          P.toLocalChartFamily P.zero 2).starProjection z)) -
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection z) ∧
    C.g₁ p = C.Ψ₁ (cgpGlobalMap P.toLocalChartFamily P.zero p) ∧ C.g₂ p = C.Ψ₂ (C.g₁ p) ∧ C.E p =
        C.Ψ₃ (C.g₂ p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Stage one on the object** (`gaf02_core_stageOne_GAF8` on the chain's data): `g₁` smooth,
`‖g₁ − 𝓔⁰‖ < c₀ρ`,
the derivative budget, small markers vanish at `g₁`, (AM0) on `[𝓔⁰ p, g₁ p]`. -/
theorem stage_one_core (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      C.g₁ ∧
    (∀ p, ‖C.g₁ p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 0 * ρ p) ∧
    (∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      C.g₁ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) *
          Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (C.g₁ q) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (C.g₁ p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, hσc, hγc, hεr⟩ := C.std
  obtain ⟨hnum, hv₁, hc₀, hd₁, hc₀κ, hc₀s, hv₂, hc₁, hd₂, hc₁κ, hc₁s, hv₃, hc₂, hd₃⟩ := C.numbers
  obtain ⟨hΞ₀, hsg₀, hmo₀, heg₀⟩ := hnum 0
  have t0 := C.test0
  have k := gaf02_core_stageOne_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    (C.sel 0) (C.hsel 0) hsg₀ hΞ₀ hmo₀ heg₀ (C.plane 0) (fun x hx => (t0.1 x hx).2)
    t0.2.2.2.2
    (fun x hx => (t0.2.2.1 x hx).imp fun i hi q hq => (hi q hq).2.1)
    ((C.slot 0).map) (C.slot 0).smooth (C.slot 0).bounds
    hv₁ hc₀
  rw [C.g₁_eq]
  exact k

/-- **Stage two on the object** ((ZM) at `g₁` from the stage-one prefix): `g₂` smooth,
`‖g₂ − 𝓔⁰‖ < c₁ρ`,
the derivative budget, small markers vanish at `g₂`, (AM0) on `[𝓔⁰ p, g₂ p]`. -/
theorem stage_two_core (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      C.g₂ ∧
    (∀ p, ‖C.g₂ p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 1 * ρ p) ∧
    (∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      C.g₂ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) *
          Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (C.g₂ q) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (C.g₂ p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, hσc, hγc, hεr⟩ := C.std
  obtain ⟨hnum, hv₁, hc₀, hd₁, hc₀κ, hc₀s, hv₂, hc₁, hd₂, hc₁κ, hc₁s, hv₃, hc₂, hd₃⟩ := C.numbers
  obtain ⟨hΞ₀, hsg₀, hmo₀, heg₀⟩ := hnum 0
  have t0 := C.test0
  obtain ⟨hΞ₁, hsg₁, hmo₁, heg₁⟩ := hnum 1
  have t1 := C.test1
  have k := gaf02_core_stageTwo_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    (C.sel 0) (C.hsel 0) hsg₀ hΞ₀ hmo₀ heg₀ (C.plane 0) (fun x hx => (t0.1 x hx).2)
    t0.2.2.2.2
    (fun x hx => (t0.2.2.1 x hx).imp fun i hi q hq => (hi q hq).2.1)
    ((C.slot 0).map) (C.slot 0).smooth (C.slot 0).bounds
    (C.sel 1) (C.hsel 1) hsg₁ hΞ₁ hmo₁ heg₁ (C.plane 1) (fun x hx => (t1.1 x hx).2)
    t1.2.2.2
    (fun x hx => (t1.2.2.1 x hx).imp fun i hi => ⟨hi.1, fun q hq => (hi.2 q hq).1⟩)
    ((C.slot 1).map) (C.slot 1).smooth (C.slot 1).bounds
    hv₁ hc₀ hd₁ hc₀κ hc₀s hv₂ hc₁
  rw [C.g₂_eq]
  exact k

/-- **Stage three on the object** ((ZM) at `g₂` from the two-stage prefix): `E` smooth,
`‖E − 𝓔⁰‖ < c₂ρ`,
the derivative budget, small markers vanish at `E`, (AM0) on `[𝓔⁰ p, E p]`. -/
theorem stage_three_core (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      C.E ∧
    (∀ p, ‖C.E p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 2 * ρ p) ∧
    (∀ p w, ‖mvfderiv 𝓘(ℝ, E3)
      C.E p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) *
          Real.sqrt (g.inner p w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (C.E q) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (C.E p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, hσc, hγc, hεr⟩ := C.std
  obtain ⟨hnum, hv₁, hc₀, hd₁, hc₀κ, hc₀s, hv₂, hc₁, hd₂, hc₁κ, hc₁s, hv₃, hc₂, hd₃⟩ := C.numbers
  obtain ⟨hΞ₀, hsg₀, hmo₀, heg₀⟩ := hnum 0
  have t0 := C.test0
  obtain ⟨hΞ₁, hsg₁, hmo₁, heg₁⟩ := hnum 1
  have t1 := C.test1
  obtain ⟨hΞ₂, hsg₂, hmo₂, heg₂⟩ := hnum 2
  have t2 := C.test2
  have k := gaf02_core_stageThree_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    (C.sel 0) (C.hsel 0) hsg₀ hΞ₀ hmo₀ heg₀ (C.plane 0) (fun x hx => (t0.1 x hx).2)
    t0.2.2.2.2
    (fun x hx => (t0.2.2.1 x hx).imp fun i hi q hq => (hi q hq).2.1)
    ((C.slot 0).map) (C.slot 0).smooth (C.slot 0).bounds
    (C.sel 1) (C.hsel 1) hsg₁ hΞ₁ hmo₁ heg₁ (C.plane 1) (fun x hx => (t1.1 x hx).2)
    t1.2.2.2
    (fun x hx => (t1.2.2.1 x hx).imp fun i hi => ⟨hi.1, fun q hq => (hi.2 q hq).1⟩)
    ((C.slot 1).map) (C.slot 1).smooth (C.slot 1).bounds
    (C.sel 2) (C.hsel 2) hsg₂ hΞ₂ hmo₂ heg₂ (C.plane 2) (fun x hx => (t2.1 x hx).2)
    t2.2.2.2
    (fun x hx => (t2.2.2.1 x hx).imp fun i hi q hq => (hi q hq).2.1)
    ((C.slot 2).map) (C.slot 2).smooth (C.slot 2).bounds
    hv₁ hc₀ hd₁ hc₀κ hc₀s hv₂ hc₁ hd₂ hc₁κ hc₁s hv₃ hc₂
  rw [C.E_eq]
  exact k

/-- **The GAF02 CORE kernel on the object** (the induction `g₀ → g₁ → ZM(g₁) → g₂ → ZM(g₂) → g₃`
on the chain's own selections, planes, nearest maps and cutoffs): smoothness of `g₁, g₂, E`; strict
cumulative value errors `< c_jρ`; derivative errors `≤ H√g` with `H < c_j`; small markers vanish at
every stage; (AM0) at `g₁, g₂, E` and on `[𝓔⁰ p, E p]`. -/
theorem core_analytic (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.g₁ ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.g₂ ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.E ∧
    (∀ p, ‖C.g₁ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 0 * ρ p) ∧
    (∀ p, ‖C.g₂ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 1 * ρ p) ∧
    (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 2 * ρ p) ∧
    (∃ Hd : ℝ, Hd < c 0 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.g₁ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∃ Hd : ℝ, Hd < c 1 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.g₂ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∃ Hd : ℝ, Hd < c 2 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E q) = 0) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (C.E p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  obtain ⟨-, -, -, hd₁, -, -, -, -, hd₂, -, -, -, -, hd₃⟩ := C.numbers
  have s1 := C.stage_one_core
  have s2 := C.stage_two_core
  have s3 := C.stage_three_core
  exact ⟨s1.1, s2.1, s3.1, s1.2.1, s2.2.1, s3.2.1, ⟨_, hd₁, s1.2.2.1⟩, ⟨_, hd₂, s2.2.2.1⟩,
    ⟨_, hd₃, s3.2.2.1⟩, s1.2.2.2.1, s2.2.2.2.1, s3.2.2.2.1,
    fun a p hp => s1.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _),
    fun a p hp => s2.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _),
    fun a p hp => s3.2.2.2.2 a p hp _ (right_mem_segment ℝ _ _), s3.2.2.2.2⟩

/-- **Stage smoothness**: `g₁`, `g₂` and `E` are smooth. -/
theorem stage_smooth (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.g₁ ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.g₂ ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.E :=
        by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact ⟨k1, k2, k3⟩

/-- **Strict cumulative value errors**: `‖g_j − 𝓔⁰‖ < c_jρ`. -/
theorem stage_error_lt (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ p, ‖C.g₁ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 0 * ρ p) ∧
    (∀ p, ‖C.g₂ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 1 * ρ p) ∧
    (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 2 * ρ p) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact ⟨k4, k5, k6⟩

/-- **Derivative errors**: `‖dg_j w − d𝓔⁰ w‖ ≤ H_j√g(w, w)` with `H_j < c_j`. -/
theorem stage_derivative_lt (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∃ Hd : ℝ, Hd < c 0 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.g₁ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∃ Hd : ℝ, Hd < c 1 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.g₂ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∃ Hd : ℝ, Hd < c 2 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact ⟨k7, k8, k9⟩

/-- **Small markers vanish** at `g₁`, `g₂`, `E` (`ρ(c_a) < ρ(q)/16`). -/
theorem stage_small_markers (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E q) = 0) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact ⟨k10, k11, k12⟩

/-- **(AM0) at every prefix**: off the support of `ζ_a`, `|v_a(g_j p)| ≤ ρ(c_a)/32`. -/
theorem prefix_am0 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact ⟨k13, k14, k15⟩

/-- **(AM0) on the segment** `[𝓔⁰ p, E p]`. -/
theorem segment_am0 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (C.E p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact k16

/-- **Kept orthogonal coordinates** (draft 59 §3.4, from (ADJ)): `Ψ_j z − z ∈ Q_j`, hence
`proj_{Q_j^⊥} Ψ_j z = proj_{Q_j^⊥} z`, and every block whose tag is not a stage tag is kept. -/
theorem keeps_orthogonal_coordinates (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (z : BlockSpace (fun _ :
    CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    C.Ψ₁ z - z ∈ (gafStageQ P.toLocalChartFamily P.zero 0) ∧ C.Ψ₂ z - z ∈ (gafStageQ
        P.toLocalChartFamily P.zero 1) ∧ C.Ψ₃ z - z ∈ (gafStageQ P.toLocalChartFamily P.zero 2) ∧
    (gafStageQ P.toLocalChartFamily P.zero 1)ᗮ.starProjection (C.Ψ₂ z) = (gafStageQ
        P.toLocalChartFamily P.zero 1)ᗮ.starProjection z ∧
    (gafStageQ P.toLocalChartFamily P.zero 2)ᗮ.starProjection (C.Ψ₃ z) = (gafStageQ
        P.toLocalChartFamily P.zero 2)ᗮ.starProjection z ∧
    (∀ t, t ∉ gafStageTags P.toLocalChartFamily P.zero 1 → C.Ψ₂ z t = z t) ∧
    ∀ t, t ∉ gafStageTags P.toLocalChartFamily P.zero 2 → C.Ψ₃ z t = z t := by
  have h1 := adjustmentMap_sub_mem_GAF8 (gafStageQ P.toLocalChartFamily P.zero 0) (C.slot 0).map
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P)) z
  have h2 := adjustmentMap_sub_mem_GAF8 (gafStageQ P.toLocalChartFamily P.zero 1) (C.slot 1).map
    (gafStageTwoCutoff P.toLocalChartFamily P.zero) z
  have h3 := adjustmentMap_sub_mem_GAF8 (gafStageQ P.toLocalChartFamily P.zero 2) (C.slot 2).map
    (gafStageThreeCutoff P.toLocalChartFamily P.zero) z
  refine ⟨h1, h2, h3, ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal _ h2
  · rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal _ h3
  · rw [C.Ψ_eq.2.1]
    exact gafStage_adjust_kept_GAF8 P.toLocalChartFamily P.zero 1 (C.slot 1).map
      (gafStageTwoCutoff P.toLocalChartFamily P.zero) z ht
  · rw [C.Ψ_eq.2.2]
    exact gafStage_adjust_kept_GAF8 P.toLocalChartFamily P.zero 2 (C.slot 2).map
      (gafStageThreeCutoff P.toLocalChartFamily P.zero) z ht

/-- **Later stages keep the earlier family blocks** (draft 59 §3.4): `E` keeps the scale block,
the `E'` block and every circle block of `g₁`, and every edge block of `g₂`. -/
theorem keeps_earlier_family_blocks (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    C.E p (cgpScaleTag P.toLocalChartFamily P.zero) = C.g₁ p (cgpScaleTag P.toLocalChartFamily
        P.zero) ∧
    C.E p (cgpEdgeTag P.toLocalChartFamily P.zero) = C.g₁ p (cgpEdgeTag P.toLocalChartFamily
        P.zero) ∧
    (∀ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
      C.E p (.inl j : CGPTag P.toLocalChartFamily P.zero) = C.g₁ p (.inl j : CGPTag
          P.toLocalChartFamily P.zero)) ∧
    ∀ j : P.toLocalChartFamily.edge.finite_centres.toFinset,
      C.E p (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) =
        C.g₂ p (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) := by
  obtain ⟨hs1, hs2, he1, he2, hc, hed, -⟩ := gafStage_kept_tags_GAF8 P.toLocalChartFamily P.zero
  have k2 : ∀ t, t ∉ gafStageTags P.toLocalChartFamily P.zero 1 → C.g₂ p t = C.g₁ p t := fun t ht =>
    ((C.keeps_orthogonal_coordinates (C.g₁ p)).2.2.2.2.2.1 t ht)
  have k3 : ∀ t, t ∉ gafStageTags P.toLocalChartFamily P.zero 2 → C.E p t = C.g₂ p t := fun t ht =>
    ((C.keeps_orthogonal_coordinates (C.g₂ p)).2.2.2.2.2.2 t ht)
  exact ⟨(k3 _ hs2).trans (k2 _ hs1), (k3 _ he2).trans (k2 _ he1),
    fun j => (k3 _ (hc j).2).trans (k2 _ (hc j).1), fun j => k3 _ (hed j)⟩

/-- **The scale exit** (SCALE-EXIT, draft 59 §3.4): `s = ℓ_ρ(E) = ℓ_ρ(g₁)`, the exact first-stage
blend `s = (1 − χ)ρ + χ z_ρ` with `χ = ψ₁ ∘ 𝓔⁰`, `z_ρ = ℓ_ρ(a₀ ∘ 𝓔⁰)`, and `s = ℓ_ρ(g₁)`
(never `s = ρ` in general). -/
theorem scale_eq_first_blend (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    C.scale p = gafScaleMarker P.toLocalChartFamily P.zero (C.g₁ p) ∧
    C.scale p = (1 - (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P)
        (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)) * ρ p +
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p) *
        gafScaleMarker P.toLocalChartFamily P.zero ((C.slot 0).map (cgpGlobalMap
            P.toLocalChartFamily P.zero p)) := by
  have hkeep : ∀ q, C.E q (cgpScaleTag P.toLocalChartFamily P.zero) = C.g₁ q (cgpScaleTag
      P.toLocalChartFamily P.zero) :=
    fun q => (C.keeps_earlier_family_blocks q).1
  have hc01 : c 0 ≤ 1 := by
    obtain ⟨-, -, hc₀, -⟩ := C.numbers
    linarith
  have hx := gafScale_exit_GAF8 P.toLocalChartFamily P.zero hc01 C.g₁ C.E C.stage_error_lt.1 hkeep p
  have hb := gafStageOne_scale_blend_GAF8 P.toLocalChartFamily P.zero (C.slot 0).map
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P)) p
  exact ⟨hx.1, hx.1.trans hb⟩

/-- **The scale is positive** (draft 59 §3.4: coarse error and `c₀ < 1`): `|s − ρ| < c₀ρ`, `s > 0`.
-/
theorem scale_pos (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    |C.scale p - ρ p| < c 0 * ρ p ∧ 0 < C.scale p := by
  have hkeep : ∀ q, C.E q (cgpScaleTag P.toLocalChartFamily P.zero) = C.g₁ q (cgpScaleTag
      P.toLocalChartFamily P.zero) :=
    fun q => (C.keeps_earlier_family_blocks q).1
  have hc01 : c 0 ≤ 1 := by
    obtain ⟨-, -, hc₀, -⟩ := C.numbers
    linarith
  have hx := gafScale_exit_GAF8 P.toLocalChartFamily P.zero hc01 C.g₁ C.E C.stage_error_lt.1 hkeep p
  exact hx.2

/-- **Inactive slots are identity stages** (draft 59 §3.5): an `inactive` slot has smoothing map
`id`, so `Ψ_j = adjustmentMap Q_j π_{Q_j} ψ_j = id`. -/
theorem inactive_stage_id (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ h, C.slot 0 = .inactive h → C.Ψ₁ = id) ∧ (∀ h, C.slot 1 = .inactive h → C.Ψ₂ = id) ∧
    ∀ h, C.slot 2 = .inactive h → C.Ψ₃ = id := by
  refine ⟨fun h hs => ?_, fun h hs => ?_, fun h hs => ?_⟩
  · rw [Gaf02Chain.Ψ₁, hs]
    exact adjustmentMap_starProjection_eq_id_GAF8 _ _
  · rw [Gaf02Chain.Ψ₂, hs]
    exact adjustmentMap_starProjection_eq_id_GAF8 _ _
  · rw [Gaf02Chain.Ψ₃, hs]
    exact adjustmentMap_starProjection_eq_id_GAF8 _ _

/-- **Empty families give identity stages** (draft 59 §3.5): the actual cutoff `ψ_j` vanishes
identically on an empty circle / edge / slim family, so `Ψ_j = id` whatever the slot. -/
theorem empty_family_stage_id (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (P.circle.centres = ∅ → C.Ψ₁ = id) ∧ (P.edge.centres = ∅ → C.Ψ₂ = id) ∧
    (P.slim.centres = ∅ → C.Ψ₃ = id) :=
  ⟨fun h => adjustmentMap_eq_id_of_cutoff_GAF8 _ _ ((gafStage_cutoff_empty_GAF8 P).1 h),
    fun h => adjustmentMap_eq_id_of_cutoff_GAF8 _ _ ((gafStage_cutoff_empty_GAF8 P).2.1 h),
    fun h => adjustmentMap_eq_id_of_cutoff_GAF8 _ _ ((gafStage_cutoff_empty_GAF8 P).2.2 h)⟩

/-- **Off the closed support the stage is the identity nearby** (CFS31: no global smooth ambient
extension is needed). -/
theorem stage_id_off_support (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (z : BlockSpace (fun _ : CGPTag
    P.toLocalChartFamily P.zero => ℝ²)) :
    (z ∉ tsupport (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector
        P)
      (gafCircleMarker P)) → C.Ψ₁ =ᶠ[𝓝 z] id) ∧
    (z ∉ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) → C.Ψ₂ =ᶠ[𝓝 z] id) ∧
    (z ∉ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) → C.Ψ₃ =ᶠ[𝓝 z] id) :=
  ⟨fun h => adjustmentMap_eventuallyEq_id_GAF5 _ _ h,
    fun h => adjustmentMap_eventuallyEq_id_GAF5 _ _ h,
    fun h => adjustmentMap_eventuallyEq_id_GAF5 _ _ h⟩

/-- **Stage inputs lie in the stage tubes** (CFS16 at the chain's prefixes): if the stage input
`g_{j−1} p` (`g₀ = 𝓔⁰`) lies in the closed support of `ψ_j`, then `x = π_j 𝓔⁰ p` is in the stage
cloud `S_j` and `π_j g_{j−1} p ∈ B(x, Σ_j ρ(sel_j x))`, a ball on which `a_j` is controlled. -/
theorem stage_input_mem_tube (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    (cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport (markerLocalitySourceCutoff
        lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 0 ∧
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ ball ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap
              P.toLocalChartFamily P.zero p))
        (S 0 * ρ (C.sel 0 ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p))))) ∧
    (C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 1 ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
              p))
        (S 1 * ρ (C.sel 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p))))) ∧
    (C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 2 ∧
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈ ball ((gafStageQ
          P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero
              p))
        (S 2 * ρ (C.sel 2 ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (cgpGlobalMap
            P.toLocalChartFamily P.zero p))))) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, -, -, -⟩ := C.std
  obtain ⟨hnum, -, -, -, hc₀κ, hc₀s, -, -, -, hc₁κ, hc₁s, -, -, -⟩ := C.numbers
  obtain ⟨-, -, -, k4, k5, -, -, -, -, -, -, -, k13, k14, -, -⟩ := C.core_analytic
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hpert₁ : ∀ q, ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q
      :=
    fun q => (k4 q).le.trans (mul_le_mul_of_nonneg_right hc₀κ (hρ q).le)
  have hpert₂ : ∀ q, ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q
      :=
    fun q => (k5 q).le.trans (mul_le_mul_of_nonneg_right hc₁κ (hρ q).le)
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · exact ⟨gaf02_stageOne_loc_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 p hp,
      mem_ball_self (mul_pos (hnum 0).2.1 (hρ _))⟩
  · have hx := (gaf02_stageTwo_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _ hpert₁
      (gaf02_familyZM_GAF7 P _ k13).1 p).1 hp
    exact ⟨hx, stage_step_mem_ball_GAF6 (gafStageQ P.toLocalChartFamily P.zero 1) (gafCloud
        P.toLocalChartFamily P.zero 1) (C.sel 1) ρ
      (hnum 1).2.1 hc₀s (cgpGlobalMap P.toLocalChartFamily P.zero) C.g₁ (hρ p) hx
      (gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 1 (C.sel 1)
          (C.hsel 1)) (k4 p).le⟩
  · have hx := (gaf02_stageThree_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _
      hpert₂ (gaf02_familyZM_GAF7 P _ k14).2 p).1 hp
    exact ⟨hx, stage_step_mem_ball_GAF6 (gafStageQ P.toLocalChartFamily P.zero 2) (gafCloud
        P.toLocalChartFamily P.zero 2) (C.sel 2) ρ
      (hnum 2).2.1 hc₁s (cgpGlobalMap P.toLocalChartFamily P.zero) C.g₂ (hρ p) hx
      (gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 2 (C.sel 2)
          (C.hsel 2)) (k5 p).le⟩

/-- **CFS31 cutoff bindings at the chain's stage inputs** (draft 59 §3.2): `ψ₁` (source cutoff),
`ψ₂` (CFS23) at `g₁`, `ψ₃` (CFS22) at `g₂`: smoothness, values in `[0, 1]`, the plateau, the closed
support localizing the original point, and `‖Dψ_j‖ ≤ b_cut/ρ` along `[𝓔⁰ p, g_{j−1} p]` (with a
positive scale for `ψ₂`); the prior errors and (ZM) used are the chain's own. -/
theorem cutoff_bindings (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (ContDiff ℝ ∞ (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector
        P)
        (gafCircleMarker P)) ∧
      (∀ z, (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
          p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) →
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p) = 1) ∧
      (∀ p, cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport (markerLocalitySourceCutoff
          lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P)) →
        ∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
          p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ ≤ 13 / 2) ∧
      ∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
          (gafCircleVector P)
        (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ ≤
        gafCutoffConstant / ρ p) ∧
    (ContDiffOn ℝ ∞ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      (∀ z, (gafStageTwoCutoff P.toLocalChartFamily P.zero) z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
        (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) = 1) ∧
      (∀ p, C.g₁ p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
        ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < gafScaleMarker P.toLocalChartFamily P.zero ((1 - t) • cgpGlobalMap P.toLocalChartFamily
            P.zero p + t • C.g₁ p) ∧
        ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
            P.toLocalChartFamily P.zero p + t • C.g₁ p)‖ ≤
          gafCutoffConstant / ρ p) ∧
    ContDiff ℝ ∞ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
      (∀ z, (gafStageThreeCutoff P.toLocalChartFamily P.zero) z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) →
        (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p) = 1) ∧
      (∀ p, C.g₂ p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
        ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
            7 * (10 ^ 5 * Δ)) ∧
      ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ((1 - t) • cgpGlobalMap
            P.toLocalChartFamily P.zero p + t • C.g₂ p)‖ ≤
          gafCutoffConstant / ρ p := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, -, -, -⟩ := C.std
  obtain ⟨-, -, -, -, hc₀κ, -, -, -, -, hc₁κ, -, -, -, -⟩ := C.numbers
  obtain ⟨-, -, -, k4, k5, -, -, -, -, -, -, -, k13, k14, -, -⟩ := C.core_analytic
  have hpert₁ : ∀ q, ‖C.g₁ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q
      :=
    fun q => (k4 q).le.trans (mul_le_mul_of_nonneg_right hc₀κ (hρ q).le)
  have hpert₂ : ∀ q, ‖C.g₂ q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q
      :=
    fun q => (k5 q).le.trans (mul_le_mul_of_nonneg_right hc₁κ (hρ q).le)
  exact ⟨gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1,
    gaf02_stageTwo_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _ hpert₁
      (gaf02_familyZM_GAF7 P _ k13).1,
    gaf02_stageThree_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _ hpert₂
      (gaf02_familyZM_GAF7 P _ k14).2⟩

/-- **GAF02 CORE on the chain object** (draft 59 §3.3): the analytic core of `C.E` (smoothness,
strict value and derivative errors, small markers, (AM0) at every prefix and on `[𝓔⁰ p, E p]`)
together with the scale exit `s = ℓ_ρ(E) = ℓ_ρ(g₁)`, `|s − ρ| < c₀ρ`, `s > 0`, and the kept earlier
blocks; every conclusion is about the object's own `E`. -/
theorem core (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.g₁ ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.g₂ ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞ C.E ∧
    (∀ p, ‖C.g₁ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 0 * ρ p) ∧
    (∀ p, ‖C.g₂ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 1 * ρ p) ∧
    (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < c 2 * ρ p) ∧
    (∃ Hd : ℝ, Hd < c 0 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.g₁ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∃ Hd : ℝ, Hd < c 1 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.g₂ p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∃ Hd : ℝ, Hd < c 2 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤ Hd * Real.sqrt (g.inner p
          w w)) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ q) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E q) = 0) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (C.E p),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    ∀ p, C.scale p = gafScaleMarker P.toLocalChartFamily P.zero (C.g₁ p) ∧ |C.scale p - ρ p| < c 0
        * ρ p ∧
      0 < C.scale p ∧ C.E p (cgpScaleTag P.toLocalChartFamily P.zero) = C.g₁ p (cgpScaleTag
          P.toLocalChartFamily P.zero) ∧
      C.E p (cgpEdgeTag P.toLocalChartFamily P.zero) = C.g₁ p (cgpEdgeTag P.toLocalChartFamily
          P.zero) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ := C.core_analytic
  exact ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, fun p =>
    ⟨(C.scale_eq_first_blend p).1, (C.scale_pos p).1, (C.scale_pos p).2,
      (C.keeps_earlier_family_blocks p).1,
      (C.keeps_earlier_family_blocks p).2.1⟩⟩

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
