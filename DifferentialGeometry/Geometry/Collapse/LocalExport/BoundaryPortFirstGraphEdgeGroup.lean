import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphEdgeGroup
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTags
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTagsScalar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualFirstGraphEdgeGroup (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstGraphEdgeGroup.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA7E_BAUGP : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Network

variable {ι : Type*} [Fintype ι]

end Network

section Actual

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The actual input of the edge network**: `V(y) = ((η_k(y))_{k ∈ S_e}, τ(y))` (`τ = t` in the
high branch of TCP04, `τ = 0` otherwise). -/
def tcpEdgeActual_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) (y : X) :
    EuclideanSpace ℝ (Option Se) :=
  WithLp.toLp 2 (fun o => Option.elim o (τ y) fun k => L.edgeB.coord_BAUGA k.1.1 y)

theorem tcpEdgeActual_some_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) (y : X) (k : Se) :
    tcpEdgeActual_BAUGP L Se τ y (some k) = L.edgeB.coord_BAUGA k.1.1 y :=
  rfl

theorem tcpEdgeActual_none_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) (y : X) :
    tcpEdgeActual_BAUGP L Se τ y none = τ y :=
  rfl

/-- The linear part `M` of the model's affine network input (rows `A1_k`, `k ∈ S_e`, and `Bτ`). -/
def tcpEdgeLinear_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (Bτ : ℝ² →L[ℝ] ℝ) : ℝ² →L[ℝ] EuclideanSpace ℝ (Option Se) :=
  tcpEdgeRows (fun q : Option Se => Option.elim q Bτ fun j : Se => A1 (.inr (.inr (.inl j.1))))

/-- The offset `u₀` of the model's affine network input (`c1_k`, `k ∈ S_e`, and `cτ`). -/
def tcpEdgeOffset_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (c1 : CGPTag_BAUGP L Z → ℝ) (cτ : ℝ) :
    EuclideanSpace ℝ (Option Se) :=
  WithLp.toLp 2 (fun q : Option Se => Option.elim q cτ fun j : Se => c1 (.inr (.inr (.inl j.1))))

/-- **An actual edge block as a network block**: where `ζ_j = f(η_j/Δ) g(τ/Δ)`,
`𝓔⁰(y)_j = R • blockLift (W(V y)_j)` with `s_k = ρ(k)/R`. -/
theorem edge_block_eq_network_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) {i y : X}
    (j : L.edgeB.finite_centres.toFinset) (hj : j ∈ Se)
    (hy : L.edgeB.cutoff_BAUGA j.1 y =
      edgeCoordinateProfile (L.edgeB.coord_BAUGA j.1 y / Δ) * edgeHeightProfile (τ y / Δ)) :
    cgpGlobalMap_BAUGP L Z y (.inr (.inr (.inl j))) =
      ρ i • blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeActual_BAUGP L Se τ y)
        (some ⟨j, hj⟩)) := by
  have hri := hρ i
  set φ := edgeCoordinateProfile (L.edgeB.coord_BAUGA j.1 y / Δ) * edgeHeightProfile (τ y / Δ) with
      hφ
  change WithLp.toLp 2 ((ρ j.1 * L.edgeB.cutoff_BAUGA j.1 y) • planeAxis (L.edgeB.coord_BAUGA j.1
      y),
    ρ j.1 * L.edgeB.cutoff_BAUGA j.1 y) = _
  rw [hy, tcpNetwork_some_apply_KA7, tcpEdgeActual_some_BAUGP, tcpEdgeActual_none_BAUGP,
    scalar_block_eq_KA6 (ρ i) (ρ j.1) φ (L.edgeB.coord_BAUGA j.1 y) hri.ne']
  congr 2
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  change WithLp.toLp 2 (φ * (ρ j.1 / ρ i * L.edgeB.coord_BAUGA j.1 y), ρ j.1 / ρ i * φ) =
    WithLp.toLp 2 (φ * (ρ j.1 / ρ i * L.edgeB.coord_BAUGA j.1 y), φ * (ρ j.1 / ρ i))
  rw [mul_comm (ρ j.1 / ρ i) φ]

/-- The actual edge sum is the network sum where the listed cutoffs are `f(η_k/Δ) g(τ/Δ)` and the
unlisted ones vanish. -/
theorem cgpEdgeSum_eq_network_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) {y : X}
    (hcut : ∀ k ∈ Se, L.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (L.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τ y / Δ))
    (hoff : ∀ k ∉ Se, L.edgeB.cutoff_BAUGA k.1 y = 0) :
    cgpEdgeSum_BAUGP L y = ∑ k : Se, edgeCoordinateProfile (Δ⁻¹ * tcpEdgeActual_BAUGP L Se τ y
        (some k)) *
      edgeHeightProfile (Δ⁻¹ * tcpEdgeActual_BAUGP L Se τ y none) := by
  classical
  unfold cgpEdgeSum_BAUGP
  rw [← Finset.sum_subset (Finset.subset_univ Se) (fun k _ hk => hoff k hk)]
  rw [← Finset.sum_coe_sort Se]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcut k.1 k.2, tcpEdgeActual_some_BAUGP, tcpEdgeActual_none_BAUGP, div_eq_inv_mul,
      div_eq_inv_mul]

/-- **The `E'` block as a network block**: where the listed cutoffs are `f(η_k/Δ) g(τ/Δ)`, the
unlisted ones vanish, and either `τ = t` or (`τ = 0` and the marker vanishes),
`𝓔⁰(y)_{E'} = (Rσ(y)) • blockLift (W(V y)_∅)` with `σ = ρ/R`. -/
theorem edgeMarker_block_eq_network_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) {i y : X}
    (hcut : ∀ k ∈ Se, L.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (L.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τ y / Δ))
    (hoff : ∀ k ∉ Se, L.edgeB.cutoff_BAUGA k.1 y = 0)
    (hτ : τ y = cgpHeight_BAUGP L y ∨ (τ y = 0 ∧ cgpEdgeMarker_BAUGP L y = 0)) :
    cgpGlobalMap_BAUGP L Z y (cgpEdgeTag_BAUGP L Z) =
      (ρ i * (ρ y / ρ i)) • blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeActual_BAUGP L Se τ y) none) := by
  have hri := hρ i
  have hR : ρ i * (ρ y / ρ i) = ρ y := by field_simp
  rw [hR, tcpNetwork_none_apply_KA7, tcpEdgeActual_none_BAUGP]
  set z := cgpEdgeH (Δ⁻¹ * τ y) * edgeSumProfile (∑ k : Se,
    edgeCoordinateProfile (Δ⁻¹ * tcpEdgeActual_BAUGP L Se τ y (some k)) *
      edgeHeightProfile (Δ⁻¹ * τ y)) with hz
  have hsm : ∀ (c : ℝ) (u : ℝ²) (t : ℝ),
      c • (WithLp.toLp 2 (u, t) : WithLp 2 (ℝ² × ℝ)) = WithLp.toLp 2 (c • u, c * t) :=
    fun c u t => rfl
  have hrhs : ρ y • blockLift_KC3 (z • WithLp.toLp 2 (1 * τ y, (1 : ℝ))) =
      WithLp.toLp 2 ((ρ y * z) • planeAxis (τ y), ρ y * z) := by
    change ρ y • blockLift_KC3 (WithLp.toLp 2 (z * (1 * τ y), z * 1)) = _
    rw [blockLift_apply_KC3, hsm, planeAxis_apply, planeAxis_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, smul_smul]
    ring_nf
  rw [hrhs]
  change WithLp.toLp 2 ((ρ y * cgpEdgeMarker_BAUGP L y) • planeAxis (cgpHeight_BAUGP L y),
    ρ y * cgpEdgeMarker_BAUGP L y) = _
  rcases hτ with hτ | ⟨hτ0, hm⟩
  · have hmz : cgpEdgeMarker_BAUGP L y = z := by
      rw [cgpEdgeMarker_BAUGP, hz, cgpEdgeSum_eq_network_KA7_BAUGP L Se τ hcut hoff,
          tcpEdgeActual_none_BAUGP,
        edgeSumProfile_eq_cfsRamp_KA7, ← hτ, div_eq_inv_mul]
    rw [hmz, hτ]
  · have hz0 : z = 0 := by
      rw [hz, hτ0, mul_zero, cgpEdgeH_eq_zero_of_le (by norm_num), zero_mul]
    rw [hm, hz0, mul_zero, zero_smul, zero_smul]

/-- The components of the derivative of the actual input are the derivatives of its components. -/
theorem mvfderiv_tcpEdgeActual_apply_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) {x : X}
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se)) (tcpEdgeActual_BAUGP L Se
        τ) x)
    (w : TangentSpace 𝓘(ℝ, E3) x) (q : Option Se) :
    mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP L Se τ) x w q =
      mvfderiv 𝓘(ℝ, E3) (fun y => tcpEdgeActual_BAUGP L Se τ y q) x w := by
  have h := mvfderiv_comp_hasFDerivAt hV
    ((EuclideanSpace.proj q : EuclideanSpace ℝ (Option Se) →L[ℝ] ℝ).hasFDerivAt) w
  exact h.symm

/-- The actual input is smooth at `x` when its coordinates are. -/
theorem contMDiffAt_tcpEdgeActual_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) {x : X}
    (hτ : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ τ x)
    (hc : ∀ k ∈ Se, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.edgeB.coord_BAUGA k.1) x) :
    ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se)) ∞ (tcpEdgeActual_BAUGP L Se τ) x := by
  have hpi : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, Option Se → ℝ) ∞
      (fun y => fun q : Option Se => Option.elim q (τ y) fun k => L.edgeB.coord_BAUGA k.1.1 y)
          x := by
    rw [contMDiffAt_pi_space]
    intro q
    cases q with
    | none => exact hτ
    | some k => exact hc k.1 k.2
  exact ((EuclideanSpace.equiv (Option Se) ℝ).symm.toContinuousLinearMap.contMDiffAt).comp x hpi

end Actual

section Errors

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The `C¹` comparison of the actual and the affine model inputs** at `x`: from
`|η_k(x) − (A1_k η(x) + c1_k)| ≤ θ`, `|dη_k(w) − A1_k dη(w)| ≤ θν(w)` (`k ∈ S_e`) and the same
for `τ` against `Bτ, cτ`, the vector input differs by at most `√(#S_e + 1) θ` (values and
derivatives), and `‖M dη(w)‖ ≤ 4√(#S_e + 1) ν(w)` when the rows have norm `≤ 2` and
`‖dη(w)‖ ≤ 2ν(w)`. -/
theorem tcp_edgeActual_compare_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) {x : X} (η : X → ℝ²)
    (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) (hν : ∀ w, 0 ≤ ν w) {θ : ℝ} (hθ : 0 ≤ θ)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se)) (tcpEdgeActual_BAUGP L Se
        τ) x)
    (hk : ∀ k : Se, |L.edgeB.coord_BAUGA k.1.1 x - (A1 (.inr (.inr (.inl k.1))) (η x) +
        c1 (.inr (.inr (.inl k.1))))| ≤ θ ∧
      ∀ w, |mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA k.1.1) x w -
        A1 (.inr (.inr (.inl k.1))) (mvfderiv 𝓘(ℝ, E3) η x w)| ≤ θ * ν w)
    (hτ : |τ x - (Bτ (η x) + cτ)| ≤ θ ∧
      ∀ w, |mvfderiv 𝓘(ℝ, E3) τ x w - Bτ (mvfderiv 𝓘(ℝ, E3) η x w)| ≤ θ * ν w)
    (hrows : ∀ k : Se, ‖A1 (.inr (.inr (.inl k.1)))‖ ≤ 2) (hB : ‖Bτ‖ ≤ 2)
    (hη : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) η x w‖ ≤ 2 * ν w) :
    ‖tcpEdgeActual_BAUGP L Se τ x -
        (tcpEdgeLinear_BAUGP L Z Se A1 Bτ (η x) + tcpEdgeOffset_BAUGP L Z Se c1 cτ)‖ ≤
        Real.sqrt ((Se.card : ℝ) + 1) * θ ∧
      (∀ w, ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP L Se τ) x w -
        tcpEdgeLinear_BAUGP L Z Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤ Real.sqrt ((Se.card : ℝ) + 1) * θ * ν w) ∧
      ∀ w, ‖tcpEdgeLinear_BAUGP L Z Se A1 Bτ
          (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤ 4 * Real.sqrt ((Se.card : ℝ) + 1) * ν w := by
  classical
  set Ar : Option Se → ℝ² →L[ℝ] ℝ :=
    fun q : Option Se => Option.elim q Bτ fun j : Se => A1 (.inr (.inr (.inl j.1))) with hAr
  have hLin : tcpEdgeLinear_BAUGP L Z Se A1 Bτ = tcpEdgeRows Ar := rfl
  rw [hLin]
  have hcardU : ((Finset.univ : Finset (Option Se)).card : ℝ) = (Se.card : ℝ) + 1 := by
    rw [Finset.card_univ, Fintype.card_option, Fintype.card_coe]
    push_cast
    rfl
  refine ⟨?_, fun w => ?_, fun w => ?_⟩
  · have h := norm_le_of_active_blocks_KA6 (V := fun _ : Option Se => ℝ)
      (tcpEdgeActual_BAUGP L Se τ x - (tcpEdgeRows Ar (η x) +
        tcpEdgeOffset_BAUGP L Z Se c1 cτ))
      Finset.univ hθ (fun q _ => ?_) (fun q hq => (hq (Finset.mem_univ q)).elim)
    · rwa [hcardU] at h
    rw [PiLp.sub_apply, PiLp.add_apply, tcpEdgeRows_apply, Real.norm_eq_abs]
    cases q with
    | none => exact hτ.1
    | some k => exact (hk k).1
  · have h := norm_le_of_active_blocks_KA6 (V := fun _ : Option Se => ℝ)
      (mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP L Se τ) x w - tcpEdgeRows Ar (mvfderiv 𝓘(ℝ, E3) η x
          w))
      Finset.univ (mul_nonneg hθ (hν w)) (fun q _ => ?_)
      (fun q hq => (hq (Finset.mem_univ q)).elim)
    · rw [hcardU] at h
      calc _ ≤ Real.sqrt ((Se.card : ℝ) + 1) * (θ * ν w) := h
        _ = Real.sqrt ((Se.card : ℝ) + 1) * θ * ν w := by ring
    rw [PiLp.sub_apply, tcpEdgeRows_apply, Real.norm_eq_abs,
      mvfderiv_tcpEdgeActual_apply_KA7_BAUGP L Se τ hV w q]
    cases q with
    | none => exact hτ.2 w
    | some k => exact (hk k).2 w
  · have hM : ‖tcpEdgeRows Ar‖ ≤ Real.sqrt ((Fintype.card (Option Se) : ℝ)) * 2 :=
      norm_tcpEdgeRows_le Ar (by norm_num) (fun q => by
        cases q with
        | none => exact hB
        | some k => exact hrows k)
    have hcard : (Fintype.card (Option Se) : ℝ) = (Se.card : ℝ) + 1 := by
      rw [← hcardU, Finset.card_univ]
    rw [hcard] at hM
    have hsq0 : 0 ≤ Real.sqrt ((Se.card : ℝ) + 1) := Real.sqrt_nonneg _
    calc ‖tcpEdgeRows Ar (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤
        ‖tcpEdgeRows Ar‖ * ‖mvfderiv 𝓘(ℝ, E3) η x w‖ := (tcpEdgeRows Ar).le_opNorm _
      _ ≤ (Real.sqrt ((Se.card : ℝ) + 1) * 2) * (2 * ν w) :=
          mul_le_mul hM (hη w) (norm_nonneg _) (by positivity)
      _ = 4 * Real.sqrt ((Se.card : ℝ) + 1) * ν w := by ring

/-- The variable scale `σ = ρ/R` on `D_i`: `|σ(x) − 1| ≤ 10Λ` and `|dσ(w)| ≤ Λ|w|` (`|w|` of
`R⁻²g`), `σ` differentiable. -/
theorem scale_ratio_bounds_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) (hΛ : 0 ≤ Λ)
    {i x : X} (hx : x ∈ ball i (10 * ρ i)) :
    MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => ρ y / ρ i) x ∧ |ρ x / ρ i - 1| ≤ 10 * Λ ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, |mvfderiv 𝓘(ℝ, E3) (fun y => ρ y / ρ i) x w| ≤
        Λ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hlip : ∀ y z : X, |ρ y - ρ z| ≤ Λ * dist y z := by
    intro y z
    have h := L.lipschitz_scale.dist_le_mul y z
    rwa [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h
  have hρd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ρ x :=
    L.contMDiff_scale.mdifferentiableAt (by simp)
  obtain ⟨J, hJ⟩ : ∃ J : ℝ →L[ℝ] ℝ, ∀ t, J t = t / ρ i :=
    ⟨(ρ i)⁻¹ • ContinuousLinearMap.id ℝ ℝ, fun t => by
      simp [div_eq_inv_mul]⟩
  have hfun : (fun y => ρ y / ρ i) = fun y => J (ρ y) := funext fun y => (hJ _).symm
  have hσd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => ρ y / ρ i) x := by
    rw [hfun]
    exact J.differentiableAt.comp_mdifferentiableAt hρd
  refine ⟨hσd, ?_, fun w => ?_⟩
  · have hq : ρ x / ρ i - 1 = (ρ x - ρ i) / ρ i := by field_simp
    rw [hq, abs_div, abs_of_pos hri, div_le_iff₀ hri]
    have hd : dist x i < 10 * ρ i := mem_ball.mp hx
    have := hlip x i
    nlinarith
  · have hd : mvfderiv 𝓘(ℝ, E3) (fun y => J (ρ y)) x w = J (mvfderiv 𝓘(ℝ, E3) ρ x w) :=
      mvfderiv_comp_hasFDerivAt hρd J.hasFDerivAt w
    rw [hfun, hd, hJ, abs_div, abs_of_pos hri, div_le_iff₀ hri]
    have hb := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ x) hρd
      (fun y _ z _ => hlip y z) w
    have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) = (ρ i)⁻¹ * Real.sqrt (g.inner x w w) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hri).le]
    rw [hsq]
    calc |mvfderiv 𝓘(ℝ, E3) ρ x w| ≤ Λ * Real.sqrt (g.inner x w w) := hb
      _ = Λ * ((ρ i)⁻¹ * Real.sqrt (g.inner x w w)) * ρ i := by field_simp

/-- **(TG) for a listed edge block** (`j ∈ S_e`) at `x ∈ D_i`: with the cutoff identity
`ζ_k = f(η_k/Δ) g(τ/Δ)` on `D_i` and the input comparison `ε`, `L`, the error against the network
block of the model is `≤ C_B ε` (value) and `≤ (C_B + C_B L) ε ν` (derivative),
`C_B = tcpBlockBound`. -/
theorem tg_edge_tag_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ) {i x : X}
    (hx : x ∈ ball i (10 * ρ i))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, L.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (L.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τ y / Δ))
    (hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound) (j : L.edgeB.finite_centres.toFinset) (hj : j ∈ Se)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se)) (tcpEdgeActual_BAUGP L Se
        τ) x)
    (η : X → ℝ²) (ν : TangentSpace 𝓘(ℝ, E3) x → ℝ) {ε₀ Lc : ℝ}
    (hval : ‖tcpEdgeActual_BAUGP L Se τ x - tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ (η x)‖ ≤ ε₀)
    (hder : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP L Se τ) x w -
      tcpEdgeLinear_BAUGP L Z Se A1 Bτ
        (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤ ε₀ * ν w)
    (hbd : ∀ w, ‖tcpEdgeLinear_BAUGP L Z Se A1 Bτ
      (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤ Lc * ν w) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP L Z x (.inr (.inr (.inl j))) -
        blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
          (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ (η x)) (some ⟨j, hj⟩))‖ ≤ tcpBlockBound * ε₀ ∧
      ∀ w, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP L Z y (.inr (.inr (.inl j))))
          x w -
        fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
          (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) (some ⟨j, hj⟩))) (η x) (mvfderiv 𝓘(ℝ, E3) η x
              w)‖ ≤
        (tcpBlockBound + tcpBlockBound * Lc) * ε₀ * ν w := by
  have hri := hρ i
  have hsI : ∀ k : Se, (fun k : Se => ρ k.1.1 / ρ i) k ∈ Icc (1 / 2 : ℝ) 2 := hs
  have hcardT : (Fintype.card Se : ℝ) ≤ fc07ActiveBound := by
    rw [Fintype.card_coe]
    exact hcard
  have hb := tcp_networkBlock_bounds_KA7 hΔ (fun k : Se => ρ k.1.1 / ρ i) hsI hcardT
    (some ⟨j, hj⟩)
  have hf : (fun y => cgpGlobalMap_BAUGP L Z y (.inr (.inr (.inl j)))) =ᶠ[𝓝 x]
      fun y => ρ i • (fun v => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) v
        (some ⟨j, hj⟩))) (tcpEdgeActual_BAUGP L Se τ y) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact edge_block_eq_network_KA7_BAUGP L Z Se τ j hj (hcut y hy j hj)
  exact tg_block_pointwise_KA6 (I := 𝓘(ℝ, E3))
    ((contDiff_tcpNetworkBlock_KA7 Δ _ _).of_le (by simp)) (fun y => (hb y).1)
    (fun y => (hb y).2) hri.ne' hf hV η _ _ ν hval hder hbd

/-- **(TG) for the `E'` block** at `x ∈ D_i` (FC11's variable factor `σ = ρ/R`): with the cutoff
identities on `D_i` (listed `ζ_k = f(η_k/Δ) g(τ/Δ)`, unlisted zero, `τ = t` or (`τ = 0` and the
marker zero)) and the input comparison `ε`, `L`, the error against the model's `E'` network block is
`≤ 10Λ·20√(#S_e+1)Δ + C_B ε` (value) and `(Λ·20√(#S_e+1)Δ + 10Λ C_B (L + ε) + (C_B + C_B L) ε) ν`
(derivative). -/
theorem tg_edgeMarker_tag_KA7_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (τ : X → ℝ) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) {i x : X}
    (hx : x ∈ ball i (10 * ρ i))
    (hcut : ∀ y ∈ ball i (10 * ρ i), ∀ k ∈ Se, L.edgeB.cutoff_BAUGA k.1 y =
      edgeCoordinateProfile (L.edgeB.coord_BAUGA k.1 y / Δ) * edgeHeightProfile (τ y / Δ))
    (hoff : ∀ y ∈ ball i (10 * ρ i), ∀ k ∉ Se, L.edgeB.cutoff_BAUGA k.1 y = 0)
    (hτ : ∀ y ∈ ball i (10 * ρ i), τ y = cgpHeight_BAUGP L y ∨ (τ y = 0 ∧ cgpEdgeMarker_BAUGP L y =
        0))
    (hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hcard : (Se.card : ℝ) ≤ fc07ActiveBound)
    (hV : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Option Se)) (tcpEdgeActual_BAUGP L Se
        τ) x)
    (η : X → ℝ²) {ε₀ Lc : ℝ}
    (hval : ‖tcpEdgeActual_BAUGP L Se τ x - tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ (η x)‖ ≤ ε₀)
    (hder : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (tcpEdgeActual_BAUGP L Se τ) x w -
      tcpEdgeLinear_BAUGP L Z Se A1 Bτ
        (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤ ε₀ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hbd : ∀ w, ‖tcpEdgeLinear_BAUGP L Z Se A1 Bτ
      (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤ Lc * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP L Z x (cgpEdgeTag_BAUGP L Z) -
        blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
          (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ (η x)) none)‖ ≤
        10 * Λ * (20 * Real.sqrt ((Se.card : ℝ) + 1) * Δ) + tcpBlockBound * ε₀ ∧
      ∀ w, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP L Z y (cgpEdgeTag_BAUGP L Z))
          x w -
        fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
          (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) none)) (η x) (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤
        (Λ * (20 * Real.sqrt ((Se.card : ℝ) + 1) * Δ) + 10 * Λ * (tcpBlockBound * (Lc + ε₀)) +
          (tcpBlockBound + tcpBlockBound * Lc) * ε₀) * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hsI : ∀ k : Se, (fun k : Se => ρ k.1.1 / ρ i) k ∈ Icc (1 / 2 : ℝ) 2 := hs
  have hcardT : (Fintype.card Se : ℝ) ≤ fc07ActiveBound := by
    rw [Fintype.card_coe]
    exact hcard
  have hb := tcp_networkBlock_bounds_KA7 hΔ (fun k : Se => ρ k.1.1 / ρ i) hsI hcardT none
  obtain ⟨hσd, hσ0, hσ1⟩ := scale_ratio_bounds_KA7_BAUGP (hρ := hρ) (g := g) (hmetric := hmetric) L
      hΛ hx
  have hf : (fun y => cgpGlobalMap_BAUGP L Z y (cgpEdgeTag_BAUGP L Z)) =ᶠ[𝓝 x]
      fun y => (ρ i * (ρ y / ρ i)) • (fun v => blockLift_KC3 (tcpNetwork Δ
        (fun k : Se => ρ k.1.1 / ρ i) v none)) (tcpEdgeActual_BAUGP L Se τ y) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact edgeMarker_block_eq_network_KA7_BAUGP L Z Se τ (hcut y hy) (hoff y hy) (hτ y hy)
  have hGm : ‖(fun v => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) v none))
      (tcpEdgeActual_BAUGP L Se τ x)‖ ≤ 20 * Real.sqrt ((Se.card : ℝ) + 1) * Δ := by
    change ‖blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
      (tcpEdgeActual_BAUGP L Se τ x) none)‖ ≤ _
    rw [norm_blockLift_apply_KC3]
    refine (PiLp.norm_apply_le _ none).trans ?_
    have h := norm_tcpNetwork_le_KA7 hΔ (fun k : Se => ρ k.1.1 / ρ i) hsI
      (tcpEdgeActual_BAUGP L Se τ x)
    rwa [Fintype.card_coe] at h
  exact tg_scaled_block_pointwise_KA6 (I := 𝓘(ℝ, E3))
    ((contDiff_tcpNetworkBlock_KA7 Δ _ _).of_le (by simp)) (fun y => (hb y).1)
    (fun y => (hb y).2) hri.ne' hf hV hσd η _ _ _ hval hder hbd hσ0 hσ1 hGm

end Errors


end DifferentialGeometry.Geometry.Collapse
