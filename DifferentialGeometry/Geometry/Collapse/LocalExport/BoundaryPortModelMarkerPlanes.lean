import DifferentialGeometry.Geometry.Fibration.ActualModelMarkerPlanes
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualModelMarkerPlanes (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualModelMarkerPlanes.lean` by
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

section Generic

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Generic

section Models

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **GAF04's plane half for TCP05's model** (circle tags): at `a`, the marker of the circle block
`j` of `Φ_i = tcpModelGraph_BAUGP` annihilates `DΦ_i(a)` when `j` is the own tag, unlisted, or
listed with
its cutoff argument in the open plateau `‖s_j⁻¹(A_j a + c_j)‖ < 8` (`s_j = ρ(j)/ρ(i)`). -/
theorem tcpModelGraph_marker_fderiv_GAFS_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (j : L.circle.finite_centres.toFinset)
    (a : ℝ²)
    (hplat : (.inl j : CGPTag_BAUGP L Z) ∈ S → j.1 ≠ i →
      ‖(ρ j.1 / ρ i)⁻¹ • (Ac (.inl j) a + cc (.inl j))‖ < 8) (h : ℝ²) :
    blockMarkerCLM (.inl j : CGPTag_BAUGP L Z) (fderiv ℝ (tcpModelGraph_BAUGP L Z i S Se Ac cc A1
        c1 Bτ cτ) a h)
      = 0 := by
  classical
  have hΦ : DifferentiableAt ℝ (tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ) a :=
    ((contDiff_tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ).differentiable (by simp)) a
  have hval : ∀ y, tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ y (.inl j) =
      tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ (.inl j) y := fun _ => rfl
  by_cases hji : j.1 = i
  · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 1) _ hΦ (Eventually.of_forall fun y => ?_) h
    dsimp only
    rw [hval]
    simp only [tcpModelComponent_BAUGP, hji, ite_true]
    rfl
  · by_cases hS : (.inl j : CGPTag_BAUGP L Z) ∈ S
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := ρ j.1 / ρ i) _ hΦ ?_ h
      have hev := scaledCutoffBlock_snd_eventually_GAFS (s := ρ j.1 / ρ i) (r := 8)
        (φ := (circleCutoffBump_LC87 : ℝ² → ℝ))
        (fun z hz => circleCutoffBump_LC87.one_of_mem_closedBall (by
          rw [mem_closedBall, dist_zero_right]; exact hz))
        (u := fun y => Ac (.inl j) y + cc (.inl j))
        ((Ac (.inl j)).continuous.add continuous_const).continuousAt (hplat hS hji)
      filter_upwards [hev] with y hy
      rw [hval]
      simp only [tcpModelComponent_BAUGP, hji, hS, ite_true, ite_false]
      exact hy
    · refine blockMarkerCLM_fderiv_eq_zero_GAFS (c := 0) _ hΦ (Eventually.of_forall fun y => ?_) h
      dsimp only
      rw [hval]
      simp only [tcpModelComponent_BAUGP, hji, hS, ite_false]
      rfl

/-- **EDP01's first-cloud planes have zero scale component**: the scale block of TCP05's model is
the constant `(0, 1)`, so `DΦ_i(a)h` has zero scale block. -/
theorem tcpModelGraph_scale_fderiv_GAFS_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (a h : ℝ²) :
    fderiv ℝ (tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ) a h (cgpScaleTag_BAUGP L Z) =
        0 := by
  have hd : ∀ t, Differentiable ℝ (tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t) := fun t
      =>
    (contDiff_tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t).differentiable (by simp)
  rw [tcpModelGraph_BAUGP, fderiv_orthogonalBlocks_apply_KA6 hd a h (cgpScaleTag_BAUGP L Z)]
  change fderiv ℝ (fun _ : ℝ² => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ))) a h = 0
  rw [fderiv_const_apply]
  rfl

end Models


end DifferentialGeometry.Geometry.Collapse
