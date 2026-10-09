import DifferentialGeometry.Geometry.Fibration.ActualFirstGraphModel
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualFirstGraphModel (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFirstGraphModel.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA6_BAUGP : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Network

variable {ι : Type*} [Fintype ι]

end Network

section Model

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The affine network input `U(a)`: `u_j`-coordinate `A1_j a + c1_j` (edge tag `j ∈ Se`) and
`v`-coordinate `Bτ a + cτ`. -/
def tcpEdgeInput_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (a : ℝ²) : EuclideanSpace ℝ (Option
        Se) :=
  tcpEdgeRows (fun o => Option.elim o Bτ fun j => A1 (.inr (.inr (.inl j.1)))) a +
    WithLp.toLp 2 (fun o => Option.elim o cτ fun j => c1 (.inr (.inr (.inl j.1))))

open Classical in
/-- **The blocks of TCP05's model graph** at the circle reference `i` (see the module
docstring). -/
def tcpModelComponent_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    (t : CGPTag_BAUGP L Z) → ℝ² → WithLp 2 (ℝ² × ℝ)
  | .inl j =>
      if j.1 = i then fun a => WithLp.toLp 2 (a, 1)
      else if (.inl j : CGPTag_BAUGP L Z) ∈ S then
        fun a => scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
          (Ac (.inl j) a + cc (.inl j))
      else 0
  | .inr (.inl j) =>
      if (.inr (.inl j) : CGPTag_BAUGP L Z) ∈ S then
        fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
          (A1 (.inr (.inl j)) a + c1 (.inr (.inl j))))
      else 0
  | .inr (.inr (.inl j)) =>
      if hj : j ∈ Se then
        fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
          (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) (some ⟨j, hj⟩))
      else 0
  | .inr (.inr (.inr (.inl k))) =>
      if (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z) ∈ S then
        fun a => blockLift_KC3 (zeroModelBlock
          ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
          (A1 (.inr (.inr (.inr (.inl k)))) a + c1 (.inr (.inr (.inr (.inl k))))))
      else 0
  | .inr (.inr (.inr (.inr false))) => fun _ => WithLp.toLp 2 (0, 1)
  | .inr (.inr (.inr (.inr true))) =>
      fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) none)

/-- **TCP05's model graph** `Φ_i : ℝ² → H`. -/
def tcpModelGraph_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP
        L Z => ℝ²) :=
  orthogonalBlocks (tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ)

end Model

section BlockBounds

end BlockBounds

section ModelFacts

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

theorem tcpEdgeInput_eq_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (Se : Finset L.edgeB.finite_centres.toFinset) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ = fun a =>
      tcpEdgeRows (fun o => Option.elim o Bτ fun j => A1 (.inr (.inr (.inl j.1)))) a +
        WithLp.toLp 2 (fun o => Option.elim o cτ fun j => c1 (.inr (.inr (.inl j.1)))) :=
  rfl

open Classical in
/-- Every block of the model is smooth. -/
theorem contDiff_tcpModelComponent_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (t : CGPTag_BAUGP L Z) :
    ContDiff ℝ ∞ (tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t) := by
  have hU : ContDiff ℝ ∞ (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ) := by
    rw [tcpEdgeInput_eq_BAUGP]
    exact (tcpEdgeRows (fun o : Option Se => Option.elim o Bτ
      fun j => A1 (.inr (.inr (.inl j.1))))).contDiff.add contDiff_const
  have hnet : ∀ o : Option Se, ContDiff ℝ ∞ (fun a => blockLift_KC3
      (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a)
          o)) := by
    intro o
    have hfun : (fun a => blockLift_KC3
        (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) o)) =
        blockLift_KC3 ∘ ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Option Se => WithLp 2 (ℝ × ℝ)) o) ∘
          (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) ∘ tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ)) :=
              rfl
    rw [hfun]
    exact blockLift_KC3.contDiff.comp
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Option Se => WithLp 2 (ℝ × ℝ)) o).contDiff.comp
        ((contDiff_tcpNetwork _ _).comp hU))
  rcases t with j | j | j | k | q
  · simp only [tcpModelComponent_BAUGP]
    split_ifs
    · exact tcp_own_bounds_KA6.1
    · exact (contDiff_scaledCutoffBlock circleCutoffBump_LC87.contDiff _).comp
        ((Ac _).contDiff.add contDiff_const)
    · exact contDiff_const
  · simp only [tcpModelComponent_BAUGP]
    split_ifs
    · exact blockLift_KC3.contDiff.comp ((contDiff_sgpModelBlock _ _).comp
        ((A1 _).contDiff.add contDiff_const))
    · exact contDiff_const
  · simp only [tcpModelComponent_BAUGP]
    split_ifs with hj
    · exact hnet _
    · exact contDiff_const
  · simp only [tcpModelComponent_BAUGP]
    split_ifs
    · exact blockLift_KC3.contDiff.comp ((contDiff_zeroModelBlock _).comp
        ((A1 _).contDiff.add contDiff_const))
    · exact contDiff_const
  · cases q
    · exact contDiff_const
    · exact hnet none

theorem contDiff_tcpModelGraph_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    ContDiff ℝ ∞ (tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ) :=
  contDiff_orthogonalBlocks (contDiff_tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ)

/-- The own block of the model is `(a, 1)`. -/
theorem tcpModelGraph_own_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (j : L.circle.finite_centres.toFinset)
    (hj : j.1 = i) (a : ℝ²) :
    tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ a (.inl j) = WithLp.toLp 2 (a, 1) := by
  change tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ (.inl j) a = _
  simp only [tcpModelComponent_BAUGP, hj, ite_true]

open Classical in
/-- The active tags of the model: the listed set `S`, the network edges `Se`, the scale and
`E'` tags. -/
def tcpModelActive_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset) :
    Finset (CGPTag_BAUGP L Z) :=
  S ∪ Se.image (fun j => (.inr (.inr (.inl j)) : CGPTag_BAUGP L Z)) ∪ {cgpScaleTag_BAUGP L Z,
      cgpEdgeTag_BAUGP L Z}

open Classical in
/-- Off the active tags every block of the model is the zero function (the own tag is in `S`). -/
theorem tcpModelComponent_eq_zero_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    (hown : ∀ j : L.circle.finite_centres.toFinset, j.1 = i → (.inl j : CGPTag_BAUGP L Z) ∈ S)
    (t : CGPTag_BAUGP L Z) (ht : t ∉ tcpModelActive_BAUGP L Z S Se) :
    tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t = 0 := by
  have hS : t ∉ S := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  rcases t with j | j | j | k | q
  · have hji : j.1 ≠ i := fun h => hS (hown j h)
    simp only [tcpModelComponent_BAUGP, hji, hS, ite_false]
  · simp only [tcpModelComponent_BAUGP, hS, ite_false]
  · have hj : j ∉ Se := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ h)))
    simp only [tcpModelComponent_BAUGP, hj, dite_false]
  · simp only [tcpModelComponent_BAUGP, hS, ite_false]
  · exact (ht (Finset.mem_union_right _ (by cases q <;> simp [cgpScaleTag_BAUGP,
      cgpEdgeTag_BAUGP]))).elim

/-- Every network block of the model (edge `j ∈ Se` or `E'`) has `C²` bounds `tcpBlockBound`. -/
theorem tcp_network_component_bounds_KA6_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (Se : Finset L.edgeB.finite_centres.toFinset) (A1 : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ)
    (hE : ∀ j ∈ Se, ‖A1 (.inr (.inr (.inl j)))‖ ≤ 2 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hB : ‖Bτ‖ ≤ 2) (hcountE : (Se.card : ℝ) ≤ fc07ActiveBound) (o : Option Se) (b : ℝ²) :
    ‖fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) o)) b‖ ≤ tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeInput_BAUGP L Z Se A1 c1 Bτ cτ a) o))) b‖ ≤ tcpBlockBound := by
  have hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 := fun k => (hE k.1 k.2).2
  have hcard : (Fintype.card Se : ℝ) ≤ fc07ActiveBound := by
    rw [Fintype.card_coe]
    exact hcountE
  have hA : ∀ o' : Option Se,
      ‖(Option.elim o' Bτ fun j => A1 (.inr (.inr (.inl j.1))) : ℝ² →L[ℝ] ℝ)‖ ≤ 2 := by
    intro o'
    cases o' with
    | none => exact hB
    | some k => exact (hE k.1 k.2).1
  exact tcp_network_block_bounds_KA6 hΔ (fun k : Se => ρ k.1.1 / ρ i) hs hcard
    (fun o' => Option.elim o' Bτ fun j => A1 (.inr (.inr (.inl j.1)))) hA
    (WithLp.toLp 2 (fun o' => Option.elim o' cτ fun j => c1 (.inr (.inr (.inl j.1))))) o b

open Classical in
/-- Every active block of the model has `C²` bounds `tcpBlockBound`. -/
theorem tcpModelComponent_bounds_KA6_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ)
    (hC : ∀ j : L.circle.finite_centres.toFinset, j.1 ≠ i → (.inl j : CGPTag_BAUGP L Z) ∈ S →
      ‖Ac (.inl j)‖ ≤ 1 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hS : ∀ j : L.slim.finite_centres.toFinset, (.inr (.inl j) : CGPTag_BAUGP L Z) ∈ S →
      ‖A1 (.inr (.inl j))‖ ≤ 1 ∧ 99 / 100 ≤ ρ j.1 / ρ i)
    (hZ : ∀ k : Z.finite_centres.toFinset, (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z) ∈ S →
      ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1 ∧
        1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hE : ∀ j ∈ Se, ‖A1 (.inr (.inr (.inl j)))‖ ≤ 2 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hB : ‖Bτ‖ ≤ 2) (hcountE : (Se.card : ℝ) ≤ fc07ActiveBound) (t : CGPTag_BAUGP L Z) (b : ℝ²) :
    ‖fderiv ℝ (tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t) b‖ ≤ tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t)) b‖ ≤
        tcpBlockBound := by
  have hB1 := one_le_tcpBlockBound
  have hB0 : 0 ≤ tcpBlockBound := by linarith
  have hge := tcpBlockBound_ge_KA6.1
  have hP := tcpProfileBound_spec
  have hnet := tcp_network_component_bounds_KA6_BAUGP L Z i Se A1 c1 Bτ cτ hΔ hE hB hcountE
  rcases t with j | j | j | k | q
  · simp only [tcpModelComponent_BAUGP]
    split_ifs with hji hjS
    · exact ⟨(tcp_own_bounds_KA6.2 b).1.trans hB1, (tcp_own_bounds_KA6.2 b).2.trans hB1⟩
    · exact tcp_circle_block_bounds_KA6 (hC j hji hjS).2 _ (hC j hji hjS).1 _ b
    · exact zero_block_bounds_KA6 b
  · simp only [tcpModelComponent_BAUGP]
    split_ifs with hjS
    · have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
      have hW (y : ℝ) := sgpModelBlock_derivative_bounds hℓ (hS j hjS).2 y
      have hsP : 50 * (sgpProfileBound + 1) ≤ tcpBlockBound := by linarith [hP.2.1]
      exact tcp_lifted_block_bounds_KA6 ((contDiff_sgpModelBlock _ _).of_le (by simp)) hB0
        (fun y => (hW y).1.trans hsP) (fun y => (hW y).2.trans hsP) _ (hS j hjS).1 _ b
    · exact zero_block_bounds_KA6 b
  · simp only [tcpModelComponent_BAUGP]
    split_ifs with hj
    · exact hnet _ b
    · exact zero_block_bounds_KA6 b
  · simp only [tcpModelComponent_BAUGP]
    split_ifs with hkS
    · have hW (y : ℝ) := zeroModelBlock_derivative_bounds (hZ k hkS).2 y
      have hzP : 50 * (zeroProfileBound + 1) ≤ tcpBlockBound := by linarith [hP.2.2.1]
      exact tcp_lifted_block_bounds_KA6 ((contDiff_zeroModelBlock _).of_le (by simp)) hB0
        (fun y => (hW y).1.trans hzP) (fun y => (hW y).2.trans hzP) _ (hZ k hkS).1 _ b
    · exact zero_block_bounds_KA6 b
  · cases q
    · exact scale_block_bounds_KA6 b
    · exact hnet none b

open Classical in
/-- The active set of the model has at most `N + 3` tags. -/
theorem tcpModelActive_card_le_KA6_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (hcount : (S.card : ℝ) + Se.card ≤ fc07ActiveBound + 1) :
    ((tcpModelActive_BAUGP L Z S Se).card : ℝ) ≤ fc07ActiveBound + 3 := by
  have h1 : (tcpModelActive_BAUGP L Z S Se).card ≤
      (S ∪ Se.image (fun j => (.inr (.inr (.inl j)) : CGPTag_BAUGP L Z))).card +
        ({cgpScaleTag_BAUGP L Z, cgpEdgeTag_BAUGP L Z} : Finset (CGPTag_BAUGP L Z)).card :=
            Finset.card_union_le _ _
  have h2 : (S ∪ Se.image (fun j => (.inr (.inr (.inl j)) : CGPTag_BAUGP L Z))).card ≤
      S.card + Se.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have h3 : ({cgpScaleTag_BAUGP L Z, cgpEdgeTag_BAUGP L Z} : Finset (CGPTag_BAUGP L Z)).card ≤ 2 :=
    Finset.card_le_two
  have h4 : (tcpModelActive_BAUGP L Z S Se).card ≤ S.card + Se.card + 2 := by omega
  have h5 : ((tcpModelActive_BAUGP L Z S Se).card : ℝ) ≤ (S.card : ℝ) + Se.card + 2 := by
    exact_mod_cast h4
  linarith

open Classical in
/-- **TCP05's model bounds (kernel form).** With `Δ ≥ 1`, the own tag in `S`, coisometric circle
rows (`‖Ac‖ ≤ 1`, `s_j ∈ [1/2, 2]`), slim rows `‖A1‖ ≤ 1` with `s_j ≥ 99/100`, zero rows
`‖A1‖ ≤ 1` with `R₀/ρ(i) ≥ 1`, edge input rows `‖A1‖ ≤ 2` with `s_j ∈ [1/2, 2]`, `‖Bτ‖ ≤ 2`, and
`#S + #Se ≤ N + 1`, `#Se ≤ N` (`N = fc07ActiveBound`): `‖DΦ_i‖, ‖D²Φ_i‖ ≤ tcpGraphConst`. -/
theorem tcp05_model_bounds_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : X)
    (S : Finset (CGPTag_BAUGP L Z)) (Se : Finset L.edgeB.finite_centres.toFinset)
    (Ac : CGPTag_BAUGP L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag_BAUGP L Z → ℝ²) (A1 : CGPTag_BAUGP L Z → ℝ²
        →L[ℝ] ℝ)
    (c1 : CGPTag_BAUGP L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ)
    (hown : ∀ j : L.circle.finite_centres.toFinset, j.1 = i → (.inl j : CGPTag_BAUGP L Z) ∈ S)
    (hC : ∀ j : L.circle.finite_centres.toFinset, j.1 ≠ i → (.inl j : CGPTag_BAUGP L Z) ∈ S →
      ‖Ac (.inl j)‖ ≤ 1 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hS : ∀ j : L.slim.finite_centres.toFinset, (.inr (.inl j) : CGPTag_BAUGP L Z) ∈ S →
      ‖A1 (.inr (.inl j))‖ ≤ 1 ∧ 99 / 100 ≤ ρ j.1 / ρ i)
    (hZ : ∀ k : Z.finite_centres.toFinset, (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z) ∈ S →
      ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1 ∧
        1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hE : ∀ j ∈ Se, ‖A1 (.inr (.inr (.inl j)))‖ ≤ 2 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hB : ‖Bτ‖ ≤ 2) (hcount : (S.card : ℝ) + Se.card ≤ fc07ActiveBound + 1)
    (hcountE : (Se.card : ℝ) ≤ fc07ActiveBound) (a : ℝ²) :
    ‖fderiv ℝ (tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ) a‖ ≤ tcpGraphConst ∧
      ‖fderiv ℝ (fderiv ℝ (tcpModelGraph_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ)) a‖ ≤
          tcpGraphConst := by
  have hB0 : 0 ≤ tcpBlockBound := le_trans zero_le_one one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hblock := tcpModelComponent_bounds_KA6_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ hΔ hC hS hZ hE hB
    hcountE
  have hmain := orthogonalBlocks_support_bounds_KA6
    (fun t => (contDiff_tcpModelComponent_BAUGP L Z i S Se Ac cc A1 c1 Bτ cτ t).of_le (by simp))
    (tcpModelActive_BAUGP L Z S Se) hB0 (tcpModelComponent_eq_zero_BAUGP L Z i S Se Ac cc A1 c1 Bτ
        cτ hown)
    (fun t _ b => (hblock t b).1) (fun t _ b => (hblock t b).2) a
  have hcard := tcpModelActive_card_le_KA6_BAUGP L Z S Se hcount
  have hsq : Real.sqrt ((tcpModelActive_BAUGP L Z S Se).card : ℝ) ≤ fc07ActiveBound + 3 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (tcpModelActive_BAUGP L Z S Se).card]
  have hfin : Real.sqrt ((tcpModelActive_BAUGP L Z S Se).card : ℝ) * tcpBlockBound ≤
      tcpGraphConst := by
    rw [tcpGraphConst]
    exact mul_le_mul_of_nonneg_right hsq hB0
  exact ⟨hmain.1.trans hfin, hmain.2.trans hfin⟩

end ModelFacts


end DifferentialGeometry.Geometry.Collapse
