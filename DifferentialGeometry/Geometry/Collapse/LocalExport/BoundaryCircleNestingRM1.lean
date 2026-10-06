import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskRimFibreOF1

/-!
# BCF02 rim clauses, G3: the circle nesting on the actual slot as access lemmas (lane S-RIM81)

External review 81 (d), D81-8: on `actualSlotsV2_BAUGD` one has `π₀ = id`, hence `f₁ = E`, and
`f₂ = π₁ ∘ f₁`, `f₃ = π₂ ∘ f₁`, `T` is a function of `E`: NO nesting field is added to the BASES
exits, only access theorems on the actual chain. (`T` is NOT asked to factor through `f₂`.)

* `BoundaryGaf02Chain.circle_stage_eq_E_RM1`: `f₁ = E`;
* `BoundaryGaf02Chain.final_data_eq_of_circle_eq_RM1`: on one `f₁`-fibre all three stage maps and
  the height ratio `T` agree (stage `1` and `T` are `edgeData_eq_of_stageMap_zero_eq_OF1`, stage `2`
  is new);
* `BoundaryGaf02Chain.stageMap_eq_proj_E_RM1`: every stage map is `π_st ∘ E` (definition).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {D : BoundaryAugmentedData S (actualSlotsV2_BAUGD S)} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

variable (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- Every stage map is `π_st ∘ E`. -/
theorem stageMap_eq_proj_E_RM1 (st : Fin 3) (p : W.Carrier) :
    C.stageMap st p = (actualSlotsV2_BAUGD S).stageProj st (C.E p) :=
  rfl

/-- **`f₁ = E` on the actual slot** (`π₀ = id`, `stageProj_zero_V2_BAUGD`). -/
theorem circle_stage_eq_E_RM1 (p : W.Carrier) : C.stageMap 0 p = C.E p :=
  C.stageMap_zero_eq_E_OF1 p

/-- **The nesting**: on one `f₁`-fibre all three stage maps and the height ratio `T` agree. -/
theorem final_data_eq_of_circle_eq_RM1 {p q : W.Carrier}
    (h : C.stageMap 0 p = C.stageMap 0 q) :
    (∀ st : Fin 3, C.stageMap st p = C.stageMap st q) ∧
      C.heightRatio p = C.heightRatio q := by
  have hE : C.E p = C.E q := by
    rw [← C.circle_stage_eq_E_RM1, ← C.circle_stage_eq_E_RM1]
    exact h
  refine ⟨fun st => ?_, ?_⟩
  · rw [C.stageMap_eq_proj_E_RM1, C.stageMap_eq_proj_E_RM1, hE]
  · exact (C.edgeData_eq_of_stageMap_zero_eq_OF1 h.symm).2.symm

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
