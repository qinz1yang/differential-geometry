import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutCoverOBD
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.StageCircleChartTrivOBDd

/-!
# The circle trivializations of the produced cut (lane S-BD2d, suffix `_OBDd`), group G9

Lane O-BD1 (by S-BD2d), hlift, the cut facts `H`: the four trivialization fields of
`CircleCutFacts74` (`neighborhood`, `mem_neighborhood`, `trivialization`,
`projection_trivialization`) for ANY `P : BoundaryStageGeometry74b zc` and the produced good open
circle base `P.cut.circleBaseOpen` (whatever it is), and the whole `CircleCutFacts74` of the cut.

* `BoundaryStageGeometry74b.circle_charts_OBDd`: the whole-fibre layer's smooth `ℝ² × S¹` chart of
  `f₁` at `ι b` (`dec.fibres.circle_chart`) gives `σ' = q₀ ∘ φ ∘ (·, 1)` and a local trivialization
  of the produced `q₀` over `range σ'` (`exists_stageTrivialization_of_chart_OBDd`; the smoothness
  of `ι` is not used);
* `BoundaryStageGeometry74b.exists_circleTrivFields_OBDd`: the four fields over `circleBaseOpen`
  (`exists_circleCutTriv_of_charts_OBDd`);
* `BoundaryGaf02ChainE.exists_circleCutFacts_OBDd`: `Nonempty (CircleCutFacts74 P.stageGeometry
  P.cut)` — with G7c's `circle_proper_OBD`, `circle_cbase_compact_OBD` and G7d's
  `cut_saturation_OBD` (premise `geom`).
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Triv

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {dec : BoundaryActualDecompositionV2b C} {zc : BoundaryZeroCuspExit74b C dec}
  (P : BoundaryStageGeometry74b zc)

include P in
/-- **The circle stage is locally trivial over a neighbourhood of every base point**, by the
smooth `ℝ² × S¹` chart of the whole-fibre layer at the image point. -/
theorem BoundaryStageGeometry74b.circle_charts_OBDd :
    ∀ b : P.stageGeometry.circle.Base, ∃ N : TopologicalSpace.Opens P.stageGeometry.circle.Base,
      b ∈ N ∧ ∃ T : (TopologicalSpace.Opens.comap P.stageGeometry.circle.proj N)
        ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (N × Circle),
        ∀ x, ((T x).1).val = P.stageGeometry.circle.proj x.val := by
  intro b
  obtain ⟨σ, φ, O, h0, hs, he, hi, hO, hr, hφ, hrφ, hf⟩ :=
    dec.fibres.circle_chart (P.ιcircle b) (P.circle_range ⟨b, rfl⟩)
  have hpar : (P.circle.parent : Set W.Carrier) = dec.bases.source 0 :=
    P.circle_ident.parent_eq
  have hφX : ∀ (x : ℝ²) (z : Circle), φ (x, z) ∈ P.circle.parent := fun x z => by
    have h : φ (x, z) ∈ range φ := mem_range_self _
    rw [hrφ] at h
    rw [← SetLike.mem_coe, hpar]
    exact h.1
  have hι : ∀ (x : ℝ²) (z : Circle) (h : φ (x, z) ∈ P.circle.parent),
      P.ιcircle (P.circle.proj ⟨φ (x, z), h⟩) = σ x := fun x z h => by
    rw [P.circle_ident.proj_eq]
    exact hf x z
  let σ' : ℝ² → P.circle.Base := fun x => P.circle.proj ⟨φ (x, 1), hφX x 1⟩
  have hσ'ι : ∀ x, P.ιcircle (σ' x) = σ x := fun x => hι x 1 (hφX x 1)
  have hσinj : Injective σ' := fun x x' hx =>
    he.injective (by rw [← hσ'ι x, ← hσ'ι x', hx])
  have hproj : ∀ (x : ℝ²) (z : Circle) (h : φ (x, z) ∈ P.circle.parent),
      P.circle.proj ⟨φ (x, z), h⟩ = σ' x := fun x z h =>
    P.circle_ident.emb.injective (by rw [hι x z h, hσ'ι x])
  have hrange : ∀ (p : W.Carrier) (hp : p ∈ P.circle.parent),
      P.circle.proj ⟨p, hp⟩ ∈ range σ' → p ∈ range φ := by
    rintro p hp ⟨x, hx⟩
    have hfp : C.stageMap 0 p = σ x := by
      rw [← P.circle_ident.proj_eq ⟨p, hp⟩, ← hx, hσ'ι x]
    have hX : p ∈ dec.bases.source 0 := by
      rw [← hpar]
      exact hp
    rw [hrφ]
    exact ⟨hX, ⟨x, hfp.symm⟩⟩
  obtain ⟨N, hNr, T, hT⟩ := exists_stageTrivialization_of_chart_OBDd P.circle σ' φ hσinj hφ hφX
    hproj hrange
  refine ⟨N, ?_, T, hT⟩
  rw [← SetLike.mem_coe, hNr]
  exact ⟨0, P.circle_ident.emb.injective ((hσ'ι 0).trans h0)⟩

include P in
/-- **The four trivialization fields of `CircleCutFacts74` for the produced cut**, over the good
open circle base `P.cut.circleBaseOpen`. -/
theorem BoundaryStageGeometry74b.exists_circleTrivFields_OBDd :
    ∃ nb : P.cut.circleBaseOpen → TopologicalSpace.Opens P.cut.circleBaseOpen,
      (∀ c, c ∈ nb c) ∧
      ∃ tr : ∀ c, (TopologicalSpace.Opens.comap
          (P.stageGeometry.circle.restrictProj P.cut.circleBaseOpen) (nb c))
          ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ (nb c × Circle),
        ∀ c x, ((tr c x).1).val =
          P.stageGeometry.circle.restrictProj P.cut.circleBaseOpen x.val :=
  exists_circleCutTriv_of_charts_OBDd P.stageGeometry.circle P.circle_charts_OBDd
    P.cut.circleBaseOpen

end Triv

section Facts

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}

include C in
/-- **`CircleCutFacts74` of the produced cut**: trivializations (G9), properness and compact
remaining base (G7c) and saturation `M₃ = q₀⁻¹(C₁)` (G7d). -/
theorem exists_circleCutFacts_OBDd (P : BoundaryStageGeometry74b zc)
    (geom : BoundaryGeometricExports74b C.toChain dec) :
    Nonempty (CircleCutFacts74 P.stageGeometry P.cut) := by
  obtain ⟨nb, hmem, tr, hp⟩ := P.exists_circleTrivFields_OBDd
  exact ⟨{ neighborhood := nb
           mem_neighborhood := hmem
           trivialization := tr
           projection_trivialization := hp
           proper := P.circle_proper_OBD
           cbase_compact := C.circle_cbase_compact_OBD P geom
           saturation := C.cut_saturation_OBD P geom }⟩

end BoundaryGaf02ChainE

end Facts

end DifferentialGeometry.Geometry.Collapse
