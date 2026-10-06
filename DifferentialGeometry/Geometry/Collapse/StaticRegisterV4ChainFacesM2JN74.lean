import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesCoreJN74

/-!
# Draft 74, fields g4 `frontier_M2` and g6 `slim_M2` of the face facts at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). On the slim pieces of the chosen exit
`slimExitAt3_OCL` (the exit-3 rows of the gate): from the zero / new decomposition of
`FacesCoreJN74` and `slim_M2_frontier_ZSP35` / `slimPiece_spec_ZSP35` (chain):

* `frontier_M₂_at_JN74`: `∂M₂ = ⋃ residual faces` (field g4);
* `slim_M₂_at_JN74`: `slimSet ∩ M₂ = ⋃ new ends` (field g6);
* `newEnd_subset_M₂_at_JN74`: every new end lies in `M₂` (the input `hNew` of
  `residualSet_disjoint_JN74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)

/-- **Field g4 at `D_R`**: `∂M₂ = ⋃ residual faces` for the slim pieces of the exit
`slimExitAt3_OCL`. -/
theorem frontier_M₂_at_JN74 :
    frontier (S.stagesAtZ_OCL B hT hεr A).cut.M₂ =
      (S.slimPieces3_JN74 B hT hεr A hK).boundaryM2 := by
  rw [S.M₂_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr), ← image_frontier_R74 M.ψ,
    (S.M₂_frontier_facts_JN74 B hT hεr).1, image_union]
  ext z
  constructor
  · rintro (⟨x, ⟨hxM, hxS⟩, rfl⟩ | ⟨x, ⟨hxS, hxM⟩, rfl⟩)
    · obtain ⟨F, -, hF⟩ := S.zeroPart_fwd_JN74 B hT hεr A hK hxM hxS
      exact mem_iUnion.2 ⟨F, hF⟩
    · obtain ⟨en, hen⟩ := S.newPart_fwd_JN74 B hT hεr A hK hxS hxM
      exact mem_iUnion.2 ⟨Sum.inr en, hen⟩
  · intro hz
    obtain ⟨F, hF⟩ := mem_iUnion.1 hz
    obtain ⟨x, rfl⟩ := M.ψ.toEquiv.surjective z
    rcases F with F | en
    · obtain ⟨hxM, hxS⟩ := S.zeroPart_bwd_JN74 B hT hεr A hK F hF
      exact Or.inl ⟨x, ⟨hxM, hxS⟩, rfl⟩
    · obtain ⟨hxS, hxM⟩ := S.newPart_bwd_JN74 B hT hεr A hK en hF
      exact Or.inr ⟨x, ⟨hxS, hxM⟩, rfl⟩

/-- **Field g6 at `D_R`**: `slimSet ∩ M₂ = ⋃ new ends` for the exit `slimExitAt3_OCL`. -/
theorem slim_M₂_at_JN74 :
    (S.stagesAtZ_OCL B hT hεr A).cut.slimSet ∩ (S.stagesAtZ_OCL B hT hεr A).cut.M₂ =
      ⋃ e : (S.slimPieces3_JN74 B hT hεr A hK).NewEnd,
        (S.slimPieces3_JN74 B hT hεr A hK).endSet e.1 := by
  rw [S.slimSet_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr),
    S.M₂_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr),
    ← image_inter (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective,
    (S.goodCut_OCL B hT hεr).slimSet_eq, (S.M₂_frontier_facts_JN74 B hT hεr).2]
  ext z
  constructor
  · rintro ⟨x, ⟨hxS, hxM⟩, rfl⟩
    obtain ⟨en, hen⟩ := S.newPart_fwd_JN74 B hT hεr A hK hxS hxM
    exact mem_iUnion.2 ⟨en, hen⟩
  · intro hz
    obtain ⟨en, hen⟩ := mem_iUnion.1 hz
    obtain ⟨x, rfl⟩ := M.ψ.toEquiv.surjective z
    obtain ⟨hxS, hxM⟩ := S.newPart_bwd_JN74 B hT hεr A hK en hen
    exact ⟨x, ⟨hxS, hxM⟩, rfl⟩

/-- **Every new end lies in `M₂`** (the input `hNew` of `residualSet_disjoint_JN74`). -/
theorem newEnd_subset_M₂_at_JN74 (e : (S.slimPieces3_JN74 B hT hεr A hK).NewEnd) :
    (S.slimPieces3_JN74 B hT hεr A hK).endSet e.1 ⊆ (S.stagesAtZ_OCL B hT hεr A).cut.M₂ := by
  intro z hz
  have h : z ∈ (S.stagesAtZ_OCL B hT hεr A).cut.slimSet ∩
      (S.stagesAtZ_OCL B hT hεr A).cut.M₂ := by
    rw [S.slim_M₂_at_JN74 B hT hεr A hK]
    exact mem_iUnion.2 ⟨e, hz⟩
  exact h.2

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
