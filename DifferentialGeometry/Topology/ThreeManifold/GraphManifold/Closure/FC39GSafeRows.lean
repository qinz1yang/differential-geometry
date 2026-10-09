import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Faces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeCircleTube

/-!
# FC39 GROUP G, lane FC39-G-SAFE: the actual sets of the rows (closedness, disjointness)

Steps S1–S3 and S5 of the lane sheet (`build-logs/resume/sheet-FC39-G-SAFE.md`; external draft
task 58 §一). Everything is read from the fields of `FC39RowsV2` (no new hypothesis):

* S1 closedness / compactness / finiteness: `isClosed_regionM2_GSAFE`, `isClosed_region_GSAFE`,
  `region_subset_regionM2_GSAFE`, `isCompact_sharedSet_GSAFE`, `finite_sharedFace_GSAFE`,
  `finite_edgeEnd_GSAFE`;
* S2a a shared face meets no residual face (`sharedSet_disjoint_residualSet_GSAFE`) and no other
  shared face (`sharedSet_pairwise_disjoint_GSAFE`), from `endSet_disjoint_GSAFE` and
  `neighbourSet_disjoint_GSAFE`;
* S2 `sharedSet_disjoint_region_GSAFE` (through `shared_removed`) and
  `sharedSet_disjoint_edgePiece_GSAFE`: a whole edge disk through a shared point would run from
  outside `regionM2` to its rim inside the circle region, hence cross `frontier regionM2 = ∂M₂`,
  i.e. a residual face, where `edge_faces` forces it to be a registered end disk lying in a
  residual face — impossible by S2a (no interior-density argument is needed);
* S3 `sharedSet_disjoint_closure_collar_GSAFE` (owner cases: `zero_cusp_disjoint`,
  `collar_closure_off`, `CuspCores.disjoint`) and `rim_disjoint_closure_collar_GSAFE` (uniform:
  a point of the closure of a port collar is on the internal end, on the external boundary torus,
  or an ambient interior point of the cusp image, and the rim is none of these);
* S5 `rimBase_injOn_cbase_GSAFE`, `rimBase_injective_GSAFE` (PUBLIC: `rim_fibre`, nonempty
  fibres, `disk_disjoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsSafeRows_GSAFE : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## Closedness of the relative complements -/

theorem relInt_subset_GSAFE {X : Type*} [TopologicalSpace X] (A S : Set X) : relInt A S ⊆ A := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

/-- Removing a relative interior from a closed set leaves a closed set. -/
theorem isClosed_diff_relInt_GSAFE {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (S : Set X) : IsClosed (A \ relInt A S) := by
  have heq : A \ relInt A S = Subtype.val '' (interior ((Subtype.val : A → X) ⁻¹' S))ᶜ := by
    ext x
    constructor
    · rintro ⟨hxA, hx⟩
      exact ⟨⟨x, hxA⟩, fun h => hx ⟨⟨x, hxA⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      exact hy (this ▸ hz)
  rw [heq]
  exact hA.isClosedEmbedding_subtypeVal.isClosedMap _ isOpen_interior.isClosed_compl

theorem isClosed_regionM1_GSAFE (Z : ZeroDomains W) (C : CuspCores W E) :
    IsClosed (regionM1 Z C) :=
  isOpen_interior.isClosed_compl

theorem isClosed_regionM2_GSAFE {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) : IsClosed (regionM2 S) :=
  isClosed_diff_relInt_GSAFE (isClosed_regionM1_GSAFE Z C) _

theorem regionM2_subset_regionM1_GSAFE {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) : regionM2 S ⊆ regionM1 Z C :=
  sdiff_subset

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- The circle region lies in `M₂` (`region_eq`). -/
theorem region_subset_regionM2_GSAFE : Rw.circle.region ⊆ regionM2 Rw.slim := by
  rw [← Rw.junctions.region_eq]
  exact sdiff_subset

/-- The circle region is closed (`region_eq`). -/
theorem isClosed_region_GSAFE : IsClosed Rw.circle.region := by
  rw [← Rw.junctions.region_eq]
  exact isClosed_diff_relInt_GSAFE (isClosed_regionM2_GSAFE Rw.slim) _

/-! ## Finiteness -/

theorem finite_slimEnd_GSAFE : Finite Rw.slim.End := by
  unfold SlimPiecesV2.End SlimEnd
  infer_instance

theorem finite_sharedFace_GSAFE : Finite Rw.SharedFace := by
  have := Rw.finite_slimEnd_GSAFE
  unfold SharedFace ActualSharedFace
  infer_instance

theorem finite_edgeEnd_GSAFE : Finite Rw.edge.EdgeEnd :=
  Finite.of_equiv _ Rw.edgeModels.endpointEquiv

end FC39RowsV2

/-! ## Ends of slim models and neighbour faces -/

theorem iccEnd_injective_GSAFE : Injective iccEnd := by
  intro b b' h
  cases b <;> cases b'
  · rfl
  · have := congrArg Subtype.val h
    simp [iccEnd] at this
  · have := congrArg Subtype.val h
    simp [iccEnd] at this
  · rfl

/-- The two end slices of a slim model are disjoint. -/
theorem slimModelEnd_disjoint_GSAFE {P : PieceEmbedding W} (m : SlimModel P) {b b' : Bool}
    (h : b ≠ b') : Disjoint (slimModelEnd m b) (slimModelEnd m b') := by
  cases m with
  | sphereInterval e =>
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, rfl⟩ ⟨z', hz'⟩
    exact h (iccEnd_injective_GSAFE (congrArg Prod.snd (e.injective hz')).symm)
  | torusInterval e =>
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, rfl⟩ ⟨z', hz'⟩
    exact h (iccEnd_injective_GSAFE (congrArg Prod.snd (e.injective hz')).symm)
  | overCircle p hp hsub fib hcl => simp [slimModelEnd]

/-- The end slices of a slim model are compact. -/
theorem isCompact_slimModelEnd_GSAFE {P : PieceEmbedding W} (m : SlimModel P) (b : Bool) :
    IsCompact (slimModelEnd m b) := by
  cases m with
  | sphereInterval e =>
    exact isCompact_range (e.continuous.comp (continuous_id.prodMk continuous_const))
  | torusInterval e =>
    exact isCompact_range (e.continuous.comp (continuous_id.prodMk continuous_const))
  | overCircle p hp hsub fib hcl => simp [slimModelEnd]

namespace SlimPiecesV2

variable {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)

theorem endSet_subset_GSAFE (e : S.End) : S.endSet e ⊆ range (S.piece e.1.1).map :=
  image_subset_range _ _

/-- Distinct actual ends of the slim pieces have disjoint whole end slices. -/
theorem endSet_disjoint_GSAFE {e e' : S.End} (h : e ≠ e') : Disjoint (S.endSet e) (S.endSet e') := by
  obtain ⟨⟨j, b⟩, hj⟩ := e
  obtain ⟨⟨j', b'⟩, hj'⟩ := e'
  by_cases hjj : j = j'
  · subst hjj
    have hb : b ≠ b' := fun hb => h (by subst hb; rfl)
    exact (Set.disjoint_image_iff (S.piece j).injective).2 (slimModelEnd_disjoint_GSAFE _ hb)
  · exact (S.disjoint hjj).mono (S.endSet_subset_GSAFE _) (S.endSet_subset_GSAFE _)

theorem isCompact_endSet_GSAFE (e : S.End) : IsCompact (S.endSet e) :=
  (isCompact_slimModelEnd_GSAFE _ _).image (S.piece e.1.1).continuous_map

end SlimPiecesV2

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

theorem neighbourSet_subset_GSAFE : ∀ F : NeighbourFace Rw.zero Rw.cusp,
    neighbourSet F ⊆ Rw.slim.rowSet (Rw.neighbourIndex F)
  | .inl _ => image_subset_range _ _
  | .inr _ => image_subset_range _ _

/-- Distinct neighbour faces have disjoint ambient images. -/
theorem neighbourSet_disjoint_GSAFE {F F' : NeighbourFace Rw.zero Rw.cusp} (h : F ≠ F') :
    Disjoint (neighbourSet F) (neighbourSet F') := by
  rcases F with ⟨i, A⟩ | ⟨b, A, hA⟩ <;> rcases F' with ⟨i', A'⟩ | ⟨b', A', hA'⟩
  · by_cases hii : i = i'
    · subst hii
      have hAA : A ≠ A' := fun hAA => h (by subst hAA; rfl)
      exact (Set.disjoint_image_iff (Rw.zero.piece i).injective).2
        (ActualComponent.disjoint_of_ne hAA)
    · exact (Rw.zero.disjoint hii).mono (image_subset_range _ _) (image_subset_range _ _)
  · exact (Rw.junctions.zero_cusp_disjoint i b').mono (image_subset_range _ _)
      (image_subset_range _ _)
  · exact (Rw.junctions.zero_cusp_disjoint i' b).symm.mono (image_subset_range _ _)
      (image_subset_range _ _)
  · by_cases hbb : b = b'
    · subst hbb
      exact absurd (by subst hA; subst hA'; rfl) h
    · exact (Rw.cusp.disjoint hbb).mono (image_subset_range _ _) (image_subset_range _ _)

/-- The shared set is the neighbour set of its registered neighbour face (`shared_eq`). -/
theorem sharedSet_eq_neighbourSet_GSAFE (σ : Rw.SharedFace) :
    Rw.sharedSet σ = neighbourSet (Rw.sharedNeighbour σ) :=
  Rw.junctions.shared_eq σ.1 _ (Option.some_get σ.2).symm

/-- **S2a** A shared face meets no residual face. -/
theorem sharedSet_disjoint_residualSet_GSAFE (σ : Rw.SharedFace) (F : Rw.slim.ResidualFace) :
    Disjoint (Rw.sharedSet σ) (Rw.slim.residualSet F) := by
  rcases F with ⟨F, hF⟩ | ⟨e, he⟩
  · rw [Rw.sharedSet_eq_neighbourSet_GSAFE σ]
    refine Rw.neighbourSet_disjoint_GSAFE fun hFF => hF σ.1 ?_
    have h1 : Rw.slim.endKind σ.1 = some (Rw.sharedNeighbour σ) := (Option.some_get σ.2).symm
    rw [h1]
    exact congrArg some hFF
  · refine Rw.slim.endSet_disjoint_GSAFE fun hee => ?_
    have h1 := σ.2
    rw [hee, he] at h1
    exact Bool.false_ne_true h1

/-- Distinct shared faces are disjoint. -/
theorem sharedSet_pairwise_disjoint_GSAFE :
    Pairwise fun σ τ : Rw.SharedFace => Disjoint (Rw.sharedSet σ) (Rw.sharedSet τ) :=
  fun _ _ h => Rw.slim.endSet_disjoint_GSAFE fun h' => h (Subtype.ext h')

theorem isCompact_sharedSet_GSAFE (σ : Rw.SharedFace) : IsCompact (Rw.sharedSet σ) :=
  Rw.slim.isCompact_endSet_GSAFE σ.1

/-! ## S2: shared faces off the circle region and the edge piece -/

/-- A shared face lies outside `M₂` (`shared_removed`). -/
theorem sharedSet_disjoint_regionM2_GSAFE (σ : Rw.SharedFace) :
    Disjoint (Rw.sharedSet σ) (regionM2 Rw.slim) :=
  Set.disjoint_left.2 fun _ hx hx2 => hx2.2 (Rw.junctions.shared_removed σ hx)

theorem sharedSet_disjoint_region_GSAFE (σ : Rw.SharedFace) :
    Disjoint (Rw.sharedSet σ) Rw.circle.region :=
  (Rw.sharedSet_disjoint_regionM2_GSAFE σ).mono_right Rw.region_subset_regionM2_GSAFE

end FC39RowsV2

namespace EdgeBundle

variable (P : EdgeBundle W)

theorem isPreconnected_disk_GSAFE (c : P.Base) : IsPreconnected (P.disk c) := by
  obtain ⟨φ, hφ, hrange⟩ := P.fibre_disk c
  rw [disk, ← hrange]
  exact isPreconnected_range_closedBall_GSAFE hφ.isEmbedding.continuous

theorem disk_subset_edgePiece_GSAFE {c : P.Base} (hc : c ∈ P.cbase) : P.disk c ⊆ P.edgePiece := by
  rintro _ ⟨x, ⟨hx, hxl⟩, rfl⟩
  exact ⟨x, ⟨hx ▸ hc, hxl⟩, rfl⟩

theorem rim_subset_disk_GSAFE (c : P.Base) : P.rim c ⊆ P.disk c := by
  rintro _ ⟨x, ⟨hx, hxl⟩, rfl⟩
  exact ⟨x, ⟨hx, hxl.le⟩, rfl⟩

theorem rim_subset_vertical_GSAFE {c : P.Base} (hc : c ∈ P.cbase) : P.rim c ⊆ P.vertical := by
  rintro _ ⟨x, ⟨hx, hxl⟩, rfl⟩
  exact ⟨x, ⟨hx ▸ hc, hxl⟩, rfl⟩

theorem rim_subset_interior_GSAFE (c : P.Base) : P.rim c ⊆ W.interior := by
  rintro _ ⟨x, -, rfl⟩
  exact P.source_interior x.2

theorem mem_cbase_of_edgeEnd_GSAFE (e : P.EdgeEnd) : e.1 ∈ P.cbase :=
  P.frontier_cbase_subset e.2

end EdgeBundle

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- The rim over a point of `C₂` lies in the circle region (`edge_region`). -/
theorem rim_subset_region_GSAFE {c : Rw.edge.Base} (hc : c ∈ Rw.edge.cbase) :
    Rw.edge.rim c ⊆ Rw.circle.region := by
  intro x hx
  have hv := Rw.edge.rim_subset_vertical_GSAFE hc hx
  rw [← Rw.junctions.edge_region] at hv
  exact hv.2

/-- The rim over a point of `C₂` is nonempty (`rim_fibre` and the trivialization). -/
theorem rim_nonempty_GSAFE {c : Rw.edge.Base} (hc : c ∈ Rw.edge.cbase) :
    (Rw.edge.rim c).Nonempty := by
  rw [Rw.junctions.rim_fibre c hc]
  exact Rw.circle.fibre_nonempty_GSAFE _

/-- **S2** A shared face does not meet the edge piece. -/
theorem sharedSet_disjoint_edgePiece_GSAFE (σ : Rw.SharedFace) :
    Disjoint (Rw.sharedSet σ) Rw.edge.edgePiece := by
  refine Set.disjoint_left.2 ?_
  rintro x hxσ ⟨y, ⟨hyc, hyl⟩, rfl⟩
  set c := Rw.edge.proj y
  have hxd : (y : W.Carrier) ∈ Rw.edge.disk c := ⟨y, ⟨rfl, hyl⟩, rfl⟩
  obtain ⟨r, hr⟩ := Rw.rim_nonempty_GSAFE hyc
  have hr2 : r ∈ regionM2 Rw.slim :=
    Rw.region_subset_regionM2_GSAFE (Rw.rim_subset_region_GSAFE hyc hr)
  have hx2 : (y : W.Carrier) ∉ regionM2 Rw.slim := fun h =>
    Set.disjoint_left.1 (Rw.sharedSet_disjoint_regionM2_GSAFE σ) hxσ h
  obtain ⟨z, hzd, hzf⟩ := inter_frontier_nonempty_of_isPreconnected_GSAFE (Rw.edge.isPreconnected_disk_GSAFE c)
    ⟨r, Rw.edge.rim_subset_disk_GSAFE c hr, hr2⟩ ⟨_, hxd, hx2⟩
  rw [Rw.junctions.frontier_M2] at hzf
  obtain ⟨F, hzF⟩ := mem_iUnion.1 hzf
  have hzP : z ∈ Rw.edge.edgePiece ∩ Rw.slim.residualSet F :=
    ⟨Rw.edge.disk_subset_edgePiece_GSAFE hyc hzd, hzF⟩
  rw [Rw.junctions.edge_faces F] at hzP
  obtain ⟨e, hzE⟩ := mem_iUnion.1 hzP
  obtain ⟨heF, hze⟩ := mem_iUnion.1 hzE
  have hce : c = e.1 := by
    by_contra hne
    exact Set.disjoint_left.1 (Rw.edge.disk_disjoint hne) hzd hze
  have hxF : (y : W.Carrier) ∈ Rw.slim.residualSet F := by
    rw [← heF]
    exact Rw.junctions.horizontal_disk e (hce ▸ hxd)
  exact Set.disjoint_left.1 (Rw.sharedSet_disjoint_residualSet_GSAFE σ F) hxσ hxF

/-! ## S3: off the closures of the port collars -/

/-- The closure of a port collar lies in its cusp image (`collar_owned`). -/
theorem closure_collar_subset_GSAFE (i : Fin n) :
    closure (E.collar i).target ⊆ range (Rw.cusp.piece i).map :=
  closure_minimal (Rw.cusp.collar_owned i) (Rw.cusp.piece i).isClosed_range

/-- **S3 (shared faces)** A shared face avoids the closure of every port collar (owner cases). -/
theorem sharedSet_disjoint_closure_collar_GSAFE (σ : Rw.SharedFace) (i : Fin n) :
    Disjoint (Rw.sharedSet σ) (closure (E.collar i).target) := by
  rw [Rw.sharedSet_eq_neighbourSet_GSAFE σ]
  rcases Rw.sharedNeighbour σ with ⟨j, A⟩ | ⟨b, A, hA⟩
  · exact (Rw.junctions.zero_cusp_disjoint j i).mono (image_subset_range _ _)
      (Rw.closure_collar_subset_GSAFE i)
  · by_cases hbi : b = i
    · subst hbi hA
      have heq : neighbourSet (Z := Rw.zero) (.inr ⟨b, Rw.cusp.internalModelFace b, rfl⟩) =
          range fun t => (Rw.cusp.piece b).map (Rw.cusp.product b (t, iccEnd true)) := by
        change (Rw.cusp.piece b).map '' (Rw.cusp.internalModelFace b).1 = _
        rw [Rw.cusp.internalModelFace_eq b, ← range_comp]
        rfl
      rw [heq]
      exact (Rw.cusp.collar_closure_off b).symm
    · exact (Rw.cusp.disjoint hbi).mono (image_subset_range _ _)
        (Rw.closure_collar_subset_GSAFE i)

/-- A point of a cusp image is on the internal end, on the external boundary torus, or an ambient
interior point of the image (`modelFace_cases`). -/
theorem cusp_point_cases_GSAFE (b : Fin n) (q : (Rw.cusp.piece b).Piece) :
    (Rw.cusp.piece b).map q ∈ (range fun t => (Rw.cusp.piece b).map (Rw.cusp.product b (t, iccEnd true))) ∨
      W.model.IsBoundaryPoint ((Rw.cusp.piece b).map q) ∨
      (Rw.cusp.piece b).map q ∈ interior (range (Rw.cusp.piece b).map) := by
  by_cases hq : (𝓡∂ 3).IsBoundaryPoint q
  · have hqF : q ∈ (ActualComponent.of (S := (𝓡∂ 3).boundary (Rw.cusp.piece b).Piece) hq).1 :=
      mem_connectedComponentIn hq
    rcases Rw.cusp.modelFace_cases b (ActualComponent.of hq) with hF | hF
    · rw [hF, Rw.cusp.internalModelFace_eq b] at hqF
      obtain ⟨t, rfl⟩ := hqF
      exact Or.inl ⟨t, rfl⟩
    · rw [hF, Rw.cusp.externalModelFace_eq b] at hqF
      obtain ⟨t, rfl⟩ := hqF
      right; left
      rw [Rw.cusp.external_end b t]
      exact E.boundary_zero b t
  · right; right
    exact (Rw.cusp.piece b).map_mem_interior_range
      (((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint q).2 hq)

/-- **S3 (rims)** The rim over a point of `C₂` avoids the closure of every port collar. -/
theorem rim_disjoint_closure_collar_GSAFE {c : Rw.edge.Base} (hc : c ∈ Rw.edge.cbase) (i : Fin n) :
    Disjoint (Rw.edge.rim c) (closure (E.collar i).target) := by
  refine Set.disjoint_left.2 fun x hxr hxc => ?_
  obtain ⟨q, rfl⟩ := Rw.closure_collar_subset_GSAFE i hxc
  rcases Rw.cusp_point_cases_GSAFE i q with h | h | h
  · exact Set.disjoint_left.1 (Rw.cusp.collar_closure_off i) hxc h
  · have hint : W.model.IsInteriorPoint ((Rw.cusp.piece i).map q) :=
      Rw.edge.rim_subset_interior_GSAFE c hxr
    exact ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).1 hint) h
  · have hM1 : (Rw.cusp.piece i).map q ∈ regionM1 Rw.zero Rw.cusp :=
      regionM2_subset_regionM1_GSAFE Rw.slim
        (Rw.region_subset_regionM2_GSAFE (Rw.rim_subset_region_GSAFE hc hxr))
    exact hM1 (interior_mono (subset_union_right.trans' (subset_iUnion
      (fun b => range (Rw.cusp.piece b).map) i)) h)

/-! ## S5: injectivity of the rim base point -/

/-- **S5** The rim base point is injective on `C₂` (`rim_fibre`, nonempty rims, disjoint disks). -/
theorem rimBase_injOn_cbase_GSAFE : Set.InjOn Rw.junctions.rimBase Rw.edge.cbase := by
  intro c hc c' hc' h
  by_contra hne
  obtain ⟨r, hr⟩ := Rw.rim_nonempty_GSAFE hc
  have hr' : r ∈ Rw.edge.rim c' := by
    rw [Rw.junctions.rim_fibre c' hc', ← h, ← Rw.junctions.rim_fibre c hc]
    exact hr
  exact Set.disjoint_left.1 (Rw.edge.disk_disjoint hne) (Rw.edge.rim_subset_disk_GSAFE c hr)
    (Rw.edge.rim_subset_disk_GSAFE c' hr')

/-- **S5 (public)** Distinct endpoints of `C₂` have distinct rim base points. -/
theorem rimBase_injective_GSAFE :
    Injective fun e : Rw.edge.EdgeEnd => Rw.junctions.rimBase e.1 := fun e e' h =>
  Subtype.ext (Rw.rimBase_injOn_cbase_GSAFE (Rw.edge.mem_cbase_of_edgeEnd_GSAFE e)
    (Rw.edge.mem_cbase_of_edgeEnd_GSAFE e') h)

/-- The whole fibre over the rim base point of an endpoint is the rim, hence it avoids the
closure of every port collar. -/
theorem fibre_rimBase_disjoint_closure_collar_GSAFE (e : Rw.edge.EdgeEnd) (i : Fin n) :
    Disjoint (Rw.circle.fibre (Rw.junctions.rimBase e.1)) (closure (E.collar i).target) := by
  rw [← Rw.junctions.rim_fibre e.1 (Rw.edge.mem_cbase_of_edgeEnd_GSAFE e)]
  exact Rw.rim_disjoint_closure_collar_GSAFE (Rw.edge.mem_cbase_of_edgeEnd_GSAFE e) i

end FC39RowsV2

end GC.GraphManifold.Assembly.FC39P0
