import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapSlab
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open DifferentialGeometry.Geometry.Collapse.EdgeCapSlab
open scoped Manifold ContDiff Topology
attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
  sourceNativeChart sourceNativeManifold
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial

def sourceFlow (t : ℝ) :
    sourceSlab ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯ sourceSlab :=
  (nativeSlabCoordinates.symm.trans (slabFlow t)).trans nativeSlabCoordinates

theorem sourceFlow_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × sourceSlab => sourceFlow q.1 q.2) :=
  nativeSlabCoordinates.contMDiff.comp (slabFlow_joint.comp
    (contMDiff_fst.prodMk (nativeSlabCoordinates.symm.contMDiff.comp contMDiff_snd)))

theorem sourceFlow_zero :
    sourceFlow 0 = Diffeomorph.refl (𝓘(ℝ, ℝ).prod (𝓡 2)) sourceSlab ∞ := by
  apply DFunLike.ext
  intro x
  change nativeSlabCoordinates (slabFlow 0 (nativeSlabCoordinates.symm x)) = x
  rw [slabFlow_zero]
  exact nativeSlabCoordinates.apply_symm_apply x

theorem sourceFlow_add (s t : ℝ) :
    (sourceFlow s).trans (sourceFlow t) = sourceFlow (s + t) := by
  apply DFunLike.ext
  intro x
  change nativeSlabCoordinates (slabFlow t (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (slabFlow s (nativeSlabCoordinates.symm x))))) =
      nativeSlabCoordinates (slabFlow (s + t) (nativeSlabCoordinates.symm x))
  rw [Diffeomorph.symm_apply_apply]
  exact congrArg nativeSlabCoordinates
    (congrArg (fun D => D (nativeSlabCoordinates.symm x)) (slabFlow_add s t))

theorem sourceFlow_boundary (t : ℝ) (x : sourceSlab) :
    sourceBoundary (sourceFlow t x) = sourceBoundary x := by
  change slabBoundary (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (slabFlow t (nativeSlabCoordinates.symm x)))) =
      slabBoundary (nativeSlabCoordinates.symm x)
  rw [Diffeomorph.symm_apply_apply]
  unfold slabBoundary
  rw [slabFlow_height]

theorem sourceFlow_height (t : ℝ) (x : sourceSlab) :
    edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (sourceFlow t x : sourceSlab) =
      edgeRowHeight capExampleDelta capExampleF (fun _ => 1) x := by
  have h := sourceFlow_boundary t x
  rw [sourceBoundary_literal, sourceBoundary_literal] at h
  linarith

theorem sourceFlow_central (x : sourceSlab) (hx : sourceCoord x = 0) (t : ℝ)
    (ht : |t| < 4 * capExampleDelta) : sourceCoord (sourceFlow t x) = t := by
  rw [sourceCoord_model]
  change slabCoord (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (slabFlow t (nativeSlabCoordinates.symm x)))) = t
  rw [Diffeomorph.symm_apply_apply]
  rw [sourceCoord_model] at hx
  exact slabFlow_central _ hx t ht

def packetBoundary (x : sourceSlab) : ℝ :=
  4 * capExampleDelta - edgeRowHeight capExampleDelta capExampleF (fun _ => 1) x

theorem packetBoundary_eq : packetBoundary = sourceBoundary := by
  funext x
  exact (sourceBoundary_literal x).symm

theorem packetBoundary_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ packetBoundary := by
  rw [packetBoundary_eq]
  exact sourceBoundary_smooth

theorem packetBoundary_regular (x : sourceSlab) (hx : packetBoundary x = 0) :
    Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun q : sourceSlab => (sourceCoord q, packetBoundary q)) x) := by
  rw [packetBoundary_eq] at hx ⊢
  exact sourceBoundary_regular x hx

def productRetraction (p : productSlab) : productSlab :=
  ⟨(0, (p : ℝ × E2).2), by
    change |(0 : ℝ)| < 5 * capExampleDelta ∧ radialHeight (p : ℝ × E2).2 < 5 * capExampleDelta
    exact ⟨by simp only [abs_zero]; exact mul_pos (by norm_num) delta_pos, p.2.2⟩⟩

theorem productRetraction_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ productRetraction := by
  apply (ContMDiff.subtypeVal_comp_iff productSlab productRetraction).mp
  exact contMDiff_const.prodMk (contMDiff_snd.comp contMDiff_subtype_val)

theorem productRetraction_recovery (p : productSlab) (hp : |slabCoord p| < 4 * capExampleDelta) :
    slabFlow (slabCoord p) (productRetraction p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact DifferentialGeometry.Geometry.Collapse.EdgeCapFlow.capScalarFlow_translation _ _ _ hp
  · rfl

def sourceRetraction (x : sourceSlab) : sourceSlab :=
  nativeSlabCoordinates (productRetraction (nativeSlabCoordinates.symm x))

theorem sourceRetraction_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ sourceRetraction :=
  nativeSlabCoordinates.contMDiff.comp
    (productRetraction_smooth.comp nativeSlabCoordinates.symm.contMDiff)

theorem sourceRetraction_coord (x : sourceSlab) : sourceCoord (sourceRetraction x) = 0 := by
  rw [sourceCoord_model]
  change slabCoord (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (productRetraction (nativeSlabCoordinates.symm x)))) = 0
  rw [Diffeomorph.symm_apply_apply]
  rfl

theorem sourceRetraction_boundary (x : sourceSlab) :
    packetBoundary (sourceRetraction x) = packetBoundary x := by
  rw [packetBoundary_eq]
  change slabBoundary (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (productRetraction (nativeSlabCoordinates.symm x)))) =
      slabBoundary (nativeSlabCoordinates.symm x)
  rw [Diffeomorph.symm_apply_apply]
  rfl

theorem sourceRetraction_recovery (x : sourceSlab) (hx : |sourceCoord x| < 4 * capExampleDelta) :
    sourceFlow (sourceCoord x) (sourceRetraction x) = x := by
  change nativeSlabCoordinates (slabFlow (sourceCoord x) (nativeSlabCoordinates.symm
    (nativeSlabCoordinates (productRetraction (nativeSlabCoordinates.symm x))))) = x
  rw [Diffeomorph.symm_apply_apply]
  rw [sourceCoord_model] at hx ⊢
  rw [productRetraction_recovery _ hx, Diffeomorph.apply_symm_apply]

abbrev actualFibre : Type := {x : sourceSlab // sourceCoord x = 0 ∧ 0 ≤ packetBoundary x}

local instance actualFibreChart : ChartedSpace (EuclideanHalfSpace 2) actualFibre :=
  DifferentialGeometry.Manifold.RegularLevel.regularSublevelChartedSpace
    finrank_real_prod_euclideanTwo sourceCoord_smooth packetBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => packetBoundary_regular x hb)

local instance actualFibreManifold : IsManifold (𝓡∂ 2) ∞ actualFibre :=
  DifferentialGeometry.Manifold.RegularLevel.regularSublevel_isManifold
    finrank_real_prod_euclideanTwo sourceCoord_smooth packetBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => packetBoundary_regular x hb)

theorem actualFibre_disk : Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ actualFibre) := by
  exact nonempty_diffeomorph_regularSublevel_of_lift
    finrank_real_prod_euclideanTwo sourceCoord_smooth packetBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => packetBoundary_regular x hb)
    diskEmbedding_smoothEmbedding sourceRadialProjection_smooth sourceDiskLift_smooth
    (fun c => ⟨sourceDiskLift_coord c, by
      rw [packetBoundary_eq]; exact sourceDiskLift_boundary c⟩)
    sourceDiskLift_projection (fun x hc hb => sourceDiskLift_surjective x hc (by
      rw [← packetBoundary_eq]; exact hb))

theorem actualFibre_boundary {x : actualFibre} :
    (𝓡∂ 2).IsBoundaryPoint x ↔ packetBoundary (x : sourceSlab) = 0 :=
  DifferentialGeometry.Manifold.RegularLevel.regularSublevel_isBoundaryPoint_iff
    finrank_real_prod_euclideanTwo sourceCoord_smooth packetBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => packetBoundary_regular x hb)

theorem actualFibre_val_smooth :
    ContMDiff (𝓡∂ 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ (Subtype.val : actualFibre → sourceSlab) :=
  DifferentialGeometry.Manifold.RegularLevel.regularSublevel_contMDiff_val
    finrank_real_prod_euclideanTwo sourceCoord_smooth packetBoundary_smooth
    (fun x _ _ => sourceCoord_regular x) (fun x _ hb => packetBoundary_regular x hb)

def timeInterval (a b : ℝ) : TopologicalSpace.Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩

def sourceFlowEval (q : ℝ × sourceSlab) : sourceSlab := sourceFlow q.1 q.2

theorem sourceFlowEval_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      sourceFlowEval := sourceFlow_joint

def trivializationParameters (a b : ℝ) (p : actualFibre × timeInterval a b) :
    ℝ × sourceSlab := ((p.2 : ℝ), (p.1 : sourceSlab))

theorem trivializationParameters_smooth (a b : ℝ) :
    ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) ∞ (trivializationParameters a b) := by
  have ht : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : actualFibre × timeInterval a b => (p.2 : ℝ)) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hx : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun p : actualFibre × timeInterval a b => (p.1 : sourceSlab)) :=
    actualFibre_val_smooth.comp contMDiff_fst
  exact ht.prodMk hx

def trivialization (a b : ℝ) : actualFibre × timeInterval a b → sourceSlab :=
  sourceFlowEval ∘ trivializationParameters a b

theorem trivialization_smooth (a b : ℝ) :
    ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ (trivialization a b) :=
  sourceFlowEval_smooth.comp (trivializationParameters_smooth a b)

theorem timeInterval_bound (a b : ℝ) (ha : -(4 * capExampleDelta) < a)
    (hb : b < 4 * capExampleDelta) (t : timeInterval a b) : |(t : ℝ)| < 4 * capExampleDelta :=
  abs_lt.mpr ⟨ha.trans t.2.1, t.2.2.trans hb⟩

theorem trivialization_coord (a b : ℝ) (ha : -(4 * capExampleDelta) < a)
    (hb : b < 4 * capExampleDelta) (p : actualFibre × timeInterval a b) :
    sourceCoord (trivialization a b p) = p.2 :=
  sourceFlow_central p.1 p.1.2.1 p.2 (timeInterval_bound a b ha hb p.2)

theorem trivialization_boundary (a b : ℝ) (p : actualFibre × timeInterval a b) :
    0 ≤ packetBoundary (trivialization a b p) := by
  rw [packetBoundary_eq]
  change 0 ≤ sourceBoundary (sourceFlow p.2 p.1)
  rw [sourceFlow_boundary]
  rw [← packetBoundary_eq]
  exact p.1.2.2

theorem trivialization_height (a b : ℝ) (p : actualFibre × timeInterval a b) :
    edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (trivialization a b p : sourceSlab) =
      edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (p.1 : sourceSlab) :=
  sourceFlow_height _ _

theorem trivialization_zero (a b : ℝ) (h0 : (0 : ℝ) ∈ Ioo a b) (x : actualFibre) :
    trivialization a b (x, ⟨0, h0⟩) = (x : sourceSlab) := by
  change sourceFlow 0 x = x
  rw [sourceFlow_zero]
  rfl

theorem trivialization_injective (a b : ℝ) (ha : -(4 * capExampleDelta) < a)
    (hb : b < 4 * capExampleDelta) : Injective (trivialization a b) := by
  intro p q h
  have ht : p.2 = q.2 := by
    apply Subtype.ext
    exact (trivialization_coord a b ha hb p).symm.trans
      ((congrArg sourceCoord h).trans (trivialization_coord a b ha hb q))
  have hx : (p.1 : sourceSlab) = (q.1 : sourceSlab) := by
    apply (sourceFlow (q.2 : ℝ)).injective
    change sourceFlow p.2 p.1 = sourceFlow q.2 q.1 at h
    rwa [ht] at h
  exact Prod.ext (Subtype.ext hx) ht

theorem trivialization_recovery (a b : ℝ) (ha : -(4 * capExampleDelta) < a)
    (hb : b < 4 * capExampleDelta) (y : sourceSlab) (hy : sourceCoord y ∈ Ioo a b)
    (hB : 0 ≤ packetBoundary y) :
    ∃ hR : sourceCoord (sourceRetraction y) = 0 ∧ 0 ≤ packetBoundary (sourceRetraction y),
      trivialization a b (⟨sourceRetraction y, hR⟩, ⟨sourceCoord y, hy⟩) = y := by
  refine ⟨⟨sourceRetraction_coord y, ?_⟩, ?_⟩
  · rw [sourceRetraction_boundary]
    exact hB
  · exact sourceRetraction_recovery y (timeInterval_bound a b ha hb ⟨sourceCoord y, hy⟩)

def rimDomain : TopologicalSpace.Opens sourceSlab := ⊤

def rimFlow (t : ℝ) :
    rimDomain ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯ rimDomain :=
  (sourceFlow t).restrict (U := rimDomain) (V := rimDomain) (fun _ => by simp [rimDomain])

theorem rimFlow_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × rimDomain => rimFlow q.1 q.2) :=
  Diffeomorph.contMDiff_restrict sourceFlow sourceFlow_joint (fun _ _ => by simp [rimDomain])

theorem rimFlow_zero :
    rimFlow 0 = Diffeomorph.refl (𝓘(ℝ, ℝ).prod (𝓡 2)) rimDomain ∞ := by
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun D => D (x : sourceSlab)) sourceFlow_zero

theorem rimFlow_add (s t : ℝ) : (rimFlow s).trans (rimFlow t) = rimFlow (s + t) := by
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun D => D (x : sourceSlab)) (sourceFlow_add s t)

theorem rimFlow_central (x : rimDomain) (hx : sourceCoord (x : sourceSlab) = 0) (t : ℝ)
    (ht : |t| < 4 * capExampleDelta) : sourceCoord (rimFlow t x : sourceSlab) = t :=
  sourceFlow_central x hx t ht

theorem rimFlow_height (x : rimDomain) (t : ℝ) :
    edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (rimFlow t x : sourceSlab) =
      edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (x : sourceSlab) :=
  sourceFlow_height t x

theorem actual_native_R2 (a b : ℝ) (ha : -(4 * capExampleDelta) < a)
    (h0 : (0 : ℝ) ∈ Ioo a b) (hb : b < 4 * capExampleDelta) :
    ∃ Θ' : actualFibre × timeInterval a b → sourceSlab,
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
      (∀ p, sourceCoord (Θ' p) = p.2 ∧ 0 ≤ packetBoundary (Θ' p)) ∧
      (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
      (∃ r' : ℝ, 0 < r' ∧
        (∀ p, packetBoundary p.1 < r' →
          edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (Θ' p : sourceSlab) =
            edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (p.1 : sourceSlab)) ∧
        ∃ (U : Set sourceSlab) (hU : IsOpen U),
        ∃ D : ℝ → (⟨U, hU⟩ : TopologicalSpace.Opens sourceSlab)
            ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯
              (⟨U, hU⟩ : TopologicalSpace.Opens sourceSlab),
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2)))
            (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
            (fun q : ℝ × (⟨U, hU⟩ : TopologicalSpace.Opens sourceSlab) => D q.1 q.2) ∧
          D 0 = Diffeomorph.refl _ _ ∞ ∧ (∀ s t, (D s).trans (D t) = D (s + t)) ∧
          (∀ p, ∃ hp : (p.1 : sourceSlab) ∈ U,
            Θ' p = (D (p.2 : ℝ) ⟨p.1, hp⟩ : sourceSlab)) ∧
          (∀ z : (⟨U, hU⟩ : TopologicalSpace.Opens sourceSlab),
            sourceCoord (z : sourceSlab) = 0 → -r' ≤ packetBoundary (z : sourceSlab) →
              ∀ t ∈ Ioo a b, sourceCoord (D t z : sourceSlab) = t) ∧
          ∀ (z : (⟨U, hU⟩ : TopologicalSpace.Opens sourceSlab)) (t : ℝ),
            |packetBoundary (z : sourceSlab)| < r' →
              edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (D t z : sourceSlab) =
                edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (z : sourceSlab)) ∧
      ∃ O' : Set sourceSlab, IsOpen O' ∧
        (∀ y : sourceSlab, sourceCoord y ∈ Ioo a b → 0 ≤ packetBoundary y → y ∈ O') ∧
        ∃ R : sourceSlab → sourceSlab,
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
          ∀ (y : sourceSlab) (hy : sourceCoord y ∈ Ioo a b), 0 ≤ packetBoundary y →
            ∃ hR : sourceCoord (R y) = 0 ∧ 0 ≤ packetBoundary (R y),
              Θ' (⟨R y, hR⟩, ⟨sourceCoord y, hy⟩) = y := by
  refine ⟨trivialization a b, trivialization_smooth a b,
    fun p => ⟨trivialization_coord a b ha hb p, trivialization_boundary a b p⟩,
    trivialization_zero a b h0, trivialization_injective a b ha hb, ?_, ?_⟩
  · refine ⟨1, by norm_num, fun p _ => trivialization_height a b p,
      univ, isOpen_univ, rimFlow, rimFlow_joint, rimFlow_zero, rimFlow_add, ?_, ?_, ?_⟩
    · intro p
      exact ⟨mem_univ _, rfl⟩
    · intro z hz _ t ht
      exact rimFlow_central z hz t (timeInterval_bound a b ha hb ⟨t, ht⟩)
    · intro z t _
      exact rimFlow_height z t
  · refine ⟨univ, isOpen_univ, fun _ _ _ => mem_univ _, sourceRetraction,
      sourceRetraction_smooth.contMDiffOn, ?_⟩
    intro y hy hB
    exact trivialization_recovery a b ha hb y hy hB

end DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial
