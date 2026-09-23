import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

theorem backwardSurvivorTerminalFaceMap_isOpenEmbedding :
    _root_.Topology.IsOpenEmbedding (H.backwardSurvivorTerminalFaceMap first i hle) :=
  IsLocalHomeomorph.isOpenEmbedding_of_injective
    (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hle).isLocalHomeomorph
    (H.backwardSurvivorTerminalFaceMap_injective first i hle)

theorem image_preimage_backwardSurvivorTerminalFaceMap
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val)) :
    H.backwardSurvivorTerminalFaceMap first i hle ''
      (H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' K) = K := by
  apply image_preimage_eq_of_subset
  intro x hx
  exact (H.mem_range_backwardSurvivorTerminalFaceMap_iff first i hle x).mpr (htrace x hx)

theorem isCompact_preimage_backwardSurvivorTerminalFaceMap
    (K : Set (H.event i).incoming.terminalRegularOpen) (hK : IsCompact K)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val)) :
    IsCompact (H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' K) := by
  rw [(H.backwardSurvivorTerminalFaceMap_isOpenEmbedding first i hle).isEmbedding.isCompact_iff]
  rw [H.image_preimage_backwardSurvivorTerminalFaceMap first i hle K htrace]
  exact hK

theorem isConnected_preimage_backwardSurvivorTerminalFaceMap
    (K : Set (H.event i).incoming.terminalRegularOpen) (hK : IsConnected K)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val)) :
    IsConnected (H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' K) := by
  have he := H.image_preimage_backwardSurvivorTerminalFaceMap first i hle K htrace
  refine ⟨?_, ?_⟩
  · have hne : (H.backwardSurvivorTerminalFaceMap first i hle ''
        (H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' K)).Nonempty := he.symm ▸ hK.nonempty
    exact hne.of_image
  · apply (_root_.Topology.IsInducing.isPreconnected_image
      (H.backwardSurvivorTerminalFaceMap_isOpenEmbedding first i hle).isInducing).mp
    simpa only [he] using hK.isPreconnected

theorem preimage_interior_backwardSurvivorTerminalFaceMap
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' interior K =
      interior (H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' K) :=
  IsOpenMap.preimage_interior_eq_interior_preimage
    (H.backwardSurvivorTerminalFaceMap_isOpenEmbedding first i hle).isOpenMap
    (H.backwardSurvivorTerminalFaceMap_isOpenEmbedding first i hle).continuous K

def backwardSurvivorFootprintInterior
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    Opens (H.backwardSurvivorTerminalFace first i hle) :=
  ⟨H.backwardSurvivorTerminalFaceMap first i hle ⁻¹' interior K,
    isOpen_interior.preimage
      (H.backwardSurvivorTerminalFaceMap_isOpenEmbedding first i hle).continuous⟩

def backwardSurvivorFootprintMap
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    H.backwardSurvivorFootprintInterior first i hle K →
      (H.event i).incoming.terminalRegularOpen :=
  H.backwardSurvivorTerminalFaceMap first i hle ∘ Subtype.val

theorem backwardSurvivorFootprintMap_isLocalDiffeomorph
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (H.backwardSurvivorFootprintMap first i hle K) := by
  intro x
  exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := ThreeModel)
    (H.backwardSurvivorFootprintInterior first i hle K) x).comp ThreeModel _
      (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hle x.val)

theorem backwardSurvivorFootprintMap_injective
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    Function.Injective (H.backwardSurvivorFootprintMap first i hle K) :=
  (H.backwardSurvivorTerminalFaceMap_injective first i hle).comp Subtype.val_injective

theorem range_backwardSurvivorFootprintMap
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val)) :
    range (H.backwardSurvivorFootprintMap first i hle K) = interior K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    obtain ⟨y, hy⟩ := (H.mem_range_backwardSurvivorTerminalFaceMap_iff first i hle x).mpr
      (htrace x (interior_subset hx))
    exact ⟨⟨y, by change H.backwardSurvivorTerminalFaceMap first i hle y ∈ interior K
                  rwa [hy]⟩, hy⟩

theorem backwardSurvivorTerminalFaceMetric_restrict_footprint_terminal
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    (H.backwardSurvivorTerminalFaceMetric first i hle (H.time i.succ)).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K) =
      localPullMetric (H.event i).terminal.metric (H.backwardSurvivorFootprintMap first i hle K)
        (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) := by
  rw [H.backwardSurvivorTerminalFaceMetric_terminal]
  rw [← DifferentialGeometry.localPullMetric_subtype_val]
  exact DifferentialGeometry.localPullMetric_comp _ _ _ _ _ _

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorDomain first i.castSucc hle).isOpen)

private local instance : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorTerminalFace first i hle).isOpen)

private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

theorem exists_backwardSurvivorFootprint_isSolutionOn
    (K : Set (H.event i).incoming.terminalRegularOpen) :
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      G (H.time i.succ) = localPullMetric (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K)
        (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × H.backwardSurvivorFootprintInterior first i hle K =>
          (⟨q.2, (G q.1).inner q.2⟩ : TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) (H.time i.succ) ×ˢ univ) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
          (RealTimeInterval.closed (H.time first) (H.time i.succ)
            (H.time_strictMono.monotone (hle.trans i.castSucc_lt_succ.le)))) := by
  obtain ⟨F, hslabs, hlast, hsm, hsol⟩ :=
    H.exists_backwardSurvivorTerminal_isSolutionOn first i hle
  let V := H.backwardSurvivorFootprintInterior first i hle K
  refine ⟨fun t => (F t).restrictOpen V, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hf hl t ht
    dsimp only
    rw [hslabs j hf hl t ht]
  · intro t ht
    dsimp only
    rw [hlast t ht]
  · dsimp only
    rw [hlast _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩]
    exact H.backwardSurvivorTerminalFaceMetric_restrict_footprint_terminal first i hle K
  · apply metricCLMSection_jointContMDiffOn_of_chartGram_on
      (fun t => (F t).restrictOpen V) _
    intro p j k
    apply chartGramMatrix_joint_contMDiffOn_of_pullback F _ hsm
      (fun t => (F t).restrictOpen V) Subtype.val contMDiff_subtype_val
    intro t ht x v w
    simp only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
  · let _ : IsManifold ThreeModel 1 V := IsManifold.of_le (n := ∞) (by decide)
    exact DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen _ hsol V

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

def backwardSurvivorFootprintPoint
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (p : (H.event i).incoming.terminalRegularOpen) (hp : p ∈ interior K) :
    H.backwardSurvivorFootprintInterior first i hle K :=
  ⟨⟨⟨p.val, htrace p (interior_subset hp)⟩, p.property⟩, hp⟩

@[simp] theorem backwardSurvivorFootprintMap_point
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (p : (H.event i).incoming.terminalRegularOpen) (hp : p ∈ interior K) :
    H.backwardSurvivorFootprintMap first i hle K
      (H.backwardSurvivorFootprintPoint first i hle K htrace p hp) = p := rfl

theorem terminal_closedBall_subset_range_backwardSurvivorFootprintMap
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (p : (H.event i).incoming.terminalRegularOpen) (R : ℝ≥0)
    (hball : {x | riemannianEDistOf (H.event i).terminal.metric p x ≤ R} ⊆ interior K) :
    {x | riemannianEDistOf (H.event i).terminal.metric p x ≤ R} ⊆
      range (H.backwardSurvivorFootprintMap first i hle K) := by
  rw [H.range_backwardSurvivorFootprintMap first i hle K htrace]
  exact hball

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

variable {X : Type*}

def backwardSurvivorFootprintLift
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (F : X → (H.event i).incoming.terminalRegularOpen) (hF : range F ⊆ interior K) :
    X → H.backwardSurvivorFootprintInterior first i hle K := fun x =>
  H.backwardSurvivorFootprintPoint first i hle K htrace (F x) (hF (mem_range_self x))

@[simp] theorem backwardSurvivorFootprintMap_lift
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (F : X → (H.event i).incoming.terminalRegularOpen) (hF : range F ⊆ interior K) (x : X) :
    H.backwardSurvivorFootprintMap first i hle K
      (H.backwardSurvivorFootprintLift first i hle K htrace F hF x) = F x := rfl

@[simp] theorem backwardSurvivorFootprintMap_comp_lift
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (F : X → (H.event i).incoming.terminalRegularOpen) (hF : range F ⊆ interior K) :
    H.backwardSurvivorFootprintMap first i hle K ∘
      H.backwardSurvivorFootprintLift first i hle K htrace F hF = F := rfl

theorem backwardSurvivorFootprintLift_unique
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (F : X → (H.event i).incoming.terminalRegularOpen) (hF : range F ⊆ interior K)
    (L : X → H.backwardSurvivorFootprintInterior first i hle K)
    (hL : H.backwardSurvivorFootprintMap first i hle K ∘ L = F) :
    L = H.backwardSurvivorFootprintLift first i hle K htrace F hF := by
  funext x
  apply H.backwardSurvivorFootprintMap_injective first i hle K
  exact congrFun hL x

variable {E XH : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace X] [ChartedSpace XH X]

theorem backwardSurvivorFootprintLift_contMDiff
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (F : X → (H.event i).incoming.terminalRegularOpen) (hF : range F ⊆ interior K)
    {n : ℕ∞ω} (hsmooth : ContMDiff I ThreeModel n F) :
    ContMDiff I ThreeModel n (H.backwardSurvivorFootprintLift first i hle K htrace F hF) := by
  apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff
    (H.backwardSurvivorFootprintInterior first i hle K) _).mp
  apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff
    (H.backwardSurvivorTerminalFace first i hle) _).mp
  apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff
    (H.backwardSurvivorDomain first i.castSucc hle) _).mp
  change ContMDiff I ThreeModel n (Subtype.val ∘ F)
  exact contMDiff_subtype_val.comp hsmooth

theorem backwardSurvivorFootprintLift_isSmoothEmbedding
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (F : X → (H.event i).incoming.terminalRegularOpen) (hF : range F ⊆ interior K)
    (hemb : IsSmoothEmbedding I ThreeModel ∞ F) :
    IsSmoothEmbedding I ThreeModel ∞
      (H.backwardSurvivorFootprintLift first i hle K htrace F hF) := by
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
    (H.backwardSurvivorFootprintInterior first i hle K)
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
    (H.backwardSurvivorTerminalFace first i hle)
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
    (H.backwardSurvivorDomain first i.castSucc hle)
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen I ThreeModel
    (H.event i).incoming.terminalRegularOpen F hemb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
