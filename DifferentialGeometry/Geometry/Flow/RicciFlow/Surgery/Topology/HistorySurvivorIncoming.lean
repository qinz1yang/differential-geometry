import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Topology.Manifold.OpenCoverLocalDiffeomorph
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

def backwardSurvivorIncomingDomain : Opens (H.backwardSurvivorDomain first last hle) :=
  ⟨Subtype.val ⁻¹' G.terminalRegularOpen,
    G.terminalRegularOpen.isOpen.preimage continuous_subtype_val⟩

private local instance : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G).isOpen)

def backwardSurvivorIncomingMap :
    H.backwardSurvivorIncomingDomain first last hle G → G.terminalRegularOpen :=
  fun x => ⟨x.val.val, x.property⟩

@[simp] theorem backwardSurvivorIncomingMap_val
    (x : H.backwardSurvivorIncomingDomain first last hle G) :
    (H.backwardSurvivorIncomingMap first last hle G x).val = x.val.val := rfl

theorem backwardSurvivorIncomingMap_contMDiff :
    ContMDiff ThreeModel ThreeModel ∞ (H.backwardSurvivorIncomingMap first last hle G) := by
  apply (ContMDiff.subtypeVal_comp_iff G.terminalRegularOpen _).mp
  change ContMDiff ThreeModel ThreeModel ∞
    (fun x : H.backwardSurvivorIncomingDomain first last hle G => x.val.val)
  exact contMDiff_subtype_val.comp contMDiff_subtype_val

theorem backwardSurvivorIncomingMap_mfderiv
    (x : H.backwardSurvivorIncomingDomain first last hle G) :
    mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G) x =
      ContinuousLinearMap.id ℝ ThreeSpace := by
  have h₁ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (H.backwardSurvivorIncomingMap first last hle G) x
  have h₂ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (Subtype.val : H.backwardSurvivorIncomingDomain first last hle G →
      H.backwardSurvivorDomain first last hle) x
  exact h₁.symm.trans (h₂.trans (DifferentialGeometry.mfderiv_subtype_val _ x))

theorem backwardSurvivorIncomingMap_injective :
    Function.Injective (H.backwardSurvivorIncomingMap first last hle G) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : G.terminalRegularOpen => z.val) hxy

theorem backwardSurvivorIncomingMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (H.backwardSurvivorIncomingMap first last hle G) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (H.backwardSurvivorIncomingMap_contMDiff first last hle G) _ rfl
  intro x
  rw [H.backwardSurvivorIncomingMap_mfderiv first last hle G x]
  exact Function.injective_id

def backwardSurvivorIncomingMetric (t : ℝ) :
    SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G) :=
  localPullMetric (L.extendedMetric t)
    (H.backwardSurvivorIncomingMap first last hle G)
    (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G)

@[simp] theorem backwardSurvivorIncomingMetric_inner
    (t : ℝ) (x : H.backwardSurvivorIncomingDomain first last hle G)
    (v w : TangentSpace ThreeModel x) :
    (H.backwardSurvivorIncomingMetric first last hle G L t).inner x v w =
      (L.extendedMetric t).inner
        (H.backwardSurvivorIncomingMap first last hle G x) v w := by
  rw [backwardSurvivorIncomingMetric, localPullMetric_inner,
    H.backwardSurvivorIncomingMap_mfderiv first last hle G x]
  rfl

theorem backwardSurvivorIncomingMetric_jointContMDiffOn :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × H.backwardSurvivorIncomingDomain first last hle G =>
        (⟨q.2, (H.backwardSurvivorIncomingMetric first last hle G L q.1).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ]
              TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Icc (H.time last) s ×ˢ univ) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (H.backwardSurvivorIncomingMetric first last hle G L) _
  intro p j k
  apply chartGramMatrix_joint_contMDiffOn_of_pullback L.extendedMetric _
    (L.extendedMetric_jointContMDiffOn le_rfl G.lt)
    (H.backwardSurvivorIncomingMetric first last hle G L)
    (H.backwardSurvivorIncomingMap first last hle G)
    (H.backwardSurvivorIncomingMap_contMDiff first last hle G)
  intro t ht x v w
  exact localPullMetric_inner _ _ _ _ _ _

theorem backwardSurvivorIncomingMetric_hasDerivAt
    {t : ℝ} (ht : t ∈ Ioo (H.time last) s)
    (x : H.backwardSurvivorIncomingDomain first last hle G) (v w : TangentSpace ThreeModel x) :
    HasDerivAt (fun u => (H.backwardSurvivorIncomingMetric first last hle G L u).inner x v w)
      (-2 * ricciTensor (H.backwardSurvivorIncomingMetric first last hle G L t) x v w) t := by
  have hd := L.extendedMetric_hasDerivAt ht
    (H.backwardSurvivorIncomingMap first last hle G x)
    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G) x v)
    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G) x w)
  dsimp only [backwardSurvivorIncomingMetric]
  rw [ricciTensor_localPullMetric]
  simpa only [localPullMetric_inner] using hd

theorem backwardSurvivorIncomingMetric_before
    {t : ℝ} (ht : t < s) :
    H.backwardSurvivorIncomingMetric first last hle G L t =
      ((G.flow.base.metric t).restrictOpen
        (H.backwardSurvivorDomain first last hle)).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorIncomingMetric_inner,
    L.extendedMetric_before ht]
  rfl

theorem backwardSurvivorIncomingMetric_initial
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last) :
    H.backwardSurvivorIncomingMetric first last hle G L (H.time last) =
      (H.backwardSurvivorInitialMetric first last hle last hle le_rfl).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorIncomingMetric_inner,
    L.extendedMetric_before G.lt]
  change (G.flow.base.metric (H.time last)).inner x.val.val v w =
    (H.backwardSurvivorInitialMetric first last hle last hle le_rfl).inner x.val v w
  rw [hinit]
  dsimp only [backwardSurvivorInitialMetric]
  erw [localPullMetric_inner]
  have hmap : H.backwardSurvivorMap first last hle last hle le_rfl =
      (Subtype.val : H.backwardSurvivorDomain first last hle →
        (H.stage last).Carrier) :=
    funext (H.backwardSurvivorMap_last first last hle)
  rw [hmap, DifferentialGeometry.mfderiv_subtype_val]
  rfl

theorem backwardSurvivorIncomingMetric_terminal :
    H.backwardSurvivorIncomingMetric first last hle G L s =
      localPullMetric L.metric
        (H.backwardSurvivorIncomingMap first last hle G)
        (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G) := by
  rw [backwardSurvivorIncomingMetric,
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]

def backwardSurvivorIncomingClosedSlab :
    SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time last) s
        G.lt.le) where
  base := { metric := H.backwardSurvivorIncomingMetric first last hle G L }

theorem backwardSurvivorIncomingClosedSlab_isSolutionOn :
    IsSolutionOn (H.backwardSurvivorIncomingClosedSlab first last hle G L) := by
  apply isSolutionOn_of_joint_metric _
    (uniqueDiffOn_Icc G.lt)
    (H.backwardSurvivorIncomingMetric first last hle G L)
    (H.backwardSurvivorIncomingMetric_jointContMDiffOn first last hle G L)
  intro t ht x v w
  exact (H.backwardSurvivorIncomingMetric_hasDerivAt first last hle G L ht x v w).hasDerivWithinAt


theorem mem_range_backwardSurvivorIncomingMap_iff
    (x : G.terminalRegularOpen) :
    x ∈ range (H.backwardSurvivorIncomingMap first last hle G) ↔
      Nonempty (BackwardPointTrace H first last hle x.val) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.property
  · intro h
    exact ⟨⟨⟨x.val, h⟩, x.property⟩, rfl⟩

theorem exists_backwardSurvivorIncoming_isSolutionOn
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last) :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × H.backwardSurvivorIncomingDomain first last hle G =>
          (⟨q.2, (gflow q.1).inner q.2⟩ : TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) s ×ˢ univ) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingDomain first last hle G)
          (RealTimeInterval.closed (H.time first) s
            ((H.time_strictMono.monotone hle).trans G.lt.le))) := by
  rcases eq_or_lt_of_le hle with he | hlt
  · subst first
    refine ⟨H.backwardSurvivorIncomingMetric last last le_rfl G L, ?_, ?_,
      H.backwardSurvivorIncomingMetric_jointContMDiffOn last last le_rfl G L,
      H.backwardSurvivorIncomingClosedSlab_isSolutionOn last last le_rfl G L⟩
    · intro j hf hl t ht
      have hfj : last.val ≤ j.val := hf
      have hji : j.val + 1 ≤ last.val := hl
      omega
    · intro t ht
      rfl
  · obtain ⟨F, hslabs, hstages, hsm, hsol⟩ :=
      H.exists_backwardSurvivor_isSolutionOn first last hlt
    let W := H.backwardSurvivorIncomingDomain first last hle G
    let gL := fun t => (F t).restrictOpen W
    let gR := H.backwardSurvivorIncomingMetric first last hle G L
    have ha : H.time first < H.time last := H.time_strictMono hlt
    have hb : H.time last < s := G.lt
    have hL : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × W => (⟨q.2, (gL q.1).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) (H.time last) ×ˢ univ) := by
      apply metricCLMSection_jointContMDiffOn_of_chartGram_on gL _
      intro p j k
      apply chartGramMatrix_joint_contMDiffOn_of_pullback F _ hsm gL
        Subtype.val contMDiff_subtype_val
      intro t ht x v w
      simp only [gL, SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
    have hpdeL : ∀ t ∈ Ioo (H.time first) (H.time last),
        ∀ x : W, ∀ v w : TangentSpace ThreeModel x,
          HasDerivAt (fun s => (gL s).inner x v w)
            (-2 * ricciTensor (gL t) x v w) t := by
      intro t ht x v w
      have hd := (hsol.equation ⟨t, ht⟩ x.val v w).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      change HasDerivAt (fun s => (F s).inner x.val v w)
        (-2 * metricRicciAt (F t) x.val (vec2 v w)) t at hd
      erw [metricRicciAt_apply_eq_ricciTensor (F t) x.val v w] at hd
      dsimp only [gL]
      rw [Geometry.Curvature.ricciTensor_restrictOpen]
      simpa only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply] using hd
    have hmatch : gL (H.time last) = gR (H.time last) := by
      dsimp only [gL, gR]
      rw [hstages last hle le_rfl, H.backwardSurvivorIncomingMetric_initial first last hle G L hinit]
    have hR := H.backwardSurvivorIncomingMetric_jointContMDiffOn first last hle G L
    have hpdeR := fun t ht x v w =>
      H.backwardSurvivorIncomingMetric_hasDerivAt first last hle G L (t := t) ht x v w
    refine ⟨fun t => if t ≤ H.time last then gL t else gR t, ?_, ?_, ?_, ?_⟩
    · intro j hf hl t ht
      have htc : t ≤ H.time last := ht.2.trans (H.time_strictMono.monotone hl)
      dsimp only
      rw [ite_eq_left htc]
      exact congrArg (fun g => g.restrictOpen W) (hslabs j hf hl t ht)
    · intro t ht
      dsimp only
      by_cases htc : t ≤ H.time last
      · have he : t = H.time last := le_antisymm htc ht.1
        subst t
        rw [ite_eq_left le_rfl]
        exact hmatch
      · rw [ite_eq_right htc]
    · exact metricCLMSection_jointContMDiffOn_ite_of_ricciFlow gL gR ha hb
        hL hR hpdeL hpdeR hmatch
    · exact isSolutionOn_ite_of_ricciFlow gL gR ha hb hL hR hpdeL hpdeR hmatch


theorem backwardSurvivorIncomingMap_isOpenEmbedding :
    _root_.Topology.IsOpenEmbedding (H.backwardSurvivorIncomingMap first last hle G) :=
  IsLocalHomeomorph.isOpenEmbedding_of_injective
    (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G).isLocalHomeomorph
    (H.backwardSurvivorIncomingMap_injective first last hle G)

theorem image_preimage_backwardSurvivorIncomingMap
    (K : Set G.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)) :
    H.backwardSurvivorIncomingMap first last hle G ''
      (H.backwardSurvivorIncomingMap first last hle G ⁻¹' K) = K := by
  apply image_preimage_eq_of_subset
  intro x hx
  exact (H.mem_range_backwardSurvivorIncomingMap_iff first last hle G x).mpr (htrace x hx)

theorem isCompact_preimage_backwardSurvivorIncomingMap
    (K : Set G.terminalRegularOpen) (hK : IsCompact K)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)) :
    IsCompact (H.backwardSurvivorIncomingMap first last hle G ⁻¹' K) := by
  rw [(H.backwardSurvivorIncomingMap_isOpenEmbedding first last hle G).isEmbedding.isCompact_iff]
  rw [H.image_preimage_backwardSurvivorIncomingMap first last hle G K htrace]
  exact hK

theorem isConnected_preimage_backwardSurvivorIncomingMap
    (K : Set G.terminalRegularOpen) (hK : IsConnected K)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)) :
    IsConnected (H.backwardSurvivorIncomingMap first last hle G ⁻¹' K) := by
  have he := H.image_preimage_backwardSurvivorIncomingMap first last hle G K htrace
  refine ⟨?_, ?_⟩
  · have hne : (H.backwardSurvivorIncomingMap first last hle G ''
        (H.backwardSurvivorIncomingMap first last hle G ⁻¹' K)).Nonempty := he.symm ▸ hK.nonempty
    exact hne.of_image
  · apply (_root_.Topology.IsInducing.isPreconnected_image
      (H.backwardSurvivorIncomingMap_isOpenEmbedding first last hle G).isInducing).mp
    simpa only [he] using hK.isPreconnected

theorem preimage_interior_backwardSurvivorIncomingMap
    (K : Set G.terminalRegularOpen) :
    H.backwardSurvivorIncomingMap first last hle G ⁻¹' interior K =
      interior (H.backwardSurvivorIncomingMap first last hle G ⁻¹' K) :=
  IsOpenMap.preimage_interior_eq_interior_preimage
    (H.backwardSurvivorIncomingMap_isOpenEmbedding first last hle G).isOpenMap
    (H.backwardSurvivorIncomingMap_isOpenEmbedding first last hle G).continuous K

def backwardSurvivorIncomingFootprint
    (K : Set G.terminalRegularOpen) :
    Opens (H.backwardSurvivorIncomingDomain first last hle G) :=
  ⟨H.backwardSurvivorIncomingMap first last hle G ⁻¹' interior K,
    isOpen_interior.preimage
      (H.backwardSurvivorIncomingMap_isOpenEmbedding first last hle G).continuous⟩

def backwardSurvivorIncomingFootprintMap
    (K : Set G.terminalRegularOpen) :
    H.backwardSurvivorIncomingFootprint first last hle G K →
      G.terminalRegularOpen :=
  H.backwardSurvivorIncomingMap first last hle G ∘ Subtype.val

theorem backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph
    (K : Set G.terminalRegularOpen) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (H.backwardSurvivorIncomingFootprintMap first last hle G K) := by
  intro x
  exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := ThreeModel)
    (H.backwardSurvivorIncomingFootprint first last hle G K) x).comp ThreeModel _
      (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G x.val)

theorem backwardSurvivorIncomingFootprintMap_injective
    (K : Set G.terminalRegularOpen) :
    Function.Injective (H.backwardSurvivorIncomingFootprintMap first last hle G K) :=
  (H.backwardSurvivorIncomingMap_injective first last hle G).comp Subtype.val_injective

theorem range_backwardSurvivorIncomingFootprintMap
    (K : Set G.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)) :
    range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    obtain ⟨y, hy⟩ := (H.mem_range_backwardSurvivorIncomingMap_iff first last hle G x).mpr
      (htrace x (interior_subset hx))
    exact ⟨⟨y, by change H.backwardSurvivorIncomingMap first last hle G y ∈ interior K
                  rwa [hy]⟩, hy⟩

theorem backwardSurvivorIncomingMetric_restrict_footprint_terminal
    (K : Set G.terminalRegularOpen) :
    (H.backwardSurvivorIncomingMetric first last hle G L s).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K) =
      localPullMetric L.metric (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) := by
  rw [H.backwardSurvivorIncomingMetric_terminal]
  rw [← DifferentialGeometry.localPullMetric_subtype_val]
  exact DifferentialGeometry.localPullMetric_comp _ _ _ _ _ _

private local instance (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

theorem exists_backwardSurvivorIncomingFootprint_isSolutionOn
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen) :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first last hle G K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      gflow s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × H.backwardSurvivorIncomingFootprint first last hle G K =>
          (⟨q.2, (gflow q.1).inner q.2⟩ : TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) s ×ˢ univ) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
          (RealTimeInterval.closed (H.time first) s
            ((H.time_strictMono.monotone hle).trans G.lt.le))) := by
  obtain ⟨F, hslabs, hlast, hsm, hsol⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hinit
  let V := H.backwardSurvivorIncomingFootprint first last hle G K
  refine ⟨fun t => (F t).restrictOpen V, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hf hl t ht
    dsimp only
    rw [hslabs j hf hl t ht]
  · intro t ht
    dsimp only
    rw [hlast t ht]
  · dsimp only
    rw [hlast _ ⟨G.lt.le, le_rfl⟩]
    exact H.backwardSurvivorIncomingMetric_restrict_footprint_terminal first last hle G L K
  · apply metricCLMSection_jointContMDiffOn_of_chartGram_on
      (fun t => (F t).restrictOpen V) _
    intro p j k
    apply chartGramMatrix_joint_contMDiffOn_of_pullback F _ hsm
      (fun t => (F t).restrictOpen V) Subtype.val contMDiff_subtype_val
    intro t ht x v w
    simp only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
  · let _ : IsManifold ThreeModel 1 V := IsManifold.of_le (n := ∞) (by decide)
    exact DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen _ hsol V


theorem exists_incomingFootprint_point_isCompact_terminal_closedBall
    (x : G.terminalRegularOpen) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x R))
    (hrange : range (H.backwardSurvivorIncomingFootprintMap first last hle G
        (riemannianClosedBallOf L.metric x R)) =
      interior (riemannianClosedBallOf L.metric x R))
    (g : SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G
        (riemannianClosedBallOf L.metric x R)))
    (hg : g = localPullMetric L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G
        (riemannianClosedBallOf L.metric x R))
      (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G
        (riemannianClosedBallOf L.metric x R))) :
    ∃ p : H.backwardSurvivorIncomingFootprint first last hle G
        (riemannianClosedBallOf L.metric x R),
      H.backwardSurvivorIncomingFootprintMap first last hle G
        (riemannianClosedBallOf L.metric x R) p = x ∧
      ∀ r : ℝ, r < R → IsCompact (riemannianClosedBallOf g p r) := by
  have hopen : IsOpen (riemannianBallOf L.metric x R) :=
    isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ x) continuous_const
  have hball : riemannianBallOf L.metric x R ⊆
      range (H.backwardSurvivorIncomingFootprintMap first last hle G
        (riemannianClosedBallOf L.metric x R)) := by
    rw [hrange]
    apply interior_maximal ?_ hopen
    intro y hy
    exact le_of_lt (show riemannianEDistOf L.metric x y <
      ENNReal.ofReal R from hy)
  obtain ⟨p, hp, hc⟩ := Geometry.Metric.exists_lift_isCompact_riemannianClosedBallOf_localPullMetric
    L.metric
    (H.backwardSurvivorIncomingFootprintMap first last hle G
      (riemannianClosedBallOf L.metric x R))
    (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G
      (riemannianClosedBallOf L.metric x R))
    (H.backwardSurvivorIncomingFootprintMap_injective first last hle G
      (riemannianClosedBallOf L.metric x R)) x hR hcompact hball
  exact ⟨p, hp, fun r hr => hg.symm ▸ hc r hr⟩


def backwardSurvivorIncomingFootprintPoint
    (K : Set G.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val))
    (p : G.terminalRegularOpen) (hp : p ∈ interior K) :
    H.backwardSurvivorIncomingFootprint first last hle G K :=
  ⟨⟨⟨p.val, htrace p (interior_subset hp)⟩, p.property⟩, hp⟩

@[simp] theorem backwardSurvivorIncomingFootprintMap_point
    (K : Set G.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val))
    (p : G.terminalRegularOpen) (hp : p ∈ interior K) :
    H.backwardSurvivorIncomingFootprintMap first last hle G K
      (H.backwardSurvivorIncomingFootprintPoint first last hle G K htrace p hp) = p := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {s : ℝ} {G : (H.stage last).IncomingSlab (H.time last) s} {L : G.TerminalLimitMetric}
  {E XH X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace X] [ChartedSpace XH X] [IsManifold I ∞ X] [T2Space X]

private theorem localPullMetric_incoming_footprint_restrict_eq
    (g : SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (K₁ K₂ : Set G.terminalRegularOpen)
    (Φ₁ : X → H.backwardSurvivorIncomingFootprint first last hle G K₁)
    (Φ₂ : X → H.backwardSurvivorIncomingFootprint first last hle G K₂)
    (hΦ₁ : IsLocalDiffeomorph I ThreeModel ∞ Φ₁)
    (hΦ₂ : IsLocalDiffeomorph I ThreeModel ∞ Φ₂)
    (hcomp : H.backwardSurvivorIncomingFootprintMap first last hle G K₁ ∘ Φ₁ =
      H.backwardSurvivorIncomingFootprintMap first last hle G K₂ ∘ Φ₂) :
    localPullMetric (g.restrictOpen (H.backwardSurvivorIncomingFootprint first last hle G K₁))
      Φ₁ hΦ₁ =
    localPullMetric (g.restrictOpen (H.backwardSurvivorIncomingFootprint first last hle G K₂))
      Φ₂ hΦ₂ := by
  have heq : (Subtype.val ∘ Φ₁ : X → H.backwardSurvivorIncomingDomain first last hle G) =
      Subtype.val ∘ Φ₂ := by
    funext x
    apply H.backwardSurvivorIncomingMap_injective first last hle G
    exact congrFun hcomp x
  rw [← localPullMetric_subtype_val g (H.backwardSurvivorIncomingFootprint first last hle G K₁),
    ← localPullMetric_subtype_val g (H.backwardSurvivorIncomingFootprint first last hle G K₂)]
  rw [localPullMetric_comp g Subtype.val Φ₁ _ hΦ₁
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΦ₁),
    localPullMetric_comp g Subtype.val Φ₂ _ hΦ₂
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΦ₂)]
  congr 1

theorem localPullMetric_backwardSurvivorIncomingFootprint_eq
    (K₁ K₂ : Set G.terminalRegularOpen)
    (G₁ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K₁))
    (G₂ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K₂))
    (hslabs₁ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ last), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      G₁ t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K₁))
    (hslabs₂ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ last), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      G₂ t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K₂))
    (hlast₁ : ∀ t ∈ Icc (H.time last) s,
      G₁ t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K₁))
    (hlast₂ : ∀ t ∈ Icc (H.time last) s,
      G₂ t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K₂))
    (Φ₁ : X → H.backwardSurvivorIncomingFootprint first last hle G K₁)
    (Φ₂ : X → H.backwardSurvivorIncomingFootprint first last hle G K₂)
    (hΦ₁ : IsLocalDiffeomorph I ThreeModel ∞ Φ₁)
    (hΦ₂ : IsLocalDiffeomorph I ThreeModel ∞ Φ₂)
    (hcomp : H.backwardSurvivorIncomingFootprintMap first last hle G K₁ ∘ Φ₁ =
      H.backwardSurvivorIncomingFootprintMap first last hle G K₂ ∘ Φ₂)
    {t : ℝ} (ht : t ∈ Icc (H.time first) s) :
    localPullMetric (G₁ t) Φ₁ hΦ₁ = localPullMetric (G₂ t) Φ₂ hΦ₂ := by
  by_cases hlast : H.time last ≤ t
  · rw [hlast₁ t ⟨hlast, ht.2⟩, hlast₂ t ⟨hlast, ht.2⟩]
    exact localPullMetric_incoming_footprint_restrict_eq _ K₁ K₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hcomp
  have hti : t < H.time last := lt_of_not_ge hlast
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
  let k := H.activeStage tH
  have hk : k < last := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt hti
  have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
  let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
  have hjnext : j.succ ≤ last := by
    change k.val + 1 ≤ last.val
    exact hk
  have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
    ⟨H.activeStage_time_le tH,
      (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
  rw [hslabs₁ j hkfirst hjnext t htj, hslabs₂ j hkfirst hjnext t htj]
  exact localPullMetric_incoming_footprint_restrict_eq _ K₁ K₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hcomp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)

theorem backwardSurvivorIncomingMap_eq_of_initial_point_eq
    {X : Type*} (J : X → (H.stage first).Carrier)
    (F : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hF : ∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (F y).val = J y)
    (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val) (y : X)
    (hbirth : J y = A.point first le_rfl hle) :
    H.backwardSurvivorIncomingMap first last hle G (F y) = x := by
  let B : BackwardPointTrace H first last hle (F y).val.val := Classical.choice (F y).val.property
  have hB : B.point first le_rfl hle = A.point first le_rfl hle := by
    have he := H.backwardSurvivorMap_eq_point first last hle first le_rfl hle (F y).val B
    exact he.symm.trans ((hF y).trans hbirth)
  exact Subtype.ext (B.endpoint_eq_of_point_first_eq A hB)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


noncomputable section
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

theorem backwardSurvivorIncomingMetric_eq_of_common_piecewise_flow
    (G₁ G₂ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs₁ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₁ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs₂ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₂ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast₁ : ∀ t ∈ Icc (H.time last) s,
      G₁ t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (hlast₂ : ∀ t ∈ Icc (H.time last) s,
      G₂ t = H.backwardSurvivorIncomingMetric first last hle G L t)
    {t : ℝ} (ht : t ∈ Icc (H.time first) s) : G₁ t = G₂ t := by
  by_cases hlast : H.time last ≤ t
  · exact (hlast₁ t ⟨hlast, ht.2⟩).trans (hlast₂ t ⟨hlast, ht.2⟩).symm
  have hti : t < H.time last := lt_of_not_ge hlast
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
  let k := H.activeStage tH
  have hk : k < last := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt hti
  have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
  let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
  have hjnext : j.succ ≤ last := by
    change k.val + 1 ≤ last.val
    exact hk
  have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
    ⟨H.activeStage_time_le tH,
      (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
  exact (hslabs₁ j hkfirst hjnext t htj).trans (hslabs₂ j hkfirst hjnext t htj).symm

theorem localPullMetric_backwardSurvivorIncoming_overlap_of_initial_eq
    {E X M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] {I : ModelWithCorners ℝ E X}
    [TopologicalSpace M] [ChartedSpace X M] [IsManifold I ∞ M] [T2Space M]
    {U V W : Opens M} (hWU : W ≤ U) (hWV : W ≤ V)
    (G₁ G₂ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs₁ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₁ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs₂ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G₂ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast₁ : ∀ t ∈ Icc (H.time last) s,
      G₁ t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (hlast₂ : ∀ t ∈ Icc (H.time last) s,
      G₂ t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (F₁ : U → H.backwardSurvivorIncomingDomain first last hle G)
    (F₂ : V → H.backwardSurvivorIncomingDomain first last hle G)
    (hF₁ : IsLocalDiffeomorph I ThreeModel ∞ F₁)
    (hF₂ : IsLocalDiffeomorph I ThreeModel ∞ F₂)
    (hbirth : ∀ y : W,
      H.backwardSurvivorMap first last hle first le_rfl hle
        (F₁ (Opens.inclusion hWU y)).val =
      H.backwardSurvivorMap first last hle first le_rfl hle
        (F₂ (Opens.inclusion hWV y)).val)
    {t : ℝ} (ht : t ∈ Icc (H.time first) s) :
    (localPullMetric (G₁ t) F₁ hF₁).restrictOpenOfSubset hWU =
      (localPullMetric (G₂ t) F₂ hF₂).restrictOpenOfSubset hWV := by
  rw [H.backwardSurvivorIncomingMetric_eq_of_common_piecewise_flow first last hle G L G₁ G₂
    hslabs₁ hslabs₂ hlast₁ hlast₂ ht]
  apply localPullMetric_restrictOpenOfSubset_eq_of_comp_eq
  funext y
  apply Subtype.ext
  exact H.backwardSurvivorMap_injective first last hle first le_rfl hle (hbirth y)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {first next last : Fin (H.eventCount + 1)}
  {hfirst : first ≤ last} {hnext : next ≤ last} (hfn : first ≤ next)

variable {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)

def backwardSurvivorIncomingRestrictFirst :
    H.backwardSurvivorIncomingDomain first last hfirst G →
      H.backwardSurvivorIncomingDomain next last hnext G := fun x =>
  ⟨Opens.inclusion (H.backwardSurvivorDomain_mono_first hfn) x.val, x.property⟩

@[simp] theorem backwardSurvivorIncomingRestrictFirst_val
    (x : H.backwardSurvivorIncomingDomain first last hfirst G) :
    (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G x).val.val = x.val.val := rfl

@[simp] theorem backwardSurvivorIncomingMap_comp_restrictFirst :
    H.backwardSurvivorIncomingMap next last hnext G ∘
      H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G =
      H.backwardSurvivorIncomingMap first last hfirst G := rfl

theorem backwardSurvivorIncomingRestrictFirst_injective :
    Function.Injective (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.val.val) hxy

theorem backwardSurvivorIncomingRestrictFirst_contMDiff :
    ContMDiff ThreeModel ThreeModel ∞ (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G) := by
  apply (ContMDiff.subtypeVal_comp_iff
    (H.backwardSurvivorIncomingDomain next last hnext G) _).mp
  exact (contMDiff_inclusion (H.backwardSurvivorDomain_mono_first hfn)).comp
    contMDiff_subtype_val

theorem backwardSurvivorIncomingRestrictFirst_mfderiv
    (x : H.backwardSurvivorIncomingDomain first last hfirst G) :
    mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G) x =
      ContinuousLinearMap.id ℝ ThreeSpace := by
  rw [← mfderiv_subtypeVal_comp]
  change mfderiv ThreeModel ThreeModel
    (Opens.inclusion (H.backwardSurvivorDomain_mono_first hfn) ∘ Subtype.val) x = _
  rw [mfderiv_comp x
    ((contMDiff_inclusion (n := ∞) (H.backwardSurvivorDomain_mono_first hfn)).mdifferentiableAt
      (by decide))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by decide)),
    mfderiv_opens_incl, mfderiv_subtype_val]
  rfl

theorem backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (H.backwardSurvivorIncomingRestrictFirst_contMDiff (hfirst := hfirst) (hnext := hnext) hfn G) _ rfl
  intro x
  rw [H.backwardSurvivorIncomingRestrictFirst_mfderiv (hfirst := hfirst) (hnext := hnext) hfn G x]
  exact Function.injective_id

theorem localPullMetric_backwardSurvivorIncomingMetric_restrictFirst
    (L : G.TerminalLimitMetric) (t : ℝ) :
    localPullMetric (H.backwardSurvivorIncomingMetric next last hnext G L t)
      (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G)
      (H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph (hfirst := hfirst) (hnext := hnext) hfn G) =
      H.backwardSurvivorIncomingMetric first last hfirst G L t := by
  rw [backwardSurvivorIncomingMetric, localPullMetric_comp _ _ _ _ _
    (isLocalDiffeomorph_comp
      (H.backwardSurvivorIncomingMap_isLocalDiffeomorph next last hnext G)
      (H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
        (hfirst := hfirst) (hnext := hnext) hfn G))]
  rfl

theorem localPullMetric_backwardSurvivorSlabMetric_incoming_restrictFirst
    (j : Fin H.eventCount) (hj : next ≤ j.castSucc) (hl : j.succ ≤ last)
    (t : ℝ) :
    localPullMetric
      ((H.backwardSurvivorSlabMetric next last hnext j hj hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain next last hnext G))
      (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G)
      (H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
        (hfirst := hfirst) (hnext := hnext) hfn G) =
      (H.backwardSurvivorSlabMetric first last hfirst j (hfn.trans hj) hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hfirst G) := by
  let inc : H.backwardSurvivorDomain first last hfirst →
      H.backwardSurvivorDomain next last hnext :=
    Opens.inclusion (H.backwardSurvivorDomain_mono_first hfn)
  let rin : H.backwardSurvivorIncomingDomain first last hfirst G →
      H.backwardSurvivorIncomingDomain next last hnext G :=
    H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G
  have hrin : IsLocalDiffeomorph ThreeModel ThreeModel ∞ rin :=
    H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
      (hfirst := hfirst) (hnext := hnext) hfn G
  have hinc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc :=
    H.backwardSurvivorDomain_inclusion_isLocalDiffeomorph
      (hfirst := hfirst) (hnext := hnext) hfn
  have hcomp : IsLocalDiffeomorph ThreeModel ThreeModel ∞
      ((Subtype.val : H.backwardSurvivorIncomingDomain next last hnext G →
        H.backwardSurvivorDomain next last hnext) ∘ rin) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hrin
  rw [← localPullMetric_subtype_val
      (H.backwardSurvivorSlabMetric next last hnext j hj hl t)
      (H.backwardSurvivorIncomingDomain next last hnext G)]
  rw [localPullMetric_comp _ _ _ _ hrin hcomp]
  have hslab := H.localPullMetric_backwardSurvivorSlabMetric_restrictFirst
    (hfirst := hfirst) (hnext := hnext) hfn j hj hl t
  rw [← localPullMetric_subtype_val
      (H.backwardSurvivorSlabMetric first last hfirst j (hfn.trans hj) hl t)
      (H.backwardSurvivorIncomingDomain first last hfirst G)]
  rw [← hslab]
  rw [localPullMetric_comp _ _ _ _ (isLocalDiffeomorph_subtype_val _)
    (isLocalDiffeomorph_comp hinc (isLocalDiffeomorph_subtype_val _))]
  rfl

theorem backwardSurvivorMap_incoming_restrictFirst
    (j : Fin (H.eventCount + 1)) (hj : next ≤ j) (hl : j ≤ last)
    (x : H.backwardSurvivorIncomingDomain first last hfirst G) :
    H.backwardSurvivorMap next last hnext j hj hl
      (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G x).val =
      H.backwardSurvivorMap first last hfirst j (hfn.trans hj) hl x.val :=
  congrFun (H.backwardSurvivorMap_comp_inclusion_first hfn j hj hl) x.val

theorem localPullMetric_backwardSurvivorIncoming_restrictFirst_of_slab_eq
    (L : G.TerminalLimitMetric)
    (F : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hfirst G))
    (N : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain next last hnext G))
    (hFslabs : ∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        F t = (H.backwardSurvivorSlabMetric first last hfirst j hj hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hfirst G))
    (hNslabs : ∀ (j : Fin H.eventCount) (hj : next ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        N t = (H.backwardSurvivorSlabMetric next last hnext j hj hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain next last hnext G))
    (hFlast : ∀ t ∈ Icc (H.time last) s,
      F t = H.backwardSurvivorIncomingMetric first last hfirst G L t)
    (hNlast : ∀ t ∈ Icc (H.time last) s,
      N t = H.backwardSurvivorIncomingMetric next last hnext G L t)
    {t : ℝ} (ht : t ∈ Icc (H.time next) s) :
    localPullMetric (N t)
      (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G)
      (H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
        (hfirst := hfirst) (hnext := hnext) hfn G) = F t := by
  by_cases hlast : H.time last ≤ t
  · rw [hFlast t ⟨hlast, ht.2⟩, hNlast t ⟨hlast, ht.2⟩]
    exact H.localPullMetric_backwardSurvivorIncomingMetric_restrictFirst hfn G L t
  have hti : t < H.time last := lt_of_not_ge hlast
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg next).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
  let k := H.activeStage tH
  have hk : k < last := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt hti
  have hknext : next ≤ k := H.le_activeStage tH next ht.1
  let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
  have hjnext : j.succ ≤ last := by
    change k.val + 1 ≤ last.val
    exact hk
  have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
    ⟨H.activeStage_time_le tH,
      (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
  rw [hFslabs j (hfn.trans hknext) hjnext t htj, hNslabs j hknext hjnext t htj]
  exact H.localPullMetric_backwardSurvivorSlabMetric_incoming_restrictFirst hfn G j hknext hjnext t

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

section

set_option autoImplicit false

noncomputable section

open Set Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable {H : ObservedHistory.{u}} {first next last : Fin (H.eventCount + 1)}
  {hfirst : first ≤ last} {hnext : next ≤ last} (hfn : first ≤ next)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

variable {E XH : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  {M : Type*} [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]
  {U V W : Opens M}

variable
  (FLong : U → H.backwardSurvivorIncomingDomain first last hfirst G)
  (FShort : V → H.backwardSurvivorIncomingDomain next last hnext G)
  (hLong : IsLocalDiffeomorph I ThreeModel ∞ FLong)
  (hShort : IsLocalDiffeomorph I ThreeModel ∞ FShort)
  (hWU : W ≤ U) (hWV : W ≤ V)
  (hmap : H.backwardSurvivorIncomingMap first last hfirst G ∘ FLong ∘ Opens.inclusion hWU =
    H.backwardSurvivorIncomingMap next last hnext G ∘ FShort ∘ Opens.inclusion hWV)

include hfn hmap in
theorem localPullMetric_backwardSurvivorIncoming_overlap_of_terminal_eq
    (gLong : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hfirst G))
    (gShort : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain next last hnext G))
    (hLongSlabs : ∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc)
      (hl : j.succ ≤ last), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      gLong t = (H.backwardSurvivorSlabMetric first last hfirst j hj hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hfirst G))
    (hShortSlabs : ∀ (j : Fin H.eventCount) (hj : next ≤ j.castSucc)
      (hl : j.succ ≤ last), ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      gShort t = (H.backwardSurvivorSlabMetric next last hnext j hj hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain next last hnext G))
    (hLongLast : ∀ t ∈ Icc (H.time last) s,
      gLong t = H.backwardSurvivorIncomingMetric first last hfirst G L t)
    (hShortLast : ∀ t ∈ Icc (H.time last) s,
      gShort t = H.backwardSurvivorIncomingMetric next last hnext G L t)
    {t : ℝ} (ht : t ∈ Icc (H.time next) s) :
    (localPullMetric (gLong t) FLong hLong).restrictOpenOfSubset hWU =
      (localPullMetric (gShort t) FShort hShort).restrictOpenOfSubset hWV := by
  have hrestrict :
      H.backwardSurvivorIncomingRestrictFirst (first := first) (next := next)
        (last := last) (hfirst := hfirst) (hnext := hnext) hfn G ∘ FLong ∘
          Opens.inclusion hWU = FShort ∘ Opens.inclusion hWV := by
    funext y
    apply H.backwardSurvivorIncomingMap_injective next last hnext G
    exact congrFun hmap y
  have hFshortLocal : IsLocalDiffeomorph I ThreeModel ∞
      (H.backwardSurvivorIncomingRestrictFirst (first := first) (next := next)
        (last := last) (hfirst := hfirst) (hnext := hnext) hfn G ∘ FLong) :=
    isLocalDiffeomorph_comp
      (H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
        (first := first) (next := next) (last := last)
        (hfirst := hfirst) (hnext := hnext) hfn G) hLong
  have hfamily := H.localPullMetric_backwardSurvivorIncoming_restrictFirst_of_slab_eq
    (first := first) (next := next) (last := last) (hfirst := hfirst) (hnext := hnext)
    hfn G L gLong gShort hLongSlabs hShortSlabs hLongLast hShortLast ht
  rw [← hfamily]
  rw [localPullMetric_comp _ _ _ _ hLong hFshortLocal]
  exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq (gShort t) hWU hWV
    _ hFshortLocal FShort hShort hrestrict

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false

noncomputable section

open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable {H : ObservedHistory.{u}} {first next last : Fin (H.eventCount + 1)}
  {hfirst : first ≤ last} {hnext : next ≤ last} (hfn : first ≤ next)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
  (KLong KShort : Set G.terminalRegularOpen)
  {E XH M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]
  {U V W : Opens M} (hWU : W ≤ U) (hWV : W ≤ V)
  (FLong : U → H.backwardSurvivorIncomingFootprint first last hfirst G KLong)
  (FShort : V → H.backwardSurvivorIncomingFootprint next last hnext G KShort)
  (hLong : IsLocalDiffeomorph I ThreeModel ∞ FLong)
  (hShort : IsLocalDiffeomorph I ThreeModel ∞ FShort)
  (hmap : H.backwardSurvivorIncomingFootprintMap first last hfirst G KLong ∘
      FLong ∘ Opens.inclusion hWU =
    H.backwardSurvivorIncomingFootprintMap next last hnext G KShort ∘
      FShort ∘ Opens.inclusion hWV)

include hmap in
private theorem localPullMetric_footprint_overlap_of_restrictFirst_eq
    (gLong : SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hfirst G))
    (gShort : SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain next last hnext G))
    (hg : localPullMetric gShort
      (H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G)
      (H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
        (hfirst := hfirst) (hnext := hnext) hfn G) = gLong) :
    (localPullMetric (gLong.restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
      FLong hLong).restrictOpenOfSubset hWU =
    (localPullMetric (gShort.restrictOpen
        (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
      FShort hShort).restrictOpenOfSubset hWV := by
  let r := H.backwardSurvivorIncomingRestrictFirst (hfirst := hfirst) (hnext := hnext) hfn G
  have hr := H.backwardSurvivorIncomingRestrictFirst_isLocalDiffeomorph
    (hfirst := hfirst) (hnext := hnext) hfn G
  let f : U → H.backwardSurvivorIncomingDomain first last hfirst G := Subtype.val ∘ FLong
  let f' : V → H.backwardSurvivorIncomingDomain next last hnext G := Subtype.val ∘ FShort
  have hf : IsLocalDiffeomorph I ThreeModel ∞ f :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hLong
  have hf' : IsLocalDiffeomorph I ThreeModel ∞ f' :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hShort
  have hrf : IsLocalDiffeomorph I ThreeModel ∞ (r ∘ f) := isLocalDiffeomorph_comp hr hf
  have heq : (r ∘ f) ∘ Opens.inclusion hWU = f' ∘ Opens.inclusion hWV := by
    funext x
    apply H.backwardSurvivorIncomingMap_injective next last hnext G
    exact congrFun hmap x
  rw [← localPullMetric_subtype_val gLong
      (H.backwardSurvivorIncomingFootprint first last hfirst G KLong),
    ← localPullMetric_subtype_val gShort
      (H.backwardSurvivorIncomingFootprint next last hnext G KShort)]
  rw [localPullMetric_comp _ _ _ _ hLong hf,
    localPullMetric_comp _ _ _ _ hShort hf', ← hg,
    localPullMetric_comp _ _ _ hr hf hrf]
  exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq gShort hWU hWV
    (r ∘ f) hrf f' hf' heq

include hfn hmap in
theorem localPullMetric_backwardSurvivorIncomingFootprint_overlap_of_terminal_eq
    (L : G.TerminalLimitMetric)
    (gLong : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
    (gShort : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
    (hLongSlabs : ∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gLong t = ((H.backwardSurvivorSlabMetric first last hfirst j hj hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hfirst G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
    (hShortSlabs : ∀ (j : Fin H.eventCount) (hj : next ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gShort t = ((H.backwardSurvivorSlabMetric next last hnext j hj hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain next last hnext G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
    (hLongLast : ∀ t ∈ Icc (H.time last) s,
      gLong t = (H.backwardSurvivorIncomingMetric first last hfirst G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hfirst G KLong))
    (hShortLast : ∀ t ∈ Icc (H.time last) s,
      gShort t = (H.backwardSurvivorIncomingMetric next last hnext G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint next last hnext G KShort))
    {t : ℝ} (ht : t ∈ Icc (H.time next) s) :
    (localPullMetric (gLong t) FLong hLong).restrictOpenOfSubset hWU =
      (localPullMetric (gShort t) FShort hShort).restrictOpenOfSubset hWV := by
  by_cases hlast : H.time last ≤ t
  · rw [hLongLast t ⟨hlast, ht.2⟩, hShortLast t ⟨hlast, ht.2⟩]
    exact localPullMetric_footprint_overlap_of_restrictFirst_eq hfn G KLong KShort
      hWU hWV FLong FShort hLong hShort hmap _ _
      (H.localPullMetric_backwardSurvivorIncomingMetric_restrictFirst hfn G L t)
  have hti : t < H.time last := lt_of_not_ge hlast
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg next).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
  let k := H.activeStage tH
  have hk : k < last := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt hti
  have hknext : next ≤ k := H.le_activeStage tH next ht.1
  let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
  have hjnext : j.succ ≤ last := by
    change k.val + 1 ≤ last.val
    exact hk
  have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
    ⟨H.activeStage_time_le tH,
      (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
  rw [hLongSlabs j (hfn.trans hknext) hjnext t htj, hShortSlabs j hknext hjnext t htj]
  exact localPullMetric_footprint_overlap_of_restrictFirst_eq hfn G KLong KShort
    hWU hWV FLong FShort hLong hShort hmap _ _
    (H.localPullMetric_backwardSurvivorSlabMetric_incoming_restrictFirst
      hfn G j hknext hjnext t)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {XH : Type uH} [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  {M : Type uM}
  (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
  (hle : first ≤ last) {s : ℝ}
  (G : (H.stage last).IncomingSlab (H.time last) s)
  (K : Set G.terminalRegularOpen)
  (htrace : ∀ y ∈ K, Nonempty (BackwardPointTrace H first last hle y.val))

variable (F : M → G.terminalRegularOpen)
  (himage : ∀ z : M, F z ∈ interior K)

def backwardSurvivorIncomingFootprintLift :
    M → H.backwardSurvivorIncomingFootprint first last hle G K :=
  fun z => H.backwardSurvivorIncomingFootprintPoint first last hle G K htrace (F z) (himage z)

@[simp] theorem backwardSurvivorIncomingFootprintMap_lift :
    H.backwardSurvivorIncomingFootprintMap first last hle G K ∘
      H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage = F := rfl

@[simp] theorem backwardSurvivorIncomingFootprintMap_lift_apply (z : M) :
    H.backwardSurvivorIncomingFootprintMap first last hle G K
      (H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage z) = F z := rfl

theorem backwardSurvivorIncomingFootprintLift_injective
    (hF : Function.Injective F) :
    Function.Injective
      (H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage) := by
  intro x y hxy
  exact hF (congrArg (H.backwardSurvivorIncomingFootprintMap first last hle G K) hxy)

variable [TopologicalSpace M] [ChartedSpace XH M]

theorem backwardSurvivorIncomingFootprintLift_isLocalDiffeomorph
    (hF : IsLocalDiffeomorph I ThreeModel ∞ F) :
    IsLocalDiffeomorph I ThreeModel ∞
      (H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage) := by
  let Ψ := H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage
  have hcomp : H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Ψ = F := rfl
  have hp := H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K
  have he := hp.isLocalHomeomorph.isOpenEmbedding_of_injective
    (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
  have hc : Continuous Ψ :=
    he.isInducing.continuous_iff.mpr (hcomp ▸ hF.contMDiff.continuous)
  intro z
  apply DifferentialGeometry.isLocalDiffeomorphAt_of_comp_right hc.continuousAt (hp (Ψ z))
  simpa only [hcomp] using hF z

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

theorem localPullMetric_backwardSurvivorIncomingFootprintLift
    (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    (g : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen) :
    localPullMetric
      (localPullMetric g (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K))
      (H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage)
      (H.backwardSurvivorIncomingFootprintLift_isLocalDiffeomorph first last hle G K
        htrace F himage hF) = localPullMetric g F hF := by
  exact localPullMetric_comp g
    (H.backwardSurvivorIncomingFootprintMap first last hle G K)
    (H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage)
    (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)
    (H.backwardSurvivorIncomingFootprintLift_isLocalDiffeomorph first last hle G K
      htrace F himage hF) hF

theorem localPullMetric_backwardSurvivorIncomingFootprintLift_terminal
    (L : G.TerminalLimitMetric) (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hterminal : gflow s = localPullMetric L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)) :
    localPullMetric (gflow s)
      (H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F himage)
      (H.backwardSurvivorIncomingFootprintLift_isLocalDiffeomorph first last hle G K
        htrace F himage hF) = localPullMetric L.metric F hF := by
  rw [hterminal]
  exact H.localPullMetric_backwardSurvivorIncomingFootprintLift first last hle G K
    htrace F himage hF L.metric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end


noncomputable section
open Set Manifold Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {XH : Type uH} [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH} [I.Boundaryless]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]

private local instance (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
private local instance (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
private local instance (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

theorem exists_historical_localPullback_solution_from_incoming_slab
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen)
    (htrace : ∀ y ∈ K, Nonempty (BackwardPointTrace H first last hle y.val))
    (F : M → G.terminalRegularOpen) (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    (hinside : ∀ z : M, F z ∈ interior K)
    {Q θ : ℝ} (hQ : 0 < Q) (hθ : 0 ≤ θ) (hstart : H.time first ≤ s - θ / Q) :
    ∃ (Ψ : M → H.backwardSurvivorIncomingFootprint first last hle G K)
      (hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ)
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first last hle G K))
      (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ))),
      Ψ = H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F hinside ∧
      H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Ψ = F ∧
      IsSolutionOn S ∧ S.base.metric 0 = localPullMetric (scaleMetric Q hQ L.metric) F hF ∧
      (∀ t, S.base.metric t = localPullMetric (scaleMetric Q hQ (gflow (s + t / Q))) Ψ hΨ) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      gflow s = localPullMetric L.metric (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) := by
  obtain ⟨gflow, hslabs, hlast, hterminal, _, hsol⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_isSolutionOn first last hle G L hinit K
  let Ψ := H.backwardSurvivorIncomingFootprintLift first last hle G K htrace F hinside
  have hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ :=
    H.backwardSurvivorIncomingFootprintLift_isLocalDiffeomorph first last hle G K htrace F hinside hF
  let D := RealTimeInterval.closed (H.time first) s
    ((H.time_strictMono.monotone hle).trans G.lt.le)
  let T : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D := { base.metric := gflow }
  let U := T.parabolicClosedWindow s Q θ hQ hθ
  have hU : IsSolutionOn U := isSolutionOn_parabolicClosedWindow T hsol hQ hθ
    (fun t ht => ⟨hstart.trans ht.1, ht.2⟩)
    (fun t ht => ⟨hstart.trans_lt ht.1, ht.2⟩)
  let S := U.localPullback Ψ hΨ
  refine ⟨Ψ, hΨ, gflow, S, rfl, rfl, hU.localPullback Ψ hΨ, ?_, fun _ => rfl,
    hslabs, hlast, hterminal⟩
  change localPullMetric (scaleMetric Q hQ (gflow (s + 0 / Q))) Ψ hΨ = _
  rw [zero_div, add_zero, DifferentialGeometry.localPullMetric_scaleMetric]
  rw [H.localPullMetric_backwardSurvivorIncomingFootprintLift_terminal
    first last hle G K htrace F hinside L hF gflow hterminal]
  exact (DifferentialGeometry.localPullMetric_scaleMetric L.metric F hF Q hQ).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem localPullMetric_backwardSurvivorIncomingMetric_eq_stage_of_initial_eq
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (j i : Fin H.eventCount) (hfirst : first ≤ j.castSucc) (hle : first ≤ i.castSucc)
    (hji : j.castSucc ≤ i.castSucc) {τ t : ℝ}
    (G : (H.stage j.castSucc).IncomingSlab (H.time j.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (hsource : ∀ v, G.flow.base.metric v = (H.event j).incoming.flow.base.metric v)
    (hterminal : L.metric =
      ((H.event j).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    {E Y X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y}
    [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X] [T2Space X]
    (Ψ : X → H.backwardSurvivorIncomingDomain first j.castSucc hfirst G)
    (F : X → H.backwardSurvivorTerminalFace first i hle)
    (hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ)
    (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    (hbirth : ∀ x, H.backwardSurvivorMap first j.castSucc hfirst first le_rfl hfirst
      (Ψ x).val = H.backwardSurvivorMap first i.castSucc hle first le_rfl hle (F x).val)
    (ht : t ≤ τ) :
    localPullMetric (H.backwardSurvivorIncomingMetric first j.castSucc hfirst G L t) Ψ hΨ =
      localPullMetric ((H.event j).incoming.flow.base.metric t)
        ((H.backwardSurvivorMap first i.castSucc hle j.castSucc hfirst hji) ∘
          Subtype.val ∘ F)
        (isLocalDiffeomorph_comp
          (H.backwardSurvivorMap_isLocalDiffeomorph first i.castSucc hle j.castSucc hfirst hji)
          (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hF)) := by
  have hext : L.extendedMetric t =
      ((H.event j).incoming.flow.base.metric t).restrictOpen G.terminalRegularOpen := by
    rcases lt_or_eq_of_le ht with hlt | rfl
    · rw [L.extendedMetric_before hlt, hsource]
    · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal,
        hterminal]
  let f := (H.backwardSurvivorMap first i.castSucc hle j.castSucc hfirst hji) ∘
    Subtype.val ∘ F
  have he : (fun x => (Ψ x).val.val) = f := by
    funext x
    have h := H.backwardSurvivorMap_eq_of_initial_eq first j.castSucc i.castSucc hfirst hle
      (Ψ x).val (F x).val (hbirth x) j.castSucc hfirst le_rfl hji
    simpa only [H.backwardSurvivorMap_last, f, Function.comp_apply] using h
  have hd (x : X) : mfderiv I ThreeModel f x =
      mfderiv I ThreeModel Ψ x := by
    rw [← he]
    exact (mfderiv_subtypeVal_comp (fun y => (Ψ y).val) x).trans
      (mfderiv_subtypeVal_comp Ψ x)
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, H.backwardSurvivorIncomingMetric_inner, hext,
    localPullMetric_inner]
  change ((H.event j).incoming.flow.base.metric t).inner (Ψ x).val.val
      (mfderiv I ThreeModel Ψ x v) (mfderiv I ThreeModel Ψ x w) =
    ((H.event j).incoming.flow.base.metric t).inner (f x)
      (mfderiv I ThreeModel f x v) (mfderiv I ThreeModel f x w)
  rw [hd, congrFun he x]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
  (hle : first ≤ last)
  {E Y X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y}
  [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X] [T2Space X]

private theorem localPullMetric_slab_before
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (F : X → H.backwardSurvivorDomain first last hle)
    (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    {t : ℝ} (ht : t < H.time j.succ) :
    localPullMetric (H.backwardSurvivorSlabMetric first last hle j hf hl t) F hF =
      localPullMetric ((H.event j).incoming.flow.base.metric t)
        (H.backwardSurvivorMap first last hle j.castSucc hf (j.castSucc_lt_succ.le.trans hl) ∘ F)
        (isLocalDiffeomorph_comp
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.castSucc hf
            (j.castSucc_lt_succ.le.trans hl)) hF) := by
  unfold backwardSurvivorSlabMetric
  rw [(H.event j).terminal.extendedMetric_before ht,
    ← localPullMetric_subtype_val]
  rw [localPullMetric_comp _ _ _ _ _
    (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle j hf hl))]
  rw [localPullMetric_comp _ _ _ _ _
    (isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
        (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle j hf hl)) hF)]
  rfl

private theorem localPullMetric_terminalFace_before
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
    (F : X → H.backwardSurvivorTerminalFace first i hf)
    (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    {t : ℝ} (ht : t < H.time i.succ) :
    localPullMetric (H.backwardSurvivorTerminalFaceMetric first i hf t) F hF =
      localPullMetric ((H.event i).incoming.flow.base.metric t)
        (H.backwardSurvivorMap first i.castSucc hf i.castSucc hf le_rfl ∘ Subtype.val ∘ F)
        (isLocalDiffeomorph_comp
          (H.backwardSurvivorMap_isLocalDiffeomorph first i.castSucc hf i.castSucc hf le_rfl)
          (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hF)) := by
  rw [H.backwardSurvivorTerminalFaceMetric_before first i hf ht,
    ← localPullMetric_subtype_val, ← localPullMetric_subtype_val]
  rw [localPullMetric_comp _ _ _ _ _
    (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
      (isLocalDiffeomorph_subtype_val _))]
  rw [localPullMetric_comp _ _ _ _ _
    (isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
        (isLocalDiffeomorph_subtype_val _)) hF)]
  congr 1
  funext x
  exact (H.backwardSurvivorMap_last first i.castSucc hf (F x).val).symm

theorem localPullMetric_backwardSurvivorIncoming_eq_terminalFace_of_initial_eq
    (j i : Fin H.eventCount) (hfirst : first ≤ j.castSucc) (hi : first ≤ i.castSucc)
    (hji : j.castSucc ≤ i.castSucc) {τ : ℝ}
    (hτ : τ ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (G : (H.stage j.castSucc).IncomingSlab (H.time j.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (hsource : ∀ v, G.flow.base.metric v = (H.event j).incoming.flow.base.metric v)
    (hterminal : L.metric =
      ((H.event j).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (gflow₁ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first j.castSucc hfirst G))
    (gflow₂ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorTerminalFace first i hi))
    (hslabs₁ : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc)
      (hl : k.succ ≤ j.castSucc), ∀ t ∈ Icc (H.time k.castSucc) (H.time k.succ),
      gflow₁ t = (H.backwardSurvivorSlabMetric first j.castSucc hfirst k hf hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first j.castSucc hfirst G))
    (hslabs₂ : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc)
      (hl : k.succ ≤ i.castSucc), ∀ t ∈ Icc (H.time k.castSucc) (H.time k.succ),
      gflow₂ t = (H.backwardSurvivorSlabMetric first i.castSucc hi k hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hi))
    (hlast₁ : ∀ t ∈ Icc (H.time j.castSucc) τ,
      gflow₁ t = H.backwardSurvivorIncomingMetric first j.castSucc hfirst G L t)
    (hlast₂ : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      gflow₂ t = H.backwardSurvivorTerminalFaceMetric first i hi t)
    (Ψ : X → H.backwardSurvivorIncomingDomain first j.castSucc hfirst G)
    (Ξ : X → H.backwardSurvivorTerminalFace first i hi)
    (hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    (hbirth : ∀ x, H.backwardSurvivorMap first j.castSucc hfirst first le_rfl hfirst
      (Ψ x).val = H.backwardSurvivorMap first i.castSucc hi first le_rfl hi (Ξ x).val)
    {t : ℝ} (ht : t ∈ Icc (H.time first) τ) :
    localPullMetric (gflow₁ t) Ψ hΨ = localPullMetric (gflow₂ t) Ξ hΞ := by
  by_cases hlate : H.time j.castSucc ≤ t
  · rw [hlast₁ t ⟨hlate, ht.2⟩]
    rw [H.localPullMetric_backwardSurvivorIncomingMetric_eq_stage_of_initial_eq
      first j i hfirst hi hji G L hsource hterminal Ψ Ξ hΨ hΞ hbirth ht.2]
    have hbefore : t < H.time j.succ := ht.2.trans_lt hτ.2
    by_cases hji_eq : j = i
    · subst i
      rw [hlast₂ t ⟨hlate, hbefore.le⟩]
      exact (H.localPullMetric_terminalFace_before first j hfirst Ξ hΞ hbefore).symm
    · have hnext : j.succ ≤ i.castSucc := by
        have hne : j.val ≠ i.val := fun h => hji_eq (Fin.ext h)
        change j.val + 1 ≤ i.val
        have hleval : j.val ≤ i.val := hji
        omega
      rw [hslabs₂ j hfirst hnext t ⟨hlate, hbefore.le⟩,
        ← localPullMetric_subtype_val]
      rw [localPullMetric_comp _ _ _ _ _
        (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ)]
      exact (H.localPullMetric_slab_before first i.castSucc hi j hfirst hnext
        (Subtype.val ∘ Ξ) (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ)
        hbefore).symm
  · have hti : t < H.time j.castSucc := lt_of_not_ge hlate
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans ht.1,
        hti.le.trans (H.time_le_horizon_at j.castSucc)⟩
    let k := H.activeStage tH
    have hk : k < j.castSucc := by
      apply H.time_strictMono.lt_iff_lt.mp
      exact (H.activeStage_time_le tH).trans_lt hti
    have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
    let l : Fin H.eventCount := ⟨k.val, by
      have := j.isLt
      change k.val < H.eventCount
      have hkj : k.val < j.val := hk
      omega⟩
    have hlnext : l.succ ≤ j.castSucc := by
      change k.val + 1 ≤ j.val
      exact hk
    have htl : t ∈ Icc (H.time l.castSucc) (H.time l.succ) :=
      ⟨H.activeStage_time_le tH,
        (H.activeStage_before_next tH (show k.val < H.eventCount from l.isLt)).le⟩
    rw [hslabs₁ l hkfirst hlnext t htl, hslabs₂ l hkfirst (hlnext.trans hji) t htl,
      ← localPullMetric_subtype_val, ← localPullMetric_subtype_val]
    rw [localPullMetric_comp _ _ _ _ _
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΨ)]
    rw [localPullMetric_comp _ _ _ _ _
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ)]
    exact H.localPullMetric_backwardSurvivorSlabMetric_eq_of_initial_eq
      first j.castSucc i.castSucc hfirst hi (Subtype.val ∘ Ψ) (Subtype.val ∘ Ξ)
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΨ)
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ)
      hbirth l hkfirst hlnext (hlnext.trans hji) t

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {τ s : ℝ}
  (G₀ : (H.stage last).IncomingSlab (H.time last) τ) (L₀ : G₀.TerminalLimitMetric)
  (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  {E Y X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y}
  [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X] [T2Space X]

theorem localPullMetric_backwardSurvivorIncoming_flow_eq_of_source_eq
    (hτ : τ < s)
    (hsource : ∀ v, G₀.flow.base.metric v = G.flow.base.metric v)
    (hterminal : L₀.metric = (G.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G₀))
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs₀ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G₀))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast₀ : ∀ t ∈ Icc (H.time last) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first last hle G₀ L₀ t)
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (Ξ₀ : X → H.backwardSurvivorIncomingDomain first last hle G₀)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ₀ : IsLocalDiffeomorph I ThreeModel ∞ Ξ₀)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ₀ x).val =
      H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val)
    {t : ℝ} (ht : t ∈ Icc (H.time first) τ) :
    localPullMetric (gflow₀ t) Ξ₀ hΞ₀ = localPullMetric (gflow t) Ξ hΞ := by
  have he : (fun x => (Ξ₀ x).val) = fun x => (Ξ x).val := by
    funext x
    apply Subtype.ext
    have hh := H.backwardSurvivorMap_eq_of_initial_eq first last last hle hle
      (Ξ₀ x).val (Ξ x).val (hbirth x) last hle le_rfl le_rfl
    simpa only [H.backwardSurvivorMap_last] using hh
  have hd (x : X) : mfderiv I ThreeModel Ξ₀ x = mfderiv I ThreeModel Ξ x := by
    rw [← mfderiv_subtypeVal_comp Ξ₀ x, ← mfderiv_subtypeVal_comp Ξ x]
    rw [he]
  by_cases hlasttime : H.time last ≤ t
  · rw [hlast₀ t ⟨hlasttime, ht.2⟩, hlast t ⟨hlasttime, ht.2.trans hτ.le⟩]
    have hext : L₀.extendedMetric t =
        (G.flow.base.metric t).restrictOpen G₀.terminalRegularOpen := by
      rcases lt_or_eq_of_le ht.2 with hlt | rfl
      · rw [L₀.extendedMetric_before hlt, hsource]
      · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal,
          hterminal]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, localPullMetric_inner,
      H.backwardSurvivorIncomingMetric_inner, H.backwardSurvivorIncomingMetric_inner,
      hext, L.extendedMetric_before (ht.2.trans_lt hτ)]
    change (G.flow.base.metric t).inner (Ξ₀ x).val.val
        (mfderiv I ThreeModel Ξ₀ x v) (mfderiv I ThreeModel Ξ₀ x w) =
      (G.flow.base.metric t).inner (Ξ x).val.val
        (mfderiv I ThreeModel Ξ x v) (mfderiv I ThreeModel Ξ x w)
    rw [hd, congrFun he x]
    rfl
  · have hti : t < H.time last := lt_of_not_ge hlasttime
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans ht.1, hti.le.trans (H.time_le_horizon_at last)⟩
    let k := H.activeStage tH
    have hk : k < last := H.time_strictMono.lt_iff_lt.mp
      ((H.activeStage_time_le tH).trans_lt hti)
    have hf : first ≤ k := H.le_activeStage tH first ht.1
    let j : Fin H.eventCount := ⟨k.val, by
      have := last.isLt
      change k.val < H.eventCount
      omega⟩
    have hl : j.succ ≤ last := hk
    have htj : t ∈ Icc (H.time j.castSucc) (H.time j.succ) :=
      ⟨H.activeStage_time_le tH,
        (H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)).le⟩
    rw [hslabs₀ j hf hl t htj, hslabs j hf hl t htj]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, localPullMetric_inner]
    change (H.backwardSurvivorSlabMetric first last hle j hf hl t).inner (Ξ₀ x).val
        (mfderiv I ThreeModel Ξ₀ x v) (mfderiv I ThreeModel Ξ₀ x w) =
      (H.backwardSurvivorSlabMetric first last hle j hf hl t).inner (Ξ x).val
        (mfderiv I ThreeModel Ξ x v) (mfderiv I ThreeModel Ξ x w)
    rw [hd, congrFun he x]
    rfl


omit G₀ L₀ G L in
theorem localPullMetric_backwardSurvivorIncomingMetric_eq_slab_of_source_eq
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (G₀ : (H.stage j.castSucc).IncomingSlab (H.time j.castSucc) τ)
    (L₀ : G₀.TerminalLimitMetric)
    (hsource : ∀ v, G₀.flow.base.metric v = (H.event j).incoming.flow.base.metric v)
    (hterminal : L₀.metric =
      ((H.event j).incoming.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (Ξ₀ : X → H.backwardSurvivorIncomingDomain first j.castSucc hf G₀)
    (F : X → H.backwardSurvivorDomain first last hle)
    (hΞ₀ : IsLocalDiffeomorph I ThreeModel ∞ Ξ₀)
    (hF : IsLocalDiffeomorph I ThreeModel ∞ F)
    (hbirth : ∀ x, H.backwardSurvivorMap first j.castSucc hf first le_rfl hf (Ξ₀ x).val =
      H.backwardSurvivorMap first last hle first le_rfl hle (F x))
    {t : ℝ} (ht : t ≤ τ) (htj : t < H.time j.succ) :
    localPullMetric (H.backwardSurvivorIncomingMetric first j.castSucc hf G₀ L₀ t) Ξ₀ hΞ₀ =
      localPullMetric (H.backwardSurvivorSlabMetric first last hle j hf hl t) F hF := by
  have hext : L₀.extendedMetric t =
      ((H.event j).incoming.flow.base.metric t).restrictOpen G₀.terminalRegularOpen := by
    rcases lt_or_eq_of_le ht with hlt | rfl
    · rw [L₀.extendedMetric_before hlt, hsource]
    · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal,
        hterminal]
  let f := H.backwardSurvivorTerminalMap first last hle j hf hl ∘ F
  have hdiff : IsLocalDiffeomorph I ThreeModel ∞ f :=
    isLocalDiffeomorph_comp
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle j hf hl) hF
  have he : (fun x => (Ξ₀ x).val.val) = fun x => (f x).val := by
    funext x
    have hh := H.backwardSurvivorMap_eq_of_initial_eq first j.castSucc last hf hle
      (Ξ₀ x).val (F x) (hbirth x) j.castSucc hf le_rfl (j.castSucc_lt_succ.le.trans hl)
    simpa only [f, Function.comp_apply, H.backwardSurvivorMap_last,
      H.backwardSurvivorTerminalMap_val] using hh
  have hd (x : X) : mfderiv I ThreeModel Ξ₀ x = mfderiv I ThreeModel f x := by
    rw [← mfderiv_subtypeVal_comp Ξ₀ x,
      ← mfderiv_subtypeVal_comp (fun y => (Ξ₀ y).val) x,
      ← mfderiv_subtypeVal_comp f x, he]
  unfold backwardSurvivorSlabMetric
  rw [localPullMetric_comp _ _ F _ hF hdiff]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, H.backwardSurvivorIncomingMetric_inner,
    hext, localPullMetric_inner, (H.event j).terminal.extendedMetric_before htj]
  change ((H.event j).incoming.flow.base.metric t).inner (Ξ₀ x).val.val
      (mfderiv I ThreeModel Ξ₀ x v) (mfderiv I ThreeModel Ξ₀ x w) =
    ((H.event j).incoming.flow.base.metric t).inner (f x).val
      (mfderiv I ThreeModel f x v) (mfderiv I ThreeModel f x w)
  rw [hd, congrFun he x]
  rfl


omit G₀ L₀ L in
theorem localPullMetric_backwardSurvivorIncoming_flow_eq_of_earlier_source_eq
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (G₀ : (H.stage j.castSucc).IncomingSlab (H.time j.castSucc) τ)
    (L₀ : G₀.TerminalLimitMetric)
    (hsource : ∀ v, G₀.flow.base.metric v = (H.event j).incoming.flow.base.metric v)
    (hterminal : L₀.metric =
      ((H.event j).incoming.flow.base.metric τ).restrictOpen G₀.terminalRegularOpen)
    (hτ : τ < H.time j.succ)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first j.castSucc hf G₀))
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs₀ : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hil : i.succ ≤ j.castSucc),
      ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first j.castSucc hf i hi hil t).restrictOpen
          (H.backwardSurvivorIncomingDomain first j.castSucc hf G₀))
    (hslabs : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hil : i.succ ≤ last),
      ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle i hi hil t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast₀ : ∀ t ∈ Icc (H.time j.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first j.castSucc hf G₀ L₀ t)
    (Ξ₀ : X → H.backwardSurvivorIncomingDomain first j.castSucc hf G₀)
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ₀ : IsLocalDiffeomorph I ThreeModel ∞ Ξ₀)
    (hΞ : IsLocalDiffeomorph I ThreeModel ∞ Ξ)
    (hbirth : ∀ x, H.backwardSurvivorMap first j.castSucc hf first le_rfl hf (Ξ₀ x).val =
      H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val)
    {t : ℝ} (ht : t ∈ Icc (H.time first) τ) :
    localPullMetric (gflow₀ t) Ξ₀ hΞ₀ = localPullMetric (gflow t) Ξ hΞ := by
  let F : X → H.backwardSurvivorDomain first last hle := Subtype.val ∘ Ξ
  have hF : IsLocalDiffeomorph I ThreeModel ∞ F :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ
  have hrestrict (g : SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorDomain first last hle)) :
      localPullMetric (g.restrictOpen (H.backwardSurvivorIncomingDomain first last hle G)) Ξ hΞ =
        localPullMetric g F hF := by
    rw [← localPullMetric_subtype_val g _, localPullMetric_comp _ _ Ξ _ hΞ hF]
  by_cases hlasttime : H.time j.castSucc ≤ t
  · rw [hlast₀ t ⟨hlasttime, ht.2⟩, hslabs j hf hl t ⟨hlasttime, ht.2.trans hτ.le⟩,
      hrestrict]
    exact H.localPullMetric_backwardSurvivorIncomingMetric_eq_slab_of_source_eq
      first last hle j hf hl G₀ L₀ hsource hterminal Ξ₀ F hΞ₀ hF hbirth ht.2
      (ht.2.trans_lt hτ)
  · have hti : t < H.time j.castSucc := lt_of_not_ge hlasttime
    let tH : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg first).trans ht.1, hti.le.trans (H.time_le_horizon_at j.castSucc)⟩
    let k := H.activeStage tH
    have hk : k < j.castSucc := H.time_strictMono.lt_iff_lt.mp
      ((H.activeStage_time_le tH).trans_lt hti)
    have hfirst : first ≤ k := H.le_activeStage tH first ht.1
    let i : Fin H.eventCount := ⟨k.val, by
      have := j.isLt
      change k.val < H.eventCount
      have hkj : k.val < j.val := hk
      omega⟩
    have hi : i.succ ≤ j.castSucc := hk
    have hilast : i.succ ≤ last := hi.trans (j.castSucc_lt_succ.le.trans hl)
    have htime : t ∈ Icc (H.time i.castSucc) (H.time i.succ) :=
      ⟨H.activeStage_time_le tH,
        (H.activeStage_before_next tH (show k.val < H.eventCount from i.isLt)).le⟩
    rw [hslabs₀ i hfirst hi t htime, hslabs i hfirst hilast t htime, hrestrict]
    let F₀ : X → H.backwardSurvivorDomain first j.castSucc hf := Subtype.val ∘ Ξ₀
    have hF₀ : IsLocalDiffeomorph I ThreeModel ∞ F₀ :=
      isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ₀
    rw [← localPullMetric_subtype_val
      (H.backwardSurvivorSlabMetric first j.castSucc hf i hfirst hi t) _,
      localPullMetric_comp _ _ Ξ₀ _ hΞ₀ hF₀]
    exact H.localPullMetric_backwardSurvivorSlabMetric_eq_of_initial_eq first j.castSucc last hf hle
      F₀ F hF₀ hF hbirth i hfirst hi hilast t

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem metric_eq_stage_pullback_of_backwardSurvivorIncoming
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (F : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
        F t = (H.backwardSurvivorSlabMetric first last hle i hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Ico (H.time last) s,
      F t = H.backwardSurvivorIncomingMetric first last hle G L t)
    (hG : ∀ t ∈ Ico (H.time last) s, G.flow.base.metric t = H.stageMetric last t)
    (j : Fin (H.eventCount + 1)) (hfirstj : first ≤ j) (hjlast : j ≤ last) {t : ℝ}
    (ht : t ∈ H.stageDomain j) (hts : t < s) :
    F t = localPullMetric (H.stageMetric j t)
      (H.backwardSurvivorMap first last hle j hfirstj hjlast ∘ Subtype.val)
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hfirstj hjlast)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) := by
  let p := H.backwardSurvivorMap first last hle j hfirstj hjlast
  have hp := H.backwardSurvivorMap_isLocalDiffeomorph first last hle
    j hfirstj hjlast
  have hv := isLocalDiffeomorph_subtype_val (I := ThreeModel) (H.backwardSurvivorIncomingDomain first last hle G)
  have hleft : H.time j ≤ t := by
    cases j using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last, mem_Icc] at ht
      exact ht.1
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
      exact ht.1
  by_cases hj : j = last
  · have htime : t ∈ Ico (H.time last) s := ⟨hj ▸ hleft, hts⟩
    subst j
    rw [hlast t htime, H.backwardSurvivorIncomingMetric_before first last hle G L hts, hG t htime]
    have hpval : p = Subtype.val := by
      funext x
      exact H.backwardSurvivorMap_last first last hle x
    change ((H.stageMetric last t).restrictOpen (H.backwardSurvivorDomain first last hle)).restrictOpen
      (H.backwardSurvivorIncomingDomain first last hle G) =
      localPullMetric (H.stageMetric last t) (p ∘ Subtype.val) _
    rw [← localPullMetric_subtype_val, ← localPullMetric_subtype_val]
    simp only [hpval]
    exact localPullMetric_comp _ _ _ _ _ _
  · have hjlt : j < last := lt_of_le_of_ne hjlast hj
    cases j using Fin.lastCases with
    | last => exact False.elim ((not_lt_of_ge (Fin.le_last last)) hjlt)
    | cast i =>
      have hil : i.succ ≤ last := hjlt
      have htt : t ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using ht
      rw [hslabs i hfirstj hil t htt,
        ObservedHistory.backwardSurvivorSlabMetric,
        (H.event i).terminal.extendedMetric_before htt.2]
      have hinner :
          localPullMetric (((H.event i).incoming.flow.base.metric t).restrictOpen
            (H.event i).incoming.terminalRegularOpen)
            (H.backwardSurvivorTerminalMap first last hle i hfirstj hil)
            (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hfirstj hil) =
          localPullMetric ((H.event i).incoming.flow.base.metric t) p hp := by
        rw [← localPullMetric_subtype_val]
        exact localPullMetric_comp _ _ _ _ _ hp
      rw [hinner, ← localPullMetric_subtype_val]
      simpa only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] using
        (localPullMetric_comp ((H.event i).incoming.flow.base.metric t) p Subtype.val hp hv
          (isLocalDiffeomorph_comp hp hv))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
