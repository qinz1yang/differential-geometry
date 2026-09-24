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
      rw [if_pos htc]
      exact congrArg (fun g => g.restrictOpen W) (hslabs j hf hl t ht)
    · intro t ht
      dsimp only
      by_cases htc : t ≤ H.time last
      · have he : t = H.time last := le_antisymm htc ht.1
        subst t
        rw [if_pos le_rfl]
        exact hmatch
      · rw [if_neg htc]
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
