import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.FiniteGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Curvature.LocalPullbackRicci
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
private local instance (i : Fin H.eventCount) :
    SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

theorem backwardSurvivorTerminalMap_isLocalDiffeomorph
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (H.backwardSurvivorTerminalMap first last hle i hf hl) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (H.backwardSurvivorTerminalMap_isSmoothEmbedding first last hle i hf hl).contMDiff
    (fun x => by
      have hi :=
        (H.backwardSurvivorTerminalMap_isSmoothEmbedding first last hle i hf hl).isImmersion
      exact (hi.isImmersionAt x).mfderiv_injective (by simp)) rfl

def backwardSurvivorSlabMetric
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) (t : ℝ) :
    SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first last hle) :=
  localPullMetric ((H.event i).terminal.extendedMetric t)
    (H.backwardSurvivorTerminalMap first last hle i hf hl)
    (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hf hl)

@[simp] theorem backwardSurvivorSlabMetric_inner
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) (t : ℝ)
    (x : H.backwardSurvivorDomain first last hle) (v w : TangentSpace ThreeModel x) :
    (H.backwardSurvivorSlabMetric first last hle i hf hl t).inner x v w =
      ((H.event i).terminal.extendedMetric t).inner
        (H.backwardSurvivorTerminalMap first last hle i hf hl x)
        (mfderiv ThreeModel ThreeModel
          (H.backwardSurvivorTerminalMap first last hle i hf hl) x v)
        (mfderiv ThreeModel ThreeModel
          (H.backwardSurvivorTerminalMap first last hle i hf hl) x w) :=
  localPullMetric_inner _ _ _ _ _ _

theorem backwardSurvivorSlabMetric_jointContMDiffOn
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × H.backwardSurvivorDomain first last hle =>
        (⟨q.2, (H.backwardSurvivorSlabMetric first last hle i hf hl q.1).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ]
              TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Icc (H.time i.castSucc) (H.time i.succ) ×ˢ univ) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (H.backwardSurvivorSlabMetric first last hle i hf hl) _
  intro p j k
  apply chartGramMatrix_joint_contMDiffOn_of_pullback (H.event i).terminal.extendedMetric _
    ((H.event i).terminal.extendedMetric_jointContMDiffOn le_rfl (H.event i).incoming.lt)
    (H.backwardSurvivorSlabMetric first last hle i hf hl)
    (H.backwardSurvivorTerminalMap first last hle i hf hl)
    (H.backwardSurvivorTerminalMap_isSmoothEmbedding first last hle i hf hl).contMDiff
  intro t ht x v w
  exact H.backwardSurvivorSlabMetric_inner first last hle i hf hl t x v w

theorem backwardSurvivorSlabMetric_hasDerivAt
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {t : ℝ} (ht : t ∈ Ioo (H.time i.castSucc) (H.time i.succ))
    (x : H.backwardSurvivorDomain first last hle) (v w : TangentSpace ThreeModel x) :
    HasDerivAt (fun u => (H.backwardSurvivorSlabMetric first last hle i hf hl u).inner x v w)
      (-2 * ricciTensor (H.backwardSurvivorSlabMetric first last hle i hf hl t) x v w) t := by
  have hd := (H.event i).terminal.extendedMetric_hasDerivAt ht
    (H.backwardSurvivorTerminalMap first last hle i hf hl x)
    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalMap first last hle i hf hl) x v)
    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalMap first last hle i hf hl) x w)
  dsimp only [backwardSurvivorSlabMetric]
  rw [ricciTensor_localPullMetric]
  simpa only [localPullMetric_inner] using hd

def backwardSurvivorInitialMetric
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first last hle) :=
  localPullMetric (H.initialMetric j) (H.backwardSurvivorMap first last hle j hj hl)
    (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hj hl)

theorem backwardSurvivorInitialMetric_last :
    H.backwardSurvivorInitialMetric first last hle last hle le_rfl =
      (H.initialMetric last).restrictOpen (H.backwardSurvivorDomain first last hle) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  dsimp only [backwardSurvivorInitialMetric]
  rw [localPullMetric_inner]
  have he : H.backwardSurvivorMap first last hle last hle le_rfl = Subtype.val := by
    funext y
    exact H.backwardSurvivorMap_last first last hle y
  rw [he, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  rfl

theorem backwardSurvivorSlabMetric_initial
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    H.backwardSurvivorSlabMetric first last hle i hf hl (H.time i.castSucc) =
      H.backwardSurvivorInitialMetric first last hle i.castSucc hf
        (i.castSucc_lt_succ.le.trans hl) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorSlabMetric_inner,
    (H.event i).terminal.extendedMetric_before (H.event i).incoming.lt,
    SmoothRiemannianMetric.restrictOpen_inner, H.event_initial i]
  dsimp only [backwardSurvivorInitialMetric]
  rw [localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (H.backwardSurvivorTerminalMap first last hle i hf hl) x
  change mfderiv ThreeModel ThreeModel
      (H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) x =
      mfderiv ThreeModel ThreeModel
        (H.backwardSurvivorTerminalMap first last hle i hf hl) x at hd
  rw [hd]
  rfl

theorem backwardSurvivorSlabMetric_terminal
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    H.backwardSurvivorSlabMetric first last hle i hf hl (H.time i.succ) =
      H.backwardSurvivorInitialMetric first last hle i.succ
        (hf.trans i.castSucc_lt_succ.le) hl := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorSlabMetric_inner,
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
  exact (H.backwardSurvivorMap_metric_crossing first last hle i hf hl x v w).symm

def backwardSurvivorClosedSlab
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle)
      (RealTimeInterval.closed (H.time i.castSucc) (H.time i.succ)
        (H.time_strictMono i.castSucc_lt_succ).le) where
  base := { metric := H.backwardSurvivorSlabMetric first last hle i hf hl }

theorem backwardSurvivorClosedSlab_isSolutionOn
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    IsSolutionOn (H.backwardSurvivorClosedSlab first last hle i hf hl) := by
  apply isSolutionOn_of_joint_metric _
    (uniqueDiffOn_Icc (H.time_strictMono i.castSucc_lt_succ))
    (H.backwardSurvivorSlabMetric first last hle i hf hl)
    (H.backwardSurvivorSlabMetric_jointContMDiffOn first last hle i hf hl)
  intro t ht x v w
  exact (H.backwardSurvivorSlabMetric_hasDerivAt first last hle i hf hl ht x v w).hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hlt : first < last)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first last hlt.le) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorDomain first last hlt.le).isOpen)

theorem exists_backwardSurvivor_isSolutionOn :
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first last hlt.le),
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
          G t = H.backwardSurvivorSlabMetric first last hlt.le i hf hl t) ∧
      (∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last),
        G (H.time j) = H.backwardSurvivorInitialMetric first last hlt.le j hj hl) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × H.backwardSurvivorDomain first last hlt.le =>
          (⟨q.2, (G q.1).inner q.2⟩ : TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) (H.time last) ×ˢ univ) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hlt.le)
          (RealTimeInterval.closed (H.time first) (H.time last)
            (H.time_strictMono hlt).le)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, last.val = first.val + n + 1 := by
    exact ⟨last.val - first.val - 1, by omega⟩
  let stageIndex (j : Fin (n + 2)) : Fin (H.eventCount + 1) :=
    ⟨first.val + j.val, by have := j.isLt; have := last.isLt; omega⟩
  let eventIndex (j : Fin (n + 1)) : Fin H.eventCount :=
    ⟨first.val + j.val, by have := j.isLt; have := last.isLt; omega⟩
  have hfirst (j : Fin (n + 1)) : first ≤ (eventIndex j).castSucc := by
    change first.val ≤ first.val + j.val
    omega
  have hlast (j : Fin (n + 1)) : (eventIndex j).succ ≤ last := by
    change first.val + j.val + 1 ≤ last.val
    have := j.isLt
    omega
  have hstage (j : Fin (n + 1)) : stageIndex j.castSucc = (eventIndex j).castSucc := rfl
  have hsucc (j : Fin (n + 1)) : stageIndex j.succ = (eventIndex j).succ := by
    apply Fin.ext
    simp only [stageIndex, eventIndex, Fin.val_succ]
    omega
  have hstart : stageIndex 0 = first := by apply Fin.ext; simp [stageIndex]
  have hend : stageIndex (Fin.last (n + 1)) = last := by
    apply Fin.ext
    simp only [stageIndex, Fin.val_last]
    omega
  have hmono : StrictMono (fun j => H.time (stageIndex j)) := by
    apply H.time_strictMono.comp
    intro j k hjk
    change first.val + j.val < first.val + k.val
    exact Nat.add_lt_add_left hjk _
  let g (j : Fin (n + 1)) :=
    H.backwardSurvivorSlabMetric first last hlt.le (eventIndex j) (hfirst j) (hlast j)
  have hsmooth (j : Fin (n + 1)) :=
    H.backwardSurvivorSlabMetric_jointContMDiffOn first last hlt.le
      (eventIndex j) (hfirst j) (hlast j)
  have hpde (j : Fin (n + 1)) (t : ℝ) :=
    H.backwardSurvivorSlabMetric_hasDerivAt first last hlt.le
      (eventIndex j) (hfirst j) (hlast j) (t := t)
  have hmatch (j : Fin n) :
      g j.castSucc (H.time (stageIndex j.succ.castSucc)) =
        g j.succ (H.time (stageIndex j.succ.castSucc)) := by
    have he : (eventIndex j.castSucc).succ = (eventIndex j.succ).castSucc := by
      apply Fin.ext
      simp only [eventIndex, Fin.val_succ, Fin.val_castSucc]
      omega
    change H.backwardSurvivorSlabMetric _ _ _ _ _ _ _ =
      H.backwardSurvivorSlabMetric _ _ _ _ _ _ _
    rw [hstage, ← he, H.backwardSurvivorSlabMetric_terminal]
    simpa only [he] using
      (H.backwardSurvivorSlabMetric_initial first last hlt.le
        (eventIndex j.succ) (hfirst j.succ) (hlast j.succ)).symm
  obtain ⟨G, heq, hsm, hsol⟩ := exists_isSolutionOn_finite_gluing n
    (fun j => H.time (stageIndex j)) hmono g
    (fun j => by simpa only [hstage, hsucc] using hsmooth j)
    (fun j t ht x v w => hpde j t (by simpa only [hstage, hsucc] using ht) x v w) hmatch
  have hslabs : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = H.backwardSurvivorSlabMetric first last hlt.le i hf hl t := by
    intro i hf hl t ht
    let j : Fin (n + 1) := ⟨i.val - first.val, by
      have hfi : first.val ≤ i.val := hf
      have hil : i.val + 1 ≤ last.val := hl
      omega⟩
    have he : eventIndex j = i := by
      apply Fin.ext
      change first.val + (i.val - first.val) = i.val
      have hfi : first.val ≤ i.val := hf
      omega
    have hx := heq j t
    apply (by simpa only [g, hstage, hsucc, he] using hx)
    exact ht
  refine ⟨G, hslabs, ?_, ?_, ?_⟩
  · intro j hj hl
    by_cases he : j = last
    · subst j
      have hg := heq (Fin.last n) (H.time last)
      have hs : stageIndex (Fin.last n).succ = last := by
        apply Fin.ext
        simp only [stageIndex, Fin.val_succ, Fin.val_last]
        omega
      have ht : H.time last ∈
          Icc (H.time (stageIndex (Fin.last n).castSucc))
            (H.time (stageIndex (Fin.last n).succ)) := by
        rw [hs]
        exact ⟨H.time_strictMono.monotone
          ((eventIndex (Fin.last n)).castSucc_lt_succ.le.trans (hlast _)), le_rfl⟩
      have hterm := H.backwardSurvivorSlabMetric_terminal first last hlt.le
        (eventIndex (Fin.last n)) (hfirst (Fin.last n)) (hlast (Fin.last n))
      have hs' : (eventIndex (Fin.last n)).succ = last := (hsucc _).symm.trans hs
      simpa only [g, hs'] using (hg ht).trans (by simpa only [hs'] using hterm)
    · have hjl : j < last := lt_of_le_of_ne hl he
      let i : Fin H.eventCount := ⟨j.val, by have := last.isLt; omega⟩
      have hi : i.castSucc = j := rfl
      have his : i.succ ≤ last := by change j.val + 1 ≤ last.val; exact hjl
      exact (hslabs i hj his (H.time j)
        ⟨le_rfl, (H.time_strictMono i.castSucc_lt_succ).le⟩).trans
          (H.backwardSurvivorSlabMetric_initial first last hlt.le i hj his)
  · simpa only [hstart, hend] using hsm
  · apply isSolutionOn_timeRestrict hsol
    · change Icc _ _ ⊆ Icc _ _
      simp only [hstart, hend, Set.Subset.rfl]
    · change Ioo _ _ ⊆ Ioo _ _
      simp only [hstart, hend, Set.Subset.rfl]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorDomain first i.castSucc hle).isOpen)

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

def backwardSurvivorTerminalFace : Opens (H.backwardSurvivorDomain first i.castSucc hle) :=
  ⟨Subtype.val ⁻¹' (H.event i).incoming.terminalRegularOpen,
    (H.event i).incoming.terminalRegularOpen.isOpen.preimage continuous_subtype_val⟩

private local instance : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorTerminalFace first i hle).isOpen)

def backwardSurvivorTerminalFaceMap :
    H.backwardSurvivorTerminalFace first i hle → (H.event i).incoming.terminalRegularOpen :=
  fun x => ⟨x.val.val, x.property⟩

@[simp] theorem backwardSurvivorTerminalFaceMap_val
    (x : H.backwardSurvivorTerminalFace first i hle) :
    (H.backwardSurvivorTerminalFaceMap first i hle x).val = x.val.val := rfl

theorem backwardSurvivorTerminalFaceMap_contMDiff :
    ContMDiff ThreeModel ThreeModel ∞ (H.backwardSurvivorTerminalFaceMap first i hle) := by
  apply (ContMDiff.subtypeVal_comp_iff (H.event i).incoming.terminalRegularOpen _).mp
  change ContMDiff ThreeModel ThreeModel ∞
    (fun x : H.backwardSurvivorTerminalFace first i hle => x.val.val)
  exact contMDiff_subtype_val.comp contMDiff_subtype_val

theorem backwardSurvivorTerminalFaceMap_mfderiv
    (x : H.backwardSurvivorTerminalFace first i hle) :
    mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalFaceMap first i hle) x =
      ContinuousLinearMap.id ℝ ThreeSpace := by
  have h₁ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (H.backwardSurvivorTerminalFaceMap first i hle) x
  have h₂ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (Subtype.val : H.backwardSurvivorTerminalFace first i hle →
      H.backwardSurvivorDomain first i.castSucc hle) x
  exact h₁.symm.trans (h₂.trans (DifferentialGeometry.mfderiv_subtype_val _ x))

theorem backwardSurvivorTerminalFaceMap_injective :
    Function.Injective (H.backwardSurvivorTerminalFaceMap first i hle) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (H.event i).incoming.terminalRegularOpen => z.val) hxy

theorem backwardSurvivorTerminalFaceMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (H.backwardSurvivorTerminalFaceMap first i hle) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (H.backwardSurvivorTerminalFaceMap_contMDiff first i hle) _ rfl
  intro x
  rw [H.backwardSurvivorTerminalFaceMap_mfderiv first i hle x]
  exact Function.injective_id

def backwardSurvivorTerminalFaceMetric (t : ℝ) :
    SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle) :=
  localPullMetric ((H.event i).terminal.extendedMetric t)
    (H.backwardSurvivorTerminalFaceMap first i hle)
    (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hle)

@[simp] theorem backwardSurvivorTerminalFaceMetric_inner
    (t : ℝ) (x : H.backwardSurvivorTerminalFace first i hle)
    (v w : TangentSpace ThreeModel x) :
    (H.backwardSurvivorTerminalFaceMetric first i hle t).inner x v w =
      ((H.event i).terminal.extendedMetric t).inner
        (H.backwardSurvivorTerminalFaceMap first i hle x) v w := by
  rw [backwardSurvivorTerminalFaceMetric, localPullMetric_inner,
    H.backwardSurvivorTerminalFaceMap_mfderiv first i hle x]
  rfl

theorem backwardSurvivorTerminalFaceMetric_jointContMDiffOn :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × H.backwardSurvivorTerminalFace first i hle =>
        (⟨q.2, (H.backwardSurvivorTerminalFaceMetric first i hle q.1).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ]
              TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Icc (H.time i.castSucc) (H.time i.succ) ×ˢ univ) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (H.backwardSurvivorTerminalFaceMetric first i hle) _
  intro p j k
  apply chartGramMatrix_joint_contMDiffOn_of_pullback (H.event i).terminal.extendedMetric _
    ((H.event i).terminal.extendedMetric_jointContMDiffOn le_rfl (H.event i).incoming.lt)
    (H.backwardSurvivorTerminalFaceMetric first i hle)
    (H.backwardSurvivorTerminalFaceMap first i hle)
    (H.backwardSurvivorTerminalFaceMap_contMDiff first i hle)
  intro t ht x v w
  exact localPullMetric_inner _ _ _ _ _ _

theorem backwardSurvivorTerminalFaceMetric_hasDerivAt
    {t : ℝ} (ht : t ∈ Ioo (H.time i.castSucc) (H.time i.succ))
    (x : H.backwardSurvivorTerminalFace first i hle) (v w : TangentSpace ThreeModel x) :
    HasDerivAt (fun u => (H.backwardSurvivorTerminalFaceMetric first i hle u).inner x v w)
      (-2 * ricciTensor (H.backwardSurvivorTerminalFaceMetric first i hle t) x v w) t := by
  have hd := (H.event i).terminal.extendedMetric_hasDerivAt ht
    (H.backwardSurvivorTerminalFaceMap first i hle x)
    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalFaceMap first i hle) x v)
    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalFaceMap first i hle) x w)
  dsimp only [backwardSurvivorTerminalFaceMetric]
  rw [ricciTensor_localPullMetric]
  simpa only [localPullMetric_inner] using hd

theorem backwardSurvivorTerminalFaceMetric_before
    {t : ℝ} (ht : t < H.time i.succ) :
    H.backwardSurvivorTerminalFaceMetric first i hle t =
      (((H.event i).incoming.flow.base.metric t).restrictOpen
        (H.backwardSurvivorDomain first i.castSucc hle)).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorTerminalFaceMetric_inner,
    (H.event i).terminal.extendedMetric_before ht]
  rfl

theorem backwardSurvivorTerminalFaceMetric_initial :
    H.backwardSurvivorTerminalFaceMetric first i hle (H.time i.castSucc) =
      (H.backwardSurvivorInitialMetric first i.castSucc hle i.castSucc hle le_rfl).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorTerminalFaceMetric_inner,
    (H.event i).terminal.extendedMetric_before (H.event i).incoming.lt]
  change ((H.event i).incoming.flow.base.metric (H.time i.castSucc)).inner x.val.val v w =
    (H.backwardSurvivorInitialMetric first i.castSucc hle i.castSucc hle le_rfl).inner x.val v w
  rw [H.event_initial i]
  dsimp only [backwardSurvivorInitialMetric]
  erw [localPullMetric_inner]
  have hmap : H.backwardSurvivorMap first i.castSucc hle i.castSucc hle le_rfl =
      (Subtype.val : H.backwardSurvivorDomain first i.castSucc hle →
        (H.stage i.castSucc).Carrier) :=
    funext (H.backwardSurvivorMap_last first i.castSucc hle)
  rw [hmap, DifferentialGeometry.mfderiv_subtype_val]
  rfl

theorem backwardSurvivorTerminalFaceMetric_terminal :
    H.backwardSurvivorTerminalFaceMetric first i hle (H.time i.succ) =
      localPullMetric (H.event i).terminal.metric
        (H.backwardSurvivorTerminalFaceMap first i hle)
        (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hle) := by
  rw [backwardSurvivorTerminalFaceMetric,
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]

def backwardSurvivorTerminalFaceClosedSlab :
    SolutionOn (I := ThreeModel) (M := H.backwardSurvivorTerminalFace first i hle)
      (RealTimeInterval.closed (H.time i.castSucc) (H.time i.succ)
        (H.time_strictMono i.castSucc_lt_succ).le) where
  base := { metric := H.backwardSurvivorTerminalFaceMetric first i hle }

theorem backwardSurvivorTerminalFaceClosedSlab_isSolutionOn :
    IsSolutionOn (H.backwardSurvivorTerminalFaceClosedSlab first i hle) := by
  apply isSolutionOn_of_joint_metric _
    (uniqueDiffOn_Icc (H.time_strictMono i.castSucc_lt_succ))
    (H.backwardSurvivorTerminalFaceMetric first i hle)
    (H.backwardSurvivorTerminalFaceMetric_jointContMDiffOn first i hle)
  intro t ht x v w
  exact (H.backwardSurvivorTerminalFaceMetric_hasDerivAt first i hle ht x v w).hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
private local instance : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorTerminalFace first i hle).isOpen)

theorem mem_range_backwardSurvivorTerminalFaceMap_iff
    (x : (H.event i).incoming.terminalRegularOpen) :
    x ∈ range (H.backwardSurvivorTerminalFaceMap first i hle) ↔
      Nonempty (BackwardPointTrace H first i.castSucc hle x.val) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.property
  · intro h
    exact ⟨⟨⟨x.val, h⟩, x.property⟩, rfl⟩

theorem exists_backwardSurvivorTerminal_isSolutionOn :
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = H.backwardSurvivorTerminalFaceMetric first i hle t) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × H.backwardSurvivorTerminalFace first i hle =>
          (⟨q.2, (G q.1).inner q.2⟩ : TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) (H.time i.succ) ×ˢ univ) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorTerminalFace first i hle)
          (RealTimeInterval.closed (H.time first) (H.time i.succ)
            (H.time_strictMono.monotone (hle.trans i.castSucc_lt_succ.le)))) := by
  rcases eq_or_lt_of_le hle with he | hlt
  · subst first
    refine ⟨H.backwardSurvivorTerminalFaceMetric i.castSucc i le_rfl, ?_, ?_,
      H.backwardSurvivorTerminalFaceMetric_jointContMDiffOn i.castSucc i le_rfl,
      H.backwardSurvivorTerminalFaceClosedSlab_isSolutionOn i.castSucc i le_rfl⟩
    · intro j hf hl t ht
      have hfj : i.val ≤ j.val := hf
      have hji : j.val + 1 ≤ i.val := hl
      omega
    · intro t ht
      rfl
  · obtain ⟨F, hslabs, hstages, hsm, hsol⟩ :=
      H.exists_backwardSurvivor_isSolutionOn first i.castSucc hlt
    let W := H.backwardSurvivorTerminalFace first i hle
    let gL := fun t => (F t).restrictOpen W
    let gR := H.backwardSurvivorTerminalFaceMetric first i hle
    have ha : H.time first < H.time i.castSucc := H.time_strictMono hlt
    have hb : H.time i.castSucc < H.time i.succ := H.time_strictMono i.castSucc_lt_succ
    have hL : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × W => (⟨q.2, (gL q.1).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) (H.time i.castSucc) ×ˢ univ) := by
      apply metricCLMSection_jointContMDiffOn_of_chartGram_on gL _
      intro p j k
      apply chartGramMatrix_joint_contMDiffOn_of_pullback F _ hsm gL
        Subtype.val contMDiff_subtype_val
      intro t ht x v w
      simp only [gL, SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
    have hpdeL : ∀ t ∈ Ioo (H.time first) (H.time i.castSucc),
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
    have hmatch : gL (H.time i.castSucc) = gR (H.time i.castSucc) := by
      dsimp only [gL, gR]
      rw [hstages i.castSucc hle le_rfl, H.backwardSurvivorTerminalFaceMetric_initial]
    have hR := H.backwardSurvivorTerminalFaceMetric_jointContMDiffOn first i hle
    have hpdeR := fun t ht x v w =>
      H.backwardSurvivorTerminalFaceMetric_hasDerivAt first i hle (t := t) ht x v w
    refine ⟨fun t => if t ≤ H.time i.castSucc then gL t else gR t, ?_, ?_, ?_, ?_⟩
    · intro j hf hl t ht
      have htc : t ≤ H.time i.castSucc := ht.2.trans (H.time_strictMono.monotone hl)
      dsimp only
      rw [ite_eq_left htc]
      exact congrArg (fun g => g.restrictOpen W) (hslabs j hf hl t ht)
    · intro t ht
      dsimp only
      by_cases htc : t ≤ H.time i.castSucc
      · have he : t = H.time i.castSucc := le_antisymm htc ht.1
        subst t
        rw [ite_eq_left le_rfl]
        exact hmatch
      · rw [ite_eq_right htc]
    · exact metricCLMSection_jointContMDiffOn_ite_of_ricciFlow gL gR ha hb
        hL hR hpdeL hpdeR hmatch
    · exact isSolutionOn_ite_of_ricciFlow gL gR ha hb hL hR hpdeL hpdeR hmatch

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end


noncomputable section
open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last₁ last₂ : Fin (H.eventCount + 1))
  (h₁ : first ≤ last₁) (h₂ : first ≤ last₂)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y}
  {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace Y X] [IsManifold I ∞ X]

theorem localPullMetric_backwardSurvivorSlabMetric_eq_of_initial_eq
    (F₁ : X → H.backwardSurvivorDomain first last₁ h₁)
    (F₂ : X → H.backwardSurvivorDomain first last₂ h₂)
    (hF₁ : IsLocalDiffeomorph I ThreeModel ∞ F₁)
    (hF₂ : IsLocalDiffeomorph I ThreeModel ∞ F₂)
    (hfirst : ∀ x, H.backwardSurvivorMap first last₁ h₁ first le_rfl h₁ (F₁ x) =
      H.backwardSurvivorMap first last₂ h₂ first le_rfl h₂ (F₂ x))
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
    (hj₁ : j.succ ≤ last₁) (hj₂ : j.succ ≤ last₂) (t : ℝ) :
    localPullMetric (H.backwardSurvivorSlabMetric first last₁ h₁ j hf hj₁ t) F₁ hF₁ =
      localPullMetric (H.backwardSurvivorSlabMetric first last₂ h₂ j hf hj₂ t) F₂ hF₂ := by
  unfold backwardSurvivorSlabMetric
  rw [DifferentialGeometry.localPullMetric_comp, DifferentialGeometry.localPullMetric_comp]
  · congr 1
    funext x
    apply Subtype.ext
    exact H.backwardSurvivorMap_eq_of_initial_eq first last₁ last₂ h₁ h₂
      (F₁ x) (F₂ x) (hfirst x) j.castSucc hf
      (j.castSucc_lt_succ.le.trans hj₁) (j.castSucc_lt_succ.le.trans hj₂)
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last₂ h₂ j hf hj₂) hF₂
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last₁ h₁ j hf hj₁) hF₁

theorem localPullMetric_backwardSurvivorTerminalFaceMetric_eq_slab_of_initial_eq
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last₂)
    (F₁ : X → H.backwardSurvivorTerminalFace first i hf)
    (F₂ : X → H.backwardSurvivorDomain first last₂ h₂)
    (hF₁ : IsLocalDiffeomorph I ThreeModel ∞ F₁)
    (hF₂ : IsLocalDiffeomorph I ThreeModel ∞ F₂)
    (hfirst : ∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (F₁ x).val =
      H.backwardSurvivorMap first last₂ h₂ first le_rfl h₂ (F₂ x)) (t : ℝ) :
    localPullMetric (H.backwardSurvivorTerminalFaceMetric first i hf t) F₁ hF₁ =
      localPullMetric (H.backwardSurvivorSlabMetric first last₂ h₂ i hf hl t) F₂ hF₂ := by
  unfold backwardSurvivorTerminalFaceMetric backwardSurvivorSlabMetric
  rw [DifferentialGeometry.localPullMetric_comp, DifferentialGeometry.localPullMetric_comp]
  · congr 1
    funext x
    apply Subtype.ext
    have he := H.backwardSurvivorMap_eq_of_initial_eq first i.castSucc last₂ hf h₂
      (F₁ x).val (F₂ x) (hfirst x) i.castSucc hf le_rfl (i.castSucc_lt_succ.le.trans hl)
    simpa only [Function.comp_apply, H.backwardSurvivorTerminalFaceMap_val,
      H.backwardSurvivorTerminalMap_val, H.backwardSurvivorMap_last] using he
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last₂ h₂ i hf hl) hF₂
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf) hF₁


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end


noncomputable section

open Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) {first next last : Fin (H.eventCount + 1)}
  {hfirst : first ≤ last} {hnext : next ≤ last} (hfn : first ≤ next)

theorem localPullMetric_backwardSurvivorSlabMetric_restrictFirst
    (j : Fin H.eventCount) (hj : next ≤ j.castSucc) (hl : j.succ ≤ last)
    (t : ℝ) :
    localPullMetric (H.backwardSurvivorSlabMetric next last hnext j hj hl t)
      (Opens.inclusion (H.backwardSurvivorDomain_mono_first hfn))
      (H.backwardSurvivorDomain_inclusion_isLocalDiffeomorph
        (hfirst := hfirst) (hnext := hnext) hfn) =
      H.backwardSurvivorSlabMetric first last hfirst j (hfn.trans hj) hl t := by
  rw [backwardSurvivorSlabMetric, localPullMetric_comp _ _ _ _ _
    (isLocalDiffeomorph_comp
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph next last hnext j hj hl)
      (H.backwardSurvivorDomain_inclusion_isLocalDiffeomorph
        (hfirst := hfirst) (hnext := hnext) hfn))]
  have heq := H.backwardSurvivorTerminalMap_comp_inclusion_first
    (hfirst := hfirst) (hnext := hnext) hfn j hj hl
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [localPullMetric_inner, backwardSurvivorSlabMetric_inner]
  rw [heq]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
