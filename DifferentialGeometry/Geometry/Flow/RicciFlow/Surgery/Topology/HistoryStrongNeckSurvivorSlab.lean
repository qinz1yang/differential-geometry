import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Seam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first k : Fin (H.eventCount + 1)) (hle : first ≤ k)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first k hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first k hle).isOpen)

theorem exists_backwardSurvivor_incomingSlab_flow {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s)
    (hinit : G.flow.base.metric (H.time k) = H.initialMetric k) :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ k),
        ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow τ = H.backwardSurvivorSlabMetric first k hle j hf hl τ) ∧
      (∀ τ ∈ Ico (H.time k) s,
        gflow τ = (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hle)) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
          (RealTimeInterval.closedOpen (H.time first) s
            ((H.time_strictMono.monotone hle).trans_lt G.lt))) := by
  rcases eq_or_lt_of_le hle with he | hlt
  · subst he
    refine ⟨fun τ => (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first first hle),
      ?_, fun _ _ => rfl, ?_⟩
    · intro j hf hl
      exact absurd (hl.trans hf) (not_le.mpr j.castSucc_lt_succ)
    · exact DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen G.flow
        G.equation _
  obtain ⟨F, hslabs, hstages, hsm, hsol⟩ := H.exists_backwardSurvivor_isSolutionOn first k hlt
  let gR : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hlt.le) :=
    fun τ => (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hlt.le)
  have ha : H.time first < H.time k := H.time_strictMono hlt
  have hb : H.time k < s := G.lt
  have hR : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × H.backwardSurvivorDomain first k hlt.le => (⟨q.2, (gR q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Ico (H.time k) s ×ˢ univ) :=
    G.smoothUpTo.restrictOpen_jointContMDiffOn (H.backwardSurvivorDomain first k hlt.le)
  have hpdeL : ∀ τ ∈ Ioo (H.time first) (H.time k), ∀ x : H.backwardSurvivorDomain first k hlt.le,
      ∀ v w : TangentSpace ThreeModel x,
      HasDerivAt (fun σ => (F σ).inner x v w) (-2 * ricciTensor (F τ) x v w) τ := by
    intro τ hτ x v w
    have hd := (hsol.equation ⟨τ, hτ⟩ x v w).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    change HasDerivAt (fun σ => (F σ).inner x v w) (-2 * metricRicciAt (F τ) x (vec2 v w)) τ at hd
    erw [metricRicciAt_apply_eq_ricciTensor (F τ) x v w] at hd
    exact hd
  have hpdeR : ∀ τ ∈ Ioo (H.time k) s, ∀ x : H.backwardSurvivorDomain first k hlt.le,
      ∀ v w : TangentSpace ThreeModel x,
      HasDerivAt (fun σ => (gR σ).inner x v w) (-2 * ricciTensor (gR τ) x v w) τ := by
    intro τ hτ x v w
    have hd := (G.equation.equation ⟨τ, hτ⟩ x.val v w).hasDerivAt (Ico_mem_nhds hτ.1 hτ.2)
    change HasDerivAt (fun σ => (G.flow.base.metric σ).inner x.val v w)
      (-2 * metricRicciAt (G.flow.base.metric τ) x.val (vec2 v w)) τ at hd
    erw [metricRicciAt_apply_eq_ricciTensor (G.flow.base.metric τ) x.val v w] at hd
    dsimp only [gR]
    rw [Geometry.Curvature.ricciTensor_restrictOpen]
    simpa only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply] using hd
  have hmatch : F (H.time k) = gR (H.time k) := by
    rw [hstages k hlt.le le_rfl, H.backwardSurvivorInitialMetric_last]
    dsimp only [gR]
    rw [hinit]
  have hjoint : ∀ b' : ℝ, H.time k < b' → b' < s →
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × H.backwardSurvivorDomain first k hlt.le =>
          (⟨q.2, ((if q.1 ≤ H.time k then F q.1 else gR q.1)).inner q.2⟩ :
          TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
            (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (Icc (H.time first) b' ×ˢ univ) := fun b' hb'1 hb'2 =>
    metricCLMSection_jointContMDiffOn_ite_of_ricciFlow F gR ha hb'1 hsm
      (hR.mono (prod_mono (Icc_subset_Ico_right hb'2) subset_rfl)) hpdeL
      (fun τ hτ => hpdeR τ ⟨hτ.1, hτ.2.trans hb'2⟩) hmatch
  refine ⟨fun τ => if τ ≤ H.time k then F τ else gR τ, ?_, ?_, ?_⟩
  · intro j hf hl τ hτ
    have hτk : τ ≤ H.time k := hτ.2.trans (H.time_strictMono.monotone hl)
    simp only [ite_eq_left hτk]
    exact hslabs j hf hl τ hτ
  · intro τ hτ
    by_cases hc : τ ≤ H.time k
    · have he : τ = H.time k := le_antisymm hc hτ.1
      subst he
      simp only [ite_eq_left le_rfl]
      exact hmatch
    · simp only [ite_eq_right hc]
      rfl
  · apply isSolutionOn_of_joint_metric _ (uniqueDiffOn_Ico _ _)
    · intro p hp
      obtain ⟨b', hb'1, hb'2⟩ : ∃ b', max p.1 (H.time k) < b' ∧ b' < s :=
        exists_between (max_lt hp.1.2 hb)
      refine (hjoint b' ((le_max_right _ _).trans_lt hb'1) hb'2 p
        ⟨⟨hp.1.1, ((le_max_left _ _).trans_lt hb'1).le⟩, hp.2⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.mpr ⟨Iio b' ×ˢ univ, isOpen_Iio.prod isOpen_univ,
        ⟨(le_max_left _ _).trans_lt hb'1, mem_univ _⟩, ?_⟩
      rintro q ⟨⟨hq1, -⟩, hq2, -⟩
      exact ⟨⟨hq2.1, hq1.le⟩, mem_univ _⟩
    · intro τ hτ x v w
      obtain ⟨b', hb'1, hb'2⟩ : ∃ b', max τ (H.time k) < b' ∧ b' < s :=
        exists_between (max_lt hτ.2 hb)
      exact (metric_inner_hasDerivAt_ite_of_ricciFlow F gR ha ((le_max_right _ _).trans_lt hb'1)
        hsm (hR.mono (prod_mono (Icc_subset_Ico_right hb'2) subset_rfl)) hpdeL
        (fun τ' hτ' => hpdeR τ' ⟨hτ'.1, hτ'.2.trans hb'2⟩) hmatch
        ⟨hτ.1, (le_max_left _ _).trans_lt hb'1⟩ x v w).hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
