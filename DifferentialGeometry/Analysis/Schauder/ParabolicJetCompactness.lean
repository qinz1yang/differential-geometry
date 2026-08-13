import DifferentialGeometry.Analysis.Schauder.HolderCompactness
import DifferentialGeometry.Analysis.Schauder.ParabolicJetLimit
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open Filter Set Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]

theorem exists_parabolic_jet_subseq_of_locally_holderOnWith
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    (uApprox dtimeUApprox : Nat → ParabolicPoint E → F)
    (duApprox : Nat → ParabolicPoint E → E →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint E → E →L[Real] E →L[Real] F)
    {r : NNReal} (hr : 0 < r)
    (huHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => uApprox n p) K)
    (hdtimeUHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => dtimeUApprox n p) K)
    (hduHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => duApprox n p) K)
    (hd2uHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => d2uApprox n p) K)
    (huBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖uApprox n p‖ ≤ M)
    (hdtimeUBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖dtimeUApprox n p‖ ≤ M)
    (hduBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖duApprox n p‖ ≤ M)
    (hd2uBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖d2uApprox n p‖ ≤ M)
    (hrealize : ∀ n, ParabolicJetRealizesOn Q
      (uApprox n) (dtimeUApprox n) (duApprox n) (d2uApprox n)) :
    ∃ (phi : Nat → Nat)
        (u dtimeU : ParabolicPoint E → F)
        (du : ParabolicPoint E → E →L[Real] F)
        (d2u : ParabolicPoint E → E →L[Real] E →L[Real] F),
      StrictMono phi ∧
        TendstoLocallyUniformlyOn (fun n => uApprox (phi n)) u atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => dtimeUApprox (phi n)) dtimeU atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => duApprox (phi n)) du atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => d2uApprox (phi n)) d2u atTop Q ∧
        ParabolicJetRealizesOn Q u dtimeU du d2u ∧
        IsParabolicC2On Q (fun t x => u (parabolicPoint t x)) := by
  classical
  letI : LocallyCompactSpace
      (Metric.Snowflaking Real (1 / 2) (by norm_num) (by norm_num)) :=
    Metric.Snowflaking.homeomorph.locallyCompactSpace_iff.mpr inferInstance
  letI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let jetApprox : Nat → Q →
      (F × F) × ((E →L[Real] F) × (E →L[Real] E →L[Real] F)) :=
    fun n p => ((uApprox n p, dtimeUApprox n p),
      (duApprox n p, d2uApprox n p))
  have hjetHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n, HolderOnWith C r (jetApprox n) K := by
    intro K hK
    rcases huHolder K hK with ⟨Cu, hu⟩
    rcases hdtimeUHolder K hK with ⟨Ct, ht⟩
    rcases hduHolder K hK with ⟨Cd, hd⟩
    rcases hd2uHolder K hK with ⟨Cd2, hd2⟩
    refine ⟨max (max Cu Ct) (max Cd Cd2), fun n => ?_⟩
    exact holderOnWith_prodMk
      (holderOnWith_prodMk (hu n) (ht n))
      (holderOnWith_prodMk (hd n) (hd2 n))
  have hjetBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖jetApprox n p‖ ≤ M := by
    intro p
    rcases huBound p with ⟨Mu, hu⟩
    rcases hdtimeUBound p with ⟨Mt, ht⟩
    rcases hduBound p with ⟨Md, hd⟩
    rcases hd2uBound p with ⟨Md2, hd2⟩
    refine ⟨max (max Mu Mt) (max Md Md2), fun n => ?_⟩
    change max (max ‖uApprox n p‖ ‖dtimeUApprox n p‖)
      (max ‖duApprox n p‖ ‖d2uApprox n p‖) ≤
        max (max Mu Mt) (max Md Md2)
    exact max_le
      ((max_le
        ((hu n).trans (le_max_left Mu Mt))
        ((ht n).trans (le_max_right Mu Mt))).trans
          (le_max_left (max Mu Mt) (max Md Md2)))
      ((max_le
        ((hd n).trans (le_max_left Md Md2))
        ((hd2 n).trans (le_max_right Md Md2))).trans
          (le_max_right (max Mu Mt) (max Md Md2)))
  rcases arzela_ascoli_subseq_tendsto_locally_uniformly_of_locally_holderOnWith
      jetApprox hr hjetHolder hjetBound with ⟨phi, g, hphi, hg, hgunif⟩
  have hgloc : TendstoLocallyUniformly (fun n => jetApprox (phi n)) g atTop := by
    intro V hV p
    rcases exists_compact_mem_nhds p with ⟨K, hK, hKmem⟩
    exact ⟨K, hKmem, hgunif K hK V hV⟩
  have hleft : TendstoLocallyUniformly
      (fun n p => (jetApprox (phi n) p).1) (fun p => (g p).1) atTop := by
    simpa only [Function.comp_apply] using
      uniformContinuous_fst.comp_tendstoLocallyUniformly hgloc
  have hright : TendstoLocallyUniformly
      (fun n p => (jetApprox (phi n) p).2) (fun p => (g p).2) atTop := by
    simpa only [Function.comp_apply] using
      uniformContinuous_snd.comp_tendstoLocallyUniformly hgloc
  have huSub : TendstoLocallyUniformly
      (fun n p => (jetApprox (phi n) p).1.1) (fun p => (g p).1.1) atTop := by
    simpa only [Function.comp_apply] using
      uniformContinuous_fst.comp_tendstoLocallyUniformly hleft
  have hdtimeUSub : TendstoLocallyUniformly
      (fun n p => (jetApprox (phi n) p).1.2) (fun p => (g p).1.2) atTop := by
    simpa only [Function.comp_apply] using
      uniformContinuous_snd.comp_tendstoLocallyUniformly hleft
  have hduSub : TendstoLocallyUniformly
      (fun n p => (jetApprox (phi n) p).2.1) (fun p => (g p).2.1) atTop := by
    simpa only [Function.comp_apply] using
      uniformContinuous_fst.comp_tendstoLocallyUniformly hright
  have hd2uSub : TendstoLocallyUniformly
      (fun n p => (jetApprox (phi n) p).2.2) (fun p => (g p).2.2) atTop := by
    simpa only [Function.comp_apply] using
      uniformContinuous_snd.comp_tendstoLocallyUniformly hright
  let u : ParabolicPoint E → F := fun p =>
    if hp : p ∈ Q then (g ⟨p, hp⟩).1.1 else 0
  let dtimeU : ParabolicPoint E → F := fun p =>
    if hp : p ∈ Q then (g ⟨p, hp⟩).1.2 else 0
  let du : ParabolicPoint E → E →L[Real] F := fun p =>
    if hp : p ∈ Q then (g ⟨p, hp⟩).2.1 else 0
  let d2u : ParabolicPoint E → E →L[Real] E →L[Real] F := fun p =>
    if hp : p ∈ Q then (g ⟨p, hp⟩).2.2 else 0
  have hu : TendstoLocallyUniformlyOn
      (fun n => uApprox (phi n)) u atTop Q := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have heq : u ∘ ((↑) : Q → ParabolicPoint E) = fun p => (g p).1.1 := by
      funext p
      simp only [u, Function.comp_apply, dif_pos p.2]
    rw [heq]
    simpa only [jetApprox] using huSub
  have hdtimeU : TendstoLocallyUniformlyOn
      (fun n => dtimeUApprox (phi n)) dtimeU atTop Q := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have heq : dtimeU ∘ ((↑) : Q → ParabolicPoint E) = fun p => (g p).1.2 := by
      funext p
      simp only [dtimeU, Function.comp_apply, dif_pos p.2]
    rw [heq]
    simpa only [jetApprox] using hdtimeUSub
  have hdu : TendstoLocallyUniformlyOn
      (fun n => duApprox (phi n)) du atTop Q := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have heq : du ∘ ((↑) : Q → ParabolicPoint E) = fun p => (g p).2.1 := by
      funext p
      simp only [du, Function.comp_apply, dif_pos p.2]
    rw [heq]
    simpa only [jetApprox] using hduSub
  have hd2u : TendstoLocallyUniformlyOn
      (fun n => d2uApprox (phi n)) d2u atTop Q := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have heq : d2u ∘ ((↑) : Q → ParabolicPoint E) = fun p => (g p).2.2 := by
      funext p
      simp only [d2u, Function.comp_apply, dif_pos p.2]
    rw [heq]
    simpa only [jetApprox] using hd2uSub
  have hd2uContinuous : ContinuousOn d2u Q := by
    rw [continuousOn_iff_continuous_restrict]
    have hproj : Continuous (fun p : Q => (g p).2.2) :=
      continuous_snd.comp (continuous_snd.comp hg)
    have heq : Q.restrict d2u = fun p => (g p).2.2 := by
      funext p
      simp only [restrict_apply, d2u, dif_pos p.2]
    rw [heq]
    exact hproj
  have hlimit : ParabolicJetRealizesOn Q u dtimeU du d2u :=
    parabolic_jet_realizes_on_of_tendsto_locally_uniformly_on hQ
      hu hdtimeU hdu hd2u (fun n => hrealize (phi n))
  exact ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
    hlimit, hlimit.isParabolicC2On hQ hd2uContinuous⟩

theorem exists_parabolic_jet_subseq_with_locally_holderOnWith
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    (uApprox dtimeUApprox : Nat → ParabolicPoint E → F)
    (duApprox : Nat → ParabolicPoint E → E →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint E → E →L[Real] E →L[Real] F)
    {r : NNReal} (hr : 0 < r)
    (huHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => uApprox n p) K)
    (hdtimeUHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => dtimeUApprox n p) K)
    (hduHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => duApprox n p) K)
    (hd2uHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun p : Q => d2uApprox n p) K)
    (huBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖uApprox n p‖ ≤ M)
    (hdtimeUBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖dtimeUApprox n p‖ ≤ M)
    (hduBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖duApprox n p‖ ≤ M)
    (hd2uBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖d2uApprox n p‖ ≤ M)
    (hrealize : ∀ n, ParabolicJetRealizesOn Q
      (uApprox n) (dtimeUApprox n) (duApprox n) (d2uApprox n)) :
    ∃ (phi : Nat → Nat)
        (u dtimeU : ParabolicPoint E → F)
        (du : ParabolicPoint E → E →L[Real] F)
        (d2u : ParabolicPoint E → E →L[Real] E →L[Real] F),
      StrictMono phi ∧
        TendstoLocallyUniformlyOn (fun n => uApprox (phi n)) u atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => dtimeUApprox (phi n)) dtimeU atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => duApprox (phi n)) du atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => d2uApprox (phi n)) d2u atTop Q ∧
        ParabolicJetRealizesOn Q u dtimeU du d2u ∧
        IsParabolicC2On Q (fun t x => u (parabolicPoint t x)) ∧
        ∀ K : Set Q, IsCompact K →
          ∃ Cu Ct Cd Cd2 : NNReal,
            HolderOnWith Cu r (fun p : Q => u p) K ∧
            HolderOnWith Ct r (fun p : Q => dtimeU p) K ∧
            HolderOnWith Cd r (fun p : Q => du p) K ∧
            HolderOnWith Cd2 r (fun p : Q => d2u p) K := by
  rcases exists_parabolic_jet_subseq_of_locally_holderOnWith hQ
      uApprox dtimeUApprox duApprox d2uApprox hr
      huHolder hdtimeUHolder hduHolder hd2uHolder
      huBound hdtimeUBound hduBound hd2uBound hrealize with
    ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
      hlimit, hclassical⟩
  refine ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
    hlimit, hclassical, ?_⟩
  intro K hK
  rcases huHolder K hK with ⟨Cu, hCu⟩
  rcases hdtimeUHolder K hK with ⟨Ct, hCt⟩
  rcases hduHolder K hK with ⟨Cd, hCd⟩
  rcases hd2uHolder K hK with ⟨Cd2, hCd2⟩
  exact ⟨Cu, Ct, Cd, Cd2,
    holderOnWith_of_tendsto (Eventually.of_forall fun n => hCu (phi n))
      (fun p _ => hu.tendsto_at p.2),
    holderOnWith_of_tendsto (Eventually.of_forall fun n => hCt (phi n))
      (fun p _ => hdtimeU.tendsto_at p.2),
    holderOnWith_of_tendsto (Eventually.of_forall fun n => hCd (phi n))
      (fun p _ => hdu.tendsto_at p.2),
    holderOnWith_of_tendsto (Eventually.of_forall fun n => hCd2 (phi n))
      (fun p _ => hd2u.tendsto_at p.2)⟩

theorem exists_parabolic_jet_subseq_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    (uApprox dtimeUApprox : Nat → ParabolicPoint E → F)
    (duApprox : Nat → ParabolicPoint E → E →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint E → E →L[Real] E →L[Real] F)
    {r : NNReal} (hr : 0 < r) (C : NNReal)
    (hgauge : ∀ n, eParabolicC2HolderGaugeWithLowerJetsOn r Q
      (fun t x ↦ uApprox n (parabolicPoint t x)) ≤ C)
    (hrealize : ∀ n, ParabolicJetRealizesOn Q
      (uApprox n) (dtimeUApprox n) (duApprox n) (d2uApprox n)) :
    ∃ (phi : Nat → Nat)
        (u dtimeU : ParabolicPoint E → F)
        (du : ParabolicPoint E → E →L[Real] F)
        (d2u : ParabolicPoint E → E →L[Real] E →L[Real] F),
      StrictMono phi ∧
        TendstoLocallyUniformlyOn (fun n => uApprox (phi n)) u atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => dtimeUApprox (phi n)) dtimeU atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => duApprox (phi n)) du atTop Q ∧
        TendstoLocallyUniformlyOn (fun n => d2uApprox (phi n)) d2u atTop Q ∧
        ParabolicJetRealizesOn Q u dtimeU du d2u ∧
        IsParabolicC2On Q (fun t x => u (parabolicPoint t x)) ∧
        ∀ K : Set Q, IsCompact K →
          ∃ Cu Ct Cd Cd2 : NNReal,
            HolderOnWith Cu r (fun p : Q => u p) K ∧
            HolderOnWith Ct r (fun p : Q => dtimeU p) K ∧
            HolderOnWith Cd r (fun p : Q => du p) K ∧
            HolderOnWith Cd2 r (fun p : Q => d2u p) K := by
  have hbase : ∀ n, eParabolicC2HolderGaugeOn r Q
      (fun t x ↦ uApprox n (parabolicPoint t x)) ≤ C := by
    intro n
    exact (eParabolicC2HolderGaugeOn_le_with_lower_jets r Q _).trans (hgauge n)
  have huHolder : ∀ K : Set Q, IsCompact K →
      ∃ C' : NNReal, ∀ n,
        HolderOnWith C' r (fun p : Q => uApprox n p) K := by
    intro K _
    refine ⟨C, fun n => ?_⟩
    have hholder := parabolicValue_holderWith_restrict_of_lower_jets (hgauge n)
    simpa only [parabolicPoint_time_space] using hholder.holderOnWith K
  have hdtimeUHolder : ∀ K : Set Q, IsCompact K →
      ∃ C' : NNReal, ∀ n,
        HolderOnWith C' r (fun p : Q => dtimeUApprox n p) K := by
    intro K _
    exact ⟨C, fun n =>
      ((hrealize n).holderWith_restrict_timeDerivative_of_lower_jets_gauge
        (hgauge n)).holderOnWith K⟩
  have hduHolder : ∀ K : Set Q, IsCompact K →
      ∃ C' : NNReal, ∀ n,
        HolderOnWith C' r (fun p : Q => duApprox n p) K := by
    intro K _
    exact ⟨C, fun n =>
      ((hrealize n).holderWith_restrict_spatialDerivative_of_lower_jets_gauge
        (hgauge n)).holderOnWith K⟩
  have hd2uHolder : ∀ K : Set Q, IsCompact K →
      ∃ C' : NNReal, ∀ n,
        HolderOnWith C' r (fun p : Q => d2uApprox n p) K := by
    intro K _
    exact ⟨C, fun n =>
      ((hrealize n).holderWith_restrict_spatialSecondDerivative_of_lower_jets_gauge
        hQ (hgauge n)).holderOnWith K⟩
  have huBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖uApprox n p‖ ≤ M := by
    intro p
    refine ⟨C, fun n => ?_⟩
    have hzero := parabolicSpatialJet_norm_le (hbase n) (j := 0) (by norm_num) p.2
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero,
      parabolicPoint_time_space] using hzero
  have hdtimeUBound : ∀ p : Q, ∃ M : Real,
      ∀ n, ‖dtimeUApprox n p‖ ≤ M := by
    intro p
    exact ⟨C, fun n =>
      (hrealize n).norm_timeDerivative_le_of_lower_jets_gauge (hgauge n) p.2⟩
  have hduBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖duApprox n p‖ ≤ M := by
    intro p
    exact ⟨C, fun n =>
      (hrealize n).norm_spatialDerivative_le_of_lower_jets_gauge (hgauge n) p.2⟩
  have hd2uBound : ∀ p : Q, ∃ M : Real, ∀ n, ‖d2uApprox n p‖ ≤ M := by
    intro p
    exact ⟨C, fun n =>
      (hrealize n).norm_spatialSecondDerivative_le_of_lower_jets_gauge
        hQ (hgauge n) p.2⟩
  exact exists_parabolic_jet_subseq_with_locally_holderOnWith hQ
    uApprox dtimeUApprox duApprox d2uApprox hr
    huHolder hdtimeUHolder hduHolder hd2uHolder
    huBound hdtimeUBound hduBound hd2uBound hrealize

end DifferentialGeometry.Analysis.Schauder

end
