import DifferentialGeometry.Analysis.Schauder.Holder
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Schauder

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

def ParabolicJetRealizesOn
    (Q : Set (ParabolicPoint E))
    (u dtimeU : ParabolicPoint E → F)
    (du : ParabolicPoint E → E →L[Real] F)
    (d2u : ParabolicPoint E → E →L[Real] E →L[Real] F) : Prop :=
  (∀ p ∈ Q, HasDerivAt (fun t ↦ u (parabolicPoint t p.space)) (dtimeU p) p.time) ∧
    (∀ p ∈ Q, HasFDerivAt (fun x ↦ u (parabolicPoint p.time x)) (du p) p.space) ∧
    ∀ p ∈ Q,
      HasFDerivAt (fun x ↦ du (parabolicPoint p.time x)) (d2u p) p.space

namespace ParabolicJetRealizesOn

theorem hasDerivAt_time
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    HasDerivAt (fun t ↦ u (parabolicPoint t p.space)) (dtimeU p) p.time :=
  h.1 p hp

theorem hasFDerivAt_space
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    HasFDerivAt (fun x ↦ u (parabolicPoint p.time x)) (du p) p.space :=
  h.2.1 p hp

theorem hasFDerivAt_gradient
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    HasFDerivAt (fun x ↦ du (parabolicPoint p.time x)) (d2u p) p.space :=
  h.2.2 p hp

theorem parabolicTimeDerivative_eq
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    parabolicTimeDerivative
        (fun t x ↦ u (parabolicPoint t x)) p = dtimeU p := by
  unfold parabolicTimeDerivative
  rw [(h.hasDerivAt_time hp).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

theorem continuousMultilinearCurryFin1_parabolicSpatialJet_one_eq
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    continuousMultilinearCurryFin1 Real E F
        (parabolicSpatialJet 1
          (fun t x ↦ u (parabolicPoint t x)) p) = du p := by
  ext v
  simp only [parabolicSpatialJet, continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply]
  rw [(h.hasFDerivAt_space hp).fderiv]
  rfl

theorem hessianCurryEquiv_parabolicSpatialJet_two_eq
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint E} (hp : p ∈ Q) :
    hessianCurryEquiv E F
        (parabolicSpatialJet 2
          (fun t x ↦ u (parabolicPoint t x)) p) = d2u p := by
  let spaceSlice : E → ParabolicPoint E := fun x ↦ parabolicPoint p.time x
  let spaceDomain : Set E := spaceSlice ⁻¹' Q
  have hspaceSlice : Continuous spaceSlice := by
    simpa only [spaceSlice, parabolicPoint] using
      (continuous_const : Continuous
        (fun _ : E ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
  have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
  have hpSpace : p.space ∈ spaceDomain := by
    change parabolicPoint p.time p.space ∈ Q
    simpa only [parabolicPoint_time_space] using hp
  have hgradient : fderiv Real (fun x ↦ u (spaceSlice x)) =ᶠ[nhds p.space]
      fun x ↦ du (spaceSlice x) := by
    filter_upwards [hspaceDomain.mem_nhds hpSpace] with x hx
    exact (h.hasFDerivAt_space hx).fderiv
  ext v w
  simp only [hessianCurryEquiv, LinearIsometryEquiv.trans_apply,
    continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryRightEquiv_apply', parabolicSpatialJet,
    iteratedFDeriv_two_apply]
  rw [show (fun x ↦ u (parabolicPoint p.time x)) =
      fun x ↦ u (spaceSlice x) by rfl,
    hgradient.fderiv_eq, (h.hasFDerivAt_gradient hp).fderiv]
  rfl

theorem holderWith_restrict_timeDerivative_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {alpha C : NNReal}
    (hgauge : eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C) :
    HolderWith C alpha (Q.restrict dtimeU) := by
  have hbase : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C :=
    (eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _).trans hgauge
  have hholder := parabolicTimeDerivative_holderWith_restrict hbase
  have heq : Q.restrict (parabolicTimeDerivative
      (fun t x ↦ u (parabolicPoint t x))) = Q.restrict dtimeU := by
    funext p
    exact h.parabolicTimeDerivative_eq p.2
  rwa [heq] at hholder

theorem holderWith_restrict_spatialDerivative_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {alpha C : NNReal}
    (hgauge : eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C) :
    HolderWith C alpha (Q.restrict du) := by
  let e := continuousMultilinearCurryFin1 Real E F
  have hjet := parabolicSpatialGradient_holderWith_restrict_of_lower_jets hgauge
  have hcomp := e.lipschitz.holderWith.comp hjet
  have heq : e ∘ Q.restrict (parabolicSpatialJet 1
      (fun t x ↦ u (parabolicPoint t x))) = Q.restrict du := by
    funext p
    exact h.continuousMultilinearCurryFin1_parabolicSpatialJet_one_eq p.2
  rw [heq] at hcomp
  simpa only [e, NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp

theorem holderWith_restrict_spatialSecondDerivative_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {alpha C : NNReal}
    (hgauge : eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C) :
    HolderWith C alpha (Q.restrict d2u) := by
  have hbase : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C :=
    (eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _).trans hgauge
  have hjet := parabolicSpatialJet_holderWith_restrict hbase
  have hcomp := (hessianCurryEquiv E F).lipschitz.holderWith.comp hjet
  have heq : hessianCurryEquiv E F ∘ Q.restrict (parabolicSpatialJet 2
      (fun t x ↦ u (parabolicPoint t x))) = Q.restrict d2u := by
    funext p
    exact h.hessianCurryEquiv_parabolicSpatialJet_two_eq hQ p.2
  rw [heq] at hcomp
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp

theorem norm_timeDerivative_le_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {alpha C : NNReal}
    (hgauge : eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C)
    {p : ParabolicPoint E} (hp : p ∈ Q) : ‖dtimeU p‖ ≤ C := by
  have hbase : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C :=
    (eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _).trans hgauge
  rw [← h.parabolicTimeDerivative_eq hp]
  exact parabolicTimeDerivative_norm_le hbase hp

theorem norm_spatialDerivative_le_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {alpha C : NNReal}
    (hgauge : eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C)
    {p : ParabolicPoint E} (hp : p ∈ Q) : ‖du p‖ ≤ C := by
  have hbase : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C :=
    (eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _).trans hgauge
  rw [← h.continuousMultilinearCurryFin1_parabolicSpatialJet_one_eq hp,
    (continuousMultilinearCurryFin1 Real E F).norm_map]
  exact parabolicSpatialJet_norm_le hbase (by norm_num) hp

theorem norm_spatialSecondDerivative_le_of_lower_jets_gauge
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {alpha C : NNReal}
    (hgauge : eParabolicC2HolderGaugeWithLowerJetsOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C)
    {p : ParabolicPoint E} (hp : p ∈ Q) : ‖d2u p‖ ≤ C := by
  have hbase : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ u (parabolicPoint t x)) ≤ C :=
    (eParabolicC2HolderGaugeOn_le_with_lower_jets alpha Q _).trans hgauge
  rw [← h.hessianCurryEquiv_parabolicSpatialJet_two_eq hQ hp,
    (hessianCurryEquiv E F).norm_map]
  exact parabolicSpatialJet_norm_le hbase (by norm_num) hp

theorem isParabolicC2On
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (h : ParabolicJetRealizesOn Q u dtimeU du d2u)
    (hd2u : ContinuousOn d2u Q) :
    IsParabolicC2On Q (fun t x ↦ u (parabolicPoint t x)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    let spaceSlice : E → ParabolicPoint E := fun x ↦ parabolicPoint p.time x
    let spaceDomain : Set E := spaceSlice ⁻¹' Q
    have hspaceSlice : Continuous spaceSlice := by
      simpa only [spaceSlice, parabolicPoint] using
        (continuous_const : Continuous
          (fun _ : E ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
    have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
    have hpSpace : p.space ∈ spaceDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have hd2uSpace : ContinuousOn (fun x ↦ d2u (spaceSlice x)) spaceDomain :=
      hd2u.comp hspaceSlice.continuousOn (fun _ hx ↦ hx)
    have hd2uAt : ContDiffAt Real 0 (fun x ↦ d2u (spaceSlice x)) p.space := by
      rw [contDiffAt_zero]
      exact ⟨spaceDomain, hspaceDomain.mem_nhds hpSpace, hd2uSpace⟩
    have hduAt : ContDiffAt Real 1 (fun x ↦ du (spaceSlice x)) p.space := by
      refine (contDiffAt_succ_iff_hasFDerivAt (n := 0)).2 ⟨
        (fun x ↦ d2u (spaceSlice x)), ?_, hd2uAt⟩
      exact ⟨spaceDomain, hspaceDomain.mem_nhds hpSpace, fun x hx ↦ by
        simpa only [spaceSlice, parabolicPoint_time, parabolicPoint_space] using
          h.hasFDerivAt_gradient hx⟩
    have huAt : ContDiffAt Real 2 (fun x ↦ u (spaceSlice x)) p.space := by
      refine (contDiffAt_succ_iff_hasFDerivAt (n := 1)).2 ⟨
        (fun x ↦ du (spaceSlice x)), ?_, hduAt⟩
      exact ⟨spaceDomain, hspaceDomain.mem_nhds hpSpace, fun x hx ↦ by
        simpa only [spaceSlice, parabolicPoint_time, parabolicPoint_space] using
          h.hasFDerivAt_space hx⟩
    simpa only [spaceSlice, parabolicPoint_time] using huAt
  · intro p hp
    exact (h.hasDerivAt_time hp).differentiableAt

end ParabolicJetRealizesOn

theorem parabolic_jet_realizes_on_of_tendsto_locally_uniformly_on
    {ι : Type*} {l : Filter ι} [NeBot l]
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {uApprox dtimeUApprox : ι → ParabolicPoint E → F}
    {duApprox : ι → ParabolicPoint E → E →L[Real] F}
    {d2uApprox : ι → ParabolicPoint E → E →L[Real] E →L[Real] F}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (hu : TendstoLocallyUniformlyOn uApprox u l Q)
    (hdtimeU : TendstoLocallyUniformlyOn dtimeUApprox dtimeU l Q)
    (hdu : TendstoLocallyUniformlyOn duApprox du l Q)
    (hd2u : TendstoLocallyUniformlyOn d2uApprox d2u l Q)
    (hrealize : ∀ i, ParabolicJetRealizesOn Q
      (uApprox i) (dtimeUApprox i) (duApprox i) (d2uApprox i)) :
    ParabolicJetRealizesOn Q u dtimeU du d2u := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    let timeSlice : Real → ParabolicPoint E := fun t ↦ parabolicPoint t p.space
    let timeDomain : Set Real := timeSlice ⁻¹' Q
    have htimeSlice : Continuous timeSlice := by
      simpa only [timeSlice, parabolicPoint] using
        Metric.Snowflaking.continuous_toSnowflaking.prodMk
          (continuous_const : Continuous (fun _ : Real ↦ p.space))
    have htimeDomain : IsOpen timeDomain := hQ.preimage htimeSlice
    have hpTime : p.time ∈ timeDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have huTime := hu.comp timeSlice (fun _ h ↦ h) htimeSlice.continuousOn
    have hdtimeUTime :=
      hdtimeU.comp timeSlice (fun _ h ↦ h) htimeSlice.continuousOn
    have hderiv := hasDerivAt_of_tendstoLocallyUniformlyOn htimeDomain
      hdtimeUTime (Eventually.of_forall fun i t ht ↦ by
        have h := (hrealize i).hasDerivAt_time ht
        simpa only [timeSlice, parabolicPoint_space, parabolicPoint_time] using h)
      (fun t ht ↦ huTime.tendsto_at ht) hpTime
    simpa only [timeSlice, Function.comp_apply, parabolicPoint_time_space] using hderiv
  · intro p hp
    let spaceSlice : E → ParabolicPoint E := fun x ↦ parabolicPoint p.time x
    let spaceDomain : Set E := spaceSlice ⁻¹' Q
    have hspaceSlice : Continuous spaceSlice := by
      simpa only [spaceSlice, parabolicPoint] using
        (continuous_const : Continuous
          (fun _ : E ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
    have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
    have hpSpace : p.space ∈ spaceDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have huSpace := hu.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hduSpace := hdu.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hderiv := hasFDerivAt_of_tendstoLocallyUniformlyOn hspaceDomain
      hduSpace (fun i x hx ↦ by
        have h := (hrealize i).hasFDerivAt_space hx
        simpa only [spaceSlice, parabolicPoint_space, parabolicPoint_time] using h)
      (fun x hx ↦ huSpace.tendsto_at hx) hpSpace
    simpa only [spaceSlice, Function.comp_apply, parabolicPoint_time_space] using hderiv
  · intro p hp
    let spaceSlice : E → ParabolicPoint E := fun x ↦ parabolicPoint p.time x
    let spaceDomain : Set E := spaceSlice ⁻¹' Q
    have hspaceSlice : Continuous spaceSlice := by
      simpa only [spaceSlice, parabolicPoint] using
        (continuous_const : Continuous
          (fun _ : E ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
    have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
    have hpSpace : p.space ∈ spaceDomain := by
      change parabolicPoint p.time p.space ∈ Q
      simpa only [parabolicPoint_time_space] using hp
    have hduSpace := hdu.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hd2uSpace := hd2u.comp spaceSlice (fun _ h ↦ h) hspaceSlice.continuousOn
    have hderiv := hasFDerivAt_of_tendstoLocallyUniformlyOn hspaceDomain
      hd2uSpace (fun i x hx ↦ by
        have h := (hrealize i).hasFDerivAt_gradient hx
        simpa only [spaceSlice, parabolicPoint_space, parabolicPoint_time] using h)
      (fun x hx ↦ hduSpace.tendsto_at hx) hpSpace
    simpa only [spaceSlice, Function.comp_apply, parabolicPoint_time_space] using hderiv

theorem isParabolicC2On_of_tendsto_locally_uniformly_on
    {ι : Type*} {l : Filter ι} [NeBot l]
    {Q : Set (ParabolicPoint E)} (hQ : IsOpen Q)
    {uApprox dtimeUApprox : ι → ParabolicPoint E → F}
    {duApprox : ι → ParabolicPoint E → E →L[Real] F}
    {d2uApprox : ι → ParabolicPoint E → E →L[Real] E →L[Real] F}
    {u dtimeU : ParabolicPoint E → F}
    {du : ParabolicPoint E → E →L[Real] F}
    {d2u : ParabolicPoint E → E →L[Real] E →L[Real] F}
    (hu : TendstoLocallyUniformlyOn uApprox u l Q)
    (hdtimeU : TendstoLocallyUniformlyOn dtimeUApprox dtimeU l Q)
    (hdu : TendstoLocallyUniformlyOn duApprox du l Q)
    (hd2u : TendstoLocallyUniformlyOn d2uApprox d2u l Q)
    (hrealize : ∀ i, ParabolicJetRealizesOn Q
      (uApprox i) (dtimeUApprox i) (duApprox i) (d2uApprox i))
    (hd2uContinuous : ∃ᶠ i in l, ContinuousOn (d2uApprox i) Q) :
    IsParabolicC2On Q (fun t x ↦ u (parabolicPoint t x)) := by
  have hlimit := parabolic_jet_realizes_on_of_tendsto_locally_uniformly_on
    hQ hu hdtimeU hdu hd2u hrealize
  exact hlimit.isParabolicC2On hQ (hd2u.continuousOn hd2uContinuous)

end DifferentialGeometry.Analysis.Schauder

end
