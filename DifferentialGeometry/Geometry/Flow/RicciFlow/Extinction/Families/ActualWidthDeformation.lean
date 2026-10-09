import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ActualWidth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ClassWidthDeformation

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

universe u

abbrev ComponentInteriorRampDeformation (P : OrientedThreeStage.{u}) (a b : ℝ) (hab : a < b)
    (c : ConnectedComponents P.Carrier) : Prop :=
  letI := P.component_connected c
  ∀ (u : ℝ) (_hu : u ∈ Ioo a b) (v : ℝ) (_hv : v ∈ Ioo u b)
    (B : RicciBackground (I := ThreeModel) (M := (P.component c).Carrier)
      (RealTimeInterval.closedOpen a b hab) u v),
    ∀ (s t : ℝ) (hst : s < t), u ≤ s → t ≤ v → RampFamilyDeformation s t hst B.family

theorem componentInteriorRampDeformation_of_family_deformation {P : OrientedThreeStage.{u}}
    {a b : ℝ} {hab : a < b} (c : ConnectedComponents P.Carrier) :
    ComponentInteriorRampDeformation P a b hab c := by
  intro u _hu v _hv B s t hst hs ht
  exact @rfs_rampFamilyDeformation_of_family_deformation _ _ _ _ _ _ _ _ _
    (inferInstance : TopologicalSpace (P.component c).Carrier)
    (inferInstance : ChartedSpace ThreeSpace (P.component c).Carrier)
    (inferInstance : IsManifold ThreeModel ∞ (P.component c).Carrier)
    (inferInstance : SigmaCompactSpace (P.component c).Carrier)
    (inferInstance : T2Space (P.component c).Carrier)
    (inferInstance : CompactSpace (P.component c).Carrier)
    (P.component_connected c)
    (inferInstance : ModelWithCorners.Boundaryless ThreeModel)
    _ _ _ B (by simp [ThreeSpace]) s t hst hs ht

variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem incoming_component_integrated_width_of_rampFamilyDeformation (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier)
    (hdata : ComponentInteriorRampDeformation P a b G.lt c) :
    ∀ s ∈ Ico a b, ∀ t ∈ Ico s b,
      0 ≤ Width.componentWidth P (G.flow.base.metric t) c hSC ∧
      Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        componentAffine P G.flow.base c s t
          (Width.componentWidth P (G.flow.base.metric s) c hSC) ∧
      componentFactor P G.flow.base c s t *
          Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        Width.componentWidth P (G.flow.base.metric s) c hSC -
          2 * Real.pi * ∫ r in s..t, componentFactor P G.flow.base c s r := by
  let := P.component_connected c
  let := hSC
  obtain ⟨F, _hF, hmetric, hscalar, hbackground⟩ := incoming_component_solution G c
  have hrho (r : ℝ) (hr : r ∈ Ico a b) :
      halfScalarMinimum F.base r = componentHalfScalar P G.flow.base c r := by
    change sInf (range (F.base.scalar r)) / 2 =
      sInf (range (fun x : (P.component c).Carrier => G.flow.base.scalar r x.1)) / 2
    rw [show F.base.scalar r =
      (fun x : (P.component c).Carrier => G.flow.base.scalar r x.1) from
        funext (hscalar r hr)]
  have hwidth (r : ℝ) (hr : r ∈ Ico a b) :
      Width.classWidth (F.base.metric r)
          (positiveFreeContractibleClass (P.component c).orientation) =
        Width.componentWidth P (G.flow.base.metric r) c hSC := by
    rw [hmetric r hr]
    rfl
  have hfactor {s t : ℝ} (hs : s ∈ Ico a b) (ht : t ∈ Ico s b) :
      areaIntegratingFactor F.base s t = componentFactor P G.flow.base c s t := by
    have hexp : areaIntegratingFactor F.base s t =
        Real.exp (∫ r in s..t, halfScalarMinimum F.base r) := by
      unfold areaIntegratingFactor halfScalarMinimum
      rw [intervalIntegral.integral_div]
      congr 1
      ring
    rw [hexp]
    unfold componentFactor
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    exact hrho r ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩
  have hinterior {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo s b) :
      componentFactor P G.flow.base c s t *
          Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        Width.componentWidth P (G.flow.base.metric s) c hSC -
          2 * Real.pi * ∫ r in s..t, componentFactor P G.flow.base c s r := by
    obtain ⟨B, hB⟩ := hbackground s hs t ht
    have hess : IsEssentialFamilyClass
        (positiveFreeContractibleClass (P.component c).orientation) :=
      isEssentialFamilyClass_of_pi2_zero
        (fun q => (rfs_homotopy_groups q).1)
        (positiveFreeContractibleClass (P.component c).orientation)
        (fun q => positiveFreeContractibleClass_nontrivial (P.component c).orientation q)
    have h := (rfs_integrated_class_width_of_rampFamilyDeformation B
      (fun p q hpq hp hq => hdata s hs t ht B p q hpq hp hq)
      (positiveFreeContractibleClass (P.component c).orientation) hess
      s ⟨le_rfl, ht.1.le⟩ t ⟨ht.1.le, le_rfl⟩).2.2
    rw [hB] at h
    have hs' : s ∈ Ico a b := ⟨hs.1.le, hs.2⟩
    have ht' : t ∈ Ico a b := ⟨hs.1.le.trans ht.1.le, ht.2⟩
    rw [hwidth s hs', hwidth t ht', hfactor hs' ⟨ht.1.le, ht.2⟩] at h
    have hJ : (∫ r in s..t, areaIntegratingFactor F.base s r) =
        ∫ r in s..t, componentFactor P G.flow.base c s r := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.1.le] at hr
      exact hfactor hs' ⟨hr.1, hr.2.trans_lt ht.2⟩
    rwa [hJ] at h
  obtain ⟨hrho_cont, hwidth_cont⟩ := incoming_component_continuity G c hSC
  intro s hs t ht
  have hnonneg := Width.componentWidth_nonneg P (G.flow.base.metric t) c hSC
  have hbound : componentFactor P G.flow.base c s t *
          Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        Width.componentWidth P (G.flow.base.metric s) c hSC -
          2 * Real.pi * ∫ r in s..t, componentFactor P G.flow.base c s r := by
    rcases eq_or_lt_of_le ht.1 with rfl | hst
    · simp only [componentFactor, intervalIntegral.integral_same, Real.exp_zero,
        one_mul, mul_zero, sub_zero, le_refl]
    · apply integrated_comparison_le_endpoints hst
        (hrho_cont.mono (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩))
        (hwidth_cont.mono (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩))
      intro u hu v hv
      exact hinterior ⟨hs.1.trans_lt hu.1, hu.2.trans ht.2⟩
        ⟨hv.1, hv.2.trans ht.2⟩
  refine ⟨hnonneg, ?_, hbound⟩
  exact (le_inv_mul_iff₀ (Real.exp_pos _)).mpr hbound

private theorem component_primitive_deriv {f : ℝ → ℝ} {l r s t : ℝ}
    (hf : ContinuousOn f (Icc l r)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    HasDerivWithinAt (fun v => ∫ w in s..v, f w) (f t) (Icc l r) t := by
  let : Fact (t ∈ Icc l r) := ⟨ht⟩
  have hi : IntervalIntegrable f volume s t :=
    (hf.mono (uIcc_subset_Icc hs ht)).intervalIntegrable
  have hm : StronglyMeasurableAtFilter f (𝓝[Icc l r] t) volume :=
    ⟨Icc l r, self_mem_nhdsWithin, hf.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right hi hm (hf t ht)

private theorem componentFactor_continuousOn
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) {l r s : ℝ}
    (hf : ContinuousOn (componentHalfScalar P F c) (Icc l r)) (hs : s ∈ Icc l r) :
    ContinuousOn (componentFactor P F c s) (Icc l r) := by
  intro t ht
  exact ((component_primitive_deriv hf hs ht).exp).continuousWithinAt

private theorem componentAffine_hasDerivWithinAt
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) {l r s t : ℝ}
    (hf : ContinuousOn (componentHalfScalar P F c) (Icc l r))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (z : ℝ) :
    HasDerivWithinAt (fun v => componentAffine P F c s v z)
      (-2 * Real.pi - componentHalfScalar P F c t * componentAffine P F c s t z)
      (Icc l r) t := by
  have hcont := componentFactor_continuousOn F c hf hs
  have hfac : HasDerivWithinAt (componentFactor P F c s)
      (componentHalfScalar P F c t * componentFactor P F c s t) (Icc l r) t := by
    change HasDerivWithinAt (fun v => Real.exp (∫ r in s..v, componentHalfScalar P F c r))
      (componentHalfScalar P F c t * Real.exp (∫ r in s..t, componentHalfScalar P F c r))
      (Icc l r) t
    simpa only [mul_comm] using (component_primitive_deriv hf hs ht).exp
  have hne : componentFactor P F c s t ≠ 0 := (Real.exp_pos _).ne'
  have hd := (hfac.inv hne).mul
    ((hasDerivWithinAt_const t (Icc l r) z).sub
      ((component_primitive_deriv hcont hs ht).const_mul (2 * Real.pi)))
  convert! hd using 1
  simp only [componentAffine, Pi.inv_apply, Pi.sub_apply]
  field_simp [hne]
  ring

theorem incoming_component_incrementBound_of_rampFamilyDeformation (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier)
    (hdata : ComponentInteriorRampDeformation P a b G.lt c) :
    ∀ t ∈ Ico a b, ∀ epsilon > 0, ∃ delta > 0,
      ∀ h ∈ Ioo (0 : ℝ) delta, t + h < b →
        (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
          Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
          -2 * Real.pi - componentHalfScalar P G.flow.base c t *
            Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon := by
  obtain ⟨hrho, _hw⟩ := incoming_component_continuity G c hSC
  have hcmp := incoming_component_integrated_width_of_rampFamilyDeformation G c hSC hdata
  have hself (s z : ℝ) : componentAffine P G.flow.base c s s z = z := by
    simp only [componentAffine, componentFactor, intervalIntegral.integral_same,
      Real.exp_zero, inv_one, one_mul, mul_zero, sub_zero]
  intro t ht epsilon hepsilon
  let v := (t + b) / 2
  have htv : t < v := by dsimp [v]; linarith [ht.2]
  have hvb : v < b := by dsimp [v]; linarith [ht.2]
  have hsub : Icc t v ⊆ Ico a b :=
    fun r hr => ⟨ht.1.trans hr.1, hr.2.trans_lt hvb⟩
  let f : ℝ → ℝ := fun r => componentAffine P G.flow.base c t r
    (Width.componentWidth P (G.flow.base.metric t) c hSC)
  have hd : HasDerivWithinAt f
      (-2 * Real.pi - componentHalfScalar P G.flow.base c t *
        Width.componentWidth P (G.flow.base.metric t) c hSC) (Icc t v) t := by
    simpa only [hself] using componentAffine_hasDerivWithinAt G.flow.base c
      (hrho.mono hsub) ⟨le_rfl, htv.le⟩ ⟨le_rfl, htv.le⟩
      (Width.componentWidth P (G.flow.base.metric t) c hSC)
  have hevent := hd.limsup_slope_le (by linarith :
    -2 * Real.pi - componentHalfScalar P G.flow.base c t *
      Width.componentWidth P (G.flow.base.metric t) c hSC <
    -2 * Real.pi - componentHalfScalar P G.flow.base c t *
      Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon)
  obtain ⟨delta, hdelta, hclose⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨min delta (v - t), lt_min hdelta (sub_pos.mpr htv), ?_⟩
  intro h hh htb
  have hhd : h < delta := hh.2.trans_le (min_le_left _ _)
  have hhv : t + h ≤ v := by
    have h := hh.2.trans_le (min_le_right delta (v - t))
    linarith
  have hball : t + h ∈ Metric.ball t delta := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh.1]
    exact hhd
  have hwindow : t + h ∈ Icc t v \ {t} := by
    refine ⟨⟨by linarith [hh.1], hhv⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [hh.1]
  have hslope : (f (t + h) - f t) / h <
      -2 * Real.pi - componentHalfScalar P G.flow.base c t *
        Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon := by
    have hc := hclose ⟨hball, hwindow⟩
    change slope f t (t + h) < _ at hc
    simpa only [slope, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hc
  have hup := (hcmp t ht (t + h) ⟨by linarith [hh.1], htb⟩).2.1
  have heq : f t = Width.componentWidth P (G.flow.base.metric t) c hSC := hself _ _
  calc
    (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
        Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
        (f (t + h) - f t) / h := by
      rw [heq]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hup _) hh.1.le
    _ ≤ _ := hslope.le

private def closedSlabIncoming (G : P.ClosedSlab a b) : P.IncomingSlab a b where
  lt := G.lt
  flow := G.flow.timeRestrict (RealTimeInterval.closedOpen a b G.lt)
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨ht.1, ht.2.le⟩) (fun _ ht => ht)
  smoothUpTo := by
    intro p t ht
    obtain ⟨U, hU, hp, hsub, V, hV, htV, A, hA, heq⟩ :=
      G.smoothUpTo p t ⟨ht.1, ht.2.le⟩
    refine ⟨U, hU, hp, hsub, V, hV, htV, A, hA, ?_⟩
    intro s hs x hx i j
    exact heq s ⟨hs.1, ⟨hs.2.1, hs.2.2.le⟩⟩ x hx i j

theorem closed_component_incrementBound_of_rampFamilyDeformation (G : P.ClosedSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier)
    (hdata : ComponentInteriorRampDeformation P a b G.lt c) :
    ∀ t ∈ Ico a b, ∀ epsilon > 0, ∃ delta > 0,
      ∀ h ∈ Ioo (0 : ℝ) delta, t + h ≤ b →
        (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
          Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
          -2 * Real.pi - componentHalfScalar P G.flow.base c t *
            Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon := by
  have hincoming :=
    incoming_component_incrementBound_of_rampFamilyDeformation (closedSlabIncoming G) c hSC hdata
  intro t ht epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := hincoming t ht epsilon hepsilon
  refine ⟨min delta (b - t), lt_min hdelta (sub_pos.mpr ht.2), ?_⟩
  intro h hh _htb
  have hsmall : h < b - t := hh.2.trans_le (min_le_right _ _)
  exact hbound h ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩ (by linarith)


end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
