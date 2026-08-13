import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import DifferentialGeometry.Analysis.Schauder.CutoffLaplacian

noncomputable section

open Filter Real Set
open scoped ContDiff NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {X A : Type*} [TopologicalSpace X]
  [NormedAddCommGroup A] [NormedSpace Real A]

def compactSupportBcf (f : X → A) (hf : Continuous f)
    (hcs : HasCompactSupport f) : BoundedContinuousFunction X A :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (Classical.choose (hf.bounded_above_of_compact_support hcs))
    (Classical.choose_spec (hf.bounded_above_of_compact_support hcs))

omit [NormedSpace Real A] in
@[simp]
theorem compactSupportBcf_apply (f : X → A) (hf : Continuous f)
    (hcs : HasCompactSupport f) (x : X) :
    compactSupportBcf f hf hcs x = f x := rfl

section Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

theorem exists_schauder_cutoff_with_hessian
    {K Omega : Set V} (hK : IsCompact K) (hOmega : IsOpen Omega)
    (hKOmega : K ⊆ Omega) {alpha : NNReal}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    ∃ (U : Set V)
      (chi : BoundedContinuousFunction V Real)
      (dchi : BoundedContinuousFunction V (V →L[Real] Real))
      (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
      (Kchi Kdchi Kd2chi Klapchi : NNReal),
      IsOpen U ∧ K ⊆ U ∧
      (∀ x ∈ U, chi x = 1) ∧
      tsupport (chi : V → Real) ⊆ Omega ∧
      Set.range (chi : V → Real) ⊆ Set.Icc 0 1 ∧
      (∀ x, HasFDerivAt (chi : V → Real) (dchi x) x) ∧
      (∀ x, HasFDerivAt (dchi : V → V →L[Real] Real) (d2chi x) x) ∧
      HolderWith Kchi alpha (chi : V → Real) ∧
      HolderWith Kdchi alpha (dchi : V → V →L[Real] Real) ∧
      HolderWith Kd2chi alpha
        (d2chi : V → V →L[Real] V →L[Real] Real) ∧
      HolderWith Klapchi alpha (coreLap d2chi : V → Real) := by
  obtain ⟨chiRaw, hchiCd, hchiCs, hchiOne, hchiSupp, hchiRange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hK hOmega hKOmega
  have hchiCont : Continuous chiRaw := hchiCd.continuous
  let dchiRaw := fderiv Real chiRaw
  have hdchiCd : ContDiff Real ∞ dchiRaw :=
    hchiCd.fderiv_right (m := ∞) (by simp)
  have hdchiCont : Continuous dchiRaw := hdchiCd.continuous
  have hdchiCs : HasCompactSupport dchiRaw := hchiCs.fderiv Real
  let d2chiRaw := fderiv Real dchiRaw
  have hd2chiCd : ContDiff Real ∞ d2chiRaw :=
    hdchiCd.fderiv_right (m := ∞) (by simp)
  have hd2chiCont : Continuous d2chiRaw := hd2chiCd.continuous
  have hd2chiCs : HasCompactSupport d2chiRaw := hdchiCs.fderiv Real
  let chi := compactSupportBcf chiRaw hchiCont hchiCs
  let dchi := compactSupportBcf dchiRaw hdchiCont hdchiCs
  let d2chi := compactSupportBcf d2chiRaw hd2chiCont hd2chiCs
  have hchiDeriv : ∀ x, HasFDerivAt (chi : V → Real) (dchi x) x := by
    intro x
    change HasFDerivAt chiRaw (fderiv Real chiRaw x) x
    exact (hchiCd.differentiable (by simp) x).hasFDerivAt
  have hdchiDeriv : ∀ x,
      HasFDerivAt (dchi : V → V →L[Real] Real) (d2chi x) x := by
    intro x
    change HasFDerivAt dchiRaw (fderiv Real dchiRaw x) x
    exact (hdchiCd.differentiable (by simp) x).hasFDerivAt
  let Kchi := max (2 * ‖chi‖₊) ‖dchi‖₊
  have hchiHolder : HolderWith Kchi alpha (chi : V → Real) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖chi‖₊) (N := ‖dchi‖₊) halpha0 halpha1 hchiDeriv
    · exact fun x ↦ by simpa using chi.norm_coe_le_norm x
    · exact fun x ↦ by simpa using dchi.norm_coe_le_norm x
  let Kdchi := max (2 * ‖dchi‖₊) ‖d2chi‖₊
  have hdchiHolder : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖dchi‖₊) (N := ‖d2chi‖₊) halpha0 halpha1 hdchiDeriv
    · exact fun x ↦ by simpa using dchi.norm_coe_le_norm x
    · exact fun x ↦ by simpa using d2chi.norm_coe_le_norm x
  let d3chiRaw := fderiv Real d2chiRaw
  have hd3chiCd : ContDiff Real ∞ d3chiRaw :=
    hd2chiCd.fderiv_right (m := ∞) (by simp)
  have hd3chiCont : Continuous d3chiRaw := hd3chiCd.continuous
  have hd3chiCs : HasCompactSupport d3chiRaw := hd2chiCs.fderiv Real
  let d3chi := compactSupportBcf d3chiRaw hd3chiCont hd3chiCs
  have hd2chiDeriv : ∀ x, HasFDerivAt
      (d2chi : V → V →L[Real] V →L[Real] Real) (d3chi x) x := by
    intro x
    change HasFDerivAt d2chiRaw (fderiv Real d2chiRaw x) x
    exact (hd2chiCd.differentiable (by simp) x).hasFDerivAt
  let Kd2chi := max (2 * ‖d2chi‖₊) ‖d3chi‖₊
  have hd2chiHolder : HolderWith Kd2chi alpha
      (d2chi : V → V →L[Real] V →L[Real] Real) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖d2chi‖₊) (N := ‖d3chi‖₊) halpha0 halpha1 hd2chiDeriv
    · exact fun x ↦ by simpa using d2chi.norm_coe_le_norm x
    · exact fun x ↦ by simpa using d3chi.norm_coe_le_norm x
  have hlapCd : ContDiff Real ∞ (coreLap d2chi : V → Real) := by
    change ContDiff Real ∞ (fun x ↦ lapEval (d2chi x))
    exact (lapEval (V := V) (F := Real)).contDiff.comp hd2chiCd
  have hlapCs : HasCompactSupport (coreLap d2chi : V → Real) := by
    change HasCompactSupport (fun x ↦ lapEval (d2chi x))
    exact hd2chiCs.comp_left (map_zero (lapEval (V := V) (F := Real)))
  let dlapRaw := fderiv Real (coreLap d2chi : V → Real)
  have hdlapCd : ContDiff Real ∞ dlapRaw :=
    hlapCd.fderiv_right (m := ∞) (by simp)
  have hdlapCont : Continuous dlapRaw := hdlapCd.continuous
  have hdlapCs : HasCompactSupport dlapRaw := hlapCs.fderiv Real
  let dlap := compactSupportBcf dlapRaw hdlapCont hdlapCs
  have hlapDeriv : ∀ x,
      HasFDerivAt (coreLap d2chi : V → Real) (dlap x) x := by
    intro x
    change HasFDerivAt (coreLap d2chi : V → Real)
      (fderiv Real (coreLap d2chi : V → Real) x) x
    exact (hlapCd.differentiable (by simp) x).hasFDerivAt
  let Klapchi := max (2 * ‖coreLap d2chi‖₊) ‖dlap‖₊
  have hlapHolder : HolderWith Klapchi alpha (coreLap d2chi : V → Real) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖coreLap d2chi‖₊) (N := ‖dlap‖₊)
      halpha0 halpha1 hlapDeriv
    · exact fun x ↦ by simpa using (coreLap d2chi).norm_coe_le_norm x
    · exact fun x ↦ by simpa using dlap.norm_coe_le_norm x
  have honeSet : {x : V | chiRaw x = 1} ∈ 𝓝ˢ K := hchiOne
  obtain ⟨U, hU, hKU, hUone⟩ := mem_nhdsSet_iff_exists.mp honeSet
  refine ⟨U, chi, dchi, d2chi, Kchi, Kdchi, Kd2chi, Klapchi,
    hU, hKU, ?_, ?_, ?_, hchiDeriv, hdchiDeriv,
    hchiHolder, hdchiHolder, hd2chiHolder, hlapHolder⟩
  · intro x hx
    exact hUone hx
  · simpa only [chi, compactSupportBcf_apply] using hchiSupp
  · simpa only [chi, compactSupportBcf_apply] using hchiRange

theorem exists_schauder_cutoff
    {K Omega : Set V} (hK : IsCompact K) (hOmega : IsOpen Omega)
    (hKOmega : K ⊆ Omega) {alpha : NNReal}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    ∃ (U : Set V)
      (chi : BoundedContinuousFunction V Real)
      (dchi : BoundedContinuousFunction V (V →L[Real] Real))
      (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
      (Kchi Kdchi Klapchi : NNReal),
      IsOpen U ∧ K ⊆ U ∧
      (∀ x ∈ U, chi x = 1) ∧
      tsupport (chi : V → Real) ⊆ Omega ∧
      Set.range (chi : V → Real) ⊆ Set.Icc 0 1 ∧
      (∀ x, HasFDerivAt (chi : V → Real) (dchi x) x) ∧
      (∀ x, HasFDerivAt (dchi : V → V →L[Real] Real) (d2chi x) x) ∧
      HolderWith Kchi alpha (chi : V → Real) ∧
      HolderWith Kdchi alpha (dchi : V → V →L[Real] Real) ∧
      HolderWith Klapchi alpha (coreLap d2chi : V → Real) := by
  obtain ⟨U, chi, dchi, d2chi, Kchi, Kdchi, Kd2chi, Klapchi,
    hU, hKU, hchiOne, hchiSupp, hchiRange, hchiDeriv, hdchiDeriv,
    hchiHolder, hdchiHolder, hd2chiHolder, hlapHolder⟩ :=
      exists_schauder_cutoff_with_hessian hK hOmega hKOmega halpha0 halpha1
  exact ⟨U, chi, dchi, d2chi, Kchi, Kdchi, Klapchi,
    hU, hKU, hchiOne, hchiSupp, hchiRange, hchiDeriv, hdchiDeriv,
    hchiHolder, hdchiHolder, hlapHolder⟩

end Euclidean

end DifferentialGeometry.Analysis.Schauder

end
