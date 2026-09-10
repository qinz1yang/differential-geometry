import DifferentialGeometry.Bundle.Orientation.Section
import DifferentialGeometry.Topology.Covering.Separation
import DifferentialGeometry.Topology.Covering.Sheets
import DifferentialGeometry.Topology.Manifold.CoveringAtlas
import DifferentialGeometry.Topology.Manifold.CountableAtlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas



noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ}

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology
local instance : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩

abbrev tangentOrientationCover (hdim : Module.finrank ℝ E = n) :=
  (DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim).TotalSpace

abbrev TangentOrientationCover (hdim : Module.finrank ℝ E = n) :=
  tangentOrientationCover (M := M) hdim


def tangentOrientationProjection (hdim : Module.finrank ℝ E = n) :
    tangentOrientationCover (M := M) hdim → M := TotalSpace.proj


def tangentOrientationFiberEquiv (hdim : Module.finrank ℝ E = n) (x : M) :
    (tangentOrientationProjection (M := M) hdim ⁻¹' {x}) ≃
      Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n) where
  toFun z := z.val.snd
  invFun o := ⟨⟨x, o⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b, o⟩, hb⟩
    change b = x at hb
    subst b
    rfl
  right_inv _ := rfl


theorem tangentOrientationProjection_isCoveringMap (hdim : Module.finrank ℝ E = n) :
    IsCoveringMap (tangentOrientationProjection (M := M) hdim) :=
  DifferentialGeometry.VectorBundle.orientationCore_isCoveringMap (tangentBundleCore 𝓘(ℝ, E) M) hdim


def tangentOrientationFiberEquivBool (hdim : Module.finrank ℝ E = n) (x : M) :
    (tangentOrientationProjection (M := M) hdim ⁻¹' {x}) ≃ Bool :=
  (tangentOrientationFiberEquiv hdim x).trans
    (DifferentialGeometry.VectorBundle.orientationEquivBool
      ((Module.finBasis ℝ E).reindex (finCongr hdim)))

theorem tangentOrientation_chart (hdim : Module.finrank ℝ E = n) (c x : M)
    (hx : x ∈ (chartAt E c).source) (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n)) :
    let Z := DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim
    (Z.localTriv (achart E c) ⟨x, o⟩).1 = x ∧
    (Z.localTriv (achart E c) ⟨x, o⟩).2 =
      Orientation.map (Fin n)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) c).continuousLinearEquivAt ℝ x hx).toLinearEquiv o := by
  refine ⟨rfl, ?_⟩
  exact DifferentialGeometry.VectorBundle.orientationCore_localTriv
    (tangentBundleCore 𝓘(ℝ, E) M) hdim (achart E c) x hx o


theorem tangentOrientationCover_t2Space [T2Space M] (hdim : Module.finrank ℝ E = n) :
    T2Space (tangentOrientationCover (M := M) hdim) :=
  DifferentialGeometry.Topology.Covering.t2Space_of_isCoveringMap
    (tangentOrientationProjection_isCoveringMap hdim)


theorem tangentOrientationCover_secondCountable [SecondCountableTopology M]
    (hdim : Module.finrank ℝ E = n) :
    SecondCountableTopology (tangentOrientationCover (M := M) hdim) := by
  let : Fintype (Orientation ℝ E (Fin n)) := Fintype.ofEquiv Bool
    (DifferentialGeometry.VectorBundle.orientationEquivBool
      ((Module.finBasis ℝ E).reindex (finCongr hdim))).symm
  exact DifferentialGeometry.Topology.Covering.secondCountableTopology_totalSpace
    (DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim)

omit [FiniteDimensional ℝ E] in
theorem tangent_orientation_transition_derivative (c d x : M)
    (hx : x ∈ (chartAt E c).source ∩ (chartAt E d).source) :
    (((tangentBundleCore 𝓘(ℝ, E) M).localTriv (achart E c)).coordChangeL ℝ
      ((tangentBundleCore 𝓘(ℝ, E) M).localTriv (achart E d)) x : E →L[ℝ] E) =
      fderiv ℝ (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm)
        (extChartAt 𝓘(ℝ, E) c x) := by
  ext v
  change ((tangentBundleCore 𝓘(ℝ, E) M).localTriv (achart E c)).coordChangeL ℝ
    ((tangentBundleCore 𝓘(ℝ, E) M).localTriv (achart E d)) x v = _
  rw [(tangentBundleCore 𝓘(ℝ, E) M).localTriv_coordChange_eq (achart E c) (achart E d) hx]
  simp only [tangentBundleCore_coordChange_achart]
  rw [show Set.range (𝓘(ℝ, E) : E → E) = Set.univ from Set.range_id, fderivWithin_univ]

omit [FiniteDimensional ℝ E] in
theorem tangent_orientation_transition_det_ne_zero (c d x : M)
    (hx : x ∈ (chartAt E c).source ∩ (chartAt E d).source) :
    (fderiv ℝ (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm)
      (extChartAt 𝓘(ℝ, E) c x)).det ≠ 0 := by
  rw [← tangent_orientation_transition_derivative c d x hx]
  exact (((tangentBundleCore 𝓘(ℝ, E) M).localTriv (achart E c)).coordChangeL ℝ
    ((tangentBundleCore 𝓘(ℝ, E) M).localTriv (achart E d)) x).toLinearEquiv.isUnit_det'.ne_zero

theorem tangent_orientation_transition_positive (hdim : Module.finrank ℝ E = n) (c d x : M)
    (hx : x ∈ (chartAt E c).source ∩ (chartAt E d).source) (o : Orientation ℝ E (Fin n)) :
    DifferentialGeometry.VectorBundle.orientationChange (tangentBundleCore 𝓘(ℝ, E) M)
      (achart E c) (achart E d) x o = o ↔
    0 < (fderiv ℝ (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm)
      (extChartAt 𝓘(ℝ, E) c x)).det := by
  rw [← tangent_orientation_transition_derivative c d x hx]
  exact DifferentialGeometry.VectorBundle.map_orientation_eq_iff hdim o _

omit [FiniteDimensional ℝ E] in
theorem tangent_orientation_transition_negative (hdim : Module.finrank ℝ E = n) (c d x : M)
    (hx : x ∈ (chartAt E c).source ∩ (chartAt E d).source) (o : Orientation ℝ E (Fin n)) :
    DifferentialGeometry.VectorBundle.orientationChange (tangentBundleCore 𝓘(ℝ, E) M)
      (achart E c) (achart E d) x o = -o ↔
    (fderiv ℝ (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm)
      (extChartAt 𝓘(ℝ, E) c x)).det < 0 := by
  rw [← tangent_orientation_transition_derivative c d x hx]
  exact o.map_eq_neg_iff_det_neg _ (by simpa using hdim.symm)

omit [FiniteDimensional ℝ E] in
theorem tangent_orientation_transition_sign_isLocallyConstant (c d : M) :
    IsLocallyConstant (fun x : ↥((chartAt E c).source ∩ (chartAt E d).source) =>
      Real.sign (fderiv ℝ (extChartAt 𝓘(ℝ, E) d ∘ (extChartAt 𝓘(ℝ, E) c).symm)
        (extChartAt 𝓘(ℝ, E) c x)).det) := by
  let Z := tangentBundleCore 𝓘(ℝ, E) M
  have hAon : ContinuousOn (fun x =>
      ((Z.localTriv (achart E c)).coordChangeL ℝ (Z.localTriv (achart E d)) x : E →L[ℝ] E))
      ((chartAt E c).source ∩ (chartAt E d).source) := by
    apply (Z.continuousOn_coordChange (achart E c) (achart E d)).congr
    intro x hx
    exact ContinuousLinearMap.ext
      (fun v => Z.localTriv_coordChange_eq (achart E c) (achart E d) hx v)
  have h := DifferentialGeometry.VectorBundle.isLocallyConstant_det_sign
    (fun x : ↥((chartAt E c).source ∩ (chartAt E d).source) =>
      (Z.localTriv (achart E c)).coordChangeL ℝ (Z.localTriv (achart E d)) x)
    (continuousOn_iff_continuous_domRestrict.mp hAon)
  convert h using 1
  ext x
  rw [tangent_orientation_transition_derivative c d x x.property]

@[instance_reducible]
def tangentOrientationChartedSpace (hdim : Module.finrank ℝ E = n) :
    ChartedSpace E (tangentOrientationCover (M := M) hdim) :=
  coveringChartedSpace (H := E) (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph


theorem tangentOrientation_isManifold (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    IsManifold 𝓘(ℝ, E) ∞ (tangentOrientationCover (M := M) hdim) :=
  covering_isManifold (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph 𝓘(ℝ, E)


def tangentOrientationSheet (hdim : Module.finrank ℝ E = n) (c : M)
    (o : Orientation ℝ E (Fin n)) : OpenPartialHomeomorph (tangentOrientationCover (M := M) hdim) M :=
  DifferentialGeometry.Topology.Covering.sheet
    ((DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim).localTriv (achart E c)) o


theorem tangentOrientationSheets_disjoint (hdim : Module.finrank ℝ E = n) (c : M)
    (o : Orientation ℝ E (Fin n)) :
    Disjoint (tangentOrientationSheet hdim c o).source (tangentOrientationSheet hdim c (-o)).source :=
  DifferentialGeometry.Topology.Covering.sheet_disjoint _ (Module.Ray.ne_neg_self o)


theorem tangentOrientationSheets_union (hdim : Module.finrank ℝ E = n) (c : M)
    (o : Orientation ℝ E (Fin n)) :
    (tangentOrientationSheet hdim c o).source ∪ (tangentOrientationSheet hdim c (-o)).source =
      tangentOrientationProjection hdim ⁻¹' (chartAt E c).source :=
  DifferentialGeometry.Topology.Covering.sheet_union _ o (-o)
    (fun q => q.eq_or_eq_neg o (by simpa using hdim.symm))


theorem tangentOrientationSheet_smooth_inverse (hdim : Module.finrank ℝ E = n) (c : M)
    (o : Orientation ℝ E (Fin n)) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (tangentOrientationSheet hdim c o).symm (chartAt E c).source :=
  covering_sheetInverse_contMDiff (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph
    𝓘(ℝ, E) (tangentOrientationSheet hdim c o) (fun _ _ => rfl)

theorem tangentOrientation_section (hdim : Module.finrank ℝ E = n)
    (s : C(M, tangentOrientationCover (M := M) hdim))
    (hs : Function.RightInverse s (tangentOrientationProjection hdim)) :
    (letI := tangentOrientationChartedSpace (M := M) hdim;
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ s) ∧
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E))
        (fun x => (s x).snd) :=
  ⟨covering_section_contMDiff (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph
      𝓘(ℝ, E) s hs,
    DifferentialGeometry.VectorBundle.compatibleOrientation_of_section (tangentBundleCore 𝓘(ℝ, E) M) hdim s hs⟩


theorem tangentOrientationCover_secondCountable_of_compact [CompactSpace M]
    (hdim : Module.finrank ℝ E = n) :
    SecondCountableTopology (tangentOrientationCover (M := M) hdim) := by
  let : SecondCountableTopology M := secondCountableTopology_of_compact (E := E)
  exact tangentOrientationCover_secondCountable hdim

end DifferentialGeometry.Topology.Manifold
