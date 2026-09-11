import DifferentialGeometry.Topology.Manifold.SmoothOrientationLocal
import DifferentialGeometry.Topology.Manifold.OrientationTransportVariation
import DifferentialGeometry.Topology.Manifold.SmoothMapDifferentialCoordinates

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M F K N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace K] (J : ModelWithCorners ℝ F K)
variable [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem coordinateDifferentialEquiv_orientation_pullback (f : M → N)
    (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (p : M)
    (x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source))
    (o : Orientation ℝ F (Fin (Module.finrank ℝ F))) :
    tangentOrientationEquiv (coordinateDifferentialEquiv I J f hbij p x).symm.toLinearEquiv
        (Orientation.map _ (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv o) =
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv
        (tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x.val).symm.toLinearEquiv o) := by
  rw [← tangentOrientationEquiv_self]
  rw [← tangentOrientationEquiv_trans]
  have he : (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv.trans
      (coordinateDifferentialEquiv I J f hbij p x).symm.toLinearEquiv =
      (differentialEquivOfBijective I J f hbij x.val).symm.toLinearEquiv.trans
        (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change preferredChartTangentEquiv I p x.val x.property.1
      ((differentialEquivOfBijective I J f hbij x.val).symm
        ((preferredChartTangentEquiv J (f p) (f x.val) x.property.2).symm
          (preferredChartTangentEquiv J (f p) (f x.val) x.property.2 v))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [he, tangentOrientationEquiv_trans, tangentOrientationEquiv_self]

def pullbackTangentOrientation (f : M → N)
    (hbij : ∀ x : M, Bijective (mfderiv I J f x))
    (o : N → Orientation ℝ F (Fin (Module.finrank ℝ F))) (x : M) :
    Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x).symm.toLinearEquiv (o (f x))

theorem locallyConstant_neighborhood_of_eventually_eq {X Y : Type*} [TopologicalSpace X]
    (S : Opens X) (x : S) (g : S → Y) (h : ∀ᶠ y in 𝓝 x, g y = g x) :
    ∃ U : Opens X, ∃ hU : (U : Set X) ⊆ S,
      x.val ∈ U ∧ IsLocallyConstant (fun y : U => g ⟨y.val, hU y.property⟩) := by
  obtain ⟨W, hW, hWopen, hxW⟩ := mem_nhds_iff.mp h
  let U : Opens X := ⟨Subtype.val '' W, S.isOpen.isOpenMap_subtype_val W hWopen⟩
  have hU : (U : Set X) ⊆ S := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  refine ⟨U, hU, ⟨x, hxW, rfl⟩, ?_⟩
  have he : (fun y : U => g ⟨y.val, hU y.property⟩) = Function.const U (g x) := by
    funext y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact hW hz
  rw [he]
  exact IsLocallyConstant.const _

def orientationPullbackChartDomain (f : M → N) (hf : ContMDiff I J ∞ f) (p : M) : Opens M :=
  ⟨(chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source,
    (chartAt H p).open_source.inter ((chartAt K (f p)).open_source.preimage hf.continuous)⟩

def orientationPullbackChartPoint (f : M → N) (hf : ContMDiff I J ∞ f) (p : M) :
    orientationPullbackChartDomain I J f hf p :=
  ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩

def orientationPullbackTargetRepresentation (f : M → N) (hf : ContMDiff I J ∞ f)
    (o : SmoothOrientation J N) (p : M)
    (x : orientationPullbackChartDomain I J f hf p) :
    Orientation ℝ F (Fin (Module.finrank ℝ F)) :=
  Orientation.map _ (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv
    (o.val (f x.val))

private def orientationPullbackTargetPoint (f : M → N) (hf : ContMDiff I J ∞ f) (p : M) :
    orientationPullbackChartDomain I J f hf p → (chartAt K (f p)).source :=
  fun x => ⟨f x.val, x.property.2⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [IsManifold J ∞ N] in
private theorem orientationPullbackTargetPoint_continuous (f : M → N)
    (hf : ContMDiff I J ∞ f) (p : M) :
    Continuous (orientationPullbackTargetPoint I J f hf p) :=
  (hf.continuous.comp continuous_subtype_val).subtype_mk _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem orientationPullbackTargetRepresentation_eq (f : M → N)
    (hf : ContMDiff I J ∞ f) (o : SmoothOrientation J N) (p : M) :
    orientationPullbackTargetRepresentation I J f hf o p =
      (fun y : (chartAt K (f p)).source =>
        Orientation.map _ (preferredChartTangentEquiv J (f p) y.val y.property).toLinearEquiv
          (o.val y.val)) ∘ orientationPullbackTargetPoint I J f hf p := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem orientationPullbackTargetRepresentation_locallyConstant (f : M → N)
    (hf : ContMDiff I J ∞ f) (o : SmoothOrientation J N) (p : M) :
    IsLocallyConstant (orientationPullbackTargetRepresentation I J f hf o p) := by
  rw [orientationPullbackTargetRepresentation_eq]
  exact (o.property (f p)).comp_continuous (orientationPullbackTargetPoint_continuous I J f hf p)

omit [FiniteDimensional ℝ F] in
theorem inverseOrientationField_eventually_eq {X : Type*} [TopologicalSpace X]
    (e : X → E ≃L[ℝ] F) (x : X)
    (he : ContinuousAt (fun y => (e y : E →L[ℝ] F)) x)
    (o : X → Orientation ℝ F (Fin (Module.finrank ℝ F))) (ho : IsLocallyConstant o) :
    ∀ᶠ y in 𝓝 x, tangentOrientationEquiv (e y).symm.toLinearEquiv (o y) =
      tangentOrientationEquiv (e x).symm.toLinearEquiv (o x) := by
  filter_upwards [ho.eventually_eq x,
    tangentOrientationEquiv_symm_eventually_eq e x he (o x)] with y hy heq
  rw [hy]
  exact heq

theorem pullbackTangentOrientation_eventually_eq (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : ∀ x : M, Bijective (mfderiv I J f x))
    (o : SmoothOrientation J N) (p : M) :
    let S := orientationPullbackChartDomain I J f hf p
    let pS := orientationPullbackChartPoint I J f hf p
    let g : S → Orientation ℝ E (Fin (Module.finrank ℝ E)) := fun x =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv
        (pullbackTangentOrientation I J f hbij o.val x.val)
    ∀ᶠ x in 𝓝 pS, g x = g pS := by
  intro S pS g
  let C : S → E ≃L[ℝ] F := coordinateDifferentialEquiv I J f hbij p
  have hc : ContinuousAt (fun x : S => (C x : E →L[ℝ] F)) pS :=
    continuousAt_coordinateDifferentialEquiv I J f hf hbij p
  have hevent := inverseOrientationField_eventually_eq C pS hc
    (orientationPullbackTargetRepresentation I J f hf o p)
    (orientationPullbackTargetRepresentation_locallyConstant I J f hf o p)
  filter_upwards [hevent] with x hx
  exact (coordinateDifferentialEquiv_orientation_pullback I J f hbij p x (o.val (f x.val))).symm.trans
    (hx.trans (coordinateDifferentialEquiv_orientation_pullback I J f hbij p pS (o.val (f p))))

theorem pullbackTangentOrientation_localRepresentations (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : ∀ x : M, Bijective (mfderiv I J f x))
    (o : SmoothOrientation J N) (p : M) :
    ∃ U : Opens M, ∃ hU : (U : Set M) ⊆ (chartAt H p).source,
      p ∈ U ∧ IsLocallyConstant (fun y : U =>
        Orientation.map _ (preferredChartTangentEquiv I p y.val (hU y.property)).toLinearEquiv
          (pullbackTangentOrientation I J f hbij o.val y.val)) := by
  let S : Opens M := ⟨(chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source,
    (chartAt H p).open_source.inter ((chartAt K (f p)).open_source.preimage hf.continuous)⟩
  let pS : S := ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩
  let g : S → Orientation ℝ E (Fin (Module.finrank ℝ E)) := fun x =>
    Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv
      (pullbackTangentOrientation I J f hbij o.val x.val)
  have h : ∀ᶠ x in 𝓝 pS, g x = g pS := pullbackTangentOrientation_eventually_eq I J f hf hbij o p
  obtain ⟨U, hU, hpU, hg⟩ := locallyConstant_neighborhood_of_eventually_eq S pS g h
  exact ⟨U, fun y hy => (hU hy).1, hpU, hg⟩

def pullbackSmoothOrientation (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) :
    SmoothOrientation I M :=
  smoothOrientationOfLocalRepresentations I (pullbackTangentOrientation I J f hbij o.val)
    (pullbackTangentOrientation_localRepresentations I J f hf hbij o)

theorem pullbackSmoothOrientation_apply (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) (x : M) :
    (pullbackSmoothOrientation I J f hf hbij o).val x =
      tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x).symm.toLinearEquiv
        (o.val (f x)) := rfl
end DifferentialGeometry.Topology.Manifold
