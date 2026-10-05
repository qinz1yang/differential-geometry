import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
# Pulling an orientation back along a `C¹` map with invertible differential

Lane C14-SLIM-STD (review 70, disposition D70-3, route β). `pullbackSmoothOrientation`
(`SmoothOrientationPullback.lean`) asks the map to be `C^∞`, but the construction only uses the
continuity of the map and of its differential in coordinates. Here the same construction for a
`C¹` map `f : M → N` between smooth manifolds whose differential is bijective everywhere (a
finite-order local diffeomorphism), and the `ManifoldOrientation` form.

* `continuousAt_coordinateDifferentialEquiv_one_SSTD`: the differential in preferred coordinates
  is continuous for a `C¹` map.
* `pullbackTangentOrientation_localRepresentations_one_SSTD`: the pulled-back tangent orientation
  is locally constant in charts.
* `pullbackSmoothOrientationOne_SSTD`: the pulled-back `SmoothOrientation` (value: the pull-back
  of the given orientation by the differential, `pullbackSmoothOrientationOne_SSTD_apply`).
* `nonempty_manifoldOrientation_pullback_one_SSTD`: an orientation of `N` gives an orientation of
  `M` (`ManifoldOrientation`, same dimension).
-/

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

/-- The differential of a `C¹` map in preferred coordinates is continuous (the `C¹` form of
`continuousAt_coordinateDifferentialEquiv`). -/
theorem continuousAt_coordinateDifferentialEquiv_one_SSTD (f : M → N)
    (hf : ContMDiff I J 1 f) (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (p : M) :
    ContinuousAt (fun x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source) =>
      (coordinateDifferentialEquiv I J f hbij p x : E →L[ℝ] F))
        ⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩ := by
  have h : ContinuousAt (inTangentCoordinates I J id f (mfderiv I J f) p) p :=
    (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have h' := h.comp (continuous_subtype_val.continuousAt (x :=
    (⟨p, mem_chart_source H p, mem_chart_source K (f p)⟩ :
      ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source))))
  have he : (fun x : ↥((chartAt H p).source ∩ f ⁻¹' (chartAt K (f p)).source) =>
      (coordinateDifferentialEquiv I J f hbij p x : E →L[ℝ] F)) =
      (fun x => inTangentCoordinates I J id f (mfderiv I J f) p x.val) := by
    funext x
    exact coordinateDifferentialEquiv_eq I J f hbij p x
  rw [he]
  exact h'

/-- The pull-back of a smooth orientation of `N` by a `C¹` map with bijective differential is
locally constant in the charts of `M`. -/
theorem pullbackTangentOrientation_localRepresentations_one_SSTD (f : M → N)
    (hf : ContMDiff I J 1 f) (hbij : ∀ x : M, Bijective (mfderiv I J f x))
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
  let C : S → E ≃L[ℝ] F := coordinateDifferentialEquiv I J f hbij p
  have hc : ContinuousAt (fun x : S => (C x : E →L[ℝ] F)) pS :=
    continuousAt_coordinateDifferentialEquiv_one_SSTD I J f hf hbij p
  let tgt : S → Orientation ℝ F (Fin (Module.finrank ℝ F)) := fun x =>
    Orientation.map _ (preferredChartTangentEquiv J (f p) (f x.val) x.property.2).toLinearEquiv
      (o.val (f x.val))
  have htgt : IsLocallyConstant tgt :=
    (o.property (f p)).comp_continuous
      (f := fun x : S => (⟨f x.val, x.property.2⟩ : (chartAt K (f p)).source))
      ((hf.continuous.comp continuous_subtype_val).subtype_mk _)
  have h : ∀ᶠ x in 𝓝 pS, g x = g pS := by
    filter_upwards [inverseOrientationField_eventually_eq C pS hc tgt htgt] with x hx
    exact (coordinateDifferentialEquiv_orientation_pullback I J f hbij p x
      (o.val (f x.val))).symm.trans (hx.trans
        (coordinateDifferentialEquiv_orientation_pullback I J f hbij p pS (o.val (f p))))
  obtain ⟨U, hU, hpU, hg⟩ := locallyConstant_neighborhood_of_eventually_eq S pS g h
  exact ⟨U, fun y hy => (hU hy).1, hpU, hg⟩

/-- **The pull-back of a smooth orientation by a `C¹` map with bijective differential.** -/
def pullbackSmoothOrientationOne_SSTD (f : M → N) (hf : ContMDiff I J 1 f)
    (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) :
    SmoothOrientation I M :=
  smoothOrientationOfLocalRepresentations I (pullbackTangentOrientation I J f hbij o.val)
    (pullbackTangentOrientation_localRepresentations_one_SSTD I J f hf hbij o)

theorem pullbackSmoothOrientationOne_SSTD_apply (f : M → N) (hf : ContMDiff I J 1 f)
    (hbij : ∀ x : M, Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) (x : M) :
    (pullbackSmoothOrientationOne_SSTD I J f hf hbij o).val x =
      tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x).symm.toLinearEquiv
        (o.val (f x)) := rfl

/-- **Orientations pull back along `C¹` local diffeomorphisms**: if `f : M → N` is `C¹` with
bijective differential everywhere and `N` carries a `ManifoldOrientation` of dimension `n`
(`dim M = n`), then so does `M`. -/
theorem nonempty_manifoldOrientation_pullback_one_SSTD {n : ℕ} (f : M → N)
    (hf : ContMDiff I J 1 f) (hbij : ∀ x : M, Bijective (mfderiv I J f x))
    (oN : DifferentialGeometry.ManifoldOrientation J N n) (hE : Module.finrank ℝ E = n) :
    Nonempty (DifferentialGeometry.ManifoldOrientation I M n) := by
  have hF := oN.dimension_eq
  subst hF
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation I
    (pullbackSmoothOrientationOne_SSTD I J f hf hbij
      (smoothOrientationOfManifoldOrientation J oN))
  exact ⟨hE ▸ O⟩

end DifferentialGeometry.Topology.Manifold
