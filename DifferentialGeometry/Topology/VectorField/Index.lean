import DifferentialGeometry.Topology.VectorField.ContinuousIsolatedZero
import DifferentialGeometry.Topology.LocalDegree.CoordinateInvariance
import DifferentialGeometry.Topology.LocalDegree.EuclideanLinearization

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]

omit [IsManifold I 1 M] in
private theorem model_mpullback_congr
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → M}
    (V : ∀ x : M, TangentSpace I x) {a : EuclideanSpace ℝ (Fin (d + 1))}
    (h : f =ᶠ[𝓝 a] g) :
    _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V a =
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I g V a := by
  unfold _root_.VectorField.mpullback
  erw [h.mfderiv_eq, h.eq_of_nhds]

omit [IsManifold I 1 M] in
private theorem model_mpullback_comp
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {g : EuclideanSpace ℝ (Fin (d + 1)) → M}
    (V : ∀ x : M, TangentSpace I x) {a : EuclideanSpace ℝ (Fin (d + 1))}
    (hf : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) f a)
    (hg : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I g (f a))
    (hi : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I g (f a)).IsInvertible) :
    _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I (g ∘ f) V a =
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) f
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I g V) a := by
  simp only [_root_.VectorField.mpullback, mfderiv_comp _ hg hf, Function.comp_apply]
  exact hi.inverse_comp_apply_of_left

theorem localDegree_in_coordinates_eq
    {V : ∀ x : M, TangentSpace I x} {x : M} (hV : HasContinuousIsolatedZero I V x)
    (c e : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 1) (hcx : x ∈ c.source) (hex : x ∈ e.source) :
    Poincare.LocalDegree.euclideanLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (c x)
        (hV.in_coordinates I c le_rfl hcx) =
      Poincare.LocalDegree.euclideanLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e.symm V) (e x)
        (hV.in_coordinates I e le_rfl hex) := by
  let f := e.symm.trans c
  have hxf : e x ∈ f.source := by
    refine ⟨e.map_source hex, ?_⟩
    change e.toPartialEquiv.symm (e x) ∈ c.source
    rw [e.left_inv hex]
    exact hcx
  have hcenter : f (e x) = c x := congrArg c (e.left_inv hex)
  have hmap : (c.symm ∘ f : EuclideanSpace ℝ (Fin (d + 1)) → M) =ᶠ[𝓝 (e x)] e.symm := by
    filter_upwards [f.open_source.mem_nhds hxf] with y hy
    exact c.left_inv hy.2
  have hfields :
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e.symm V =ᶠ[𝓝 (e x)]
        _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) f
          (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) := by
    filter_upwards [hmap.eventuallyEq_nhds, f.open_source.mem_nhds hxf] with y hy hys
    exact (model_mpullback_congr I V hy).symm.trans
      (model_mpullback_comp I V (f.mdifferentiableAt one_ne_zero hys)
        (c.symm.mdifferentiableAt one_ne_zero (c.map_source hys.2))
        (isInvertible_mfderiv_partialDiffeomorph c.symm one_ne_zero (c.map_source hys.2)))
  have hc := hV.in_coordinates I c le_rfl hcx
  have he := hV.in_coordinates I e le_rfl hex
  have hcf : Poincare.LocalDegree.isolatedZero
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (f (e x)) :=
    hcenter.symm ▸ hc
  have hp := Poincare.LocalDegree.isolatedZero_mpullback_partialDiffeomorph f le_rfl hxf hcf
  have hdegree := Poincare.LocalDegree.euclideanLocalDegree_mpullback_partialDiffeomorph f le_rfl hxf hcf
  have hsame := Poincare.LocalDegree.euclideanLocalDegree_congr he hp hfields
  exact (hsame.trans (by simpa only [hcenter] using hdegree)).symm

variable [I.Boundaryless]

def indexChart (x : M) : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
    (EuclideanSpace ℝ (Fin (d + 1))) 1 where
  toPartialEquiv := extChartAt I x
  open_source := (chartAt H x).isOpen_extend_source
  open_target := (chartAt H x).isOpen_extend_target
  contMDiffOn_toFun := by simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x


@[simp]
theorem indexChart_source (x : M) : (indexChart I x).source = (chartAt H x).source :=
  extChartAt_source I x

def index (V : ∀ x : M, TangentSpace I x) (x : M) (hV : HasContinuousIsolatedZero I V x) : ℤ :=
  Poincare.LocalDegree.euclideanLocalDegree
    (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I (indexChart I x).symm V)
    (indexChart I x x)
    (hV.in_coordinates I (indexChart I x) le_rfl (by simp))


theorem index_eq_in_coordinates
    {V : ∀ x : M, TangentSpace I x} {x : M} (hV : HasContinuousIsolatedZero I V x)
    (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 1) (hx : x ∈ c.source) :
    index I V x hV = Poincare.LocalDegree.euclideanLocalDegree
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (c x)
      (hV.in_coordinates I c le_rfl hx) :=
  localDegree_in_coordinates_eq I hV (indexChart I x) c (by simp) hx

theorem index_eq_localDegree
    {V : ∀ x : M, TangentSpace I x}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    {a : EuclideanSpace ℝ (Fin (d + 1))} (ha : a ∈ f.source)
    (hV : HasContinuousIsolatedZero I V (f a)) :
    index I V (f a) hV = Poincare.LocalDegree.euclideanLocalDegree
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a
      (hV.model_pullback I f le_rfl ha) := by
  have hh := index_eq_in_coordinates I hV f.symm (f.map_source ha)
  change index I V (f a) hV = Poincare.LocalDegree.euclideanLocalDegree
    (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V)
    (f.toPartialEquiv.symm (f a)) _ at hh
  simpa only [f.left_inv ha] using hh

theorem index_generator
    {V : ∀ x : M, TangentSpace I x} {x : M} (hV : HasContinuousIsolatedZero I V x)
    (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 1) (hx : x ∈ c.source)
    {R : ℝ} (hR : Poincare.LocalDegree.IsolatingRadius
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (c x) R)
    (r : Ioc (0 : ℝ) R) :
    Poincare.Homology.reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (Poincare.LocalDegree.sphereMap
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (c x) R
        hR.continuousOn hR.nonzero r)) d (Poincare.LocalDegree.euclideanSphereTopGenerator d) =
      index I V x hV • Poincare.LocalDegree.euclideanSphereTopGenerator d := by
  rw [index_eq_in_coordinates I hV c hx]
  exact Poincare.LocalDegree.euclideanLocalDegree_generator _ hR r

theorem index_eq_linear_of_hasFDerivAt
    {V : ∀ x : M, TangentSpace I x}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    {a : EuclideanSpace ℝ (Fin (d + 1))} (ha : a ∈ f.source)
    (hV : HasContinuousIsolatedZero I V (f a))
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hd : HasFDerivAt (_root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) A.toContinuousLinearMap a) :
    index I V (f a) hV = Poincare.LocalDegree.euclideanSphereDegree
      (Poincare.LocalDegree.linearSphereMap A) := by
  have h := hV.model_pullback I f le_rfl ha
  have hR := h.choose_spec
  rw [index_eq_localDegree I f ha hV]
  exact Poincare.LocalDegree.euclideanLocalDegree_eq_linear_of_hasFDerivAt A
    (Metric.closedBall_mem_nhds _ hR.pos) hR.continuousOn hR.zero hd h

end Poincare.VectorField
