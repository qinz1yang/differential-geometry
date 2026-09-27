import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.VectorField.Index
import DifferentialGeometry.Topology.LocalDegree.Negation

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]

def interiorIndex (V : ∀ x : M, TangentSpace I x) (x : M)
    (hV : HasContinuousIsolatedZero I V x) (hx : I.IsInteriorPoint x) : ℤ :=
  DifferentialGeometry.LocalDegree.euclideanLocalDegree
    (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (DifferentialGeometry.Manifold.interiorChart I 1 x).symm V)
    (DifferentialGeometry.Manifold.interiorChart I 1 x x)
    (hV.in_coordinates I (DifferentialGeometry.Manifold.interiorChart I 1 x) le_rfl
      ((DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx))

theorem interiorIndex_eq_in_coordinates
    {V : ∀ x : M, TangentSpace I x} {x : M} (hV : HasContinuousIsolatedZero I V x)
    (hx : I.IsInteriorPoint x)
    (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 1) (hcx : x ∈ c.source) :
    interiorIndex I V x hV hx = DifferentialGeometry.LocalDegree.euclideanLocalDegree
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (c x)
      (hV.in_coordinates I c le_rfl hcx) :=
  localDegree_in_coordinates_eq I hV (DifferentialGeometry.Manifold.interiorChart I 1 x) c
    ((DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx) hcx


theorem interiorIndex_eq_index [I.Boundaryless]
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) (hx : I.IsInteriorPoint x) :
    interiorIndex I V x hV hx = index I V x hV :=
  (index_eq_in_coordinates I hV (DifferentialGeometry.Manifold.interiorChart I 1 x)
    ((DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx)).symm

theorem interiorIndex_eq_localDegree
    {V : ∀ x : M, TangentSpace I x}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    {a : EuclideanSpace ℝ (Fin (d + 1))} (ha : a ∈ f.source)
    (hV : HasContinuousIsolatedZero I V (f a)) :
    interiorIndex I V (f a) hV
        (DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I 1 f one_ne_zero ha) =
      DifferentialGeometry.LocalDegree.euclideanLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a
        (hV.model_pullback I f le_rfl ha) := by
  have hh := interiorIndex_eq_in_coordinates I hV
    (DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I 1 f one_ne_zero ha)
    f.symm (f.map_source ha)
  change interiorIndex I V (f a) hV _ = DifferentialGeometry.LocalDegree.euclideanLocalDegree
    (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V)
    (f.toPartialEquiv.symm (f a)) _ at hh
  simpa only [f.left_inv ha] using hh

theorem interiorIndex_generator
    {V : ∀ x : M, TangentSpace I x} {x : M} (hV : HasContinuousIsolatedZero I V x)
    (hx : I.IsInteriorPoint x)
    (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 1) (hcx : x ∈ c.source)
    {R : ℝ} (hR : DifferentialGeometry.LocalDegree.IsolatingRadius
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) (c x) R)
    (r : Ioc (0 : ℝ) R) :
    DifferentialGeometry.Homology.reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (DifferentialGeometry.LocalDegree.sphereMap
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V)
        (c x) R hR.continuousOn hR.nonzero r)) d (DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator d) =
      interiorIndex I V x hV hx • DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator d := by
  rw [interiorIndex_eq_in_coordinates I hV hx c hcx]
  exact DifferentialGeometry.LocalDegree.euclideanLocalDegree_generator _ hR r

theorem interiorIndex_neg {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) (hx : I.IsInteriorPoint x) :
    interiorIndex I (-V) x (hV.neg I) hx =
      (-1 : ℤ) ^ (d + 1) * interiorIndex I V x hV hx := by
  let c := DifferentialGeometry.Manifold.interiorChart I 1 x
  have hcx : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx
  have h := hV.in_coordinates I c le_rfl hcx
  have hn := (hV.neg I).in_coordinates I c le_rfl hcx
  rw [interiorIndex_eq_in_coordinates I (hV.neg I) hx c hcx,
    interiorIndex_eq_in_coordinates I hV hx c hcx]
  have he : _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm (-V) =ᶠ[𝓝 (c x)]
        (fun y => -_root_.VectorField.mpullback
          𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V y) :=
    Filter.Eventually.of_forall (fun _ => _root_.VectorField.mpullback_neg_apply)
  exact (DifferentialGeometry.LocalDegree.euclideanLocalDegree_congr hn
    (DifferentialGeometry.LocalDegree.isolatedZero_neg h) he).trans
      (DifferentialGeometry.LocalDegree.euclideanLocalDegree_neg h)

end DifferentialGeometry.VectorField
