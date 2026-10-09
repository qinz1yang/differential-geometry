import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

def inclusionDifferentialEquiv (x : K) :
    let _ := C.toChartedSpace
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] E := by
  let _ := C.toChartedSpace
  exact Manifold.differentialEquivOfBijective (𝓡∂ n) I (Subtype.val : K → M)
    C.mfderiv_subtypeVal_bijective x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem inclusionDifferentialEquiv_apply (x : K) (v : EuclideanSpace ℝ (Fin n)) :
    let _ := C.toChartedSpace
    C.inclusionDifferentialEquiv x v = mfderiv (𝓡∂ n) I (Subtype.val : K → M) x v := rfl

private theorem orientation_cast_apply {a b : ℕ} (h : a = b)
    (O : ManifoldOrientation I M a) (x : M) :
    (cast (congrArg (fun k => ManifoldOrientation I M k) h) O).orientation x =
      Orientation.reindex ℝ (TangentSpace I x) (finCongr h) (O.orientation x) := by
  subst b
  change O.orientation x = Orientation.reindex ℝ (TangentSpace I x) (Equiv.refl _) _
  rw [Orientation.reindex_refl]
  rfl

private theorem exists_orientation_pullback
    (O : ManifoldOrientation I M n) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    ∃ OK : ManifoldOrientation (𝓡∂ n) K n,
      ∀ x : K, Orientation.map (Fin n) (C.inclusionDifferentialEquiv x).toLinearEquiv
        (OK.orientation x) = O.orientation x.val := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  have hE := O.dimension_eq
  have hF : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  let O' : ManifoldOrientation I M (Module.finrank ℝ E) :=
    cast (congrArg (fun k => ManifoldOrientation I M k) hE.symm) O
  have hO' (x : M) : O'.orientation x =
      Orientation.reindex ℝ (TangentSpace I x) (finCongr hE.symm) (O.orientation x) :=
    orientation_cast_apply hE.symm O x
  let s := Manifold.smoothOrientationOfManifoldOrientation I O'
  let t := Manifold.pullbackSmoothOrientation (𝓡∂ n) I (Subtype.val : K → M)
    C.contMDiff_subtype_val C.mfderiv_subtypeVal_bijective s
  obtain ⟨OK, hOK⟩ := Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ n) t
  let OK' : ManifoldOrientation (𝓡∂ n) K n :=
    cast (congrArg (fun k => ManifoldOrientation (𝓡∂ n) K k) hF) OK
  have hOK' (x : K) : OK'.orientation x =
      Orientation.reindex ℝ (TangentSpace (𝓡∂ n) x) (finCongr hF) (t.val x) := by
    rw [show OK'.orientation x = _ from orientation_cast_apply hF OK x]
    rw [congrFun hOK x]
  refine ⟨OK', ?_⟩
  intro x
  rw [hOK']
  change Orientation.map (Fin n) (C.inclusionDifferentialEquiv x).toLinearEquiv
    (Orientation.reindex ℝ (EuclideanSpace ℝ (Fin n)) (finCongr hF)
      (Manifold.tangentOrientationEquiv (C.inclusionDifferentialEquiv x).symm.toLinearEquiv
        (O'.orientation x.val))) = _
  rw [hO']
  exact Manifold.tangentOrientationEquiv_symm_reindex_map
    (C.inclusionDifferentialEquiv x).toLinearEquiv hF hE (O.orientation x.val)

def orientation (O : ManifoldOrientation I M n) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    ManifoldOrientation (𝓡∂ n) K n :=
  Classical.choose (C.exists_orientation_pullback O)

theorem orientation_map_inclusion (O : ManifoldOrientation I M n) (x : K) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    Orientation.map (Fin n) (C.inclusionDifferentialEquiv x).toLinearEquiv
      ((C.orientation O).orientation x) = O.orientation x.val :=
  Classical.choose_spec (C.exists_orientation_pullback O) x

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
