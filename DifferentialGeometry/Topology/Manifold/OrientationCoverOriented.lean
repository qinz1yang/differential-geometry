import DifferentialGeometry.Topology.Manifold.OrientationCoverCanonical
import DifferentialGeometry.Topology.Manifold.CoveringTangentAtlas



noncomputable section
open Bundle Manifold Set Filter
open scoped Topology Manifold ContDiff
open DifferentialGeometry.VectorBundle

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
attribute [local instance] orientationTopology
local instance : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩

theorem tangentOrientationCanonical_chart (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    ∀ (x y : tangentOrientationCover (M := M) hdim)
      (hy : y ∈ (chartAt E x).source)
      (_hb : y.proj ∈ (chartAt E x.proj).source),
      Orientation.map (Fin n)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt
           ℝ y hy).toLinearEquiv
        (tangentOrientationCanonical hdim y) =
      (((orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim).localTriv (achart E x.proj)) y).2 := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  intro x y hy hb
  let P := ((tangentOrientationProjection_isLocalDiffeomorph hdim).mfderivToContinuousLinearEquiv
     (by decide) y).toLinearEquiv
  let A := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt
     ℝ y hy).toLinearEquiv
  let B := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x.proj).continuousLinearEquivAt
     ℝ y.proj hb).toLinearEquiv
  have hcomp : P.trans B = A := by
    ext v
    exact (covering_tangent_trivialization
      (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph x y hy hb v).symm
  change Orientation.map (Fin n) A (tangentOrientationCanonical hdim y) = _
  rw [← hcomp]
  exact (map_orientation_trans_between P B (tangentOrientationCanonical hdim y)).symm.trans
    ((congrArg (Orientation.map (Fin n) B) (tangentOrientationCanonical_projects hdim y)).trans
      (tangentOrientation_chart hdim x.proj y.proj hb y.snd).2.symm)

theorem tangentOrientationCanonical_compatible (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    letI := tangentOrientation_isManifold (M := M) hdim
    IsCompatibleOrientation (F := E)
      (TangentSpace 𝓘(ℝ, E) : tangentOrientationCover (M := M) hdim → Type _)
      (tangentOrientationCanonical hdim) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  intro x
  let T := (orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim).localTriv (achart E x.proj)
  have hxT : x ∈ T.source := mem_chart_source E x.proj
  have hlabel : ∀ᶠ y in 𝓝 x, (T y).2 = (T x).2 :=
    (T.continuousAt hxT).snd.eventually
      ((isOpen_discrete {(T x).2}).mem_nhds rfl)
  let U := (chartAt E x).source ∩ {y | (T y).2 = (T x).2}
  have hUx : U ∈ 𝓝 x := inter_mem
    ((chartAt E x).open_source.mem_nhds (mem_chart_source E x)) hlabel
  refine ⟨trivializationAt E (TangentSpace 𝓘(ℝ, E)) x, inferInstance, U, hUx,
    (fun y hy => hy.1), (T x).2, ?_⟩
  intro y hy
  have hb : y.proj ∈ (chartAt E x.proj).source := by
    simpa only [OpenPartialHomeomorph.symm_symm, IsLocalHomeomorph.localInverseAt_symm,
      Set.mem_preimage, tangentOrientationProjection] using hy.1.2
  exact (tangentOrientationCanonical_chart hdim x y hy.1 hb).trans hy.2

end DifferentialGeometry.Topology.Manifold
