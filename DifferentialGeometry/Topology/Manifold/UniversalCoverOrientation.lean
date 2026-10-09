import DifferentialGeometry.Bundle.Orientation.CompatibleSection
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckIsometry
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.VectorBundle

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

attribute [local instance] orientationTopology
local instance universalOrientationDiscreteTopology : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCover_tangent_trivialization (x y : UniversalCover M)
    (hy : y ∈ (chartAt E x).source)
    (hb : UniversalCover.proj y ∈ (chartAt E (UniversalCover.proj x)).source)
    (v : TangentSpace 𝓘(ℝ, E) y) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ y hy v =
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (UniversalCover.proj x)).continuousLinearEquivAt
        ℝ (UniversalCover.proj y) hb (v : E) := by
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hy,
    Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hb,
    TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.continuousLinearMapAt_trivializationAt hb]
  have heq : (extChartAt 𝓘(ℝ, E) x : UniversalCover M → E) =
      extChartAt 𝓘(ℝ, E) (UniversalCover.proj x) ∘ UniversalCover.proj :=
    funext (UniversalCover.extChartAt_proj_eq (I := 𝓘(ℝ, E)) x)
  rw [heq]
  have hc := mfderiv_comp_apply y (mdifferentiableAt_extChartAt hb)
    (UniversalCover.hasMFDerivAt_proj (I := 𝓘(ℝ, E)) y).mdifferentiableAt v
  rw [(UniversalCover.hasMFDerivAt_proj (I := 𝓘(ℝ, E)) y).mfderiv] at hc
  exact hc

def universalCoverOrientation
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (z : UniversalCover M) : Orientation ℝ (TangentSpace 𝓘(ℝ, E) z) (Fin n) :=
  (o (UniversalCover.proj z) : Orientation ℝ E (Fin n))

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCoverOrientation_projects
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n)) (z : UniversalCover M) :
    Orientation.map (Fin n)
      ((UniversalCover.proj_localDiffeo (I := 𝓘(ℝ, E))).mfderivToContinuousLinearEquiv
        (by decide) z).toLinearEquiv (universalCoverOrientation o z) = o (UniversalCover.proj z) := by
  have hD : ((UniversalCover.proj_localDiffeo (I := 𝓘(ℝ, E))).mfderivToContinuousLinearEquiv
      (by decide) z).toLinearEquiv = LinearEquiv.refl ℝ E := by
    ext v
    exact congrArg (fun D : E →L[ℝ] E => D v)
      (UniversalCover.hasMFDerivAt_proj (I := 𝓘(ℝ, E)) z).mfderiv
  rw [hD]
  change Orientation.map (Fin n) (LinearEquiv.refl ℝ E)
    (o (UniversalCover.proj z) : Orientation ℝ E (Fin n)) = o (UniversalCover.proj z)
  simp only [Orientation.map_refl]
  rfl

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCoverOrientation_compatible (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (ho : IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E) : UniversalCover M → Type _)
      (universalCoverOrientation o) := by
  let Z := tangentBundleCore 𝓘(ℝ, E) M
  let s : C(M, (orientationCore Z hdim).TotalSpace) :=
    ⟨fun x => ⟨x, o x⟩, continuous_section_of_compatibleOrientation Z hdim o ho⟩
  intro x
  let p : UniversalCover M → M := UniversalCover.proj
  let T := (orientationCore Z hdim).localTriv (achart E (p x))
  have hcont : ContinuousAt (fun y : UniversalCover M => (T (s (p y))).2) x :=
    ContinuousAt.comp (f := fun y : UniversalCover M => s (p y)) (x := x)
      (T.continuousAt (mem_chart_source E (p x))).snd
      (s.continuous.comp UniversalCover.proj_continuous).continuousAt
  have hlabel : ∀ᶠ y in 𝓝 x, (T (s (p y))).2 = (T (s (p x))).2 :=
    hcont.eventually ((isOpen_discrete {(T (s (p x))).2}).mem_nhds rfl)
  let U := (chartAt E x).source ∩ p ⁻¹' (chartAt E (p x)).source ∩
    {y | (T (s (p y))).2 = (T (s (p x))).2}
  have hU : U ∈ 𝓝 x := inter_mem (inter_mem
    ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
    (UniversalCover.proj_continuous.continuousAt
      ((chartAt E (p x)).open_source.mem_nhds (mem_chart_source E (p x))))) hlabel
  refine ⟨trivializationAt E (TangentSpace 𝓘(ℝ, E)) x, inferInstance, U, hU,
    (fun _ hy => hy.1.1), (T (s (p x))).2, ?_⟩
  intro y hy
  have hA : ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt
      ℝ y hy.1.1).toLinearEquiv =
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p x)).continuousLinearEquivAt
        ℝ (p y) hy.1.2).toLinearEquiv := by
    ext v
    exact universalCover_tangent_trivialization x y hy.1.1 hy.1.2 v
  rw [hA]
  exact (orientationCore_localTriv Z hdim (achart E (p x)) (p y) hy.1.2 (o (p y))).symm.trans hy.2

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCoverDeck_preserves_orientation
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (a : FundamentalGroup M (default : M)) (z : UniversalCover M) :
    Orientation.map (Fin n)
      ((UniversalCover.deckDiffeo (I := 𝓘(ℝ, E)) a).mfderivToContinuousLinearEquiv
        (by decide) z).toLinearEquiv (universalCoverOrientation o z) =
      universalCoverOrientation o (a • z) := by
  have hD : ((UniversalCover.deckDiffeo (I := 𝓘(ℝ, E)) a).mfderivToContinuousLinearEquiv
      (by decide) z).toLinearEquiv = LinearEquiv.refl ℝ E := by
    ext v
    exact congrArg (fun D : E →L[ℝ] E => D v)
      (UniversalCover.hasMFDerivAt_deck (I := 𝓘(ℝ, E)) a z).mfderiv
  rw [hD]
  change Orientation.map (Fin n) (LinearEquiv.refl ℝ E)
    (o (UniversalCover.proj z) : Orientation ℝ E (Fin n)) = o (UniversalCover.proj z)
  simp only [Orientation.map_refl]
  rfl

end DifferentialGeometry.Topology.Manifold
