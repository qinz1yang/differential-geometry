import DifferentialGeometry.Geometry.Comparison.Volume.PointedLimitAVR
import DifferentialGeometry.Geometry.Comparison.Volume.PointedRicci

set_option autoImplicit false

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem capturedPointedLimit_noncompact_ricciNonnegative_avrLower
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Phi)
    (capture : CapturesSourceBalls (I := I) X L subseq Phi)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (_hsourceNoncompact : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      NoncompactSpace (X.obj i).M)
    (_hlimitComplete : MetricComplete (I := I) L)
    (_hlimitConnected :
      letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M)
    (_hDim : 2 ≤ Module.finrank ℝ E)
    (hRic : ∀ i : ℕ,
      let Y := X.obj i
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      RicciBoundedBelow (I := I) Y.metric 0)
    {v : ℝ} (hv : 0 < v)
    (hAVR : ∀ i : ℕ, ENNReal.ofReal v ≤
      pointedAsymptoticVolumeRatio (I := I) (X.obj i)) :
    (letI : TopologicalSpace L.M := L.topology;
      NoncompactSpace L.M) ∧
      (letI : TopologicalSpace L.M := L.topology
       letI : ChartedSpace H L.M := L.charted
       letI : IsManifold I ∞ L.M := L.smooth
       letI : T2Space L.M := L.t2
       letI : SigmaCompactSpace L.M := L.sigmaCompact
       RicciBoundedBelow (I := I) L.metric 0) ∧
      ENNReal.ofReal v ≤ pointedAsymptoticVolumeRatio (I := I) L := by
  have hvolume :=
    pointedAsymptoticVolumeRatio_lower_and_noncompact_of_source_AVR_real
      (I := I) C capture hcomplete hconnected hv hAVR
  have hcurvature :=
    ricciNonnegative_of_canonicalPointedLimit (I := I) C hRic
  exact ⟨hvolume.1, hcurvature, hvolume.2⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
