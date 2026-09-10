import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem path_integral_subtype_val
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    {x y : U} (γ : Path x y) (hγ : CMDiff 1 γ) :
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      (g.inner ((γ.map continuous_subtype_val) t)
        (mfderiv% (γ.map continuous_subtype_val) t 1)
        (mfderiv% (γ.map continuous_subtype_val) t 1)))) =
    ∫⁻ t, ENNReal.ofReal (Real.sqrt
      ((g.restrictOpen U).inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
  apply lintegral_congr
  intro t
  have hc := mfderiv_comp t
    (hasMFDerivAt_subtype_val (I := I) U (γ t)).mdifferentiableAt
    (hγ.mdifferentiableAt one_ne_zero)
  change mfderiv% (γ.map continuous_subtype_val) t = _ at hc
  rw [hc, mfderiv_subtype_val]
  rfl

theorem riemannianEDistOf_le_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (x y : U) :
    riemannianEDistOf (I := I) g (x : M) (y : M) ≤
      riemannianEDistOf (I := I) (g.restrictOpen (I := I) U) x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun gamma => ?_
  refine le_iInf fun hgamma => ?_
  let gammaM : Path (x : M) (y : M) := gamma.map continuous_subtype_val
  have hgammaM : CMDiff 1 gammaM :=
    (contMDiff_subtype_val (I := I) (U := U)).comp hgamma
  refine iInf_le_of_le gammaM (iInf_le_of_le hgammaM ?_)
  exact le_of_eq (by
    simpa only [gammaM] using path_integral_subtype_val g U gamma hgamma)

theorem riemannianEDistOf_restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (hU : IsClosed (U : Set M)) (x y : U) :
    riemannianEDistOf (g.restrictOpen U) x y = riemannianEDistOf g (x : M) (y : M) := by
  rw [edistOf_iInf, edistOf_iInf]
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun hγ => ?_
    have hγU (t : unitInterval) : γ t ∈ U := by
      have hcomponent := γ.continuous.mapsTo_connectedComponent (0 : unitInterval)
      have ht : t ∈ connectedComponent (0 : unitInterval) := by simp
      have himage := hcomponent ht
      rw [γ.source] at himage
      exact (show IsClopen (U : Set M) from ⟨hU, U.isOpen⟩).connectedComponent_subset
        x.property himage
    let δ : Path x y :=
      ⟨⟨fun t => ⟨γ t, hγU t⟩, γ.continuous.subtype_mk _⟩,
        Subtype.ext γ.source, Subtype.ext γ.target⟩
    have hδ : CMDiff 1 δ := by
      intro t
      exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp (𝓡∂ 1) I 1) δ Set.univ t).mp (hγ t)
    refine iInf_le_of_le δ (iInf_le_of_le hδ ?_)
    have hmap : δ.map continuous_subtype_val = γ := by ext; rfl
    rw [← path_integral_subtype_val g U δ hδ, hmap]
  · refine le_iInf fun γ => le_iInf fun hγ => ?_
    have hm : CMDiff 1 (γ.map continuous_subtype_val) :=
      (contMDiff_subtype_val (I := I) (U := U)).comp hγ
    refine iInf_le_of_le (γ.map continuous_subtype_val) (iInf_le_of_le hm ?_)
    exact le_of_eq (path_integral_subtype_val g U γ hγ)

open Bundle

variable [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.restrictOpen
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete g)
    (U : TopologicalSpace.Opens M) (hU : IsClosed (U : Set M)) :
    letI : SigmaCompactSpace U := hU.sigmaCompactSpace
    RiemannianMetricComplete (g.restrictOpen U) := by
  let : SigmaCompactSpace U := hU.sigmaCompactSpace
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let mM := EMetricSpace.ofRiemannianMetric I M
  let : EMetricSpace M := mM
  let : CompleteSpace M := hg.complete
  let : RiemannianBundle (fun x : U => TangentSpace I x) :=
    ⟨(g.restrictOpen U).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x) :=
    ⟨⟨(g.restrictOpen U).inner, (g.restrictOpen U).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let mU := EMetricSpace.ofRiemannianMetric I U
  have hi : @Isometry U M mU.toPseudoEMetricSpace mM.toPseudoEMetricSpace
      (Subtype.val : U → M) := by
    intro x y
    change riemannianEDistOf g (x : M) (y : M) = riemannianEDistOf (g.restrictOpen U) x y
    exact (riemannianEDistOf_restrictOpen_of_isClosed g U hU x y).symm
  constructor
  change @CompleteSpace U mU.toUniformSpace
  have hui := @Isometry.isUniformInducing U M mU.toPseudoEMetricSpace
    mM.toPseudoEMetricSpace (Subtype.val : U → M) hi
  apply @IsUniformInducing.completeSpace U M mU.toUniformSpace mM.toUniformSpace
    (Subtype.val : U → M) hui
  change IsComplete (Set.range (Subtype.val : U → M))
  rw [Subtype.range_coe_subtype]
  exact hU.isComplete

end DifferentialGeometry
