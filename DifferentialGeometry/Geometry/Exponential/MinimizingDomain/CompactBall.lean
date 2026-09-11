import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Basic
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.RadialSurjectivity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open VolumeComparison (gBall)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

theorem image_expMap_minimizingDomain_inter_gBall
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (R : ℝ)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R))) :
    (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) ''
        (minimizingDomain (I := I) g p ∩ gBall (I := I) g p R) =
      {q : M | riemannianEDist I p q < ENNReal.ofReal R} := by
  let : T2Space M := gauss_t2Space_base I
  ext q
  constructor
  · rintro ⟨v, ⟨hv, hvr⟩, rfl⟩
    change riemannianEDist I p (expMap (I := I) g p
      (show TangentSpace I p from v)) < ENNReal.ofReal R
    have hvnorm : ENNReal.ofReal (Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v))) =
        riemannianEDist I p (expMap (I := I) g p
          (show TangentSpace I p from v)) := hv
    rw [← hvnorm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).mpr hvr
  · intro hq
    cases subsingleton_or_nontrivial E with
    | inl h =>
      let _ : Subsingleton H := I.injective.subsingleton
      let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
      obtain ⟨γ, hγ0, hγ1, hγsmooth, _⟩ := exists_lt_of_riemannianEDist_lt hq
      have hpq : p = q := by
        rw [← hγ0, ← hγ1]
        exact isPreconnected_Icc.constant hγsmooth.continuousOn
          (by simp) (by simp)
      cases hpq
      change riemannianEDist I p p < ENNReal.ofReal R at hq
      rw [riemannianEDist_self] at hq
      have hR : 0 < R := ENNReal.ofReal_pos.mp hq
      refine ⟨0, ⟨zero_mem_minimizingDomain (I := I) g p, ?_⟩, expMap_zero (I := I) g p⟩
      change Real.sqrt (g.inner p (0 : TangentSpace I p) 0) < R
      simpa using hR
    | inr h =>
      let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
      obtain ⟨v, _, hvexp, hvlen⟩ :=
        RadialSurjectivity.minExp_of_cptBall (I := I) g hEnorm p q hq hcpt
      refine ⟨v, ⟨?_, ?_⟩, hvexp⟩
      · subst q
        exact hvlen
      · exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (Real.sqrt_nonneg _)).mp (hvlen.trans_lt hq)

end DifferentialGeometry.Geometry.Riemannian.Exponential
