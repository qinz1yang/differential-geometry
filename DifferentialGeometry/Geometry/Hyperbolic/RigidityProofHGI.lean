import DifferentialGeometry.Geometry.Hyperbolic.Rigidity
import DifferentialGeometry.Geometry.Hyperbolic.MostowRigidity
import DifferentialGeometry.Geometry.Hyperbolic.IsometryDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Topology.Homotopy.Equiv

/-!
# `mostow_prasad` proved: twin of the W8 skeleton theorem (S-HG-INTAKE, suffix `_HGI`)

`mostow_prasad_HGI` has the statement of `DifferentialGeometry.Geometry.Hyperbolic.mostow_prasad`
(formerly the retained declaration in `Rigidity.lean`) and the proof of the donor branch
`codex/della-mostow-smooth-adapter-20261004` (`Geometry/Hyperbolic/Rigidity.lean`, byte-for-byte
modulo: the `hasConstantSectionalCurvature` definition is imported from `Rigidity` instead of
re-declared, and the private helper and the theorem carry the suffix `_HGI`).
The retained declaration has been removed; the explicit original contract below checks this adapter.
-/

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem curvature_identity_of_constant_sectional_curvature_HGI
    (g : SmoothRiemannianMetric (𝓡 3) M) (K : ℝ)
    (hg : hasConstantSectionalCurvature g K)
    (p : M) (v w : TangentSpace (𝓡 3) p) :
    Curvature.metricRm04StandardAt g p v w w v =
      K * (g.inner p v v * g.inner p w w - g.inner p v w * g.inner p v w) := by
  by_cases hvw : LinearIndependent ℝ ![v, w]
  · have hd := Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g p v w hvw
    have hk := hg p v w hvw
    rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div] at hk
    have hd' : g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 ≠ 0 := by
      simpa only [Riemannian.sectionalCurvatureDenominator_def] using ne_of_gt hd
    simpa only [pow_two] using (div_eq_iff hd').mp hk
  · rw [Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent g p v w hvw]
    have hd : Riemannian.sectionalCurvatureDenominator g p v w = 0 := by
      apply le_antisymm _ (Riemannian.sectionalCurvatureDenominator_nonneg g p v w)
      apply le_of_not_gt
      intro hpos
      exact hvw (Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
        g p v w hpos)
    rw [Riemannian.sectionalCurvatureDenominator_def, pow_two] at hd
    rw [hd, mul_zero]

theorem mostow_prasad_HGI
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (h : SmoothRiemannianMetric (𝓡 3) N)
    (K : ℝ) (hK : K < 0)
    (hgcurvature : hasConstantSectionalCurvature g K)
    (hhcurvature : hasConstantSectionalCurvature h K)
    (hgcomplete : RiemannianMetricComplete g)
    (hhcomplete : RiemannianMetricComplete h)
    (hgvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hhvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤)
    (u : ContinuousMap.HomotopyEquiv M N) :
    ∃! f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N,
      (∀ (p : M) (v w : TangentSpace (𝓡 3) p),
        h.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v)
          (mfderiv (𝓡 3) (𝓡 3) f p w) = g.inner p v w) ∧
      (⟨f, f.continuous⟩ : C(M, N)).Homotopic u.toFun := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  have hg := curvature_identity_of_constant_sectional_curvature_HGI g K hgcurvature
  have hh := curvature_identity_of_constant_sectional_curvature_HGI h K hhcurvature
  obtain ⟨a, ha, hunique⟩ := DifferentialGeometry.mostow_prasad_rigidity
    g h K u hK hgcomplete hhcomplete hgvolume hhvolume hg hh
  obtain ⟨f, hfa, hfmetric⟩ :=
    exists_diffeomorph_eq_isometryEquiv_of_constant_negative_curvature
      g h K hK hgcomplete hhcomplete hg hh a
  have hfa' : (⟨f, f.continuous⟩ : C(M, N)) = (a : C(M, N)) := by
    ext x
    exact hfa x
  refine ⟨f, ⟨hfmetric, ?_⟩, ?_⟩
  · rw [hfa']
    exact ha.symm
  · intro b hb
    have hmetric : Diffeomorph.pullbackMetricCross h b = g := by
      apply SmoothRiemannianMetric.ext_inner
      intro p v w
      rw [Diffeomorph.pullbackMetricCross_inner]
      exact hb.1 p v w
    let b' : M ≃ᵢ N := {
      b.toEquiv with
      isometry_toFun := fun x y => by
        change riemannianEDistOf h (b x) (b y) = riemannianEDistOf g x y
        rw [← Metric.edistOf_pullbackMetricCross h b, hmetric] }
    have hb' : u.toFun.Homotopic (b' : C(M, N)) := hb.2.symm
    have hba : b' = a := hunique b' hb'
    apply Diffeomorph.ext
    intro x
    exact (congrArg (fun e : M ≃ᵢ N => e x) hba).trans (hfa x).symm

universe u v

/-- The proved adapter satisfies the original smooth Mostow–Prasad contract explicitly. -/
example {M : Type u} {N : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (h : SmoothRiemannianMetric (𝓡 3) N)
    (K : ℝ) (hK : K < 0)
    (hgcurvature : hasConstantSectionalCurvature g K)
    (hhcurvature : hasConstantSectionalCurvature h K)
    (hgcomplete : RiemannianMetricComplete g)
    (hhcomplete : RiemannianMetricComplete h)
    (hgvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hhvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤)
    (u : ContinuousMap.HomotopyEquiv M N) :
    ∃! f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N,
      (∀ (p : M) (v w : TangentSpace (𝓡 3) p),
        h.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v)
          (mfderiv (𝓡 3) (𝓡 3) f p w) = g.inner p v w) ∧
      (⟨f, f.continuous⟩ : C(M, N)).Homotopic u.toFun :=
  mostow_prasad_HGI g h K hK hgcurvature hhcurvature hgcomplete hhcomplete
    hgvolume hhvolume u

end DifferentialGeometry.Geometry.Hyperbolic
