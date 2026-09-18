import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem IsSolutionOn.congr_metric
    {D : RealTimeInterval} {g h : ℝ → SmoothRiemannianMetric I M}
    (hg : IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M) D))
    (heq : EqOn g h D.carrier) :
    IsSolutionOn ({ base.metric := h } : SolutionOn (I := I) (M := M) D) := by
  have hscalar (t : ℝ) (ht : t ∈ D.carrier) (x : M) :
      metricScalarAt (g t) x = metricScalarAt (h t) x := by rw [heq ht]
  have hmetric : MetricFamilySmoothOn D h := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x v w
      exact (hg.smoothMetric.coeff x v w).congr (fun t ht => by rw [← heq (D.regular_subset ht)]; rfl)
    · intro x v w
      exact (hg.smoothMetric.coeff_cont x v w).congr (fun t ht => by rw [← heq ht]; rfl)
    · exact hg.smoothMetric.metricTensor_cont.congr (fun t ht x => by
        change Tensor0SBundle.metricTensorField (g t) x = Tensor0SBundle.metricTensorField (h t) x
        rw [heq ht])
    · intro Idx _ frame u hframe i j
      exact (hg.smoothMetric.frameCompSmooth frame hframe i j).congr
        (fun p hp => by rw [← heq (D.regular_subset hp.1)]; rfl)
  refine ⟨hmetric, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    have hm := hg.smoothConnection t
    change CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (h (t : ℝ))) ∞
    rw [← heq t.property]
    exact hm
  · intro t x v w
    have hx := hg.equation t x v w
    have ht : (t : ℝ) ∈ D.carrier := D.regular_subset t.property
    have hd : RicciAtFamily.toTensorField (I := I)
        ({ base.metric := g } : SolutionOn (I := I) (M := M) D).ricciAt t x v w =
        RicciAtFamily.toTensorField (I := I)
        ({ base.metric := h } : SolutionOn (I := I) (M := M) D).ricciAt t x v w := by
      change metricRicciAt (g t) x (vec2 v w) = metricRicciAt (h t) x (vec2 v w)
      rw [heq ht]
    rw [hd] at hx
    exact hx.congr (fun s hs => by change (h s).inner x v w = (g s).inner x v w; rw [heq hs])
      (by change (h t).inner x v w = (g t).inner x v w; rw [heq ht])
  · exact hg.scalarCont.congr (fun p hp => (hscalar p.1 hp.1 p.2).symm)
  · intro K t ht hK x
    exact (hg.scalarTime ht hK x).congr (fun s hs => (hscalar s (hK hs) x).symm)
      (hscalar t (hK ht) x).symm
  · exact hg.ricciCont.congr (fun t ht x => by
      change metricRicciAt (g t) x = metricRicciAt (h t) x
      rw [heq ht])
  · exact hg.rm04Cont.congr (fun t ht x => by
      change metricRm04At (g t) x = metricRm04At (h t) x
      rw [heq ht])
  · intro t ht x
    have he : ricciNorm ({ base.metric := g } : SolutionOn (I := I) (M := M) D) t =
        ricciNorm ({ base.metric := h } : SolutionOn (I := I) (M := M) D) t := by
      funext y
      change Tensor0SBundle.normSq0S (g t) y 2 (metricRicciAt (g t) y) =
        Tensor0SBundle.normSq0S (h t) y 2 (metricRicciAt (h t) y)
      rw [heq ht]
    rw [← he]
    exact hg.ricciNormSpace t ht x
  · intro t ht x
    have he : ricciNorm ({ base.metric := g } : SolutionOn (I := I) (M := M) D) t =
        ricciNorm ({ base.metric := h } : SolutionOn (I := I) (M := M) D) t := by
      funext y
      change Tensor0SBundle.normSq0S (g t) y 2 (metricRicciAt (g t) y) =
        Tensor0SBundle.normSq0S (h t) y 2 (metricRicciAt (h t) y)
      rw [heq ht]
    change MDifferentiableAt I I.tangent
      (fun y : M => (⟨y, DifferentialGeometry.Geometry.Operator.gradientFun (h t)
        (ricciNorm ({ base.metric := h } : SolutionOn (I := I) (M := M) D) t) y⟩ :
          TangentBundle I M)) x
    rw [← he, ← heq ht]
    exact hg.ricciNormGrad t ht x

end DifferentialGeometry.PDE.RicciFlow
