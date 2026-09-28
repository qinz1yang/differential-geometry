import DifferentialGeometry.Geometry.Metric.UniformExponential
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic



noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



def minimizingLog (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    (x y : M) : TangentSpace I x :=
  if h : Manifold.riemannianEDist I x y ≠ ⊤ then
    (minExp_of_ne_top (I := I) g hg x y h).choose else 0


theorem minimizingLog_exp (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    {x y : M} (h : Manifold.riemannianEDist I x y ≠ ⊤) :
    expMapIntrinsic (I := I) g hg x (minimizingLog g hg x y) = y := by
  rw [minimizingLog, dite_eq_left h]
  exact (minExp_of_ne_top (I := I) g hg x y h).choose_spec.1


theorem minimizingLog_norm (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    {x y : M} (h : Manifold.riemannianEDist I x y ≠ ⊤) :
    Real.sqrt (g.inner x (minimizingLog g hg x y) (minimizingLog g hg x y)) =
      (Manifold.riemannianEDist I x y).toReal := by
  rw [minimizingLog, dite_eq_left h]
  exact (minExp_of_ne_top (I := I) g hg x y h).choose_spec.2


def minimizingDiagLog (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    (p : M × M) : TangentBundle I M := TotalSpace.mk' E p.1 (minimizingLog g hg p.1 p.2)




theorem minimizingDiagLog_eventually_eq_branch (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (p : M) :
    minimizingDiagLog g hg =ᶠ[𝓝 (p, p)]
      (standardDiagonalInverseBranch (I := I) g hg p).inv := by
  obtain ⟨ε, hε, hinj⟩ := exists_uniform_diagExp_injective g hg
  let B := standardDiagonalInverseBranch (I := I) g hg p
  have hBi : ContinuousAt B.inv (p, p) := by
    rw [show B.inv = diagExpInv (I := I) g hg p from
      standardDiagonalInverseBranch_inv g hg p]
    exact (diagExpInv_contMDiffAt (I := I) g hg p).continuousAt
  have hB0 : B.inv (p, p) = (TotalSpace.mk' E p 0 : TangentBundle I M) := by
    rw [show B.inv = diagExpInv (I := I) g hg p from
      standardDiagonalInverseBranch_inv g hg p]
    exact diagExpInv_center (I := I) g hg p
  have hN : ContinuousAt (fun y : M × M =>
      Real.sqrt (g.inner (B.inv y).proj (B.inv y).2 (B.inv y).2)) (p, p) :=
    (metricQuad_cont g).sqrt.continuousAt.comp hBi
  have hsmallB : ∀ᶠ y in 𝓝 (p, p),
      Real.sqrt (g.inner (B.inv y).proj (B.inv y).2 (B.inv y).2) < ε := by
    apply hN.eventually (gt_mem_nhds ?_)
    change Real.sqrt (g.inner (B.inv (p, p)).proj (B.inv (p, p)).2 (B.inv (p, p)).2) < ε
    rw [hB0]
    change Real.sqrt (g.inner p 0 0) < ε
    simpa only [map_zero, Real.sqrt_zero] using hε
  have hsmallD : ∀ᶠ y : M × M in 𝓝 (p, p), Manifold.riemannianEDist I y.1 y.2 < ENNReal.ofReal ε := by
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    change ∀ᶠ y : M × M in 𝓝 (p, p), edist y.1 y.2 < ENNReal.ofReal ε
    exact (continuous_fst.edist continuous_snd).continuousAt (x := (p, p)) |>.eventually
      (gt_mem_nhds (show edist p p < ENNReal.ofReal ε by
        simpa only [edist_self] using ENNReal.ofReal_pos.mpr hε))
  filter_upwards [hsmallB, hsmallD, diagExp_diagExpInv (I := I) g hg p] with y hyB hyD hyinv
  have hfin : Manifold.riemannianEDist I y.1 y.2 ≠ ⊤ := ne_top_of_lt hyD
  apply hinj
  · change Real.sqrt (g.inner y.1 (minimizingLog g hg y.1 y.2) (minimizingLog g hg y.1 y.2)) ≤ ε
    rw [minimizingLog_norm g hg hfin]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hyD.le).trans_eq (ENNReal.toReal_ofReal hε.le)
  · exact hyB.le
  · have hlog : diagExp (I := I) g hg (minimizingDiagLog g hg y) = y := by
      change (y.1, expMapIntrinsic (I := I) g hg y.1 (minimizingLog g hg y.1 y.2)) = y
      rw [minimizingLog_exp g hg hfin]
    rw [hlog]
    exact hyinv.symm.trans (by rw [standardDiagonalInverseBranch_inv])

end DifferentialGeometry.Geometry
