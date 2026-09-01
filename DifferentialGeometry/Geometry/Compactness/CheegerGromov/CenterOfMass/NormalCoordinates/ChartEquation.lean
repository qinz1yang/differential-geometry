import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverse.Branch
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Smoothness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set
open scoped BigOperators ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

noncomputable def chartCmEqnC
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (c : NormalBallChart (I := I) p)
    (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z : E) (params : (ι → Real) × (ι → E)) : E :=
  ∑ i, params.1 i •
    B.chartReadout c (c.hom z, c.hom (params.2 i))

def HasCmSolC
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (c : NormalBallChart (I := I) p)
    (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z : E)
    (params : (ι → Real) × (ι → E)) : Prop :=
  z ∈ Metric.ball (0 : E) c.radius ∧
    (∀ i, params.2 i ∈ Metric.ball (0 : E) c.radius) ∧
    (∀ i, (c.hom z, c.hom (params.2 i)) ∈ B.chartReadDom c) ∧
    chartCmEqnC (I := I) g hEnorm p c B z params = 0 ∧
    ∃ L : E ≃L[Real] E,
      HasFDerivAt
          (fun u : E => chartCmEqnC (I := I) g hEnorm p c B u params)
          (L : E →L[Real] E) z ∧
        ∃ (f : ((ι → Real) × (ι → E)) → E)
            (Df : ((ι → Real) × (ι → E)) →L[Real] E),
          f params = z ∧ HasStrictFDerivAt f Df params ∧
            (∀ᶠ params' in nhds params,
              chartCmEqnC (I := I) g hEnorm p c B
                (f params') params' = 0) ∧
            (∀ᶠ zp in nhds (z, params),
              chartCmEqnC (I := I) g hEnorm p c B zp.1 zp.2 = 0 →
                zp.1 = f zp.2)

omit [T2Space (TangentBundle I M)] [CompleteSpace E] [ConnectedSpace M]
    [T3Space M] in
theorem chartCmC_zero_of_sum
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (c : NormalBallChart (I := I) p)
    (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z : E) (mu : ι → Real) (xi : ι → E)
    (hz : z ∈ Metric.ball (0 : E) c.radius)
    (hdom : ∀ i,
      (c.hom z, c.hom (xi i)) ∈ B.chartReadDom c)
    (hsum : ∑ i, mu i •
      (show TangentSpace I (c.hom z) from
        (B.inv (c.hom z, c.hom (xi i))).snd) = 0) :
    chartCmEqnC (I := I) g hEnorm p c B z (mu, xi) = 0 := by
  classical
  have hzTarget : c.hom z ∈ c.restrictBall.target := by
    have hmap := c.restrictBall.map_source hz
    simpa only [NormalBallChart.restrict_ball_apply] using hmap
  have hinvBase (i : ι) :
      B.inv (c.hom z, c.hom (xi i)) =
        (⟨c.hom z,
          (show TangentSpace I (c.hom z) from
            (B.inv (c.hom z, c.hom (xi i))).snd)⟩ :
          TangentBundle I M) := by
    refine Bundle.TotalSpace.ext (B.proj_eq (hdom i).1) ?_
    exact heq_of_eq rfl
  have hterm (i : ι) :
      B.chartReadout c (c.hom z, c.hom (xi i)) =
        mfderiv I (modelWithCornersSelf Real E) c.inv (c.hom z)
          (show TangentSpace I (c.hom z) from
            (B.inv (c.hom z, c.hom (xi i))).snd) := by
    unfold DiagInvBranch.chartReadout
    rw [hinvBase i, c.tangentHome_symm_apply hzTarget]
  unfold chartCmEqnC
  have hlinear :
      ∑ i, mu i • B.chartReadout c (c.hom z, c.hom (xi i)) =
        mfderiv I (modelWithCornersSelf Real E) c.inv (c.hom z)
          (∑ i, mu i •
            (show TangentSpace I (c.hom z) from
              (B.inv (c.hom z, c.hom (xi i))).snd)) := by
    simp_rw [hterm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_smul _ (mu i) _).symm
  rw [hlinear, hsum, map_zero]
  rfl

omit [CompleteSpace E] [ConnectedSpace M] [T3Space M] in
omit [T2Space (TangentBundle I M)] in
theorem chartCmEqnC_cdAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (c : NormalBallChart (I := I) p)
    (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → Real) × (ι → E))
    (n : ℕ∞)
    (hz : z₀ ∈ Metric.ball (0 : E) c.radius)
    (hξ : ∀ i, params₀.2 i ∈ Metric.ball (0 : E) c.radius)
    (hdom : ∀ i,
      (c.hom z₀, c.hom (params₀.2 i)) ∈ B.chartReadDom c) :
    ContDiffAt Real n
      (fun w : E × ((ι → Real) × (ι → E)) =>
        chartCmEqnC (I := I) g hEnorm p c B w.1 w.2)
      (z₀, params₀) := by
  unfold chartCmEqnC
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hcenter : ContMDiffAt 𝓘(Real, E) I n c.hom z₀ :=
      (c.smooth_to z₀ hz).contMDiffAt
        (Metric.isOpen_ball.mem_nhds hz) |>.of_le (by simp)
    have hpoint : ContMDiffAt 𝓘(Real, E) I n c.hom (params₀.2 i) :=
      (c.smooth_to (params₀.2 i) (hξ i)).contMDiffAt
        (Metric.isOpen_ball.mem_nhds (hξ i)) |>.of_le (by simp)
    have hfst : ContMDiffAt
        𝓘(Real, E × ((ι → Real) × (ι → E))) 𝓘(Real, E) n
        (fun w : E × ((ι → Real) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hproj : ContMDiffAt
        𝓘(Real, E × ((ι → Real) × (ι → E))) 𝓘(Real, E) n
        (fun w : E × ((ι → Real) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hinner : ContMDiffAt
        𝓘(Real, E × ((ι → Real) × (ι → E))) (I.prod I) n
        (fun w : E × ((ι → Real) × (ι → E)) =>
          (c.hom w.1, c.hom (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (hcenter.comp (z₀, params₀) hfst)
        (hpoint.comp (z₀, params₀) hproj)
    have hread : ContMDiffAt (I.prod I) 𝓘(Real, E) n
        (B.chartReadout c) (c.hom z₀, c.hom (params₀.2 i)) :=
      ((B.chartReadoutInf c).2.2.1
        (c.hom z₀, c.hom (params₀.2 i)) (hdom i)).contMDiffAt
          ((B.chartReadoutInf c).1.mem_nhds (hdom i)) |>.of_le (by simp)
    have hcomp : ContMDiffAt
        𝓘(Real, E × ((ι → Real) × (ι → E))) 𝓘(Real, E) n
        (fun w : E × ((ι → Real) × (ι → E)) =>
          B.chartReadout c (c.hom w.1, c.hom (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.comp
        (I := 𝓘(Real, E × ((ι → Real) × (ι → E))))
        (I' := I.prod I) (I'' := 𝓘(Real, E))
        (f := fun w : E × ((ι → Real) × (ι → E)) =>
          (c.hom w.1, c.hom (w.2.2 i)))
        (g := B.chartReadout c)
        (z₀, params₀) hread hinner
    exact hcomp

omit [CompleteSpace E] [ConnectedSpace M] [T3Space M]
  [T2Space (TangentBundle I M)] in
theorem readoutSolC_strict
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (c : NormalBallChart (I := I) p)
    (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → Real) × (ι → E))
    (hz : z₀ ∈ Metric.ball (0 : E) c.radius)
    (hξ : ∀ i, params₀.2 i ∈ Metric.ball (0 : E) c.radius)
    (hdom : ∀ i,
      (c.hom z₀, c.hom (params₀.2 i)) ∈ B.chartReadDom c)
    (hinv : ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun z : E => chartCmEqnC (I := I) g hEnorm p c B z params₀)
        (L : E →L[Real] E) z₀)
    (hzero : chartCmEqnC (I := I) g hEnorm p c B z₀ params₀ = 0) :
    ∃ (f : ((ι → Real) × (ι → E)) → E)
      (Df : ((ι → Real) × (ι → E)) →L[Real] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀,
          chartCmEqnC (I := I) g hEnorm p c B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqnC (I := I) g hEnorm p c B zp.1 zp.2 = 0 →
            zp.1 = f zp.2) := by
  have hsmooth : ContDiffAt Real 1
      (fun w : E × ((ι → Real) × (ι → E)) =>
        chartCmEqnC (I := I) g hEnorm p c B w.1 w.2)
      (z₀, params₀) :=
    chartCmEqnC_cdAt (I := I) g hEnorm p c B z₀ params₀ 1 hz hξ hdom
  have hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → Real) × (ι → E)) =>
        chartCmEqnC (I := I) g hEnorm p c B w.1 w.2)
      (fderiv Real (fun w : E × ((ι → Real) × (ι → E)) =>
        chartCmEqnC (I := I) g hEnorm p c B w.1 w.2) (z₀, params₀))
      (z₀, params₀) :=
    hsmooth.hasStrictFDerivAt one_ne_zero
  exact implicitSol_hasStrictFDerivAt
    (fun z params => chartCmEqnC (I := I) g hEnorm p c B z params)
    z₀ params₀ _ hjoint hinv hzero

omit [CompleteSpace E] [ConnectedSpace M] [T3Space M]
  [T2Space (TangentBundle I M)] in
theorem readoutSolC_cdAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (c : NormalBallChart (I := I) p)
    (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → Real) × (ι → E))
    (n : Nat) (hn : 1 ≤ n)
    (hz : z₀ ∈ Metric.ball (0 : E) c.radius)
    (hξ : ∀ i, params₀.2 i ∈ Metric.ball (0 : E) c.radius)
    (hdom : ∀ i,
      (c.hom z₀, c.hom (params₀.2 i)) ∈ B.chartReadDom c)
    (hinv : ∃ L : E ≃L[Real] E,
      HasFDerivAt
        (fun z : E => chartCmEqnC (I := I) g hEnorm p c B z params₀)
        (L : E →L[Real] E) z₀)
    (hzero : chartCmEqnC (I := I) g hEnorm p c B z₀ params₀ = 0) :
    ∃ f : ((ι → Real) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt Real (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀,
          chartCmEqnC (I := I) g hEnorm p c B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqnC (I := I) g hEnorm p c B zp.1 zp.2 = 0 →
            zp.1 = f zp.2) := by
  have hjoint : ContDiffAt Real (n : ℕ∞)
      (fun w : E × ((ι → Real) × (ι → E)) =>
        chartCmEqnC (I := I) g hEnorm p c B w.1 w.2) (z₀, params₀) :=
    chartCmEqnC_cdAt (I := I) g hEnorm p c B z₀ params₀ n hz hξ hdom
  exact implicitSol_contDiffAt
    (fun z params => chartCmEqnC (I := I) g hEnorm p c B z params)
    z₀ params₀ n hn hjoint hinv hzero

end HCGCompactness
end DifferentialGeometry
