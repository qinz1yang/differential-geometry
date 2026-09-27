import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleHessianSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import DifferentialGeometry.Bundle.FiberBundleHausdorff


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped BigOperators ContDiff _root_.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

theorem exists_lMinimizingVector_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (hregD : D.regular = Iio 0) (b Q K : Real)
    (hb : b < 0) (hQ : 0 < Q) (hbmem : b ∈ D.carrier)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric b))
    (x y : M) (tau : Real) (htau : 0 < tau)
    (hRm : ∀ q ∈ Icc (b - tau / Q) b, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (alpha0 : Real → M) (halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y) :
    let Sraw := parabolicSolution S b Q hQ hbmem
    let Sres := curvatureNormalizedSolution S b Q hQ hbmem
    ∃ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain Sraw 0 x ∧ lExp Sraw 0 x Z tau = y ∧
      ∀ epsilon : Real, 0 < epsilon →
        ∃ (P : Fin (Module.finrank Real E) →
          ∀ s, TangentSpace I (lRegularizedCurve Sraw 0 x Z s)) (Omega : Set Real),
          IsOpen Omega ∧ Icc (0 : Real) (Real.sqrt tau) ⊆ Omega ∧
          (∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent ∞
            (fun s : Real ↦
              (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
                (lRegularizedCurve Sraw 0 x Z s) (P i s) : TangentBundle I M)) Omega) ∧
          (∀ i, IsLAdapted Sraw 0 (lRegularizedCurve Sraw 0 x Z) (P i) Omega) ∧
          (∀ i j, (Sres.base.metric (-tau)).inner y
            (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = if i = j then 1 else 0) ∧
          ∃ U : Set M, IsOpen U ∧ y ∈ U ∧
            ∃ phi : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ phi U ∧
              phi y = redLength Sres 0 x y tau ∧
              (∀ y ∈ U, redLength Sres 0 x y tau ≤ phi y) ∧
              gradientFun (I := I) (Sres.base.metric (-tau)) phi
                y = (2 * Real.sqrt tau)⁻¹ •
                  lVelocity (I := I) (lRegularizedCurve Sraw 0 x Z) (Real.sqrt tau) ∧
              (∑ i : Fin (Module.finrank Real E),
                hessFun (I := I) (Sres.base.metric (-tau)) phi y
                  (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) <
                (1 / 2 : Real) * (Sres.base.metric (-tau)).inner y
                  (gradientFun (I := I) (Sres.base.metric (-tau)) phi y)
                  (gradientFun (I := I) (Sres.base.metric (-tau)) phi y) -
                  (1 / 2 : Real) * Sres.scalar (-tau) y +
                  ((Module.finrank Real E : Real) -
                    redLength Sres 0 x y tau) / (2 * tau) + epsilon := by
  dsimp only
  let _ : T2Space (TangentBundle I M) := inferInstance
  let Sraw := parabolicSolution S b Q hQ hbmem
  have hraw : IsSolutionOn (I := I) Sraw :=
    parabolicSolution_isSolutionOn S hS b Q hQ hbmem
  have hgRaw : RiemannianMetricComplete (I := I) (Sraw.base.metric 0) := by
    have hbase : RiemannianMetricComplete (I := I)
        (S.base.metric (parabolicTime b Q 0)) := by
      simpa only [parabolicTime_zero] using hg
    simpa only [curvatureNormalizedSolution, SolutionOn.timeRestrict, Sraw] using
      curvatureNormalizedSolution_complete S b Q hQ hbmem 0 hbase
  have hreg : Icc (0 - tau) 0 ⊆ (parabolicInterval D b Q hbmem).regular := by
    intro s hs
    exact Iic_subset_parabolicInterval_regular_of_neg hregD hb hQ hbmem hs.2
  have hRmRaw : ∀ s ∈ Icc (0 - tau) 0, ∀ z : M,
      normSq0S (I := I) (Sraw.base.metric s) z 4 (Sraw.base.rm04 s z) ≤
        Q⁻¹ ^ 2 * K := by
    intro s hs z
    change normSq0S (I := I)
      ((parabolicSolution S b Q hQ hbmem).base.metric s) z 4
      ((parabolicSolution S b Q hQ hbmem).base.rm04 s z) ≤ _
    rw [parabolicRmNormSq]
    have htime : parabolicTime b Q s ∈ Icc (b - tau / Q) b := by
      constructor
      · have hlo : -(tau / Q) ≤ s / Q := by
          simpa only [zero_sub, neg_div] using
            div_le_div_of_nonneg_right hs.1 hQ.le
        change b - tau / Q ≤ b + s / Q
        linarith
      · exact add_le_of_nonpos_right
          (div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le)
    exact mul_le_mul_of_nonneg_left (hRm _ htime z) (sq_nonneg _)
  obtain ⟨Z, hmin, hExp⟩ := exists_lMinimizingVector_rm (I := I)
    Sraw hraw (Q⁻¹ ^ 2 * K) 0 hgRaw tau htau hreg hRmRaw
      x y alpha0 halpha0 h00 h0t
  refine ⟨Z, hmin, hExp, ?_⟩
  intro epsilon hepsilon
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, phi, hphism, hcontact, hupper, hgrad, htrace⟩ :=
    exists_contMDiffOn_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt
      (I := I) S hS hregD b Q K hb hQ hbmem x hmin hRm hepsilon
  rw [hExp] at hyU hON hcontact hgrad htrace
  exact ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
    U, hUopen, hyU, phi, hphism, hcontact, hupper, hgrad, htrace⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
