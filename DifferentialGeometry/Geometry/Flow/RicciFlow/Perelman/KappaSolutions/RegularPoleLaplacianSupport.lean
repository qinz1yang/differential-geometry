import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleHessianSupportExistence
import DifferentialGeometry.Geometry.Operator.Laplacian.LocalOrthonormalTrace
import DifferentialGeometry.Geometry.Operator.GradientTouchingSupport


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff _root_.Manifold _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] {D : RealTimeInterval}

theorem exists_curvatureNormalizedSolution_redLength_upper_support_laplacian_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (hregD : D.regular = Iio 0) (b Q K : Real)
    (hb : b < 0) (hQ : 0 < Q) (hbmem : b ∈ D.carrier)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric b))
    (x y : M) (tau : Real) (htau : 0 < tau)
    (hRm : ∀ q ∈ Icc (b - tau / Q) b, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (alpha0 : Real → M) (halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y)
    (hdiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun z ↦ redLength (curvatureNormalizedSolution S b Q hQ hbmem) 0 x z tau) y)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    let Sres := curvatureNormalizedSolution S b Q hQ hbmem
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧
      ∃ phi : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ phi U ∧
        phi y = redLength Sres 0 x y tau ∧
        (∀ z ∈ U, redLength Sres 0 x z tau ≤ phi z) ∧
        gradientFun (I := I) (Sres.base.metric (-tau)) phi y =
          gradientFun (I := I) (Sres.base.metric (-tau))
            (fun z ↦ redLength Sres 0 x z tau) y ∧
        laplacian (I := I) (LeviCivita (I := I) (Sres.base.metric (-tau)))
          (Sres.base.metric (-tau)) phi y <
          (1 / 2 : Real) * (Sres.base.metric (-tau)).inner y
            (gradientFun (I := I) (Sres.base.metric (-tau))
              (fun z ↦ redLength Sres 0 x z tau) y)
            (gradientFun (I := I) (Sres.base.metric (-tau))
              (fun z ↦ redLength Sres 0 x z tau) y) -
            (1 / 2 : Real) * Sres.scalar (-tau) y +
            ((Module.finrank Real E : Real) - redLength Sres 0 x y tau) / (2 * tau) +
            epsilon := by
  dsimp only
  let Sres := curvatureNormalizedSolution S b Q hQ hbmem
  obtain ⟨Z, hmin, hExp, hsupports⟩ :=
    exists_lMinimizingVector_curvatureNormalizedSolution_redLength_upper_support_hess_trace_lt
      (I := I) S hS hregD b Q K hb hQ hbmem hg x y tau htau hRm
      alpha0 halpha0 h00 h0t
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, phi, hphism, hphicontact, hupper, hgrad, htrace⟩ :=
    hsupports epsilon hepsilon
  have hphiAt : ContMDiffAt I 𝓘(Real, Real) ∞ phi y :=
    (hphism y hyU).contMDiffAt (hUopen.mem_nhds hyU)
  have hupperEv : ∀ᶠ z in nhds y, redLength Sres 0 x z tau ≤ phi z :=
    Filter.eventually_of_mem (hUopen.mem_nhds hyU) (fun z hz => hupper z hz)
  have hgradEq := gradientFun_eq_of_touching_upper_support
    (I := I) (Sres.base.metric (-tau)) hdiff
    (hphiAt.mdifferentiableAt (by simp)) hphicontact hupperEv
  refine ⟨U, hUopen, hyU, phi, hphism, hphicontact, hupper, hgradEq.symm, ?_⟩
  rw [laplacian_eq_sum_hessFun_of_contMDiffOn_orthonormal
    (I := I) (Sres.base.metric (-tau)) hUopen hphism hyU
    (fun i ↦ P i (Real.sqrt tau)) hON]
  rw [← hgradEq] at htrace
  exact htrace

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
