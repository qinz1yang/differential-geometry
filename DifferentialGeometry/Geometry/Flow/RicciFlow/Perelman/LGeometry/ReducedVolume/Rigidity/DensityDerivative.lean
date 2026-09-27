import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.Equation
import DifferentialGeometry.Geometry.Operator.LaplacianExponential


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

theorem redDensity_hasDerivAt_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x s) :
    HasDerivAt (fun r => redDensity S T x (lExp S T x Z s) r)
      (laplacian (LeviCivita (S.base.metric (T - s))) (S.base.metric (T - s))
          (fun y => redDensity S T x y s) (lExp S T x Z s) -
        S.scalar (T - s) (lExp S T x Z s) *
          redDensity S T x (lExp S T x Z s) s) s := by
  let y := lExp S T x Z s
  let g := S.base.metric (T - s)
  let f := fun z : M => redLength S T x z s
  let n : ℝ := Module.finrank ℝ E
  let c : ℝ := -(n / 2) * Real.log s - (n / 2) * Real.log (4 * Real.pi)
  let phi : M → ℝ := fun z => c - f z
  let q : ℝ := g.inner y (gradientFun g f y) (gradientFun g f y)
  obtain ⟨U, hU, hyU, hfU⟩ := redLength_smooth_of_rm S hS T hg x hRm hs hZ
  have hf : ContMDiffAt I 𝓘(ℝ) ∞ f y :=
    (hfU y hyU).contMDiffAt (hU.mem_nhds hyU)
  have hphi : ContMDiffAt I 𝓘(ℝ) ∞ phi y := contMDiffAt_const.sub hf
  have hphiLap : laplacian (LeviCivita g) g phi y =
      -laplacian (LeviCivita g) g f y := by
    have h := laplacian_sub_at_of_contMDiffAt (LeviCivita g) g
      (f := fun _ : M => c) contMDiffAt_const hf
    simpa only [laplacian_const, zero_sub, phi] using h
  have hphiGrad : gradientFun g phi y = -gradientFun g f y := by
    have h := gradientFun_sub g (f := fun _ : M => c)
      mdifferentiableAt_const (hf.mdifferentiableAt (by simp))
    simpa only [gradientFun_const, zero_sub, phi] using h
  have heq : (fun z : M => redDensity S T x z s) =
      (fun z : M => Real.exp (phi z)) := by
    funext z
    apply congrArg Real.exp
    dsimp only [redDensity, phi, c, f, n]
    ring
  have hlap : laplacian (LeviCivita g) g (fun z => redDensity S T x z s) y =
      redDensity S T x y s * (-laplacian (LeviCivita g) g f y + q) := by
    rw [heq, laplacian_exp (LeviCivita g) g
      (hphi.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), hphiLap,
      hphiGrad]
    simp only [map_neg, neg_apply, neg_neg]
    rw [← congrFun heq y]
  have hpde := redLength_conjugateHeat_of_redVolume_eq_one
    S hS T hg x hRm hs hstau hslab hvol hZ
  change deriv (fun r => redLength S T x y r) s -
    laplacian (LeviCivita g) g f y + q - S.scalar (T - s) y +
    n / (2 * s) = 0 at hpde
  have ht := (redLength_hasDeriv_of_rm S hS T hg x hRm hs hZ).differentiableAt.hasDerivAt
  have hd := ((ht.neg.sub ((Real.hasDerivAt_log hs.ne').const_mul (n / 2))).sub_const
    ((n / 2) * Real.log (4 * Real.pi))).exp
  change HasDerivAt (fun r => redDensity S T x y r)
    (redDensity S T x y s *
      (-deriv (fun r => redLength S T x y r) s - n / 2 * s⁻¹)) s at hd
  have hfrac : n / 2 * s⁻¹ = n / (2 * s) := by
    rw [← div_eq_mul_inv, div_div]
  have hcoef : -deriv (fun r => redLength S T x y r) s - n / 2 * s⁻¹ =
      -laplacian (LeviCivita g) g f y + q - S.scalar (T - s) y := by
    rw [hfrac]
    linarith only [hpde]
  apply hd.congr_deriv
  rw [hcoef, hlap]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
