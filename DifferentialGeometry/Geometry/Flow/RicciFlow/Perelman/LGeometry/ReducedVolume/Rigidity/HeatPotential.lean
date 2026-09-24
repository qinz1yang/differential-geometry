import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.DensityDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Equation


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped ContDiff Manifold

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

theorem isHeatPotOn_redDensity_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau a b : ℝ} (ha : 0 < a) (hab : a < b) (hbtau : b < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    IsHeatPotOn (RealTimeInterval.closed a b hab.le)
      (reverseFamily (flowG S) T) (fun r z => -S.scalar (T - r) z)
      (fun r z => redDensity S T x z r) := by
  have hell := redLength_joint_contMDiffOn_of_redVolume_eq_one
    S hS T hg x hRm hslab hvol
  have hmap : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ)) ∞
      (fun p : ℝ × M => (p.2, p.1)) := contMDiff_snd.prodMk contMDiff_fst
  have hmaps : MapsTo (fun p : ℝ × M => (p.2, p.1))
      (Icc a b ×ˢ (univ : Set M)) (univ ×ˢ Ioo 0 tau) := by
    intro p hp
    exact ⟨mem_univ p.2, ha.trans_le hp.1.1, hp.1.2.trans_lt hbtau⟩
  have hellM : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => redLength S T x p.2 p.1)
      (Icc a b ×ˢ (univ : Set M)) :=
    hell.comp hmap.contMDiffOn hmaps
  have hlog : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => Real.log p.1) (Icc a b ×ˢ (univ : Set M)) := by
    intro p hp
    exact ((Real.contDiffAt_log.mpr (ha.trans_le hp.1.1).ne').contMDiffAt.comp p
      contMDiffAt_fst).contMDiffWithinAt
  have hdensity : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => redDensity S T x p.2 p.1)
      (Icc a b ×ˢ (univ : Set M)) := by
    have hphi := (hellM.neg.sub
      ((contMDiffOn_const (c := (Module.finrank ℝ E : ℝ) / 2)).mul hlog)).sub
      (contMDiffOn_const (c := ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
    exact Real.contDiff_exp.contMDiff.comp_contMDiffOn hphi
  refine
    { jointSmooth := hdensity.mono ?_
      jointCont := hdensity.continuousOn
      sliceSmooth := ?_
      equation := ?_ }
  · intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  · intro r hr
    have hslice : ContMDiffOn I 𝓘(ℝ) ∞
        (fun y : M => redDensity S T x y r) univ := by
      apply hdensity.comp ((contMDiff_const (c := r)).prodMk contMDiff_id).contMDiffOn
      intro y _
      exact ⟨hr, mem_univ y⟩
    exact contMDiffOn_univ.mp hslice
  · intro r hr y
    have hcoverage := lExp_inj_image_eq_univ_of_redVolume_eq_one S hS T hg x hRm
      (ha.trans hr.1) (hr.2.trans hbtau) hslab hvol
    have hy : y ∈ (fun Z : E => lExp S T x Z r) '' lInjDomain S T x r := by
      rw [hcoverage]
      exact mem_univ y
    obtain ⟨W, hW, hend⟩ := hy
    change lExp S T x W r = y at hend
    have hd := redDensity_hasDerivAt_of_redVolume_eq_one S hS T hg x hRm
      (ha.trans hr.1) (hr.2.trans hbtau) hslab hvol hW
    rw [hend] at hd
    change HasDerivAt (fun q => redDensity S T x y q)
      (laplacian (LeviCivita (S.base.metric (T - r))) (S.base.metric (T - r))
          (fun z => redDensity S T x z r) y +
        (-S.scalar (T - r) y) * redDensity S T x y r) r
    convert hd using 1
    ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
