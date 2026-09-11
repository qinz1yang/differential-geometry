import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lMinDomain_down_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x)
    {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hle : tau ≤ sigma)
    (hbddTau : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt tau) = lExp S T x Z tau ∧
        lRegularizedAction S T alpha 0 (Real.sqrt tau) = r})
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    (Z, tau) ∈ lMinDomain S T x := by
  classical
  rcases lt_or_eq_of_le hle with hlt | rfl
  · have hvec := (mem_lMinDomain S T x Z sigma).1 hmin
    have hdomTau : (Z, tau) ∈ lExpPosDom S T x :=
      lExpPosDom_down S T x Z hvec.1 htau hle
    obtain ⟨hsigma, _hsigma0, hbSigma⟩ :=
      (mem_lExpPosDom S T x Z sigma).1 hvec.1
    obtain ⟨_htau, _htau0, hbTau⟩ :=
      (mem_lExpPosDom S T x Z tau).1 hdomTau
    let gamma : ℝ → M := lRegularizedCurve S T x Z
    have hsqrtTau : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
    have hsqrtLt : Real.sqrt tau < Real.sqrt sigma :=
      Real.sqrt_lt_sqrt htau.le hlt
    have hgammaC1 :
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma
          (Icc (0 : ℝ) (Real.sqrt sigma)) := by
      simpa only [gamma] using
        lRegularizedCurve_c1On S hS T x Z hbSigma
    have hregSigma :
        ∀ s ∈ Icc (0 : ℝ) (Real.sqrt sigma),
          T - s ^ 2 ∈ D.regular := by
      intro s hs
      exact lExpPosDom_regularity S T x Z hvec.1 hs
    have hcostSigma :
        lRegularizedAction S T gamma 0 (Real.sqrt sigma) =
          lRegularizedCostC1 S T 0 (Real.sqrt sigma) x
            (gamma (Real.sqrt sigma)) := by
      calc
        lRegularizedAction S T gamma 0 (Real.sqrt sigma) =
            lLength S T (squareRootReparametrization gamma) 0 sigma :=
          (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T gamma sigma hsigma.le).symm
        _ = lLength S T (fun r : ℝ ↦ lExp S T x Z r) 0 sigma := rfl
        _ = lCost S T x (lExp S T x Z sigma) sigma := hvec.2
        _ = lRegularizedCostC1 S T 0 (Real.sqrt sigma) x
            (lExp S T x Z sigma) :=
          lCost_eq_regularity (I := I) S T x
            (lExp S T x Z sigma) sigma hsigma.le
        _ = lRegularizedCostC1 S T 0 (Real.sqrt sigma) x
            (gamma (Real.sqrt sigma)) := rfl
    have hminSigma :
        ∀ delta : ℝ → M,
          ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 delta →
          delta 0 = gamma 0 →
          delta (Real.sqrt sigma) = gamma (Real.sqrt sigma) →
          lRegularizedAction S T gamma 0 (Real.sqrt sigma) ≤
            lRegularizedAction S T delta 0 (Real.sqrt sigma) := by
      intro delta hdelta hd0 hdb
      rw [hcostSigma]
      exact lRegularizedCostC1_le_bdd (I := I) S T 0
        (Real.sqrt sigma) x (gamma (Real.sqrt sigma))
        hbddSigma delta hdelta
        (hd0.trans (by simp only [gamma, lRegularizedCurve_zero])) hdb
    have hminTau :=
      lRegularized_prefix_min (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        T 0 (Real.sqrt tau) (Real.sqrt sigma)
        hsqrtTau hsqrtLt gamma hgammaC1 hregSigma hminSigma
    have hcostsNonempty :
        {r : ℝ | ∃ alpha : ℝ → M,
          ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
            alpha 0 = x ∧
            alpha (Real.sqrt tau) = gamma (Real.sqrt tau) ∧
            lRegularizedAction S T alpha 0 (Real.sqrt tau) = r}.Nonempty := by
      obtain ⟨rho, hrho, hrhoId, _hrhoDeriv, hrhoRange⟩ :=
        exists_lRegularizedDomain_smoothClamp S T x Z hsqrtTau hbTau
      let z : E := Z
      let alpha : ℝ → M :=
        fun s ↦ lRegularizedCurve S T x Z (rho s)
      have hrhoM :
          ContMDiff (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) ∞ rho :=
        contMDiff_iff_contDiff.mpr hrho
      have hpair :
          ContMDiff (modelWithCornersSelf ℝ ℝ)
            ((modelWithCornersSelf ℝ E).prod
              (modelWithCornersSelf ℝ ℝ)) ∞
            (fun s : ℝ ↦ (z, rho s)) :=
        contMDiff_const.prodMk hrhoM
      have halphaInf :
          ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ alpha := by
        rw [← contMDiffOn_univ]
        change ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ∞
          ((fun p : E × ℝ ↦ lRegularizedCurve S T x p.1 p.2) ∘
            fun s : ℝ ↦ (z, rho s)) univ
        exact (lRegularizedCurve_smoothOn S hS T x).comp hpair.contMDiffOn
          (fun s _hs ↦ by
            change rho s ∈ lRegularizedDomain S T x Z
            exact hrhoRange s)
      have halpha :
          ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha :=
        halphaInf.of_le (by norm_num)
      have hrho0 : rho 0 = 0 := by
        simpa only [id_eq] using
          hrhoId ⟨le_rfl, hsqrtTau.le⟩
      have hrhob : rho (Real.sqrt tau) = Real.sqrt tau := by
        simpa only [id_eq] using
          hrhoId ⟨hsqrtTau.le, le_rfl⟩
      refine ⟨lRegularizedAction S T alpha 0 (Real.sqrt tau),
        alpha, halpha, ?_, ?_, rfl⟩
      · simp only [alpha, hrho0, lRegularizedCurve_zero]
      · change lRegularizedCurve S T x Z (rho (Real.sqrt tau)) =
          lRegularizedCurve S T x Z (Real.sqrt tau)
        rw [hrhob]
    have hcostGe :
        lRegularizedAction S T gamma 0 (Real.sqrt tau) ≤
          lRegularizedCostC1 S T 0 (Real.sqrt tau) x
            (gamma (Real.sqrt tau)) := by
      unfold lRegularizedCostC1
      apply le_csInf hcostsNonempty
      rintro r ⟨delta, hdelta, hd0, hdb, rfl⟩
      exact hminTau delta hdelta.contMDiffOn
        (hd0.trans (by simp only [gamma, lRegularizedCurve_zero])) hdb
    have hcostLe :
        lCost S T x (gamma (Real.sqrt tau)) tau ≤
          lRegularizedAction S T gamma 0 (Real.sqrt tau) := by
      simpa only [gamma, Real.sq_sqrt htau.le] using
        lCost_le_ray_bdd (I := I) S hS T x Z
          (Real.sqrt tau) hsqrtTau hbTau hbddTau
    have hcostEq :
        lRegularizedAction S T gamma 0 (Real.sqrt tau) =
          lCost S T x (gamma (Real.sqrt tau)) tau := by
      apply le_antisymm
      · rw [lCost_eq_regularity (I := I) S T x
          (gamma (Real.sqrt tau)) tau htau.le]
        exact hcostGe
      · exact hcostLe
    apply (mem_lMinDomain S T x Z tau).2
    refine ⟨hdomTau, ?_⟩
    calc
      lLength S T (fun r : ℝ ↦ lExp S T x Z r) 0 tau =
          lRegularizedAction S T gamma 0 (Real.sqrt tau) := by
        change lLength S T (squareRootReparametrization gamma) 0 tau =
          lRegularizedAction S T gamma 0 (Real.sqrt tau)
        exact lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T gamma tau htau.le
      _ = lCost S T x (lExp S T x Z tau) tau := hcostEq
  · exact hmin

theorem lMinDomain_down_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M) (Z : TangentSpace I x)
    {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hle : tau ≤ sigma)
    (hRmSigma : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    (Z, tau) ∈ lMinDomain S T x := by
  have hdomSigma : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hsigma : 0 < sigma := htau.trans_le hle
  have hregSigma : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by
      linarith [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈
        Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdomSigma hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  have hsub : Icc (T - tau) T ⊆ Icc (T - sigma) T := by
    intro t ht
    exact ⟨(sub_le_sub_left hle T).trans ht.1, ht.2⟩
  have hregTau : Icc (T - tau) T ⊆ D.regular := by
    intro t ht
    exact hregSigma (hsub ht)
  have hRmTau : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K := by
    intro t ht z
    exact hRmSigma t (hsub ht) z
  apply lMinDomain_down_of_bdd (I := I) S hS T x Z hmin htau hle
  · exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt tau)
      le_rfl (Real.sqrt_nonneg tau)
      (by simpa only [Real.sq_sqrt htau.le] using hregTau)
      (by simpa only [Real.sq_sqrt htau.le] using hRmTau)
      x (lExp S T x Z tau)
  · exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt sigma)
      le_rfl (Real.sqrt_nonneg sigma)
      (by simpa only [Real.sq_sqrt hsigma.le] using hregSigma)
      (by simpa only [Real.sq_sqrt hsigma.le] using hRmSigma)
      x (lExp S T x Z sigma)

end DifferentialGeometry.PDE.RicciFlow
