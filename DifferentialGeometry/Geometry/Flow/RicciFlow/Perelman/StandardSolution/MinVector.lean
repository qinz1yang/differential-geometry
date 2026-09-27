import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostEndpoint
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
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

theorem lMinVec_lim_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : ℕ → TangentSpace I x}
    {Z₀ : TangentSpace I x} {tau : ℝ}
    (hmin : ∀ n, (Z n, tau) ∈ lMinDomain S T x)
    (hZ : Tendsto Z atTop (𝓝 Z₀))
    (hdom : (Z₀, tau) ∈ lExpPosDom S T x)
    (hbdd : ∀ y : M,
      BddBelow {r : ℝ | ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
          lRegularizedAction S T alpha 0 (Real.sqrt tau) = r}) :
    (Z₀, tau) ∈ lMinDomain S T x := by
  classical
  obtain ⟨htau, _htau0, hbDom⟩ :=
    (mem_lExpPosDom S T x Z₀ tau).1 hdom
  let b : ℝ := Real.sqrt tau
  let gamma : ℝ → M := lRegularizedCurve S T x Z₀
  let y : M := lExp S T x Z₀ tau
  let q : ℕ → M := fun n ↦ lExp S T x (Z n) tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hreg : ∀ s ∈ Icc (0 : ℝ) b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lExpPosDom_regularity S T x Z₀ hdom hs
  have hExpAt : ContinuousAt
      (fun p : E × ℝ ↦ lExp S T x p.1 p.2) (Z₀, tau) :=
    ((lExp_smoothOn S hS T x) (Z₀, tau) hdom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hdom)
  have hq : Tendsto q atTop (𝓝 y) := by
    exact hExpAt.tendsto.comp
      (hZ.prodMk_nhds tendsto_const_nhds)
  have hactLim : Tendsto
      (fun n ↦ lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b)
      atTop (𝓝 (lRegularizedAction S T gamma 0 b)) := by
    have hpair : Tendsto (fun n ↦ (Z n, b)) atTop (𝓝 (Z₀, b)) :=
      hZ.prodMk_nhds tendsto_const_nhds
    change Tendsto
      ((fun p : E × ℝ ↦
        lRegularizedAction S T (lRegularizedCurve S T x p.1) 0 p.2) ∘
          fun n ↦ (Z n, b)) atTop
        (𝓝 (lRegularizedAction S T (lRegularizedCurve S T x Z₀) 0 b))
    exact (continuousAt_lRegularizedAction_lRegularizedCurve
      (I := I) S hS T x hb hbDom).tendsto.comp hpair
  have hactEq (n : ℕ) :
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b =
        lCost S T x (q n) tau := by
    have hn := ((mem_lMinDomain S T x (Z n) tau).1 (hmin n)).2
    calc
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b =
          lLength S T (squareRootReparametrization (lRegularizedCurve S T x (Z n))) 0 tau := by
        simpa only [b] using
          (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
            (lRegularizedCurve S T x (Z n)) tau htau.le).symm
      _ = lCost S T x (q n) tau := by
        rw [show squareRootReparametrization (lRegularizedCurve S T x (Z n)) =
          (fun r ↦ lRegularizedCurve S T x (Z n) (Real.sqrt r)) by rfl]
        simpa only [lExp, q] using hn
  have hmin0 : ∀ delta : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 delta →
      delta 0 = x → delta b = y →
      lRegularizedAction S T gamma 0 b ≤ lRegularizedAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    by_contra hnot
    have hlt :
        lRegularizedAction S T delta 0 b < lRegularizedAction S T gamma 0 b :=
      lt_of_not_ge hnot
    let A : ℝ :=
      (lRegularizedAction S T delta 0 b + lRegularizedAction S T gamma 0 b) / 2
    have hdeltaA : lRegularizedAction S T delta 0 b < A := by
      dsimp only [A]
      linarith
    have hnear : ∀ᶠ z in 𝓝 y, lCost S T x z (b ^ 2) < A :=
      lCost_lt_event_of_bdd (I := I) S hS T b hb hreg
        x y delta hdelta hd0 hdb hbdd A hdeltaA
    have hcostEvent :
        ∀ᶠ n in atTop, lCost S T x (q n) tau < A := by
      simpa only [hb2] using hq.eventually hnear
    have hactEvent : ∀ᶠ n in atTop,
        lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b ≤ A := by
      filter_upwards [hcostEvent] with n hn
      rw [hactEq n]
      exact hn.le
    have hle : lRegularizedAction S T gamma 0 b ≤ A :=
      le_of_tendsto hactLim hactEvent
    dsimp only [A] at hle
    linarith
  have hcostsNonempty :
      {r : ℝ | ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧ alpha b = y ∧
          lRegularizedAction S T alpha 0 b = r}.Nonempty := by
    obtain ⟨rho, hrho, hrhoId, _hrhoDeriv, hrhoRange⟩ :=
      exists_lRegularizedDomain_smoothClamp S T x Z₀ hb hbDom
    let z : E := Z₀
    let alpha : ℝ → M :=
      fun s ↦ lRegularizedCurve S T x Z₀ (rho s)
    have hrhoM : ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞ rho :=
      contMDiff_iff_contDiff.mpr hrho
    have hpair : ContMDiff (modelWithCornersSelf ℝ ℝ)
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
          change rho s ∈ lRegularizedDomain S T x Z₀
          exact hrhoRange s)
    have halpha :
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha :=
      halphaInf.of_le (by norm_num)
    have hrho0 : rho 0 = 0 := by
      simpa only [id_eq] using hrhoId ⟨le_rfl, hb.le⟩
    have hrhob : rho b = b := by
      simpa only [id_eq] using hrhoId ⟨hb.le, le_rfl⟩
    refine ⟨lRegularizedAction S T alpha 0 b, alpha, halpha, ?_, ?_, rfl⟩
    · simp only [alpha, hrho0, lRegularizedCurve_zero]
    · change lRegularizedCurve S T x Z₀ (rho b) =
        lRegularizedCurve S T x Z₀ b
      rw [hrhob]
  have hcostGe :
      lRegularizedAction S T gamma 0 b ≤ lRegularizedCostC1 S T 0 b x y := by
    unfold lRegularizedCostC1
    apply le_csInf hcostsNonempty
    rintro r ⟨delta, hdelta, hd0, hdb, rfl⟩
    exact hmin0 delta hdelta hd0 hdb
  have hcostLe :
      lCost S T x y tau ≤ lRegularizedAction S T gamma 0 b := by
    have hle :=
      lCost_le_ray_bdd (I := I) S hS T x Z₀ b hb hbDom (hbdd y)
    change lCost S T x y (b ^ 2) ≤
      lRegularizedAction S T gamma 0 b at hle
    simpa only [hb2] using hle
  have hcostEq :
      lRegularizedAction S T gamma 0 b = lCost S T x y tau := by
    apply le_antisymm
    · rw [lCost_eq_regularity (I := I) S T x y tau htau.le]
      exact hcostGe
    · exact hcostLe
  apply (mem_lMinDomain S T x Z₀ tau).2
  refine ⟨hdom, ?_⟩
  calc
    lLength S T (fun r : ℝ ↦ lExp S T x Z₀ r) 0 tau =
        lRegularizedAction S T gamma 0 b := by
      change lLength S T (squareRootReparametrization gamma) 0 tau =
        lRegularizedAction S T gamma 0 (Real.sqrt tau)
      exact lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T gamma tau htau.le
    _ = lCost S T x (lExp S T x Z₀ tau) tau := hcostEq

theorem measurableSet_lMinDomain_slice_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (tau : ℝ)
    (hbdd : ∀ y : M,
      BddBelow {r : ℝ | ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
          lRegularizedAction S T alpha 0 (Real.sqrt tau) = r}) :
    @MeasurableSet E (borel E)
      {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let U : Set E := {Z : E | (Z, tau) ∈ lExpPosDom S T x}
  let A : Set U := {Z : U | ((Z : E), tau) ∈ lMinDomain S T x}
  have hU : IsOpen U := by
    change IsOpen
      ((fun Z : E ↦ (Z, tau)) ⁻¹' lExpPosDom S T x)
    exact (lExpPosDom_open S hS T x).preimage
      (continuous_id.prodMk continuous_const)
  have hA : IsClosed A := by
    rw [← isSeqClosed_iff_isClosed]
    intro Z Z₀ hmin hZ
    have hZval : Tendsto (fun n ↦ (Z n : E)) atTop
        (𝓝 (Z₀ : E)) :=
      (continuous_subtype_val.tendsto Z₀).comp hZ
    have hdom : ((Z₀ : E), tau) ∈ lExpPosDom S T x :=
      Z₀.property
    have hminVal :
        ∀ n, ((Z n : E), tau) ∈ lMinDomain S T x := by
      intro n
      exact hmin n
    change ((Z₀ : E), tau) ∈ lMinDomain S T x
    exact lMinVec_lim_of_bdd (I := I) S hS T x
      (Z := fun n ↦ (Z n : E)) (Z₀ := (Z₀ : E))
      hminVal hZval hdom hbdd
  have himage :
      (Subtype.val : U → E) '' A =
        {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
    ext Z
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact hW
    · intro hZ
      have hZU : Z ∈ U :=
        ((mem_lMinDomain S T x Z tau).1 hZ).1
      refine ⟨⟨Z, hZU⟩, ?_, rfl⟩
      exact hZ
  rw [← himage]
  exact
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr
      hA.measurableSet

theorem measurableSet_lMinDomain_slice_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    (hRm : ∀ tau : ℝ, 0 < tau →
      Icc (T - tau) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - tau) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K) :
    ∀ tau : ℝ, @MeasurableSet E (borel E)
      {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
  intro tau
  classical
  by_cases hexp : ∃ Z : E, (Z, tau) ∈ lExpPosDom S T x
  · obtain ⟨Z, hdom⟩ := hexp
    have htau : 0 < tau :=
      ((mem_lExpPosDom S T x Z tau).1 hdom).1
    have hreg : Icc (T - tau) T ⊆ D.regular := by
      intro t ht
      have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have hle : T - t ≤ tau := by
        linarith [ht.1]
      have hsqrt : Real.sqrt (T - t) ∈
          Icc (0 : ℝ) (Real.sqrt tau) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
      have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
      have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
        rw [Real.sq_sqrt hnonneg]
        ring
      simpa only [heq] using hclock
    obtain ⟨K, hK⟩ := hRm tau htau hreg
    apply measurableSet_lMinDomain_slice_of_bdd (I := I) S hS T x tau
    intro y
    exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt tau)
      le_rfl (Real.sqrt_nonneg tau)
      (by simpa only [Real.sq_sqrt htau.le] using hreg)
      (by simpa only [Real.sq_sqrt htau.le] using hK)
      x y
  · have hempty :
        {Z : E | (Z, tau) ∈ lMinDomain S T x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro Z hZ
      exact hexp ⟨Z, ((mem_lMinDomain S T x Z tau).1 hZ).1⟩
    rw [hempty]
    exact @MeasurableSet.empty E (borel E)

end DifferentialGeometry.PDE.RicciFlow
