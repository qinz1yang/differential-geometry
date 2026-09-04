import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.InitialVector.FixedEndpoint

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_ray_near
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z)
    (A : Real)
    (hA : lRegAction S T (lRegCurve S T x Z) 0 b < A)
    (q : Nat → M)
    (hq : Tendsto q atTop (nhds (lRegCurve S T x Z b))) :
    ∀ᶠ n in atTop, lCost S T x (q n) (b ^ 2) < A := by
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    exists_lRegDomain_smoothClamp S T x Z hb0 hb
  let z : E := Z
  let gamma : Real → M := fun s ↦ lRegCurve S T x Z (rho s)
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, rho s)) :=
    contMDiff_const.prodMk hrhoM
  have hgammaInf : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      (fun s ↦ lRegCurve S T x Z (rho s)) univ
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_range s)
  have hgamma : ContMDiff (modelWithCornersSelf Real Real) I 1 gamma :=
    hgammaInf.of_le (by norm_num)
  have heq : EqOn gamma (lRegCurve S T x Z) (Icc (0 : Real) b) := by
    intro s hs
    exact congrArg (lRegCurve S T x Z) (hrho_id hs)
  have hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegDomain_reg S T x Z
      (lRegDomain_seg S T x Z hb hs.1 hs.2)
  have htime : Icc (T - b ^ 2) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hle : T - r ≤ b ^ 2 := by linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ Icc (0 : Real) b := by
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      calc
        Real.sqrt (T - r) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
        _ = b := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb0]
    have hregR := hreg (Real.sqrt (T - r)) hsqrt
    have heqR : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heqR] using hregR)
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    intro s hs
    have hsq : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb0.le).2 hs.2
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hact : lRegAction S T gamma 0 b =
      lRegAction S T (lRegCurve S T x Z) 0 b := by
    apply lRegAction_congr (I := I) S T gamma (lRegCurve S T x Z) 0 b
    intro s hs
    apply heq
    have hs' : s ∈ Ioo (0 : Real) b := by
      simpa only [uIoo_of_le hb0.le] using hs
    exact ⟨hs'.1.le, hs'.2.le⟩
  have hrho0 : rho 0 = 0 := by
    simpa only [id_eq] using hrho_id ⟨le_rfl, hb0.le⟩
  have hrhob : rho b = b := by
    simpa only [id_eq] using hrho_id ⟨hb0.le, le_rfl⟩
  have hback' : ∀ s ∈ Icc (0 : Real) (Real.sqrt (b ^ 2)),
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb0] using hback
  have hreg' : ∀ s ∈ Icc (0 : Real) (Real.sqrt (b ^ 2)),
      T - s ^ 2 ∈ D.regular := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb0] using hreg
  have hA' : lRegAction S T gamma 0 (Real.sqrt (b ^ 2)) < A := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb0, hact]
    exact hA
  exact lCost_lt_event (I := I) S hS T (T - b ^ 2) T (b ^ 2)
    (sq_pos_of_pos hb0) htime hback' x (lRegCurve S T x Z b) gamma hgamma
    (by simp only [gamma, hrho0, lRegCurve_zero])
    (by simp only [gamma, Real.sqrt_sq_eq_abs, abs_of_pos hb0, hrhob])
    hreg' A hA' q hq

theorem lMinVec_end_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z)
    (W : Nat → TangentSpace I x)
    (hmin : ∀ n, (W n, b ^ 2) ∈ lMinDomain S T x)
    (hend : Tendsto (fun n ↦ lExp S T x (W n) (b ^ 2)) atTop
      (nhds (lRegCurve S T x Z b))) :
    Bornology.IsBounded (Set.range W) := by
  let act : Nat → Real := fun n ↦
    lRegAction S T (lRegCurve S T x (W n)) 0 b
  let A : Real := lRegAction S T (lRegCurve S T x Z) 0 b + 1
  have hA : lRegAction S T (lRegCurve S T x Z) 0 b < A := by
    dsimp only [A]
    linarith
  have hcost : ∀ᶠ n in atTop,
      lCost S T x (lExp S T x (W n) (b ^ 2)) (b ^ 2) < A :=
    lCost_ray_near (I := I) S hS T x Z b hb0 hb A hA
      (fun n ↦ lExp S T x (W n) (b ^ 2)) hend
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcost
  have hactEq (n : Nat) : act n =
      lCost S T x (lExp S T x (W n) (b ^ 2)) (b ^ 2) := by
    have hminEq := ((mem_lMinDomain S T x (W n) (b ^ 2)).1 (hmin n)).2
    calc
      act n = lLength S T
          (squareRootReparametrization (lRegCurve S T x (W n))) 0 (b ^ 2) := by
        simpa only [act, Real.sqrt_sq_eq_abs, abs_of_pos hb0] using
          (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x (W n))
            (b ^ 2) (sq_nonneg b)).symm
      _ = lCost S T x (lExp S T x (W n) (b ^ 2)) (b ^ 2) := by
        rw [show squareRootReparametrization (lRegCurve S T x (W n)) =
          (fun r ↦ lRegCurve S T x (W n) (Real.sqrt r)) by rfl]
        exact hminEq
  let A' : Real := max A 0 + ∑ i ∈ Finset.range N, |act i|
  have hact (n : Nat) : act n ≤ A' := by
    by_cases hn : n < N
    · have habs : |act n| ≤ ∑ i ∈ Finset.range N, |act i| := by
        exact Finset.single_le_sum
          (fun i hi ↦ abs_nonneg (act i)) (Finset.mem_range.mpr hn)
      calc
        act n ≤ |act n| := le_abs_self (act n)
        _ ≤ ∑ i ∈ Finset.range N, |act i| := habs
        _ ≤ A' := by
          dsimp only [A']
          exact le_add_of_nonneg_left (le_max_right A 0)
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have hlt : act n < A := by
        rw [hactEq n]
        exact hN n hn'
      calc
        act n ≤ A := hlt.le
        _ ≤ max A 0 := le_max_left A 0
        _ ≤ A' := by
          dsimp only [A']
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ abs_nonneg (act i))
  have hslab : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hle : T - r ≤ b ^ 2 := by linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ Icc (0 : Real) b := by
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      calc
        Real.sqrt (T - r) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
        _ = b := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hb0]
    have hreg := lRegDomain_reg S T x Z
      (lRegDomain_seg S T x Z hb hsqrt.1 hsqrt.2)
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hreg
  have hdom (n : Nat) : b ∈ lRegDomain S T x (W n) := by
    have hpos := ((mem_lMinDomain S T x (W n) (b ^ 2)).1 (hmin n)).1
    have hdata := (mem_lExpPosDom S T x (W n) (b ^ 2)).1 hpos
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb0] using hdata.2.2
  apply isBounded_range_initialVector_of_lRegAction_le_fixed_parameter (I := I) S hS T x W b A' hb0 hslab hdom
  intro n
  simpa only [act] using hact n

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
