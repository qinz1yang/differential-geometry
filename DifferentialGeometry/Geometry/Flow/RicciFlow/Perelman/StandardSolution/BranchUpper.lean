import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
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

theorem lActBranch_upper_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConjugate S T x Z tau)
    (hbdd : ∀ᶠ y in nhds (lExp S T x Z tau),
      BddBelow {r : ℝ | ∃ gamma : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
          gamma 0 = x ∧ gamma (Real.sqrt tau) = y ∧
          lRegularizedAction S T gamma 0 (Real.sqrt tau) = r}) :
    (fun y : M => lCost S T x y tau) ≤ᶠ[nhds (lExp S T x Z tau)]
      lActBranch S hS T x Z tau hdom hconj := by
  let z : E := Z
  let hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) I ∞
      (fun W : E => lExp S T x W tau) z :=
    lExp_localDiffeo S hS T x Z tau hdom hconj
  let y0 : M := lExp S T x Z tau
  let U : Set E := {W : E | (W, tau) ∈ lExpPosDom S T x}
  have hUopen : IsOpen U := by
    have hpair : Continuous (fun W : E => (W, tau)) :=
      continuous_id.prodMk continuous_const
    exact (lExpPosDom_open S hS T x).preimage hpair
  have hzU : z ∈ U := hdom
  have hinv : hloc.localInverse y0 = z :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hsrc : hloc.localInverse.source ∈ nhds y0 :=
    hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
  have hpre : hloc.localInverse ⁻¹' U ∈ nhds y0 := by
    apply hloc.contMDiffAt_localInverse.continuousAt.preimage_mem_nhds
    rw [hinv]
    exact hUopen.mem_nhds hzU
  filter_upwards [hsrc, hpre, hbdd] with y hySrc hyU hybdd
  let W : E := hloc.localInverse y
  have hWpos : (W, tau) ∈ lExpPosDom S T x := hyU
  rcases (mem_lExpPosDom S T x W tau).1 hWpos with
    ⟨htau, _hTtau, hWdom⟩
  have hright : lExp S T x W tau = y :=
    hloc.localInverse_right_inv hySrc
  have hWbdd : BddBelow {r : ℝ | ∃ gamma : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
        gamma 0 = x ∧
        gamma (Real.sqrt tau) = lExp S T x W tau ∧
        lRegularizedAction S T gamma 0 (Real.sqrt tau) = r} := by
    rw [hright]
    exact hybdd
  have hle := lCost_le_ray_bdd (I := I) S hS T x W
    (Real.sqrt tau) (Real.sqrt_pos.2 htau) hWdom hWbdd
  have hle' : lCost S T x (lExp S T x W tau) tau ≤
      lRegularizedAction S T (lRegularizedCurve S T x W) 0 (Real.sqrt tau) := by
    simpa only [lExp, Real.sq_sqrt htau.le] using hle
  change lCost S T x y tau ≤
    lRegularizedAction S T (lRegularizedCurve S T x W) 0 (Real.sqrt tau)
  simpa only [hright] using hle'

theorem lActBranch_upper_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConjugate S T x Z tau)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    (fun y : M => lCost S T x y tau) ≤ᶠ[nhds (lExp S T x Z tau)]
      lActBranch S hS T x Z tau hdom hconj := by
  have htau : 0 < tau := ((mem_lExpPosDom S T x Z tau).1 hdom).1
  have hreg : Icc (T - tau) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ tau := by
      linarith [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈
        Icc (0 : ℝ) (Real.sqrt tau) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  apply lActBranch_upper_of_bdd (I := I) S hS T x Z tau hdom hconj
  exact Filter.Eventually.of_forall (fun y =>
    lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt tau)
      le_rfl (Real.sqrt_nonneg tau)
      (by simpa only [Real.sq_sqrt htau.le] using hreg)
      (by simpa only [Real.sq_sqrt htau.le] using hRm)
      x y)

theorem lCost_nondiff_two_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) {Z W : TangentSpace I x} {tau : ℝ}
    (hZmin : (Z, tau) ∈ lMinDomain S T x)
    (hWmin : (W, tau) ∈ lMinDomain S T x)
    (hZconj : ¬ IsLConjugate S T x Z tau)
    (hWconj : ¬ IsLConjugate S T x W tau)
    (hZW : Z ≠ W)
    (hpos : lExp S T x Z tau = lExp S T x W tau)
    (hbdd : ∀ᶠ y in nhds (lExp S T x Z tau),
      BddBelow {r : ℝ | ∃ gamma : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 gamma ∧ gamma 0 = x ∧ gamma (Real.sqrt tau) = y ∧
          lRegularizedAction S T gamma 0 (Real.sqrt tau) = r}) :
    ¬ MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => lCost S T x y tau) (lExp S T x Z tau) := by
  let hZdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hZmin).1
  let hWdom : (W, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x W tau).1 hWmin).1
  let b : ℝ := Real.sqrt tau
  let y : M := lExp S T x Z tau
  let vZ : TangentSpace I y :=
    lVelocity (I := I) (lRegularizedCurve S T x Z) b
  let vW : TangentSpace I y :=
    lVelocity (I := I) (lRegularizedCurve S T x W) b
  let V : TangentSpace I y := vZ - vW
  obtain ⟨UZ, hUZopen, hyUZ, hZder⟩ :=
    exists_branch_deriv S hS T x Z tau hZdom hZconj
  obtain ⟨UW, hUWopen, hyWU, hWder⟩ :=
    exists_branch_deriv S hS T x W tau hWdom hWconj
  have hyUW : y ∈ UW := by
    dsimp only [y]
    rw [hpos]
    exact hyWU
  obtain ⟨eta, heta, hetaU, heta0, hetaVel⟩ :=
    exists_smooth_curve y V (UZ ∩ UW) (hUZopen.inter hUWopen)
      ⟨by simpa only [y] using hyUZ, hyUW⟩
  have hetaZ : ∀ u : ℝ, eta u ∈ UZ :=
    fun u => (hetaU u).1
  have hetaW : ∀ u : ℝ, eta u ∈ UW :=
    fun u => (hetaU u).2
  have heta0Z : eta 0 = lExp S T x Z tau := by
    simpa only [y] using heta0
  have heta0W : eta 0 = lExp S T x W tau := heta0Z.trans hpos
  have hetaVel' : lVelocity (I := I) eta 0 = V := by
    simpa only [lVelocity] using hetaVel
  let F : ℝ → ℝ := fun u =>
    lActBranch S hS T x Z tau hZdom hZconj (eta u)
  let G : ℝ → ℝ := fun u =>
    lActBranch S hS T x W tau hWdom hWconj (eta u)
  let c : ℝ → ℝ := fun u => lCost S T x (eta u) tau
  have heta8 : ContMDiff (modelWithCornersSelf ℝ ℝ) I (8 : Nat) eta :=
    heta.of_le (by
      change (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hFd : HasDerivAt F
      ((S.base.metric (T - tau)).inner y V vZ) 0 := by
    simpa only [F, y, b, vZ, hetaVel'] using
      hZder eta heta8 hetaZ heta0Z
  have hGd : HasDerivAt G
      ((S.base.metric (T - tau)).inner y V vW) 0 := by
    have hraw := hWder eta heta8 hetaW heta0W
    rw [← hpos] at hraw
    simpa only [G, y, b, vW, hetaVel'] using hraw
  have hZup : c ≤ᶠ[nhds (0 : ℝ)] F := by
    have htend : Tendsto eta (nhds (0 : ℝ)) (nhds y) := by
      have hcont : ContinuousAt eta (0 : ℝ) :=
        heta.continuous.continuousAt
      change Tendsto eta (nhds (0 : ℝ)) (nhds (eta 0)) at hcont
      rw [heta0] at hcont
      exact hcont
    have hup := htend.eventually
      (lActBranch_upper_of_bdd S hS T x Z tau hZdom hZconj hbdd)
    change ∀ᶠ u in nhds (0 : ℝ),
      lCost S T x (eta u) tau ≤
        lActBranch S hS T x Z tau hZdom hZconj (eta u)
    exact hup
  have hWup : c ≤ᶠ[nhds (0 : ℝ)] G := by
    have htend : Tendsto eta (nhds (0 : ℝ))
        (nhds (lExp S T x W tau)) := by
      have hcont : ContinuousAt eta (0 : ℝ) :=
        heta.continuous.continuousAt
      change Tendsto eta (nhds (0 : ℝ)) (nhds (eta 0)) at hcont
      rw [heta0W] at hcont
      exact hcont
    have hup := htend.eventually
      (lActBranch_upper_of_bdd S hS T x W tau hWdom hWconj (by simpa only [← hpos] using hbdd))
    change ∀ᶠ u in nhds (0 : ℝ),
      lCost S T x (eta u) tau ≤
        lActBranch S hS T x W tau hWdom hWconj (eta u)
    exact hup
  have hFtouch : F 0 = c 0 := by
    simpa only [F, c, heta0Z] using
      lActBranch_touch S hS T x Z tau hZmin hZconj
  have hGtouch : G 0 = c 0 := by
    simpa only [G, c, heta0W] using
      lActBranch_touch S hS T x W tau hWmin hWconj
  rcases (mem_lExpPosDom S T x Z tau).1 hZdom with
    ⟨_htau, _hZtau, hZb⟩
  rcases (mem_lExpPosDom S T x W tau).1 hWdom with
    ⟨_hWtau, _hWtau0, hWb⟩
  have hvelNe : vZ ≠ vW := by
    apply lRegularizedCurve_endpoint_velocity_ne_of_initialVector_ne_of_endpoint_eq S hS T x hZb hWb hZW
    simpa only [vZ, vW, y, b, lExp] using hpos
  have hVne : V ≠ 0 := sub_ne_zero.mpr hvelNe
  have hvalNe :
      (S.base.metric (T - tau)).inner y V vZ ≠
        (S.base.metric (T - tau)).inner y V vW := by
    intro heq
    have hzero : (S.base.metric (T - tau)).inner y V V = 0 := by
      dsimp only [V]
      rw [((S.base.metric (T - tau)).inner y (vZ - vW)).map_sub,
        heq, sub_self]
    exact (ne_of_gt ((S.base.metric (T - tau)).pos y V hVne)) hzero
  have hderNe : fderiv ℝ F 0 ≠ fderiv ℝ G 0 := by
    intro heq
    have happ := congrArg (fun L : ℝ →L[ℝ] ℝ => L (1 : ℝ)) heq
    rw [hFd.hasFDerivAt.fderiv, hGd.hasFDerivAt.fderiv] at happ
    exact hvalNe (by simpa using happ)
  have hcnot : ¬ DifferentiableAt ℝ c 0 :=
    not_diff_two_upper hFd.differentiableAt hGd.differentiableAt
      hZup hWup hFtouch hGtouch hderNe
  intro hcost
  have hetaMd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I eta 0 :=
    heta.mdifferentiableAt (by norm_num)
  have hcomp : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ)
      ((fun q : M => lCost S T x q tau) ∘ eta) 0 :=
    MDifferentiableAt.comp_of_eq (x := (0 : ℝ)) (f := eta)
      hcost hetaMd heta0Z
  apply hcnot
  exact mdifferentiableAt_iff_differentiableAt.mp
    (by
      change MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ)
        (fun u : ℝ => lCost S T x (eta u) tau) 0 at hcomp
      exact hcomp)

theorem lCost_nondiff_two_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M) {Z W : TangentSpace I x} {tau : ℝ}
    (hZmin : (Z, tau) ∈ lMinDomain S T x)
    (hWmin : (W, tau) ∈ lMinDomain S T x)
    (hZconj : ¬ IsLConjugate S T x Z tau)
    (hWconj : ¬ IsLConjugate S T x W tau)
    (hZW : Z ≠ W)
    (hpos : lExp S T x Z tau = lExp S T x W tau)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    ¬ MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => lCost S T x y tau) (lExp S T x Z tau) := by
  have hdom := ((mem_lMinDomain S T x Z tau).mp hZmin).1
  have htau := ((mem_lExpPosDom S T x Z tau).mp hdom).1
  have hreg : Icc (T - tau) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ tau := by linarith [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt tau) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by rw [Real.sq_sqrt hnonneg]; ring
    simpa only [heq] using hclock
  apply lCost_nondiff_two_of_bdd S hS T x hZmin hWmin hZconj hWconj hZW hpos
  exact Filter.Eventually.of_forall (fun y =>
    lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt tau) le_rfl (Real.sqrt_nonneg tau)
      (by simpa only [Real.sq_sqrt htau.le] using hreg)
      (by simpa only [Real.sq_sqrt htau.le] using hRm) x y)

end DifferentialGeometry.PDE.RicciFlow

end
