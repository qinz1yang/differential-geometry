import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.Attainment

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def redMinVal (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x : M) (tau : Real) : Real :=
  sInf (range fun y : M ↦ redLength S T x y tau)

def redMinAct (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x : M) (b : Real) : Real :=
  2 * b * redMinVal S T x (b ^ 2)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem redMinVal_eq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real)
    (hmin : ∀ z : M, redLength S T x y tau ≤ redLength S T x z tau) :
    redMinVal S T x tau = redLength S T x y tau := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨redLength S T x y tau, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hmin z
    · exact mem_range_self y
  · apply le_csInf
    · exact ⟨redLength S T x y tau, mem_range_self y⟩
    · rintro _ ⟨z, rfl⟩
      exact hmin z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_redMin_vec [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (tau : Real) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) :
    ∃ (y : M) (Z : TangentSpace I x),
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y ∧
      redMinVal S T x tau = redLength S T x y tau ∧
      ∀ z : M, redLength S T x y tau ≤ redLength S T x z tau := by
  obtain ⟨y, hy⟩ := exists_redMin_rm (I := I) S hS K T hg tau htau hreg hRm x
  let b : Real := Real.sqrt tau
  have hb : 0 < b := by simpa only [b] using Real.sqrt_pos.2 htau
  obtain ⟨alpha0, halpha0, halpha00, halpha0b⟩ :
      ∃ alpha0 : Real → M, ContMDiff 𝓘(Real, Real) I 1 alpha0 ∧
        alpha0 0 = x ∧ alpha0 (Real.sqrt tau) = y := by
    let g := S.base.metric T
    let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E
        (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
      lt_of_le_of_ne le_top
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) x y)
    obtain ⟨path, hpath, _hlen⟩ :=
      DifferentialGeometry.Geometry.Riemannian.CGT.exists_flat_path
        (I := I) hxy
    let alpha0 : Real → M := fun s ↦ path.extend (s / b)
    have halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0 := by
      apply hpath.c1.comp
      rw [contMDiff_iff_contDiff]
      fun_prop
    refine ⟨alpha0, halpha0, ?_, ?_⟩
    · simp only [alpha0, zero_div, Path.extend_zero]
    · simp only [alpha0, b, div_self hb.ne', Path.extend_one]
  obtain ⟨Z, hZmin, hZend⟩ :=
    exists_lMinVec_rm (I := I) S hS K T hg tau htau hreg hRm
      x y alpha0 halpha0 halpha00 halpha0b
  exact ⟨y, Z, hZmin, hZend, redMinVal_eq S T x y tau hy, hy⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem redMinAct_eq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (b : Real) (hb : 0 < b) (Z : TangentSpace I x)
    (hZmin : (Z, b ^ 2) ∈ lMinDomain S T x)
    (hZend : lExp S T x Z (b ^ 2) = y)
    (hmin : ∀ z : M,
      redLength S T x y (b ^ 2) ≤ redLength S T x z (b ^ 2)) :
    lRegAction S T (lRegCurve S T x Z) 0 b = redMinAct S T x b := by
  have hlen : lRegAction S T (lRegCurve S T x Z) 0 b =
      lLength S T (fun r : Real ↦ lExp S T x Z r) 0 (b ^ 2) := by
    change lRegAction S T (lRegCurve S T x Z) 0 b =
      lLength S T (squareRootReparametrization (lRegCurve S T x Z)) 0 (b ^ 2)
    simpa only [Real.sqrt_sq hb.le] using
      (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x Z)
        (b ^ 2) (sq_nonneg b)).symm
  have hcost := ((mem_lMinDomain S T x Z (b ^ 2)).1 hZmin).2
  have hact : lRegAction S T (lRegCurve S T x Z) 0 b =
      lCost S T x y (b ^ 2) := by
    rw [hlen, hcost, hZend]
  rw [redMinAct, redMinVal_eq S T x y (b ^ 2) hmin, redLength,
    Real.sqrt_sq hb.le, ← hact]
  field_simp [hb.ne']

private def redPotBound (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E]
    (K sigma : Real) : Real :=
  2 * sigma * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem redPotBound_nonneg
    (K sigma : Real) (hsigma : 0 ≤ sigma) :
    0 ≤ redPotBound E K sigma := by
  exact mul_nonneg (mul_nonneg (by norm_num) hsigma)
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K))

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
private theorem scalar_abs_rm
    (S : SolutionOn (I := I) (M := M) D) (K T sigma : Real)
    (hsigma : 0 ≤ sigma)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (y : M) (s : Real)
    (hs : s ∈ Icc (0 : Real) (Real.sqrt sigma)) :
    |S.scalar (T - s ^ 2) y| ≤
      (Module.finrank Real E : Real) ^ 2 * Real.sqrt K := by
  have hs2 : s ^ 2 ≤ sigma := by
    rw [← Real.sq_sqrt hsigma]
    exact (sq_le_sq₀ hs.1 (Real.sqrt_nonneg sigma)).2 hs.2
  have ht : T - s ^ 2 ∈ Icc (T - sigma) T := by
    constructor <;> linarith [sq_nonneg s]
  have hscalar := scalar_abs_le_rm (I := I) (S.base.metric (T - s ^ 2)) y
  have hout := hscalar.trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hRm _ ht y)) (sq_nonneg _))
  rw [show Module.finrank Real (TangentSpace I y) =
    Module.finrank Real E from rfl] at hout
  simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
    metricRm04_apply] using hout

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
private theorem lRegLag_ge_rm
    (S : SolutionOn (I := I) (M := M) D) (K T sigma : Real)
    (hsigma : 0 ≤ sigma)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (alpha : Real → M) (s : Real)
    (hs : s ∈ Icc (0 : Real) (Real.sqrt sigma)) :
    -redPotBound E K sigma ≤ lRegLagrangian S T alpha s := by
  let F : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  have hF : 0 ≤ F := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have hs2 : s ^ 2 ≤ sigma := by
    rw [← Real.sq_sqrt hsigma]
    exact (sq_le_sq₀ hs.1 (Real.sqrt_nonneg sigma)).2 hs.2
  have hscalar := scalar_abs_rm (I := I) S K T sigma hsigma hRm (alpha s) s hs
  have hlow : -F ≤ S.scalar (T - s ^ 2) (alpha s) := by
    simpa only [F] using neg_le_of_abs_le hscalar
  have hpot : -redPotBound E K sigma ≤
      2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) := by
    have hmul : 2 * s ^ 2 * (-F) ≤
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) :=
      mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num) (sq_nonneg s))
    have hsq : 2 * s ^ 2 * F ≤ 2 * sigma * F :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hF
    dsimp only [redPotBound, F]
    linarith
  have hspeed := lRegSpeedSq_nonneg (I := I) S T alpha s
  dsimp only [lRegLagrangian]
  change 0 ≤ (S.base.metric (T - s ^ 2)).inner (alpha s)
    (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) at hspeed
  linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
private theorem lRegLag_const_le
    (S : SolutionOn (I := I) (M := M) D) (K T sigma : Real)
    (hsigma : 0 ≤ sigma)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (y : M) (s : Real)
    (hs : s ∈ Icc (0 : Real) (Real.sqrt sigma)) :
    lRegLagrangian S T (fun _ : Real ↦ y) s ≤ redPotBound E K sigma := by
  let F : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K
  have hF : 0 ≤ F := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have hs2 : s ^ 2 ≤ sigma := by
    rw [← Real.sq_sqrt hsigma]
    exact (sq_le_sq₀ hs.1 (Real.sqrt_nonneg sigma)).2 hs.2
  have hscalar := scalar_abs_rm (I := I) S K T sigma hsigma hRm y s hs
  have hupp : S.scalar (T - s ^ 2) y ≤ F := by
    simpa only [F] using le_of_abs_le hscalar
  have hpot : 2 * s ^ 2 * S.scalar (T - s ^ 2) y ≤
      redPotBound E K sigma := by
    have hmul : 2 * s ^ 2 * S.scalar (T - s ^ 2) y ≤ 2 * s ^ 2 * F :=
      mul_le_mul_of_nonneg_left hupp (mul_nonneg (by norm_num) (sq_nonneg s))
    have hsq : 2 * s ^ 2 * F ≤ 2 * sigma * F :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hF
    exact hmul.trans (by simpa only [redPotBound, F] using hsq)
  dsimp only [lRegLagrangian, redPotBound]
  have hvel : lVelocity (I := I) (fun _ : Real ↦ y) s = 0 := by
    simp only [lVelocity, mfderiv_const]
    rfl
  rw [hvel]
  simp only [map_zero, mul_zero, zero_add]
  simpa only [redPotBound] using hpot

omit [NeZero (Module.finrank Real E)]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
private theorem lRegAct_const_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma b c : Real) (hsigma : 0 ≤ sigma)
    (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ Real.sqrt sigma)
    (hreg : Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (y : M) :
    lRegAction S T (fun _ : Real ↦ y) b c ≤
      redPotBound E K sigma * (c - b) := by
  have hseg : Icc b c ⊆ Icc (0 : Real) (Real.sqrt sigma) := by
    intro s hs
    exact ⟨hb.trans hs.1, hs.2.trans hc⟩
  have hregBack : ∀ s ∈ Icc b c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs' := hseg hs
    have hs2 : s ^ 2 ≤ sigma := by
      rw [← Real.sq_sqrt hsigma]
      exact (sq_le_sq₀ hs'.1 (Real.sqrt_nonneg sigma)).2 hs'.2
    constructor <;> linarith [sq_nonneg s]
  have hint := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T b c hbc (fun _ : Real ↦ y)
      contMDiff_const.contMDiffOn hregBack
  have hmono : lRegAction S T (fun _ : Real ↦ y) b c ≤
      ∫ _s in b..c, redPotBound E K sigma := by
    exact intervalIntegral.integral_mono_on hbc hint intervalIntegrable_const
      (fun s hs ↦ lRegLag_const_le (I := I) S K T sigma hsigma hRm y s (hseg hs))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, lRegAction,
    mul_comm] using hmono

omit [NeZero (Module.finrank Real E)]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
private theorem lRegAct_tail_ge
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma b c : Real) (hsigma : 0 ≤ sigma)
    (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ Real.sqrt sigma)
    (hreg : Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (Icc b c)) :
    -redPotBound E K sigma * (c - b) ≤ lRegAction S T alpha b c := by
  have hseg : Icc b c ⊆ Icc (0 : Real) (Real.sqrt sigma) := by
    intro s hs
    exact ⟨hb.trans hs.1, hs.2.trans hc⟩
  have hregBack : ∀ s ∈ Icc b c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs' := hseg hs
    have hs2 : s ^ 2 ≤ sigma := by
      rw [← Real.sq_sqrt hsigma]
      exact (sq_le_sq₀ hs'.1 (Real.sqrt_nonneg sigma)).2 hs'.2
    constructor <;> linarith [sq_nonneg s]
  have hint := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T b c hbc alpha halpha hregBack
  have hmono : (∫ _s in b..c, -redPotBound E K sigma) ≤
      lRegAction S T alpha b c := by
    exact intervalIntegral.integral_mono_on hbc intervalIntegrable_const hint
      (fun s hs ↦ lRegLag_ge_rm (I := I) S K T sigma hsigma hRm alpha s (hseg hs))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, lRegAction,
    mul_comm] using hmono

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem redMinAct_ord [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (hsigma : 0 < sigma)
    (hreg : Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) {a b : Real} (ha : 0 < a) (hab : a < b)
    (hb : b < Real.sqrt sigma) :
    |redMinAct S T x b - redMinAct S T x a| ≤
      redPotBound E K sigma * (b - a) := by
  have hb0 : 0 < b := ha.trans hab
  have ha2b2 : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha.le hb0.le).2 hab.le
  have hb2sigma : b ^ 2 ≤ sigma := by
    rw [← Real.sq_sqrt hsigma.le]
    exact (sq_le_sq₀ hb0.le (Real.sqrt_nonneg sigma)).2 hb.le
  have hregB : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro q hq
    exact hreg ⟨(sub_le_sub_left hb2sigma T).trans hq.1, hq.2⟩
  have hRmB : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    intro q hq z
    exact hRm q ⟨(sub_le_sub_left hb2sigma T).trans hq.1, hq.2⟩ z
  have hregA : Icc (T - a ^ 2) T ⊆ D.regular := by
    intro q hq
    exact hregB ⟨(sub_le_sub_left ha2b2 T).trans hq.1, hq.2⟩
  have hRmA : ∀ q ∈ Icc (T - a ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    intro q hq z
    exact hRmB q ⟨(sub_le_sub_left ha2b2 T).trans hq.1, hq.2⟩ z
  obtain ⟨ya, Za, hZaMin, hZaEnd, hvalA, hminA⟩ :=
    exists_redMin_vec (I := I) S hS K T hg (a ^ 2) (sq_pos_of_pos ha)
      hregA hRmA x
  obtain ⟨yb, Zb, hZbMin, hZbEnd, hvalB, hminB⟩ :=
    exists_redMin_vec (I := I) S hS K T hg (b ^ 2) (sq_pos_of_pos hb0)
      hregB hRmB x
  have hZaDom : a ∈ lRegDomain S T x Za := by
    have hdom := (((mem_lExpPosDom S T x Za (a ^ 2)).1
      ((mem_lMinDomain S T x Za (a ^ 2)).1 hZaMin).1).2).2
    simpa only [lExpDomain, Real.sqrt_sq_eq_abs, abs_of_pos ha] using hdom
  have hZbDom : b ∈ lRegDomain S T x Zb := by
    have hdom := (((mem_lExpPosDom S T x Zb (b ^ 2)).1
      ((mem_lMinDomain S T x Zb (b ^ 2)).1 hZbMin).1).2).2
    simpa only [lExpDomain, Real.sqrt_sq_eq_abs, abs_of_pos hb0] using hdom
  have hcurveA : lRegCurve S T x Za a = ya := by
    simpa only [lExp, Real.sqrt_sq ha.le] using hZaEnd
  have hactA : lRegAction S T (lRegCurve S T x Za) 0 a =
      redMinAct S T x a :=
    redMinAct_eq (I := I) S T x ya a ha Za hZaMin hZaEnd hminA
  have hactB : lRegAction S T (lRegCurve S T x Zb) 0 b =
      redMinAct S T x b :=
    redMinAct_eq (I := I) S T x yb b hb0 Zb hZbMin hZbEnd hminB
  have hregBackB : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hregB
    have hs2 : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb0.le).2 hs.2
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hbdd := lRegCosts_bdd_rm (I := I) S hS K T 0 b le_rfl hb0.le
    hregB hRmB x ya
  have hjoin := lCost_le_join_bdd (I := I) S hS T b hb0 x ya
    ha hab hbdd hregBackB (lRegCurve S T x Za) (fun _ : Real ↦ ya)
    (lRegCurve_c1On (I := I) S hS T x Za hZaDom)
    contMDiff_const.contMDiffOn hcurveA
    (by simp only [lRegCurve_zero]) rfl
  have hconst := lRegAct_const_le (I := I) S hS K T sigma a b hsigma.le
    ha.le hab.le hb.le hreg hRm ya
  have hminCostB : redMinAct S T x b ≤ lCost S T x ya (b ^ 2) := by
    calc
      redMinAct S T x b = 2 * b * redLength S T x yb (b ^ 2) := by
        rw [redMinAct, hvalB]
      _ ≤ 2 * b * redLength S T x ya (b ^ 2) :=
        mul_le_mul_of_nonneg_left (hminB ya)
          (mul_nonneg (by norm_num) hb0.le)
      _ = lCost S T x ya (b ^ 2) := by
        rw [redLength, Real.sqrt_sq hb0.le]
        field_simp [hb0.ne']
  have hupp : redMinAct S T x b ≤
      redMinAct S T x a + redPotBound E K sigma * (b - a) := by
    calc
      redMinAct S T x b ≤ lCost S T x ya (b ^ 2) := hminCostB
      _ ≤ lRegAction S T (lRegCurve S T x Za) 0 a +
          lRegAction S T (fun _ : Real ↦ ya) a b := hjoin
      _ ≤ redMinAct S T x a + redPotBound E K sigma * (b - a) := by
        rw [hactA]
        simpa only [add_comm] using add_le_add_left hconst (redMinAct S T x a)
  have hZbA : a ∈ lRegDomain S T x Zb :=
    lRegDomain_seg S T x Zb hZbDom ha.le hab.le
  have hcurveB := lRegCurve_c1On (I := I) S hS T x Zb hZbDom
  have hcurveHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (lRegCurve S T x Zb) (Icc (0 : Real) a) :=
    hcurveB.mono fun s hs ↦ ⟨hs.1, hs.2.trans hab.le⟩
  have hcurveTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (lRegCurve S T x Zb) (Icc a b) :=
    hcurveB.mono fun s hs ↦ ⟨ha.le.trans hs.1, hs.2⟩
  have hheadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T 0 a ha.le (lRegCurve S T x Zb) hcurveHead
      (fun s hs ↦ lRegDomain_reg S T x Zb
        (lRegDomain_seg S T x Zb hZbDom hs.1 (hs.2.trans hab.le)))
  have htailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T a b hab.le (lRegCurve S T x Zb) hcurveTail
      (fun s hs ↦ lRegDomain_reg S T x Zb
        (lRegDomain_seg S T x Zb hZbDom (ha.le.trans hs.1) hs.2))
  have hadd := lRegAction_add (I := I) S T (lRegCurve S T x Zb) 0 a b
    hheadInt htailInt
  have htail := lRegAct_tail_ge (I := I) S hS K T sigma a b hsigma.le
    ha.le hab.le hb.le hreg hRm (lRegCurve S T x Zb) hcurveTail
  have hminCostA : redMinAct S T x a ≤
      lCost S T x (lRegCurve S T x Zb a) (a ^ 2) := by
    calc
      redMinAct S T x a = 2 * a * redLength S T x ya (a ^ 2) := by
        rw [redMinAct, hvalA]
      _ ≤ 2 * a * redLength S T x (lRegCurve S T x Zb a) (a ^ 2) :=
        mul_le_mul_of_nonneg_left (hminA (lRegCurve S T x Zb a))
          (mul_nonneg (by norm_num) ha.le)
      _ = lCost S T x (lRegCurve S T x Zb a) (a ^ 2) := by
        rw [redLength, Real.sqrt_sq ha.le]
        field_simp [ha.ne']
  have hbddA := lRegCosts_bdd_rm (I := I) S hS K T 0 a le_rfl ha.le
    hregA hRmA x (lRegCurve S T x Zb a)
  have hcostRayA := lCost_le_ray_bdd (I := I) S hS T x Zb a ha hZbA hbddA
  have hheadLe : lRegAction S T (lRegCurve S T x Zb) 0 a ≤
      redMinAct S T x b + redPotBound E K sigma * (b - a) := by
    rw [← hactB, ← hadd]
    linarith
  have hlow : redMinAct S T x a ≤
      redMinAct S T x b + redPotBound E K sigma * (b - a) := by
    calc
      redMinAct S T x a ≤
          lCost S T x (lRegCurve S T x Zb a) (a ^ 2) := hminCostA
      _ ≤ lRegAction S T (lRegCurve S T x Zb) 0 a := hcostRayA
      _ ≤ redMinAct S T x b + redPotBound E K sigma * (b - a) := hheadLe
  rw [abs_le]
  constructor <;> linarith

theorem redMinAct_lip [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (hsigma : 0 < sigma)
    (hreg : Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) :
    ∃ C : NNReal, LipschitzOnWith C (redMinAct S T x)
      (Ioo 0 (Real.sqrt sigma)) := by
  let P : Real := redPotBound E K sigma
  refine ⟨Real.toNNReal P,
    LipschitzOnWith.of_dist_le' (K := P) ?_⟩
  intro a ha b hb
  rcases lt_trichotomy a b with hab | hab | hab
  · have hord := redMinAct_ord (I := I) S hS K T sigma hg hsigma hreg hRm x
      ha.1 hab hb.2
    simpa only [P, Real.dist_eq, abs_sub_comm,
      abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub] using hord
  · subst b
    simp only [dist_self, mul_zero, le_refl]
  · rw [dist_comm (redMinAct S T x a) (redMinAct S T x b), dist_comm a b]
    have hord := redMinAct_ord (I := I) S hS K T sigma hg hsigma hreg hRm x
      hb.1 hab ha.2
    simpa only [P, Real.dist_eq, abs_sub_comm,
      abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub] using hord

theorem redMinVal_cont [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (hsigma : 0 < sigma)
    (hreg : Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) :
    ContinuousOn (redMinVal S T x) (Ioo 0 sigma) := by
  obtain ⟨C, hC⟩ := redMinAct_lip (I := I) S hS K T sigma hg hsigma hreg hRm x
  have hsqrt : MapsTo Real.sqrt (Ioo (0 : Real) sigma)
      (Ioo 0 (Real.sqrt sigma)) := by
    intro tau htau
    exact ⟨Real.sqrt_pos.2 htau.1,
      Real.sqrt_lt_sqrt htau.1.le htau.2⟩
  have hnum : ContinuousOn
      (fun tau : Real ↦ redMinAct S T x (Real.sqrt tau)) (Ioo 0 sigma) :=
    hC.continuousOn.comp' continuousOn_id.sqrt hsqrt
  have hden : ContinuousOn (fun tau : Real ↦ 2 * Real.sqrt tau)
      (Ioo 0 sigma) :=
    continuousOn_const.mul continuousOn_id.sqrt
  have hquot : ContinuousOn
      (fun tau : Real ↦ redMinAct S T x (Real.sqrt tau) /
        (2 * Real.sqrt tau)) (Ioo 0 sigma) :=
    hnum.div₀ hden fun tau htau ↦
      mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau.1).ne'
  refine hquot.congr ?_
  intro tau htau
  change redMinVal S T x tau =
    redMinAct S T x (Real.sqrt tau) / (2 * Real.sqrt tau)
  rw [redMinAct, Real.sq_sqrt htau.1.le]
  field_simp [(Real.sqrt_pos.2 htau.1).ne']

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
