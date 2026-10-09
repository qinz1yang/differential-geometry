import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.Basic
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Barrier.Exponential
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def planeDirections : Fin 2 → ℂ := ![1, Complex.I]

private def planarOperator (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (beta : ℂ → Fin 2 → ℝ) (u : ℂ → ℝ) (x : ℂ) : ℝ :=
  (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
    fderiv ℝ (fderiv ℝ u) x (planeDirections i) (planeDirections j)) +
    ∑ i : Fin 2, beta x i * fderiv ℝ u x (planeDirections i)

private theorem fderiv_comp_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (p : F) {u : F → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u (p + L x)) :
    fderiv ℝ (fun y => u (p + L y)) x =
      (fderiv ℝ u (p + L x)).comp L := by
  have hT : HasFDerivAt (fun y => p + L y) L x :=
    L.hasFDerivAt.const_add p
  exact (hu.hasFDerivAt.comp x hT).fderiv

private theorem second_derivative_comp_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (p : F) {u : F → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (p + L x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => u (p + L y))) x v w =
      fderiv ℝ (fderiv ℝ u) (p + L x) (L v) (L w) := by
  have hT : HasFDerivAt (fun y => p + L y) L x :=
    L.hasFDerivAt.const_add p
  have hnear : fderiv ℝ (fun y => u (p + L y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ u (p + L y)).comp L := by
    filter_upwards [hT.continuousAt.eventually (hu.eventually (by norm_num))] with y hy
    exact fderiv_comp_affine L p (hy.differentiableAt (by norm_num))
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp x hT
  have hcomp := (hd.clm_comp (hasFDerivAt_const (𝕜 := ℝ) L x)).fderiv
  change fderiv ℝ (fun y => (fderiv ℝ u (p + L y)).comp L) x = _ at hcomp
  rw [hnear.fderiv_eq, hcomp]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]

private theorem planar_operator_affine
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ)
    (p : ℂ) {u : ℂ → ℝ} {x : Plane}
    (hu : ContDiffAt ℝ 2 u (p + Complex.orthonormalBasisOneI.repr.symm x)) :
    scalarEllipticOperator
        (fun y => A (p + Complex.orthonormalBasisOneI.repr.symm y))
        (fun y => beta (p + Complex.orthonormalBasisOneI.repr.symm y))
        (fun y => u (p + Complex.orthonormalBasisOneI.repr.symm y)) x =
      planarOperator A beta u (p + Complex.orthonormalBasisOneI.repr.symm x) := by
  let L : Plane →L[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hdir (i : Fin 2) : L (EuclideanSpace.single i 1) = planeDirections i := by
    fin_cases i <;> simp [L, planeDirections]
  have hfirst := fderiv_comp_affine L p (hu.differentiableAt (by norm_num))
  have hsecond (i j : Fin 2) := second_derivative_comp_affine L p hu
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  change scalarEllipticOperator (fun y => A (p + L y)) (fun y => beta (p + L y))
      (fun y => u (p + L y)) x = planarOperator A beta u (p + L x)
  simp only [scalarEllipticOperator, planarOperator, hfirst, hsecond,
    ContinuousLinearMap.comp_apply, hdir]

private def inwardBarrier (r k : ℝ) (x : Plane) : ℝ :=
  -exponentialBallBarrier r (-k) x

private theorem inwardBarrier_smooth (r k : ℝ) :
    ContDiff ℝ ∞ (inwardBarrier r k) :=
  (contDiff_exponentialBallBarrier r (-k)).neg

private theorem inwardBarrier_operator
    (A : Plane → Matrix (Fin 2) (Fin 2) ℝ) (beta : Plane → Fin 2 → ℝ)
    (r k : ℝ) (x : Plane) :
    scalarEllipticOperator A beta (inwardBarrier r k) x =
      Real.exp (-k * ‖x‖ ^ 2) *
        (4 * k ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, x i * A x i j * x j) -
          2 * k * ((∑ i : Fin 2, A x i i) + ∑ i : Fin 2, beta x i * x i)) := by
  have hD (i : Fin 2) : fderiv ℝ (inwardBarrier r k) x (EuclideanSpace.single i 1) =
      -(2 * k * Real.exp (-k * ‖x‖ ^ 2) * x i) := by
    change fderiv ℝ (fun y => -exponentialBallBarrier r (-k) y) x _ = _
    rw [fderiv_fun_neg, neg_apply]
    change -DeGiorgi.smoothGradField (exponentialBallBarrier r (-k)) x i = _
    rw [smoothGradField_exponentialBallBarrier]
    ring
  have hDD (i j : Fin 2) :
      fderiv ℝ (fderiv ℝ (inwardBarrier r k)) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        Real.exp (-k * ‖x‖ ^ 2) *
          (4 * k ^ 2 * x i * x j - 2 * k * (if i = j then 1 else 0)) := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (exponentialBallBarrier (d := 2) r (-k))) x :=
      ((contDiff_exponentialBallBarrier (d := 2) r (-k)).contDiffAt.fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have he : fderiv ℝ (fun y => DeGiorgi.smoothGradField
          (exponentialBallBarrier r (-k)) y j) x (EuclideanSpace.single i 1) =
        fderiv ℝ (fderiv ℝ (exponentialBallBarrier r (-k))) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
      change fderiv ℝ (fun y => fderiv ℝ (exponentialBallBarrier r (-k)) y
        (EuclideanSpace.single j 1)) x _ = _
      rw [fderiv_clm_apply hd (differentiableAt_const _)]
      simp
    have hnegfirst : fderiv ℝ (inwardBarrier r k) =
        fun y => -fderiv ℝ (exponentialBallBarrier r (-k)) y := by
      funext y
      exact fderiv_fun_neg
    simp only [hnegfirst, fderiv_fun_neg, neg_apply]
    rw [← he, fderiv_smoothGradField_exponentialBallBarrier]
    ring
  simp only [scalarEllipticOperator, hD, hDD, Fin.sum_univ_two]
  simp only [Fin.reduceEq, ite_true, ite_false]
  ring

private theorem inwardBarrier_inward_derivative
    {r k : ℝ} {q : Plane} (hq : ‖q‖ = r) :
    fderiv ℝ (inwardBarrier r k) q (-q) =
      2 * k * Real.exp (-k * r ^ 2) * r ^ 2 := by
  have hb := (((hasFDerivAt_id q).norm_sq.const_mul (-k)).exp).sub
    (hasFDerivAt_const (Real.exp (-k * r ^ 2)) q)
  have he := hb.fderiv
  change fderiv ℝ (fun x : Plane => Real.exp (-k * ‖x‖ ^ 2) -
    Real.exp (-k * r ^ 2)) q = _ at he
  have hfun : inwardBarrier r k =
      fun x : Plane => Real.exp (-k * ‖x‖ ^ 2) - Real.exp (-k * r ^ 2) := by
    funext x
    simp only [inwardBarrier, exponentialBallBarrier, neg_sub]
  rw [hfun, he]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, id_eq, innerSL_apply_apply,
    sub_zero, smul_eq_mul, inner_neg_right, real_inner_self_eq_norm_sq, hq]
  ring

private theorem exists_strict_inward_barrier
    {A : Plane → Matrix (Fin 2) (Fin 2) ℝ}
    {beta : Plane → Fin 2 → ℝ} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hA_cont : ∀ i j, ContinuousOn (fun x => A x i j) (closedBall 0 r))
    (hbeta_cont : ∀ i, ContinuousOn (fun x => beta x i) (closedBall 0 r))
    (hA_pos : ∀ x ∈ closedBall 0 r, (A x).PosDef) :
    ∃ k : ℝ, 0 < k ∧ ∀ x ∈ closedBall (0 : Plane) r \ ball 0 (r / 2),
      0 < scalarEllipticOperator A beta (inwardBarrier r k) x - C * inwardBarrier r k x := by
  classical
  let K : Set Plane := closedBall 0 r \ ball 0 (r / 2)
  have hK : IsCompact K := (isCompact_closedBall (0 : Plane) r).diff isOpen_ball
  let Q (x : Plane) : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, x i * A x i j * x j
  let T (x : Plane) : ℝ := (∑ i : Fin 2, A x i i) + ∑ i : Fin 2, beta x i * x i
  have hQc : ContinuousOn Q K := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((EuclideanSpace.proj i).continuous.continuousOn.mul
      ((hA_cont i j).mono fun _ hx => hx.1)).mul
      (EuclideanSpace.proj j).continuous.continuousOn)
  have hQpos (x : Plane) (hx : x ∈ K) : 0 < Q x := by
    have hx0 : (fun i : Fin 2 => x i) ≠ 0 := by
      intro he
      have hz : x = 0 := by ext i; exact congrFun he i
      have hnot := hx.2
      apply hnot
      simpa only [hz] using mem_ball_self (half_pos hr)
    simpa only [Q, dotProduct, Matrix.mulVec, star_trivial,
      Finset.mul_sum, mul_assoc] using (hA_pos x hx.1).dotProduct_mulVec_pos hx0
  obtain ⟨lam, hlam, hQlam⟩ := hK.exists_forall_le' hQc hQpos
  have hTc : ContinuousOn T K := by
    apply ContinuousOn.add
    · apply continuousOn_finsetSum
      intro i _
      exact (hA_cont i i).mono fun _ hx => hx.1
    · apply continuousOn_finsetSum
      intro i _
      exact ((hbeta_cont i).mono fun _ hx => hx.1).mul
        (EuclideanSpace.proj i).continuous.continuousOn
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hTc
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hTle (x : Plane) (hx : x ∈ K) : T x ≤ M := by
    have hh : |T x| ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ x hx
    exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
  let k : ℝ := (M + C + 1) / lam + 1
  have hkone : 1 ≤ k := by
    dsimp only [k]
    exact le_add_of_nonneg_left (div_nonneg (by positivity) hlam.le)
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one hkone
  have hklam : M + C + 1 ≤ k * lam := by
    have he : k * lam = M + C + 1 + lam := by
      dsimp [k]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hlam), one_mul]
    linarith
  refine ⟨k, hk, ?_⟩
  intro x hx
  have hQx := hQlam x hx
  have hTx := hTle x hx
  have hquad : C < 4 * k ^ 2 * Q x - 2 * k * T x := by
    have h1 : 0 ≤ k ^ 2 * (Q x - lam) := mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hQx)
    have h2 : 0 ≤ k * (M - T x) := mul_nonneg hk.le (sub_nonneg.mpr hTx)
    have h3 : 0 ≤ k * (k * lam - (M + C + 1)) :=
      mul_nonneg hk.le (sub_nonneg.mpr hklam)
    have h4 : 0 ≤ (k - 1) * (C + 1) := mul_nonneg (sub_nonneg.mpr hkone) (by positivity)
    have h5 : 0 ≤ k * M := mul_nonneg hk.le hM
    nlinarith
  rw [inwardBarrier_operator]
  change 0 < Real.exp (-k * ‖x‖ ^ 2) *
    (4 * k ^ 2 * Q x - 2 * k * T x) - C * inwardBarrier r k x
  have hE := Real.exp_pos (-k * ‖x‖ ^ 2)
  have hR := Real.exp_pos (-k * r ^ 2)
  have hstrict := mul_pos hE (sub_pos.mpr hquad)
  have hnonneg := mul_nonneg hC hR.le
  dsimp only [inwardBarrier, exponentialBallBarrier]
  nlinarith

private theorem centered_hopf_inward_pos
    {A : Plane → Matrix (Fin 2) (Fin 2) ℝ}
    {beta : Plane → Fin 2 → ℝ} {u : Plane → ℝ} {q : Plane} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hA_cont : ∀ i j, ContinuousOn (fun x => A x i j) (closedBall 0 r))
    (hbeta_cont : ∀ i, ContinuousOn (fun x => beta x i) (closedBall 0 r))
    (hA_pos : ∀ x ∈ closedBall 0 r, (A x).PosDef)
    (hu : ContDiffOn ℝ 2 u (ball 0 r)) (hu_cont : ContinuousOn u (closedBall 0 r))
    (hq : q ∈ sphere 0 r) (huq : DifferentiableAt ℝ u q)
    (hpos : ∀ x ∈ ball 0 r, 0 < u x) (hzero : u q = 0)
    (hL : ∀ x ∈ ball 0 r, scalarEllipticOperator A beta u x - C * u x ≤ 0) :
    0 < fderiv ℝ u q (-q) := by
  classical
  obtain ⟨k, hk, hbarrier⟩ := exists_strict_inward_barrier hr hC hA_cont hbeta_cont hA_pos
  let b : Plane → ℝ := inwardBarrier r k
  have hb : ContDiff ℝ ∞ b := inwardBarrier_smooth r k
  have hqnorm : ‖q‖ = r := by simpa only [mem_sphere, dist_zero_right] using hq
  have hbq : b q = 0 := by
    dsimp only [b, inwardBarrier]
    rw [exponentialBallBarrier_eq_zero hq, neg_zero]
  have hb_le_one (x : Plane) : b x ≤ 1 := by
    have he : Real.exp (-k * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sq_nonneg ‖x‖))
    have heR := Real.exp_pos (-k * r ^ 2)
    dsimp only [b, inwardBarrier, exponentialBallBarrier]
    linarith
  have hsball : sphere (0 : Plane) (r / 2) ⊆ ball 0 r :=
    sphere_subset_ball (half_lt_self hr)
  obtain ⟨mu, hmu, humu⟩ := (isCompact_sphere (0 : Plane) (r / 2)).exists_forall_le'
    (hu_cont.mono (hsball.trans ball_subset_closedBall)) (fun x hx => hpos x (hsball hx))
  let eps : ℝ := mu / 2
  have heps : 0 < eps := half_pos hmu
  have hu_nonneg : ∀ x ∈ closedBall (0 : Plane) r, 0 ≤ u x := by
    have hc : closure (ball (0 : Plane) r) = closedBall 0 r := closure_ball (0 : Plane) (ne_of_gt hr)
    intro x hx
    exact le_on_closure (fun y hy => (hpos y hy).le) continuousOn_const
      (by rwa [hc]) (by rwa [hc])
  let K : Set Plane := closedBall 0 r \ ball 0 (r / 2)
  have hK : IsCompact K := (isCompact_closedBall (0 : Plane) r).diff isOpen_ball
  have hqK : q ∈ K := by
    refine ⟨sphere_subset_closedBall hq, ?_⟩
    simp only [mem_ball, dist_zero_right, hqnorm]
    linarith
  let v : Plane → ℝ := fun x => u x + (-eps) * b x
  have hv_cont : ContinuousOn v K :=
    (hu_cont.mono fun _ hx => hx.1).add (continuousOn_const.mul hb.continuous.continuousOn)
  have hvq : v q = 0 := by simp only [v, hzero, hbq, mul_zero, add_zero]
  have hvnonneg : ∀ x ∈ K, 0 ≤ v x := by
    intro x hx
    by_contra hn
    have hxneg : v x < 0 := lt_of_not_ge hn
    obtain ⟨z, hzK, hmin⟩ := hK.exists_isMinOn ⟨q, hqK⟩ hv_cont
    have hzneg : v z < 0 := lt_of_le_of_lt (hmin hx) hxneg
    have hzupper : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hzK.1
    have hzlower : r / 2 ≤ ‖z‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hzK.2
    have hzouter : ‖z‖ < r := by
      apply lt_of_le_of_ne hzupper
      intro he
      have hzs : z ∈ sphere (0 : Plane) r := by simpa only [mem_sphere, dist_zero_right] using he
      have hbz : b z = 0 := by
        dsimp only [b, inwardBarrier]
        rw [exponentialBallBarrier_eq_zero hzs, neg_zero]
      have hun := hu_nonneg z hzK.1
      simp only [v, hbz, mul_zero, add_zero] at hzneg
      exact (not_lt_of_ge hun) hzneg
    have hzinner : r / 2 < ‖z‖ := by
      apply lt_of_le_of_ne hzlower
      intro he
      have hzs : z ∈ sphere (0 : Plane) (r / 2) := by
        simpa only [mem_sphere, dist_zero_right] using he.symm
      have huz := humu z hzs
      have hbb := mul_le_mul_of_nonneg_left (hb_le_one z) heps.le
      dsimp only [v, eps] at hzneg
      dsimp only [eps] at hbb
      nlinarith
    have hzball : z ∈ ball (0 : Plane) r := by simpa only [mem_ball, dist_zero_right] using hzouter
    have hnear : K ∈ 𝓝 z := by
      have h1 : ball (0 : Plane) r ∈ 𝓝 z := isOpen_ball.mem_nhds hzball
      have h2 : {t : Plane | r / 2 < ‖t‖} ∈ 𝓝 z :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hzinner
      exact Filter.mem_of_superset (inter_mem h1 h2) fun t ht =>
        ⟨ball_subset_closedBall ht.1, by simpa only [mem_ball, dist_zero_right, not_lt] using ht.2.le⟩
    have hvc : ContDiffAt ℝ 2 v z :=
      (hu.contDiffAt (isOpen_ball.mem_nhds hzball)).add
        (contDiffAt_const.mul (hb.contDiffAt.of_le (by norm_num)))
    have hnegmax : IsLocalMax (fun t => -v t) z := (hmin.isLocalMin hnear).neg
    have htest := scalarEllipticOperator_nonpos_of_isLocalMax A beta hvc.neg hnegmax (hA_pos z hzK.1)
    have hnop : scalarEllipticOperator A beta (fun t => -v t) z =
        -scalarEllipticOperator A beta v z := by
      simpa only [neg_one_mul] using scalarEllipticOperator_const_mul A beta hvc (-1)
    rw [hnop] at htest
    have hvop : scalarEllipticOperator A beta v z =
        scalarEllipticOperator A beta u z - eps * scalarEllipticOperator A beta b z := by
      rw [scalarEllipticOperator_add A beta (hu.contDiffAt (isOpen_ball.mem_nhds hzball))
        (contDiffAt_const.mul (hb.contDiffAt.of_le (by norm_num))),
        scalarEllipticOperator_const_mul A beta (hb.contDiffAt.of_le (by norm_num))]
      ring
    have huL := hL z hzball
    have hbL := hbarrier z hzK
    have hstrict := mul_pos heps hbL
    have hCv := mul_nonpos_of_nonneg_of_nonpos hC hzneg.le
    dsimp only [v] at hCv
    rw [hvop] at htest
    change 0 < eps * (scalarEllipticOperator A beta b z - C * b z) at hstrict
    nlinarith
  have hsegment : segment ℝ q ((1 / 2 : ℝ) • q) ⊆ K := by
    rw [segment_eq_image]
    rintro x ⟨t, ht, rfl⟩
    have he : (1 - t) • q + t • ((1 / 2 : ℝ) • q) = (1 - t / 2) • q := by
      rw [smul_smul, ← add_smul]
      congr 1
      ring
    change (1 - t) • q + t • ((1 / 2 : ℝ) • q) ∈ K
    rw [he]
    have hcoeff : 0 ≤ 1 - t / 2 := by linarith [ht.2]
    have hnorm : ‖(1 - t / 2) • q‖ = (1 - t / 2) * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff, hqnorm]
    constructor
    · simp only [mem_closedBall, dist_zero_right, hnorm]
      nlinarith [ht.1]
    · simp only [mem_ball, dist_zero_right, hnorm, not_lt]
      nlinarith [ht.2]
  have hvmin : IsLocalMinOn v K q := (show IsMinOn v K q from fun x hx => by
    rw [hvq]
    exact hvnonneg x hx).isLocalMinOn
  have hd := hvmin.hasFDerivWithinAt_nonneg
    ((huq.hasFDerivAt.add (((hb.differentiable (by simp) q).hasFDerivAt).const_mul (-eps))).hasFDerivWithinAt)
    (sub_mem_posTangentConeAt_of_segment_subset hsegment)
  have hdir : (1 / 2 : ℝ) • q - q = (1 / 2 : ℝ) • (-q) := by
    calc
      (1 / 2 : ℝ) • q - q = ((1 / 2 : ℝ) - 1) • q := by rw [sub_smul, one_smul]
      _ = (-(1 / 2 : ℝ)) • q := by congr 1; norm_num
      _ = (1 / 2 : ℝ) • (-q) := by rw [neg_smul, smul_neg]
  rw [hdir] at hd
  have hdb := inwardBarrier_inward_derivative (k := k) hqnorm
  change fderiv ℝ b q (-q) = _ at hdb
  simp only [add_apply, smul_apply, map_smul, smul_eq_mul] at hd
  rw [hdb] at hd
  have hprod : 0 < eps * (2 * k * Real.exp (-k * r ^ 2) * r ^ 2) := by positivity
  nlinarith

private theorem compact_zero_set
    {K : Set ℂ} (hK : IsCompact K) {w : ℂ → ℝ} (hw : ContinuousOn w K) :
    IsCompact {x : ℂ | x ∈ K ∧ w x = 0} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun x : K => w x.val) := continuousOn_iff_continuous_domRestrict.mp hw
  have hz : IsClosed {x : K | w x.val = 0} := isClosed_eq hc continuous_const
  have hi := hz.isCompact.image continuous_subtype_val
  convert hi using 1
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    exact ⟨⟨x, hx⟩, hzero, rfl⟩
  · rintro ⟨z, hzero, rfl⟩
    exact ⟨z.property, hzero⟩

private theorem positive_on_ball_of_positive
    {w : ℂ → ℝ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hw : ContinuousOn w (ball p r))
    (hne : ∀ x ∈ ball p r, w x ≠ 0) (hp : 0 < w p) :
    ∀ x ∈ ball p r, 0 < w x := by
  intro x hx
  by_contra hn
  have hneg : w x < 0 := lt_of_le_of_ne (le_of_not_gt hn) (hne x hx)
  obtain ⟨z, hz, hzero⟩ := (convex_ball p r).isPreconnected.intermediate_value
    hx (mem_ball_self hr) hw ⟨hneg.le, hp.le⟩
  exact hne z hz hzero


end DifferentialGeometry.Analysis

open DifferentialGeometry.Analysis

theorem DifferentialGeometry.Analysis.planar_hopf_inward_pos
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {beta : ℂ → Fin 2 → ℝ} {u : ℂ → ℝ}
    {p q : ℂ} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hA_cont : ∀ i j : Fin 2,
      ContinuousOn (fun x => A x i j) (Metric.closedBall p r))
    (hbeta_cont : ∀ i : Fin 2,
      ContinuousOn (fun x => beta x i) (Metric.closedBall p r))
    (hA_pos : ∀ x ∈ Metric.closedBall p r, (A x).PosDef)
    (hu : ContDiffOn ℝ 2 u (Metric.ball p r))
    (hu_cont : ContinuousOn u (Metric.closedBall p r))
    (hq : q ∈ Metric.sphere p r)
    (huq : DifferentiableAt ℝ u q)
    (hpos : ∀ x ∈ Metric.ball p r, 0 < u x)
    (hzero : u q = 0)
    (hL : ∀ x ∈ Metric.ball p r,
      (∑ i : Fin 2, ∑ j : Fin 2,
        A x i j * fderiv ℝ (fderiv ℝ u) x
          ((![1, Complex.I] : Fin 2 → ℂ) i)
          ((![1, Complex.I] : Fin 2 → ℂ) j)) +
        (∑ i : Fin 2, beta x i * fderiv ℝ u x
          ((![1, Complex.I] : Fin 2 → ℂ) i)) - C * u x ≤ 0) :
    0 < fderiv ℝ u q (p - q) := by
  let L : Plane →L[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let T : Plane → ℂ := fun x => p + L x
  let q0 : Plane := Complex.orthonormalBasisOneI.repr (q - p)
  have hTnorm (x : Plane) : dist (T x) p = ‖x‖ := by
    calc
      dist (T x) p = ‖Complex.orthonormalBasisOneI.repr.symm x‖ := by
        rw [dist_eq_norm]
        change ‖(p + Complex.orthonormalBasisOneI.repr.symm x) - p‖ = _
        congr 1
        abel
      _ = ‖x‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map x
  have hTq : T q0 = q := by
    change p + Complex.orthonormalBasisOneI.repr.symm
      (Complex.orthonormalBasisOneI.repr (q - p)) = q
    rw [LinearIsometryEquiv.symm_apply_apply]
    abel
  have hTc : ContDiff ℝ ∞ T := contDiff_const.add L.contDiff
  have hTclosed : MapsTo T (closedBall (0 : Plane) r) (closedBall p r) := by
    intro x hx
    simpa only [mem_closedBall, hTnorm, dist_zero_right] using hx
  have hTball : MapsTo T (ball (0 : Plane) r) (ball p r) := by
    intro x hx
    simpa only [mem_ball, hTnorm, dist_zero_right] using hx
  have hq0 : q0 ∈ sphere (0 : Plane) r := by
    have hh : dist (T q0) p = r := by simpa only [hTq] using (mem_sphere.mp hq)
    simpa only [mem_sphere, dist_zero_right, hTnorm] using hh
  have hu0 : ContDiffOn ℝ 2 (fun x => u (T x)) (ball 0 r) :=
    hu.comp (hTc.of_le (by norm_num)).contDiffOn hTball
  have huc0 : ContinuousOn (fun x => u (T x)) (closedBall 0 r) :=
    hu_cont.comp hTc.continuous.continuousOn hTclosed
  have huq0 : DifferentiableAt ℝ (fun x => u (T x)) q0 := by
    have hh : DifferentiableAt ℝ u (T q0) := by rwa [hTq]
    exact hh.comp q0 (hTc.differentiable (by simp) q0)
  have hL0 (x : Plane) (hx : x ∈ ball (0 : Plane) r) :
      scalarEllipticOperator (fun t => A (T t)) (fun t => beta (T t))
        (fun t => u (T t)) x - C * u (T x) ≤ 0 := by
    have hc : ContDiffAt ℝ 2 u (T x) := hu.contDiffAt (isOpen_ball.mem_nhds (hTball hx))
    have he := planar_operator_affine A beta p hc
    change scalarEllipticOperator (fun t => A (T t)) (fun t => beta (T t))
      (fun t => u (T t)) x = planarOperator A beta u (T x) at he
    rw [he]
    exact hL (T x) (hTball hx)
  have hhopf := centered_hopf_inward_pos hr hC
    (fun i j => (hA_cont i j).comp hTc.continuous.continuousOn hTclosed)
    (fun i => (hbeta_cont i).comp hTc.continuous.continuousOn hTclosed)
    (fun x hx => hA_pos (T x) (hTclosed hx)) hu0 huc0 hq0 huq0
    (fun x hx => hpos (T x) (hTball hx)) (by rwa [hTq]) hL0
  have huat : DifferentiableAt ℝ u (p + L q0) := by change DifferentiableAt ℝ u (T q0); rwa [hTq]
  have hfirst := fderiv_comp_affine L p huat
  change fderiv ℝ (fun t => u (T t)) q0 = (fderiv ℝ u (T q0)).comp L at hfirst
  rw [hfirst, ContinuousLinearMap.comp_apply, hTq] at hhopf
  have hdir : L (-q0) = p - q := by
    change Complex.orthonormalBasisOneI.repr.symm
      (-Complex.orthonormalBasisOneI.repr (q - p)) = p - q
    rw [map_neg, LinearIsometryEquiv.symm_apply_apply, neg_sub]
  rwa [hdir] at hhopf

theorem DifferentialGeometry.Analysis.exists_regular_zero_near_of_elliptic_eq_zero
    {O : Set ℂ} (hO : IsOpen O)
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {beta : ℂ → Fin 2 → ℝ} {c w : ℂ → ℝ}
    (hA_cont : ∀ i j : Fin 2, ContinuousOn (fun x => A x i j) O)
    (hbeta_cont : ∀ i : Fin 2, ContinuousOn (fun x => beta x i) O)
    (hc_cont : ContinuousOn c O)
    (hA_pos : ∀ x ∈ O, (A x).PosDef)
    (hw : ContDiffOn ℝ 2 w O)
    (hL : ∀ x ∈ O,
      (∑ i : Fin 2, ∑ j : Fin 2,
        A x i j * fderiv ℝ (fderiv ℝ w) x
          ((![1, Complex.I] : Fin 2 → ℂ) i)
          ((![1, Complex.I] : Fin 2 → ℂ) j)) +
        (∑ i : Fin 2, beta x i * fderiv ℝ w x
          ((![1, Complex.I] : Fin 2 → ℂ) i)) + c x * w x = 0)
    {a : ℂ} (ha : a ∈ O) (hzero : w a = 0)
    (hnonzero : a ∈ closure {x : ℂ | w x ≠ 0}) :
    ∀ ρ : ℝ, 0 < ρ →
      ∃ q ∈ O, q ∈ Metric.ball a ρ ∧ w q = 0 ∧ fderiv ℝ w q ≠ 0 := by
  classical
  intro ρ hρ
  obtain ⟨R₁, hR₁, hR₁sub⟩ := Metric.isOpen_iff.mp hO a ha
  let R₀ : ℝ := min (R₁ / 2) (ρ / 2)
  have hR₀ : 0 < R₀ := lt_min (half_pos hR₁) (half_pos hρ)
  have hR₀R₁ : R₀ < R₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hR₁)
  have hR₀ρ : R₀ < ρ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
  have hKO : closedBall a R₀ ⊆ O := (closedBall_subset_ball hR₀R₁).trans hR₁sub
  obtain ⟨p, hpw, hap⟩ := Metric.mem_closure_iff.mp hnonzero (R₀ / 4) (by positivity)
  have hpa : dist p a < R₀ / 4 := by rwa [dist_comm] at hap
  let Z : Set ℂ := {z | z ∈ closedBall a R₀ ∧ w z = 0}
  have hZ : IsCompact Z := compact_zero_set (isCompact_closedBall a R₀)
    (hw.continuousOn.mono hKO)
  have haZ : a ∈ Z := ⟨mem_closedBall_self hR₀.le, hzero⟩
  obtain ⟨q, hqZ, hmin⟩ := hZ.exists_isMinOn (f := fun x => dist p x) ⟨a, haZ⟩
    (continuous_const.dist continuous_id).continuousOn
  let R : ℝ := dist p q
  have hRle : R ≤ dist p a := hmin haZ
  have hpq : p ≠ q := by
    intro h
    subst q
    exact hpw hqZ.2
  have hR : 0 < R := dist_pos.mpr hpq
  have hballK : closedBall p R ⊆ closedBall a R₀ := by
    intro x hx
    apply mem_closedBall.mpr
    have ht := dist_triangle x p a
    have hxR : dist x p ≤ R := mem_closedBall.mp hx
    linarith
  have hballO : closedBall p R ⊆ O := hballK.trans hKO
  have hqR : q ∈ sphere p R := by simp only [mem_sphere, R, dist_comm]
  have hqball : q ∈ closedBall p R := sphere_subset_closedBall hqR
  have hqO : q ∈ O := hballO hqball
  have hqρ : q ∈ ball a ρ :=
    (closedBall_subset_ball hR₀ρ) (hballK hqball)
  have hnonzeroBall : ∀ x ∈ ball p R, w x ≠ 0 := by
    intro x hx hzeroX
    have hxZ : x ∈ Z := ⟨hballK (ball_subset_closedBall hx), hzeroX⟩
    have hle : R ≤ dist p x := hmin hxZ
    have hlt : dist p x < R := by simpa only [dist_comm] using mem_ball.mp hx
    exact (not_lt_of_ge hle) hlt
  have hwball : ContDiffOn ℝ 2 w (ball p R) := hw.mono (ball_subset_closedBall.trans hballO)
  have hwclosed : ContinuousOn w (closedBall p R) := hw.continuousOn.mono hballO
  have hwq : DifferentiableAt ℝ w q :=
    (hw.contDiffAt (hO.mem_nhds hqO)).differentiableAt (by norm_num)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall p R).exists_bound_of_continuousOn
    (hc_cont.mono hballO)
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hcplus (x : ℂ) (hx : x ∈ closedBall p R) : 0 ≤ c x + C := by
    have hb₀ : |c x| ≤ C₀ := by simpa only [Real.norm_eq_abs] using hC₀ x hx
    have hb : |c x| ≤ C := hb₀.trans (le_max_left _ _)
    linarith [neg_abs_le (c x)]
  have hAclosed (i j : Fin 2) : ContinuousOn (fun x => A x i j) (closedBall p R) :=
    (hA_cont i j).mono hballO
  have hbetaclosed (i : Fin 2) : ContinuousOn (fun x => beta x i) (closedBall p R) :=
    (hbeta_cont i).mono hballO
  have hAclosedpos (x : ℂ) (hx : x ∈ closedBall p R) : (A x).PosDef := hA_pos x (hballO hx)
  refine ⟨q, hqO, hqρ, hqZ.2, ?_⟩
  by_cases hp : 0 < w p
  · have hpositive := positive_on_ball_of_positive hR hwball.continuousOn hnonzeroBall hp
    have hopf := planar_hopf_inward_pos hR hC hAclosed hbetaclosed hAclosedpos
      hwball hwclosed hqR hwq hpositive hqZ.2 (fun x hx => by
        have heq := hL x (hballO (ball_subset_closedBall hx))
        have hc := hcplus x (ball_subset_closedBall hx)
        have hmul := mul_nonneg hc (hpositive x hx).le
        linarith)
    intro hd
    rw [hd, zero_apply] at hopf
    exact (lt_irrefl 0) hopf
  · have hnegp : w p < 0 := lt_of_le_of_ne (le_of_not_gt hp) hpw
    have hnegative : ∀ x ∈ ball p R, 0 < -w x :=
      positive_on_ball_of_positive (w := fun x => -w x) hR hwball.continuousOn.neg
        (fun x hx => neg_ne_zero.mpr (hnonzeroBall x hx)) (neg_pos.mpr hnegp)
    have hLneg : ∀ x ∈ ball p R,
        (∑ i : Fin 2, ∑ j : Fin 2,
          A x i j * fderiv ℝ (fderiv ℝ (fun z => -w z)) x
            ((![1, Complex.I] : Fin 2 → ℂ) i)
            ((![1, Complex.I] : Fin 2 → ℂ) j)) +
          (∑ i : Fin 2, beta x i * fderiv ℝ (fun z => -w z) x
            ((![1, Complex.I] : Fin 2 → ℂ) i)) - C * (-w x) ≤ 0 := by
      intro x hx
      have heq := hL x (hballO (ball_subset_closedBall hx))
      have hc := hcplus x (ball_subset_closedBall hx)
      have hmul := mul_nonneg hc (hnegative x hx).le
      have hnegfirst : fderiv ℝ (fun z => -w z) = fun z => -fderiv ℝ w z := by
        funext z
        exact fderiv_fun_neg
      simp only [hnegfirst, fderiv_fun_neg, neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith
    have hopf := planar_hopf_inward_pos hR hC hAclosed hbetaclosed hAclosedpos
      hwball.neg hwclosed.neg hqR hwq.neg hnegative (by simp only [hqZ.2, neg_zero]) hLneg
    intro hd
    simp only [fderiv_fun_neg, hd, zero_apply, neg_zero] at hopf
    exact (lt_irrefl 0) hopf
