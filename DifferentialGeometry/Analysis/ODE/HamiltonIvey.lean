import DifferentialGeometry.Analysis.Calculus.MatrixInverseSmooth
import DifferentialGeometry.Analysis.ODE.Nagumo
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.SelfAdjointRegion
import Mathlib.Analysis.CStarAlgebra.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Analysis.ODE
open Filter Set
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem contDiff_curvatureOperatorReaction3 :
    ContDiff Real ∞ curvatureOperatorReaction3 := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff Real ∞ (fun A : Matrix (Fin 3) (Fin 3) Real =>
    (A * A) i j + A.adjugate i j)
  apply ContDiff.add
  · simp only [Matrix.mul_apply]
    exact ContDiff.sum (fun _ _ => by fun_prop)
  · exact DifferentialGeometry.Analysis.contDiff_adjugate_of_entries id
      (fun i j => by fun_prop) i j

theorem smul_add_curvatureOperatorReaction3_mem_posTangentConeAt
    {K : Real} (hK : 0 < K) {A : Matrix (Fin 3) (Fin 3) Real}
    (hA : A ∈ hamiltonIveyConvexMatrixRegion K 0) :
    K • A + curvatureOperatorReaction3 A ∈
      posTangentConeAt (hamiltonIveyConvexMatrixRegion K 0) A := by
  obtain ⟨eps, heps, hstep⟩ :=
    hamiltonIveyConvexMatrixRegion_reaction_small_time hK le_rfl A hA
  let γ : Real → Matrix (Fin 3) (Fin 3) Real := fun t =>
    (1 + K * t) • (A + (t / 2) • hamiltonIveyMatrixReaction A)
  have hγ₀ : γ 0 = A := by simp [γ]
  have hreaction : (1 / 2 : Real) • hamiltonIveyMatrixReaction A =
      curvatureOperatorReaction3 A := by
    unfold hamiltonIveyMatrixReaction curvatureOperatorReaction3
    module
  have hγ : HasDerivAt γ (K • A + curvatureOperatorReaction3 A) 0 := by
    have hc : HasDerivAt (fun t : Real => 1 + K * t) K 0 := by
      simpa using ((hasDerivAt_id (0 : Real)).const_mul K).const_add 1
    have hB : HasDerivAt (fun t : Real => A + (t / 2) • hamiltonIveyMatrixReaction A)
        ((1 / 2 : Real) • hamiltonIveyMatrixReaction A) 0 :=
      (((hasDerivAt_id (0 : Real)).div_const 2).smul_const _).const_add A
    simpa only [γ, mul_zero, add_zero, zero_div, zero_smul,
      zero_add, one_smul, hreaction, add_comm] using! hc.smul hB
  have hmem : ∀ᶠ t in 𝓝[>] (0 : Real), γ (0 + t) ∈
      hamiltonIveyConvexMatrixRegion K 0 := by
    have hsmall : ∀ᶠ t : Real in 𝓝[>] 0, t < 2 * eps :=
      (eventually_lt_nhds (by positivity : (0 : Real) < 2 * eps)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htSmall
    have htPos : 0 < t := ht
    have ht' : t / 2 ∈ Icc 0 eps := ⟨by positivity, by linarith⟩
    have hscaled := smul_mem_hamiltonIveyConvexMatrixRegion_initial hK ht'.1
      (by simpa only [zero_add] using hstep (t / 2) ht')
    have hcoef : 1 + 2 * K * (t / 2) = 1 + K * t := by ring
    simpa only [hcoef, γ, zero_add] using hscaled
  simpa only [hγ₀] using!
    HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right hγ hmem

theorem isForwardInvariantForODE_hamiltonIveyConvexMatrixRegion_initial
    {K : Real} (hK : 0 < K) :
    IsForwardInvariantForODE
      (fun _ A => K • A + curvatureOperatorReaction3 A)
      (hamiltonIveyConvexMatrixRegion K 0) := by
  apply nagumo_isForwardInvariantForODE_of_contDiff
    (isClosed_hamiltonIveyConvexMatrixRegion hK)
    (convex_hamiltonIveyConvexMatrixRegion hK le_rfl)
    (fun _ _ hA => smul_add_curvatureOperatorReaction3_mem_posTangentConeAt hK hA)
  change ContDiff Real 1 (fun p : Real × Matrix (Fin 3) (Fin 3) Real =>
    K • p.2 + curvatureOperatorReaction3 p.2)
  have hQ : ContDiff Real 1 curvatureOperatorReaction3 :=
    contDiff_curvatureOperatorReaction3.of_le (by norm_num)
  have hlin : ContDiff Real 1 (fun p : Real × Matrix (Fin 3) (Fin 3) Real => K • p.2) := by
    simpa only [Pi.smul_apply'] using!
      (contDiff_snd : ContDiff Real 1
        (Prod.snd : Real × Matrix (Fin 3) (Fin 3) Real → _)).const_smul K
  exact hlin.add (hQ.comp contDiff_snd)

theorem isForwardInvariantForODE_hamiltonIveyConvexMatrixRegion_normalized :
    IsForwardInvariantForODE
      (fun _ A => A + curvatureOperatorReaction3 A)
      (hamiltonIveyConvexMatrixRegion 1 0) := by
  simpa only [one_smul] using
    isForwardInvariantForODE_hamiltonIveyConvexMatrixRegion_initial zero_lt_one

theorem hasDerivWithinAt_pinchingRatioLog_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ} {J : Set ℝ}
    (hn : n t ≠ 0)
    (hl : HasDerivWithinAt l (a * l t + b * (l t ^ 2 + m t * n t)) J t)
    (hm : HasDerivWithinAt m (a * m t + b * (m t ^ 2 + l t * n t)) J t)
    (hn' : HasDerivWithinAt n (a * n t + b * (n t ^ 2 + l t * m t)) J t) :
    HasDerivWithinAt
      (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s))
      (b * (-n t) - a + b *
        (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
          (-n t) ^ 2) J t := by
  have hq : HasDerivWithinAt (fun s => -n s) (- (a * n t + b * (n t ^ 2 + l t * m t))) J t := hn'.neg
  have hq0 : -n t ≠ 0 := neg_ne_zero.mpr hn
  have hS : HasDerivWithinAt (fun s => l s + m s + n s)
      (a * (l t + m t + n t) + b *
        (l t ^ 2 + m t ^ 2 + n t ^ 2 + l t * m t + l t * n t + m t * n t)) J t := by
    exact ((hl.add hm).add hn').congr_deriv (by ring)
  have hquot := hS.div hq hq0
  have hlog := hq.log hq0
  have hsum := hquot.sub hlog
  have hfun : (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s)) =
      ((fun s => l s + m s + n s) / (fun s => -n s)) - (fun y => Real.log (-n y)) := by
    funext s
    rfl
  rw [hfun]
  exact hsum.congr_deriv (by field_simp [hq0, hn]; ring)

theorem hasDerivAt_pinchingRatioLog_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ}
    (hn : n t ≠ 0)
    (hl : HasDerivAt l (a * l t + b * (l t ^ 2 + m t * n t)) t)
    (hm : HasDerivAt m (a * m t + b * (m t ^ 2 + l t * n t)) t)
    (hn' : HasDerivAt n (a * n t + b * (n t ^ 2 + l t * m t)) t) :
    HasDerivAt
      (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s))
      (b * (-n t) - a + b *
        (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
          (-n t) ^ 2) t := by
  exact hasDerivWithinAt_univ.mp
    (hasDerivWithinAt_pinchingRatioLog_of_reaction hn
      hl.hasDerivWithinAt hm.hasDerivWithinAt hn'.hasDerivWithinAt)

theorem deriv_pinchingRatioLog_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ}
    (hn : n t ≠ 0)
    (hl : HasDerivAt l (a * l t + b * (l t ^ 2 + m t * n t)) t)
    (hm : HasDerivAt m (a * m t + b * (m t ^ 2 + l t * n t)) t)
    (hn' : HasDerivAt n (a * n t + b * (n t ^ 2 + l t * m t)) t) :
    deriv (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s)) t =
      b * (-n t) - a + b *
        (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
          (-n t) ^ 2 :=
  (hasDerivAt_pinchingRatioLog_of_reaction hn hl hm hn').deriv

theorem deriv_pinchingRatioLog_ge_of_reaction
    {l m n : ℝ → ℝ} {t a b : ℝ}
    (hnl : n t ≤ l t) (hnm : n t ≤ m t) (hn : n t < 0)
    (hb : 0 ≤ b)
    (hl : HasDerivAt l (a * l t + b * (l t ^ 2 + m t * n t)) t)
    (hm : HasDerivAt m (a * m t + b * (m t ^ 2 + l t * n t)) t)
    (hn' : HasDerivAt n (a * n t + b * (n t ^ 2 + l t * m t)) t) :
    b * (-n t) - a ≤
      deriv (fun s => (l s + m s + n s) / (-n s) - Real.log (-n s)) t := by
  rw [deriv_pinchingRatioLog_of_reaction hn.ne hl hm hn']
  have hraw := hamilton_ivey_algebraic_inequality hnl hnm hn.le
  have hpi : 0 ≤ l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2) := by
    nlinarith only [hraw]
  have hden : 0 ≤ (-n t) ^ 2 := sq_nonneg _
  have hfrac : 0 ≤ b *
      (l t * m t * (l t + m t - n t) - n t * (l t ^ 2 + m t ^ 2)) /
        (-n t) ^ 2 := by
    exact div_nonneg (mul_nonneg hb hpi) hden
  linarith

private def orderedDiagonalMatrices3 : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {A | (∀ i j, i ≠ j → A i j = 0) ∧ A 1 1 ≤ A 0 0 ∧ A 2 2 ≤ A 1 1}

private theorem isClosed_orderedDiagonalMatrices3 : IsClosed orderedDiagonalMatrices3 := by
  change IsClosed ({A : Matrix (Fin 3) (Fin 3) ℝ | ∀ i j, i ≠ j → A i j = 0} ∩
    ({A | A 1 1 ≤ A 0 0} ∩ {A | A 2 2 ≤ A 1 1}))
  refine IsClosed.inter ?_ ((isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_le (by fun_prop) (by fun_prop)))
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (by fun_prop) continuous_const

private theorem convex_orderedDiagonalMatrices3 : Convex ℝ orderedDiagonalMatrices3 := by
  intro A hA B hB a b ha hb _
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    change a * A i j + b * B i j = 0
    rw [hA.1 i j hij, hB.1 i j hij]
    ring
  · change a * A 1 1 + b * B 1 1 ≤ a * A 0 0 + b * B 0 0
    exact add_le_add (mul_le_mul_of_nonneg_left hA.2.1 ha)
      (mul_le_mul_of_nonneg_left hB.2.1 hb)
  · change a * A 2 2 + b * B 2 2 ≤ a * A 1 1 + b * B 1 1
    exact add_le_add (mul_le_mul_of_nonneg_left hA.2.2 ha)
      (mul_le_mul_of_nonneg_left hB.2.2 hb)

private theorem diagonal_eq_of_mem_orderedDiagonalMatrices3
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ orderedDiagonalMatrices3) :
    A = Matrix.diagonal ![A 0 0, A 1 1, A 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hA.1]

private theorem normalized_curvature_reaction_diagonal (l m n : ℝ) :
    Matrix.diagonal ![l, m, n] + curvatureOperatorReaction3 (Matrix.diagonal ![l, m, n]) =
      Matrix.diagonal ![l + l ^ 2 + m * n, m + m ^ 2 + l * n, n + n ^ 2 + l * m] := by
  rw [curvatureOperatorReaction3_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring

private theorem smul_normalized_curvature_reaction_tangent_orderedDiagonalMatrices3
    (r : ℝ) {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ orderedDiagonalMatrices3) :
    r • (A + curvatureOperatorReaction3 A) ∈ posTangentConeAt orderedDiagonalMatrices3 A := by
  have hdiag := diagonal_eq_of_mem_orderedDiagonalMatrices3 hA
  have hreaction : A + curvatureOperatorReaction3 A =
      Matrix.diagonal ![A 0 0 + (A 0 0) ^ 2 + A 1 1 * A 2 2,
        A 1 1 + (A 1 1) ^ 2 + A 0 0 * A 2 2,
        A 2 2 + (A 2 2) ^ 2 + A 0 0 * A 1 1] :=
    (congrArg (fun B => B + curvatureOperatorReaction3 B) hdiag).trans
      (normalized_curvature_reaction_diagonal _ _ _)
  have h01 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      0 < 1 + t * r * (1 + A 0 0 + A 1 1 - A 2 2) := by
    apply (show ContinuousAt (fun t : ℝ =>
      1 + t * r * (1 + A 0 0 + A 1 1 - A 2 2)) 0 by fun_prop).eventually (eventually_gt_nhds (by norm_num))
  have h12 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      0 < 1 + t * r * (1 + A 1 1 + A 2 2 - A 0 0) := by
    apply (show ContinuousAt (fun t : ℝ =>
      1 + t * r * (1 + A 1 1 + A 2 2 - A 0 0)) 0 by fun_prop).eventually (eventually_gt_nhds (by norm_num))
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      A + t • (r • (A + curvatureOperatorReaction3 A)) ∈ orderedDiagonalMatrices3 := by
    filter_upwards [h01.filter_mono inf_le_left, h12.filter_mono inf_le_left] with t ht01 ht12
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      change A i j + t * (r * ((A + curvatureOperatorReaction3 A) i j)) = 0
      rw [hA.1 i j hij, hreaction]
      simp [Matrix.diagonal, hij]
    · change A 1 1 + t * (r * ((A + curvatureOperatorReaction3 A) 1 1)) ≤
        A 0 0 + t * (r * ((A + curvatureOperatorReaction3 A) 0 0))
      rw [hreaction]
      simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hprod := mul_nonneg (sub_nonneg.mpr hA.2.1) ht01.le
      nlinarith only [hprod]
    · change A 2 2 + t * (r * ((A + curvatureOperatorReaction3 A) 2 2)) ≤
        A 1 1 + t * (r * ((A + curvatureOperatorReaction3 A) 1 1))
      rw [hreaction]
      simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      have hprod := mul_nonneg (sub_nonneg.mpr hA.2.2) ht12.le
      nlinarith only [hprod]
  exact mem_posTangentConeAt_of_frequently_mem hev.frequently

private theorem isForwardInvariantForODE_smul_normalized_curvature_reaction_orderedDiagonalMatrices3
    (r : ℝ) : IsForwardInvariantForODE
      (fun _ A => r • (A + curvatureOperatorReaction3 A)) orderedDiagonalMatrices3 := by
  apply nagumo_isForwardInvariantForODE_of_contDiff isClosed_orderedDiagonalMatrices3
    convex_orderedDiagonalMatrices3
    (fun _ _ hA => smul_normalized_curvature_reaction_tangent_orderedDiagonalMatrices3 r hA)
  exact (contDiff_snd.add
    ((contDiff_curvatureOperatorReaction3.of_le (by norm_num)).comp contDiff_snd)).const_smul r

theorem diagonal_ordered_of_normalized_curvature_reaction_ode
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {J : Set ℝ} {t₀ : ℝ}
    (hA : IsIntegralCurveOn A (fun _ C => C + curvatureOperatorReaction3 C) J)
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hdiag : A t₀ = Matrix.diagonal ![A t₀ 0 0, A t₀ 1 1, A t₀ 2 2])
    (h01 : A t₀ 1 1 ≤ A t₀ 0 0) (h12 : A t₀ 2 2 ≤ A t₀ 1 1) :
    ∀ t ∈ J,
      A t = Matrix.diagonal ![A t 0 0, A t 1 1, A t 2 2] ∧
      A t 1 1 ≤ A t 0 0 ∧ A t 2 2 ≤ A t 1 1 := by
  have hinit : A t₀ ∈ orderedDiagonalMatrices3 := by
    refine ⟨?_, h01, h12⟩
    intro i j hij
    rw [hdiag]
    simp [Matrix.diagonal, hij]
  intro t ht
  let φ : ℝ → ℝ := fun s => t₀ + s * (t - t₀)
  have hmap : MapsTo φ (Icc (0 : ℝ) 1) J := by
    intro s hs
    have hm := (convex_iff_ordConnected.mpr hJ) ht₀ ht
      (sub_nonneg.mpr hs.2) hs.1 (show (1 - s) + s = 1 by ring)
    convert hm using 1
    dsimp [φ]
    ring
  have hcurve : IsIntegralCurveOn (fun s => A (φ s))
      (fun _ C => (t - t₀) • (C + curvatureOperatorReaction3 C)) (Icc 0 1) := by
    intro s hs
    have hφ : HasDerivWithinAt φ (t - t₀) (Icc 0 1) s := by
      simpa only [φ, id_eq, one_mul] using
        (((hasDerivAt_id s).mul_const (t - t₀)).const_add t₀).hasDerivWithinAt
    exact (hA (φ s) (hmap hs)).scomp s hφ hmap
  have hstart : A (φ 0) ∈ orderedDiagonalMatrices3 := by simpa [φ] using hinit
  have hend := isForwardInvariantForODE_smul_normalized_curvature_reaction_orderedDiagonalMatrices3
    (t - t₀) 0 1 (by norm_num) (fun s => A (φ s)) hcurve hstart
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hmem : A t ∈ orderedDiagonalMatrices3 := by simpa [φ] using hend
  exact ⟨diagonal_eq_of_mem_orderedDiagonalMatrices3 hmem, hmem.2⟩

theorem hasDerivWithinAt_diagonal_of_normalized_curvature_reaction_ode
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {J : Set ℝ} {t : ℝ}
    (hA : IsIntegralCurveOn A (fun _ C => C + curvatureOperatorReaction3 C) J)
    (ht : t ∈ J)
    (hdiag : A t = Matrix.diagonal ![A t 0 0, A t 1 1, A t 2 2]) :
    ∀ i : Fin 3, HasDerivWithinAt (fun u => A u i i)
      (![A t 0 0 + (A t 0 0) ^ 2 + A t 1 1 * A t 2 2,
        A t 1 1 + (A t 1 1) ^ 2 + A t 0 0 * A t 2 2,
        A t 2 2 + (A t 2 2) ^ 2 + A t 0 0 * A t 1 1] i) J t := by
  intro i
  have hval : A t + curvatureOperatorReaction3 (A t) = Matrix.diagonal
      ![A t 0 0 + (A t 0 0) ^ 2 + A t 1 1 * A t 2 2,
        A t 1 1 + (A t 1 1) ^ 2 + A t 0 0 * A t 2 2,
        A t 2 2 + (A t 2 2) ^ 2 + A t 0 0 * A t 1 1] :=
    (congrArg (fun C => C + curvatureOperatorReaction3 C) hdiag).trans
      (by rw [curvatureOperatorReaction3_diagonal]; ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring)
  have hd := hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp (hA t ht) i) i
  apply hd.congr_deriv
  simpa only [Matrix.diagonal_apply_eq] using congrArg (fun C => C i i) hval

private theorem isIntegralCurveOn_linearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℝ → E} {J : Set ℝ} {f : ℝ → E → E} {g : ℝ → F → F}
    (hA : IsIntegralCurveOn A f J) (L : E →L[ℝ] F)
    (hL : ∀ t C, L (f t C) = g t (L C)) :
    IsIntegralCurveOn (fun t => L (A t)) g J := by
  intro t ht
  have hd := L.hasFDerivAt.comp_hasDerivWithinAt t (hA t ht)
  simpa only [Function.comp_def, hL] using hd

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private def selfAdjointMatrixMap (b : OrthonormalBasis (Fin 3) ℝ W) :
    selfAdjoint (W →L[ℝ] W) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  { toFun := fun A => LinearMap.toMatrix b.toBasis b.toBasis (A : W →L[ℝ] W).toLinearMap
    map_add' := by intros; simp
    map_smul' := by intros; simp }

private theorem selfAdjointMatrixMap_continuous (b : OrthonormalBasis (Fin 3) ℝ W) :
    Continuous (selfAdjointMatrixMap b) := by
  change Continuous (fun A : selfAdjoint (W →L[ℝ] W) =>
    LinearMap.toMatrix b.toBasis b.toBasis (A : W →L[ℝ] W).toLinearMap)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simpa only [LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply] using!
    (continuous_const.inner (continuous_subtype_val.clm_apply continuous_const) :
      Continuous (fun A : selfAdjoint (W →L[ℝ] W) =>
        inner ℝ (b i) ((A : W →L[ℝ] W) (b j))))

private theorem selfAdjointMatrixMap_reaction (b : OrthonormalBasis (Fin 3) ℝ W)
    (A : selfAdjoint (W →L[ℝ] W)) :
    selfAdjointMatrixMap b (curvatureOperatorReactionSelfAdjoint3 A) =
      curvatureOperatorReaction3 (selfAdjointMatrixMap b A) := by
  change LinearMap.toMatrix b.toBasis b.toBasis
      (curvatureOperatorReactionEndomorphism3 (A : W →L[ℝ] W).toLinearMap) = _
  exact curvatureOperatorReactionEndomorphism3_toMatrix b.toBasis _

private theorem selfAdjointMatrixMap_region (b : OrthonormalBasis (Fin 3) ℝ W) (A : selfAdjoint (W →L[ℝ] W)) :
    A ∈ hamiltonIveyRegion (W := W) 1 ↔
      selfAdjointMatrixMap b A ∈ hamiltonIveyConvexMatrixRegion 1 0 := by
  exact mem_hamiltonIveyRegion_iff_toMatrix b (K := 1) (by norm_num) A

private theorem mem_posTangentConeAt_smul_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {x v : E} {c : ℝ} (hc : 0 ≤ c)
    (hv : v ∈ posTangentConeAt C x) : c • v ∈ posTangentConeAt C x := by
  rcases exists_fun_of_mem_tangentConeAt hv with ⟨ι, l, hl, d, e, he₀, heC, hde⟩
  let c' : ℝ≥0 := ⟨c, hc⟩
  refine mem_tangentConeAt_of_seq l (fun n => c' * d n) e he₀ heC ?_
  apply Tendsto.congr' _ (hde.const_smul c)
  filter_upwards with n
  change c • (d n : ℝ) • e n = ((c' * d n : ℝ≥0) : ℝ) • e n
  rw [NNReal.coe_mul, smul_smul]
  congr 1

private theorem nonnegative_time_multiple_hamiltonIvey_matrix
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hanonneg : ∀ t, 0 ≤ a t) :
    IsForwardInvariantForODE
      (fun t A => a t • (A + curvatureOperatorReaction3 A))
      (hamiltonIveyConvexMatrixRegion 1 0) := by
  apply nagumo_isForwardInvariantForODE_of_contDiff
    (isClosed_hamiltonIveyConvexMatrixRegion (K := 1) (by norm_num))
    (convex_hamiltonIveyConvexMatrixRegion (K := 1) (by norm_num) (by norm_num))
  · intro t A hA
    apply mem_posTangentConeAt_smul_nonneg (hanonneg t)
    simpa only [one_smul] using!
      smul_add_curvatureOperatorReaction3_mem_posTangentConeAt (K := 1) (by norm_num) hA
  · change ContDiff ℝ 1 (Function.uncurry (fun t A => a t • (A + curvatureOperatorReaction3 A)))
    have hQ : ContDiff ℝ 1 curvatureOperatorReaction3 :=
      contDiff_curvatureOperatorReaction3.of_le (by norm_num)
    exact (ha.comp contDiff_fst).smul (contDiff_snd.add (hQ.comp contDiff_snd))

theorem isForwardInvariantForODE_hamiltonIveyRegion_smul
    (hdim : Module.finrank ℝ W = 3)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hanonneg : ∀ t, 0 ≤ a t) :
    IsForwardInvariantForODE
      (fun t A => a t • (A + curvatureOperatorReactionSelfAdjoint3 A))
      (hamiltonIveyRegion (W := W) 1) := by
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  let L : selfAdjoint (W →L[ℝ] W) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    { toLinearMap := selfAdjointMatrixMap b
      cont := selfAdjointMatrixMap_continuous b }
  have hL : ∀ t ∈ (univ : Set ℝ), ∀ A : selfAdjoint (W →L[ℝ] W),
      L (a t • (A + curvatureOperatorReactionSelfAdjoint3 A)) =
        a t • (L A + curvatureOperatorReaction3 (L A)) := by
    intro t _ A
    rw [map_smul, map_add]
    congr 2
    exact selfAdjointMatrixMap_reaction b A
  have hset : hamiltonIveyRegion (W := W) 1 =
      L ⁻¹' hamiltonIveyConvexMatrixRegion 1 0 := by
    ext A
    exact selfAdjointMatrixMap_region b A
  intro t u htu γ hγ hinit
  have hmat := (isForwardInvariantForODEOn_univ.mpr
      (nonnegative_time_multiple_hamiltonIvey_matrix ha hanonneg)).preimage L hL
      t u htu (subset_univ _) γ hγ
      ((hset ▸ hinit))
  intro s hs
  have hm := hmat hs
  exact (selfAdjointMatrixMap_region b (γ s)).mpr hm

theorem isForwardInvariantForODE_hamiltonIveyRegion_normalized
    (hdim : Module.finrank ℝ W = 3) :
    IsForwardInvariantForODE
      (fun _ A => A + curvatureOperatorReactionSelfAdjoint3 A)
      (hamiltonIveyRegion (W := W) 1) := by
  simpa only [one_smul] using
    (isForwardInvariantForODE_hamiltonIveyRegion_smul (W := W) hdim
      (a := fun _ : ℝ => 1) contDiff_const (fun _ => by norm_num))

theorem exists_orthonormalBasis_diagonal_of_normalized_curvature_reaction_ode
    {A : ℝ → selfAdjoint (W →L[ℝ] W)} {J : Set ℝ} {t₀ : ℝ}
    (hdim : Module.finrank ℝ W = 3)
    (hA : IsIntegralCurveOn A
      (fun _ C => C + curvatureOperatorReactionSelfAdjoint3 C) J)
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ W, ∃ l m n : ℝ → ℝ,
      ∀ t ∈ J,
        LinearMap.toMatrix b.toBasis b.toBasis (A t : W →L[ℝ] W).toLinearMap =
          Matrix.diagonal ![l t, m t, n t] ∧
        m t ≤ l t ∧ n t ≤ m t ∧
        HasDerivWithinAt l (l t + l t ^ 2 + m t * n t) J t ∧
        HasDerivWithinAt m (m t + m t ^ 2 + l t * n t) J t ∧
        HasDerivWithinAt n (n t + n t ^ 2 + l t * m t) J t := by
  let hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (A t₀).property
  let b := hS.eigenvectorBasis hdim
  let L : selfAdjoint (W →L[ℝ] W) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    { toLinearMap := selfAdjointMatrixMap b
      cont := selfAdjointMatrixMap_continuous b }
  have hL : ∀ C,
      selfAdjointMatrixMap b (C + curvatureOperatorReactionSelfAdjoint3 C) =
        selfAdjointMatrixMap b C + curvatureOperatorReaction3 (selfAdjointMatrixMap b C) := by
    intro C
    rw [map_add, selfAdjointMatrixMap_reaction]
  have hcurve : IsIntegralCurveOn (fun t => selfAdjointMatrixMap b (A t))
      (fun _ C => C + curvatureOperatorReaction3 C) J := by
    exact isIntegralCurveOn_linearMap hA L (fun _ C => hL C)
  have hinit : selfAdjointMatrixMap b (A t₀) = Matrix.diagonal (hS.eigenvalues hdim) :=
    hS.toMatrix_eigenvectorBasis hdim
  have hdiag : selfAdjointMatrixMap b (A t₀) =
      Matrix.diagonal ![(selfAdjointMatrixMap b (A t₀)) 0 0,
        (selfAdjointMatrixMap b (A t₀)) 1 1,
        (selfAdjointMatrixMap b (A t₀)) 2 2] := by
    rw [hinit]
    congr 1
    funext i
    fin_cases i <;> simp
  have h01 : selfAdjointMatrixMap b (A t₀) 1 1 ≤ selfAdjointMatrixMap b (A t₀) 0 0 := by
    simpa only [hinit, Matrix.diagonal_apply_eq] using
      hS.eigenvalues_antitone hdim (by decide : (0 : Fin 3) ≤ 1)
  have h12 : selfAdjointMatrixMap b (A t₀) 2 2 ≤ selfAdjointMatrixMap b (A t₀) 1 1 := by
    simpa only [hinit, Matrix.diagonal_apply_eq] using
      hS.eigenvalues_antitone hdim (by decide : (1 : Fin 3) ≤ 2)
  refine ⟨b, (fun t => selfAdjointMatrixMap b (A t) 0 0),
    (fun t => selfAdjointMatrixMap b (A t) 1 1),
    (fun t => selfAdjointMatrixMap b (A t) 2 2), ?_⟩
  intro t ht
  have horder := diagonal_ordered_of_normalized_curvature_reaction_ode
    hcurve hJ ht₀ hdiag h01 h12 t ht
  have hcoords := hasDerivWithinAt_diagonal_of_normalized_curvature_reaction_ode
    hcurve ht horder.1
  refine ⟨horder.1, horder.2.1, horder.2.2, ?_, ?_, ?_⟩
  · exact hcoords 0
  · exact hcoords 1
  · exact hcoords 2

end DifferentialGeometry.Geometry.Curvature.DimensionThree
