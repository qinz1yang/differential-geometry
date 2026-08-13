import DifferentialGeometry.Analysis.Schauder.Composition

noncomputable section

open Filter
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Schauder

variable {V W F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup W] [NormedSpace Real W]
  [NormedAddCommGroup F] [NormedSpace Real F]

def c1PullbackGradient
    (Dphi : V →L[Real] W) (Du : W →L[Real] F) : V →L[Real] F :=
  Du.comp Dphi

theorem norm_c1PullbackGradient_le
    (Dphi : V →L[Real] W) (Du : W →L[Real] F) :
    ‖c1PullbackGradient Dphi Du‖ ≤ ‖Du‖ * ‖Dphi‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

theorem continuousMultilinearCurryFin1_iteratedFDeriv_one_eq_fderiv
    (f : V → F) (x : V) :
    continuousMultilinearCurryFin1 Real V F
        (iteratedFDeriv Real 1 f x) =
      fderiv Real f x := by
  ext v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  rfl

theorem norm_c1PullbackGradient_sub_le
    (Dphi Dphi' : V →L[Real] W) (Du Du' : W →L[Real] F) :
    ‖c1PullbackGradient Dphi Du - c1PullbackGradient Dphi' Du'‖ ≤
      ‖Du - Du'‖ * ‖Dphi‖ + ‖Du'‖ * ‖Dphi - Dphi'‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro a
  simp only [c1PullbackGradient, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  have heq : Du (Dphi a) - Du' (Dphi' a) =
      (Du - Du') (Dphi a) + Du' ((Dphi - Dphi') a) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  have hfirst : ‖(Du - Du') (Dphi a)‖ ≤
      ‖Du - Du'‖ * (‖Dphi‖ * ‖a‖) := by
    calc
      ‖(Du - Du') (Dphi a)‖ ≤ ‖Du - Du'‖ * ‖Dphi a‖ :=
        (Du - Du').le_opNorm _
      _ ≤ ‖Du - Du'‖ * (‖Dphi‖ * ‖a‖) :=
        mul_le_mul_of_nonneg_left (Dphi.le_opNorm a) (norm_nonneg (Du - Du'))
  have hsecond : ‖Du' ((Dphi - Dphi') a)‖ ≤
      ‖Du'‖ * (‖Dphi - Dphi'‖ * ‖a‖) := by
    calc
      ‖Du' ((Dphi - Dphi') a)‖ ≤ ‖Du'‖ * ‖(Dphi - Dphi') a‖ :=
        Du'.le_opNorm _
      _ ≤ ‖Du'‖ * (‖Dphi - Dphi'‖ * ‖a‖) :=
        mul_le_mul_of_nonneg_left ((Dphi - Dphi').le_opNorm a)
          (norm_nonneg Du')
  rw [heq]
  calc
    ‖(Du - Du') (Dphi a) + Du' ((Dphi - Dphi') a)‖ ≤
        ‖(Du - Du') (Dphi a)‖ + ‖Du' ((Dphi - Dphi') a)‖ :=
      norm_add_le _ _
    _ ≤ ‖Du - Du'‖ * (‖Dphi‖ * ‖a‖) +
        ‖Du'‖ * (‖Dphi - Dphi'‖ * ‖a‖) :=
      add_le_add hfirst hsecond
    _ = (‖Du - Du'‖ * ‖Dphi‖ + ‖Du'‖ * ‖Dphi - Dphi'‖) *
        ‖a‖ := by ring

def c1PullbackGradientHolderConst
    (Kphi Ku Mphi Mu : NNReal) : NNReal :=
  Mphi * Ku + Mu * Kphi

theorem holderWith_c1PullbackGradient
    {X : Type*} [MetricSpace X]
    {alpha Kphi Ku Mphi Mu : NNReal}
    {Dphi : X → V →L[Real] W} {Du : X → W →L[Real] F}
    (hDphi : HolderWith Kphi alpha Dphi)
    (hDu : HolderWith Ku alpha Du)
    (hDphiNorm : ∀ x, ‖Dphi x‖ ≤ Mphi)
    (hDuNorm : ∀ x, ‖Du x‖ ≤ Mu) :
    HolderWith (c1PullbackGradientHolderConst Kphi Ku Mphi Mu) alpha
      (fun x => c1PullbackGradient (Dphi x) (Du x)) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hDphiDiff : ‖Dphi x - Dphi y‖ ≤
      (Kphi : Real) * dist x y ^ (alpha : Real) := by
    simpa only [dist_eq_norm] using hDphi.dist_le x y
  have hDuDiff : ‖Du x - Du y‖ ≤
      (Ku : Real) * dist x y ^ (alpha : Real) := by
    simpa only [dist_eq_norm] using hDu.dist_le x y
  have hraw := norm_c1PullbackGradient_sub_le
    (Dphi x) (Dphi y) (Du x) (Du y)
  have hreal :
      ‖c1PullbackGradient (Dphi x) (Du x) -
          c1PullbackGradient (Dphi y) (Du y)‖ ≤
        (c1PullbackGradientHolderConst Kphi Ku Mphi Mu : Real) *
          dist x y ^ (alpha : Real) := by
    refine hraw.trans ?_
    calc
      ‖Du x - Du y‖ * ‖Dphi x‖ + ‖Du y‖ * ‖Dphi x - Dphi y‖ ≤
          ((Ku : Real) * dist x y ^ (alpha : Real)) * Mphi +
            Mu * ((Kphi : Real) * dist x y ^ (alpha : Real)) := by
        gcongr
        · exact hDphiNorm x
        · exact hDuNorm y
      _ = (c1PullbackGradientHolderConst Kphi Ku Mphi Mu : Real) *
          dist x y ^ (alpha : Real) := by
        unfold c1PullbackGradientHolderConst
        push_cast
        ring
  calc
    ENNReal.ofReal (dist
        (c1PullbackGradient (Dphi x) (Du x))
        (c1PullbackGradient (Dphi y) (Du y))) ≤
      ENNReal.ofReal
        ((c1PullbackGradientHolderConst Kphi Ku Mphi Mu : Real) *
          dist x y ^ (alpha : Real)) := by
      rw [dist_eq_norm
        (c1PullbackGradient (Dphi x) (Du x))
        (c1PullbackGradient (Dphi y) (Du y))]
      exact ENNReal.ofReal_le_ofReal hreal
    _ = (c1PullbackGradientHolderConst Kphi Ku Mphi Mu : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = (c1PullbackGradientHolderConst Kphi Ku Mphi Mu : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

theorem continuousMultilinearCurryFin1_iteratedFDeriv_one_comp
    {f : W → F} {phi : V → W} {x : V}
    (hf : DifferentiableAt Real f (phi x))
    (hphi : DifferentiableAt Real phi x) :
    continuousMultilinearCurryFin1 Real V F
        (iteratedFDeriv Real 1 (f ∘ phi) x) =
      c1PullbackGradient (fderiv Real phi x) (fderiv Real f (phi x)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply,
    fderiv_comp x hf hphi]
  rfl

def c2PullbackHessian
    (Dphi : V →L[Real] W) (D2phi : V →L[Real] V →L[Real] W)
    (Du : W →L[Real] F) (D2u : W →L[Real] W →L[Real] F) :
    V →L[Real] V →L[Real] F :=
  (ContinuousLinearMap.compL Real V W F Du).comp D2phi +
    ((ContinuousLinearMap.compL Real V W F).flip Dphi).comp
      (D2u.comp Dphi)

theorem norm_c2PullbackHessian_le
    (Dphi : V →L[Real] W) (D2phi : V →L[Real] V →L[Real] W)
    (Du : W →L[Real] F) (D2u : W →L[Real] W →L[Real] F) :
    ‖c2PullbackHessian Dphi D2phi Du D2u‖ ≤
      ‖Du‖ * ‖D2phi‖ + ‖D2u‖ * ‖Dphi‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂
  · positivity
  intro a b
  simp only [c2PullbackHessian, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  have hfirst : ‖Du (D2phi a b)‖ ≤
      ‖Du‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) := by
    calc
      ‖Du (D2phi a b)‖ ≤ ‖Du‖ * ‖D2phi a b‖ := Du.le_opNorm _
      _ ≤ ‖Du‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (D2phi.le_opNorm₂ a b) (norm_nonneg Du)
  have hsecond : ‖D2u (Dphi a) (Dphi b)‖ ≤
      ‖D2u‖ * (‖Dphi‖ * ‖a‖) * (‖Dphi‖ * ‖b‖) := by
    calc
      ‖D2u (Dphi a) (Dphi b)‖ ≤
          ‖D2u‖ * ‖Dphi a‖ * ‖Dphi b‖ :=
        D2u.le_opNorm₂ (Dphi a) (Dphi b)
      _ ≤ ‖D2u‖ * (‖Dphi‖ * ‖a‖) * (‖Dphi‖ * ‖b‖) := by
        gcongr
        · exact Dphi.le_opNorm a
        · exact Dphi.le_opNorm b
  calc
    ‖Du (D2phi a b) + D2u (Dphi a) (Dphi b)‖ ≤
        ‖Du (D2phi a b)‖ + ‖D2u (Dphi a) (Dphi b)‖ :=
      norm_add_le _ _
    _ ≤ ‖Du‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) +
        (‖D2u‖ * (‖Dphi‖ * ‖a‖) * (‖Dphi‖ * ‖b‖)) :=
      add_le_add hfirst hsecond
    _ = (‖Du‖ * ‖D2phi‖ + ‖D2u‖ * ‖Dphi‖ ^ 2) *
        ‖a‖ * ‖b‖ := by ring

theorem norm_c2PullbackHessian_sub_le
    (Dphi Dphi' : V →L[Real] W)
    (D2phi D2phi' : V →L[Real] V →L[Real] W)
    (Du Du' : W →L[Real] F)
    (D2u D2u' : W →L[Real] W →L[Real] F) :
    ‖c2PullbackHessian Dphi D2phi Du D2u -
        c2PullbackHessian Dphi' D2phi' Du' D2u'‖ ≤
      ‖Du - Du'‖ * ‖D2phi‖ + ‖Du'‖ * ‖D2phi - D2phi'‖ +
        ‖D2u - D2u'‖ * ‖Dphi‖ ^ 2 +
        ‖D2u'‖ * ‖Dphi - Dphi'‖ * ‖Dphi‖ +
        ‖D2u'‖ * ‖Dphi'‖ * ‖Dphi - Dphi'‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂
  · positivity
  intro a b
  simp only [c2PullbackHessian, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  let z1 := (Du - Du') (D2phi a b)
  let z2 := Du' ((D2phi - D2phi') a b)
  let z3 := (D2u - D2u') (Dphi a) (Dphi b)
  let z4 := D2u' ((Dphi - Dphi') a) (Dphi b)
  let z5 := D2u' (Dphi' a) ((Dphi - Dphi') b)
  have heq :
      Du (D2phi a b) + D2u (Dphi a) (Dphi b) -
          (Du' (D2phi' a b) + D2u' (Dphi' a) (Dphi' b)) =
        z1 + z2 + z3 + z4 + z5 := by
    simp only [z1, z2, z3, z4, z5, ContinuousLinearMap.sub_apply,
      map_sub]
    abel
  have hz1 : ‖z1‖ ≤ ‖Du - Du'‖ * ‖D2phi‖ * ‖a‖ * ‖b‖ := by
    calc
      ‖z1‖ ≤ ‖Du - Du'‖ * ‖D2phi a b‖ := by
        exact (Du - Du').le_opNorm _
      _ ≤ ‖Du - Du'‖ * (‖D2phi‖ * ‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left (D2phi.le_opNorm₂ a b)
          (norm_nonneg (Du - Du'))
      _ = ‖Du - Du'‖ * ‖D2phi‖ * ‖a‖ * ‖b‖ := by ring
  have hz2 : ‖z2‖ ≤ ‖Du'‖ * ‖D2phi - D2phi'‖ * ‖a‖ * ‖b‖ := by
    calc
      ‖z2‖ ≤ ‖Du'‖ * ‖(D2phi - D2phi') a b‖ := Du'.le_opNorm _
      _ ≤ ‖Du'‖ * (‖D2phi - D2phi'‖ * ‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left ((D2phi - D2phi').le_opNorm₂ a b)
          (norm_nonneg Du')
      _ = ‖Du'‖ * ‖D2phi - D2phi'‖ * ‖a‖ * ‖b‖ := by ring
  have hz3 : ‖z3‖ ≤
      ‖D2u - D2u'‖ * ‖Dphi‖ ^ 2 * ‖a‖ * ‖b‖ := by
    calc
      ‖z3‖ ≤ ‖D2u - D2u'‖ * ‖Dphi a‖ * ‖Dphi b‖ :=
        (D2u - D2u').le_opNorm₂ (Dphi a) (Dphi b)
      _ ≤ ‖D2u - D2u'‖ * (‖Dphi‖ * ‖a‖) *
          (‖Dphi‖ * ‖b‖) := by
        gcongr
        · exact Dphi.le_opNorm a
        · exact Dphi.le_opNorm b
      _ = ‖D2u - D2u'‖ * ‖Dphi‖ ^ 2 * ‖a‖ * ‖b‖ := by ring
  have hz4 : ‖z4‖ ≤
      ‖D2u'‖ * ‖Dphi - Dphi'‖ * ‖Dphi‖ * ‖a‖ * ‖b‖ := by
    calc
      ‖z4‖ ≤ ‖D2u'‖ * ‖(Dphi - Dphi') a‖ * ‖Dphi b‖ :=
        D2u'.le_opNorm₂ ((Dphi - Dphi') a) (Dphi b)
      _ ≤ ‖D2u'‖ * (‖Dphi - Dphi'‖ * ‖a‖) *
          (‖Dphi‖ * ‖b‖) := by
        gcongr
        · exact (Dphi - Dphi').le_opNorm a
        · exact Dphi.le_opNorm b
      _ = ‖D2u'‖ * ‖Dphi - Dphi'‖ * ‖Dphi‖ * ‖a‖ * ‖b‖ := by ring
  have hz5 : ‖z5‖ ≤
      ‖D2u'‖ * ‖Dphi'‖ * ‖Dphi - Dphi'‖ * ‖a‖ * ‖b‖ := by
    calc
      ‖z5‖ ≤ ‖D2u'‖ * ‖Dphi' a‖ * ‖(Dphi - Dphi') b‖ :=
        D2u'.le_opNorm₂ (Dphi' a) ((Dphi - Dphi') b)
      _ ≤ ‖D2u'‖ * (‖Dphi'‖ * ‖a‖) *
          (‖Dphi - Dphi'‖ * ‖b‖) := by
        gcongr
        · exact Dphi'.le_opNorm a
        · exact (Dphi - Dphi').le_opNorm b
      _ = ‖D2u'‖ * ‖Dphi'‖ * ‖Dphi - Dphi'‖ * ‖a‖ * ‖b‖ := by ring
  rw [heq]
  calc
    ‖z1 + z2 + z3 + z4 + z5‖ ≤
        ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ := by
      calc
        ‖z1 + z2 + z3 + z4 + z5‖ ≤
            ‖z1 + z2 + z3 + z4‖ + ‖z5‖ := norm_add_le _ _
        _ ≤ (‖z1 + z2 + z3‖ + ‖z4‖) + ‖z5‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ((‖z1 + z2‖ + ‖z3‖) + ‖z4‖) + ‖z5‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (((‖z1‖ + ‖z2‖) + ‖z3‖) + ‖z4‖) + ‖z5‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (‖Du - Du'‖ * ‖D2phi‖ + ‖Du'‖ * ‖D2phi - D2phi'‖ +
          ‖D2u - D2u'‖ * ‖Dphi‖ ^ 2 +
          ‖D2u'‖ * ‖Dphi - Dphi'‖ * ‖Dphi‖ +
          ‖D2u'‖ * ‖Dphi'‖ * ‖Dphi - Dphi'‖) * ‖a‖ * ‖b‖ := by
      calc
        ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ ≤
            (‖Du - Du'‖ * ‖D2phi‖ * ‖a‖ * ‖b‖) +
            (‖Du'‖ * ‖D2phi - D2phi'‖ * ‖a‖ * ‖b‖) +
            (‖D2u - D2u'‖ * ‖Dphi‖ ^ 2 * ‖a‖ * ‖b‖) +
            (‖D2u'‖ * ‖Dphi - Dphi'‖ * ‖Dphi‖ * ‖a‖ * ‖b‖) +
            (‖D2u'‖ * ‖Dphi'‖ * ‖Dphi - Dphi'‖ * ‖a‖ * ‖b‖) := by
          gcongr
        _ = _ := by ring

def c2PullbackHessianHolderConst
    (Kphi K2phi Ku K2u Mphi M2phi Mu M2u : NNReal) : NNReal :=
  M2phi * Ku + Mu * K2phi + Mphi ^ 2 * K2u +
    2 * M2u * Mphi * Kphi

theorem holderWith_c2PullbackHessian
    {X : Type*} [MetricSpace X]
    {alpha Kphi K2phi Ku K2u Mphi M2phi Mu M2u : NNReal}
    {Dphi : X → V →L[Real] W}
    {D2phi : X → V →L[Real] V →L[Real] W}
    {Du : X → W →L[Real] F}
    {D2u : X → W →L[Real] W →L[Real] F}
    (hDphi : HolderWith Kphi alpha Dphi)
    (hD2phi : HolderWith K2phi alpha D2phi)
    (hDu : HolderWith Ku alpha Du)
    (hD2u : HolderWith K2u alpha D2u)
    (hDphiNorm : ∀ x, ‖Dphi x‖ ≤ Mphi)
    (hD2phiNorm : ∀ x, ‖D2phi x‖ ≤ M2phi)
    (hDuNorm : ∀ x, ‖Du x‖ ≤ Mu)
    (hD2uNorm : ∀ x, ‖D2u x‖ ≤ M2u) :
    HolderWith
      (c2PullbackHessianHolderConst
        Kphi K2phi Ku K2u Mphi M2phi Mu M2u)
      alpha
      (fun x => c2PullbackHessian (Dphi x) (D2phi x) (Du x) (D2u x)) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hDphiDiff : ‖Dphi x - Dphi y‖ ≤
      (Kphi : Real) * dist x y ^ (alpha : Real) := by
    simpa only [dist_eq_norm] using hDphi.dist_le x y
  have hD2phiDiff : ‖D2phi x - D2phi y‖ ≤
      (K2phi : Real) * dist x y ^ (alpha : Real) := by
    simpa only [dist_eq_norm] using hD2phi.dist_le x y
  have hDuDiff : ‖Du x - Du y‖ ≤
      (Ku : Real) * dist x y ^ (alpha : Real) := by
    simpa only [dist_eq_norm] using hDu.dist_le x y
  have hD2uDiff : ‖D2u x - D2u y‖ ≤
      (K2u : Real) * dist x y ^ (alpha : Real) := by
    simpa only [dist_eq_norm] using hD2u.dist_le x y
  have hraw := norm_c2PullbackHessian_sub_le
    (Dphi x) (Dphi y) (D2phi x) (D2phi y)
      (Du x) (Du y) (D2u x) (D2u y)
  have hreal :
      ‖c2PullbackHessian (Dphi x) (D2phi x) (Du x) (D2u x) -
          c2PullbackHessian (Dphi y) (D2phi y) (Du y) (D2u y)‖ ≤
        (c2PullbackHessianHolderConst
          Kphi K2phi Ku K2u Mphi M2phi Mu M2u : Real) *
          dist x y ^ (alpha : Real) := by
    refine hraw.trans ?_
    calc
      ‖Du x - Du y‖ * ‖D2phi x‖ + ‖Du y‖ * ‖D2phi x - D2phi y‖ +
          ‖D2u x - D2u y‖ * ‖Dphi x‖ ^ 2 +
          ‖D2u y‖ * ‖Dphi x - Dphi y‖ * ‖Dphi x‖ +
          ‖D2u y‖ * ‖Dphi y‖ * ‖Dphi x - Dphi y‖ ≤
        ((Ku : Real) * dist x y ^ (alpha : Real)) * M2phi +
          Mu * ((K2phi : Real) * dist x y ^ (alpha : Real)) +
          ((K2u : Real) * dist x y ^ (alpha : Real)) * Mphi ^ 2 +
          M2u * ((Kphi : Real) * dist x y ^ (alpha : Real)) * Mphi +
          M2u * Mphi * ((Kphi : Real) * dist x y ^ (alpha : Real)) := by
        gcongr
        · exact hD2phiNorm x
        · exact hDuNorm y
        · exact hDphiNorm x
        · exact hD2uNorm y
        · exact hDphiNorm x
        · exact hD2uNorm y
        · exact hDphiNorm y
      _ = (c2PullbackHessianHolderConst
          Kphi K2phi Ku K2u Mphi M2phi Mu M2u : Real) *
          dist x y ^ (alpha : Real) := by
        unfold c2PullbackHessianHolderConst
        push_cast
        ring
  calc
    ENNReal.ofReal (dist
        (c2PullbackHessian (Dphi x) (D2phi x) (Du x) (D2u x))
        (c2PullbackHessian (Dphi y) (D2phi y) (Du y) (D2u y))) ≤
      ENNReal.ofReal
        ((c2PullbackHessianHolderConst
          Kphi K2phi Ku K2u Mphi M2phi Mu M2u : Real) *
          dist x y ^ (alpha : Real)) := by
      rw [dist_eq_norm
        (c2PullbackHessian (Dphi x) (D2phi x) (Du x) (D2u x))
        (c2PullbackHessian (Dphi y) (D2phi y) (Du y) (D2u y))]
      exact ENNReal.ofReal_le_ofReal hreal
    _ = (c2PullbackHessianHolderConst
        Kphi K2phi Ku K2u Mphi M2phi Mu M2u : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = (c2PullbackHessianHolderConst
        Kphi K2phi Ku K2u Mphi M2phi Mu M2u : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

theorem hessianCurryEquiv_iteratedFDeriv_two_comp
    {f : W → F} {phi : V → W} {x : V}
    (hf : ContDiffAt Real 2 f (phi x))
    (hphi : ContDiffAt Real 2 phi x) :
    hessianCurryEquiv V F (iteratedFDeriv Real 2 (f ∘ phi) x) =
      c2PullbackHessian (fderiv Real phi x)
        (hessianCurryEquiv V W (iteratedFDeriv Real 2 phi x))
        (fderiv Real f (phi x))
        (hessianCurryEquiv W F (iteratedFDeriv Real 2 f (phi x))) := by
  rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
  have hfdiff : DifferentiableAt Real (fderiv Real f) (phi x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hphidiff : DifferentiableAt Real phi x :=
    hphi.differentiableAt (by norm_num)
  have hDphidiff : DifferentiableAt Real (fderiv Real phi) x :=
    (hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcompdiff : DifferentiableAt Real
      (fun y => fderiv Real f (phi y)) x :=
    hfdiff.comp x hphidiff
  have hphieventually : ∀ᶠ y in nhds x, ContDiffAt Real 2 phi y :=
    hphi.eventually (by norm_num)
  have hfeventually : ∀ᶠ y in nhds x, ContDiffAt Real 2 f (phi y) :=
    hphi.continuousAt (hf.eventually (by norm_num))
  have hfirst : fderiv Real (f ∘ phi) =ᶠ[nhds x]
      fun y => (fderiv Real f (phi y)).comp (fderiv Real phi y) := by
    filter_upwards [hphieventually, hfeventually] with y hyphi hyf
    exact fderiv_comp y (hyf.differentiableAt (by norm_num))
      (hyphi.differentiableAt (by norm_num))
  rw [hfirst.fderiv_eq, fderiv_clm_comp hcompdiff hDphidiff]
  unfold c2PullbackHessian
  rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
    hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
  have hchain : fderiv Real (fun y => fderiv Real f (phi y)) x =
      (fderiv Real (fderiv Real f) (phi x)).comp
        (fderiv Real phi x) := by
    simpa only [Function.comp_apply] using
      fderiv_comp x hfdiff hphidiff
  rw [hchain]

end DifferentialGeometry.Analysis.Schauder
