import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotentialMeasurability

noncomputable section

open MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def heatPotentialSchauderConst
    (alpha K B Csource : NNReal) (T : Real) : NNReal :=
  (heatPotentialC2HolderGaugeConst (V := V) alpha K B Csource
    (Real.toNNReal (T * (B : Real)))
    (Real.toNNReal (2 * (B : Real) * heatC1 V * Real.sqrt T)) T).toNNReal

def heatDuhConstSchauderConst
    (alpha K B : NNReal) (T : Real) : NNReal :=
  4 * heatPotentialSchauderConst (V := V) alpha K B K T

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem real_toNNReal_nnreal_mul (c : NNReal) (x : Real) :
    Real.toNNReal ((c : Real) * x) = c * Real.toNNReal x := by
  rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe]

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhHolderConst alpha v w K := by
  simp [d2DuhHolderConst]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhSpaceHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhSpaceHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhSpaceHolderConst alpha v w K := by
  simp [d2DuhSpaceHolderConst]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhTimeHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhTimeHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhTimeHolderConst alpha v w K := by
  simp [d2DuhTimeHolderConst]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhParabolicHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhParabolicHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhParabolicHolderConst alpha v w K := by
  rw [d2DuhParabolicHolderConst, d2DuhParabolicHolderConst,
    d2DuhSpaceHolderConst_nnreal_mul, d2DuhTimeHolderConst_nnreal_mul]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhJetNormConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) (T : Real) :
    d2DuhJetNormConst (V := V) alpha (c * K) T =
      c * d2DuhJetNormConst (V := V) alpha K T := by
  rw [d2DuhJetNormConst, d2DuhJetNormConst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhHolderConst_nnreal_mul]
  rw [show (c : Real) * d2DuhHolderConst alpha
      ((stdOrthonormalBasis Real V) (beta 0))
      ((stdOrthonormalBasis Real V) (beta 1)) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      (c : Real) * (d2DuhHolderConst alpha
        ((stdOrthonormalBasis Real V) (beta 0))
        ((stdOrthonormalBasis Real V) (beta 1)) K *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2))) by ring]
  exact real_toNNReal_nnreal_mul c _

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhJetHolderConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) :
    d2DuhJetHolderConst (V := V) alpha (c * K) =
      c * d2DuhJetHolderConst (V := V) alpha K := by
  rw [d2DuhJetHolderConst, d2DuhJetHolderConst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhParabolicHolderConst_nnreal_mul,
    real_toNNReal_nnreal_mul]

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem lapDuhNormConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) (T : Real) :
    lapDuhNormConst (V := V) alpha (c * K) T =
      c * lapDuhNormConst (V := V) alpha K T := by
  rw [lapDuhNormConst, lapDuhNormConst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [d2DuhHolderConst_nnreal_mul]
  rw [show (c : Real) * d2DuhHolderConst alpha
      ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      (c : Real) * (d2DuhHolderConst alpha
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) K *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2))) by ring]
  exact real_toNNReal_nnreal_mul c _

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem lapDuhParabolicHolderConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) :
    lapDuhParabolicHolderConst (V := V) alpha (c * K) =
      (c : Real) * lapDuhParabolicHolderConst (V := V) alpha K := by
  rw [lapDuhParabolicHolderConst, lapDuhParabolicHolderConst,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact d2DuhParabolicHolderConst_nnreal_mul alpha _ _ c K

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem heatPotentialC2HolderGaugeConst_nnreal_mul
    (alpha : NNReal) (c K B Csource C0 C1 : NNReal) (T : Real) :
    heatPotentialC2HolderGaugeConst (V := V)
        alpha (c * K) (c * B) (c * Csource) (c * C0) (c * C1) T =
      c * heatPotentialC2HolderGaugeConst (V := V)
        alpha K B Csource C0 C1 T := by
  rw [heatPotentialC2HolderGaugeConst, heatPotentialC2HolderGaugeConst,
    d2DuhJetNormConst_nnreal_mul, lapDuhNormConst_nnreal_mul,
    d2DuhJetHolderConst_nnreal_mul,
    lapDuhParabolicHolderConst_nnreal_mul,
    real_toNNReal_nnreal_mul]
  push_cast
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatPotentialSchauderConst_nnreal_mul
    (alpha : NNReal) (c K B Csource : NNReal) (T : Real) :
    heatPotentialSchauderConst (V := V)
        alpha (c * K) (c * B) (c * Csource) T =
      c * heatPotentialSchauderConst (V := V) alpha K B Csource T := by
  have hC0 : Real.toNNReal (T * ((c * B : NNReal) : Real)) =
      c * Real.toNNReal (T * (B : Real)) := by
    rw [show T * ((c * B : NNReal) : Real) =
      (c : Real) * (T * (B : Real)) by push_cast; ring,
      real_toNNReal_nnreal_mul]
  have hC1 : Real.toNNReal
      (2 * ((c * B : NNReal) : Real) * heatC1 V * Real.sqrt T) =
      c * Real.toNNReal
        (2 * (B : Real) * heatC1 V * Real.sqrt T) := by
    rw [show 2 * ((c * B : NNReal) : Real) * heatC1 V * Real.sqrt T =
      (c : Real) *
        (2 * (B : Real) * heatC1 V * Real.sqrt T) by push_cast; ring,
      real_toNNReal_nnreal_mul]
  unfold heatPotentialSchauderConst
  rw [hC0, hC1, heatPotentialC2HolderGaugeConst_nnreal_mul,
    ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatDuhConstSchauderConst_nnreal_mul
    (alpha : NNReal) (c K B : NNReal) (T : Real) :
    heatDuhConstSchauderConst (V := V) alpha (c * K) (c * B) T =
      c * heatDuhConstSchauderConst (V := V) alpha K B T := by
  rw [heatDuhConstSchauderConst, heatDuhConstSchauderConst,
    heatPotentialSchauderConst_nnreal_mul]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhHolderConst alpha v w (K₁ + K₂) =
      d2DuhHolderConst alpha v w K₁ +
        d2DuhHolderConst alpha v w K₂ := by
  simp [d2DuhHolderConst]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhSpaceHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhSpaceHolderConst alpha v w (K₁ + K₂) =
      d2DuhSpaceHolderConst alpha v w K₁ +
        d2DuhSpaceHolderConst alpha v w K₂ := by
  simp [d2DuhSpaceHolderConst]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhTimeHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhTimeHolderConst alpha v w (K₁ + K₂) =
      d2DuhTimeHolderConst alpha v w K₁ +
        d2DuhTimeHolderConst alpha v w K₂ := by
  simp [d2DuhTimeHolderConst]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhParabolicHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhParabolicHolderConst alpha v w (K₁ + K₂) =
      d2DuhParabolicHolderConst alpha v w K₁ +
        d2DuhParabolicHolderConst alpha v w K₂ := by
  rw [d2DuhParabolicHolderConst, d2DuhParabolicHolderConst,
    d2DuhParabolicHolderConst,
    d2DuhSpaceHolderConst_add, d2DuhTimeHolderConst_add]
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhHolderConst_nonneg'
    (alpha : NNReal) (v w : V) (K : NNReal) :
    0 ≤ d2DuhHolderConst alpha v w K := by
  unfold d2DuhHolderConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
    (heatC2Holder_nonneg (V := V) alpha)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhJetNormConst_add
    {alpha : NNReal} (K₁ K₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    d2DuhJetNormConst (V := V) alpha (K₁ + K₂) T =
      d2DuhJetNormConst (V := V) alpha K₁ T +
        d2DuhJetNormConst (V := V) alpha K₂ T := by
  rw [d2DuhJetNormConst, d2DuhJetNormConst, d2DuhJetNormConst,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhHolderConst_add]
  rw [show (d2DuhHolderConst alpha
        ((stdOrthonormalBasis Real V) (beta 0))
        ((stdOrthonormalBasis Real V) (beta 1)) K₁ +
      d2DuhHolderConst alpha
        ((stdOrthonormalBasis Real V) (beta 0))
        ((stdOrthonormalBasis Real V) (beta 1)) K₂) *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      d2DuhHolderConst alpha
          ((stdOrthonormalBasis Real V) (beta 0))
          ((stdOrthonormalBasis Real V) (beta 1)) K₁ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) +
        d2DuhHolderConst alpha
          ((stdOrthonormalBasis Real V) (beta 0))
          ((stdOrthonormalBasis Real V) (beta 1)) K₂ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) by ring,
    Real.toNNReal_add]
  · exact mul_nonneg (d2DuhHolderConst_nonneg' alpha _ _ K₁)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))
  · exact mul_nonneg (d2DuhHolderConst_nonneg' alpha _ _ K₂)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhJetHolderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1) (K₁ K₂ : NNReal) :
    d2DuhJetHolderConst (V := V) alpha (K₁ + K₂) =
      d2DuhJetHolderConst (V := V) alpha K₁ +
        d2DuhJetHolderConst (V := V) alpha K₂ := by
  rw [d2DuhJetHolderConst, d2DuhJetHolderConst,
    d2DuhJetHolderConst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhParabolicHolderConst_add, Real.toNNReal_add]
  · exact d2DuhParabolicHolderConst_nonneg halpha1.le _ _ K₁
  · exact d2DuhParabolicHolderConst_nonneg halpha1.le _ _ K₂

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem lapDuhNormConst_add
    {alpha : NNReal} (K₁ K₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    lapDuhNormConst (V := V) alpha (K₁ + K₂) T =
      lapDuhNormConst (V := V) alpha K₁ T +
        lapDuhNormConst (V := V) alpha K₂ T := by
  rw [lapDuhNormConst, lapDuhNormConst, lapDuhNormConst,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [d2DuhHolderConst_add]
  rw [show (d2DuhHolderConst alpha
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) K₁ +
      d2DuhHolderConst alpha
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) K₂) *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      d2DuhHolderConst alpha
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K₁ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) +
        d2DuhHolderConst alpha
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K₂ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) by ring,
    Real.toNNReal_add]
  · exact mul_nonneg (d2DuhHolderConst_nonneg' alpha _ _ K₁)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))
  · exact mul_nonneg (d2DuhHolderConst_nonneg' alpha _ _ K₂)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem lapDuhParabolicHolderConst_add
    (alpha : NNReal) (K₁ K₂ : NNReal) :
    lapDuhParabolicHolderConst (V := V) alpha (K₁ + K₂) =
      lapDuhParabolicHolderConst (V := V) alpha K₁ +
        lapDuhParabolicHolderConst (V := V) alpha K₂ := by
  rw [lapDuhParabolicHolderConst, lapDuhParabolicHolderConst,
    lapDuhParabolicHolderConst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact d2DuhParabolicHolderConst_add alpha _ _ K₁ K₂

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem lapDuhParabolicHolderConst_nonneg'
    {alpha : NNReal} (halpha1 : alpha < 1) (K : NNReal) :
    0 ≤ lapDuhParabolicHolderConst (V := V) alpha K := by
  unfold lapDuhParabolicHolderConst
  exact Finset.sum_nonneg fun i hi ↦
    d2DuhParabolicHolderConst_nonneg halpha1.le _ _ K

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem heatPotentialC2HolderGaugeConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ Csource₁ Csource₂ C0₁ C0₂ C1₁ C1₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    heatPotentialC2HolderGaugeConst (V := V) alpha
        (K₁ + K₂) (B₁ + B₂) (Csource₁ + Csource₂)
        (C0₁ + C0₂) (C1₁ + C1₂) T =
      heatPotentialC2HolderGaugeConst (V := V)
          alpha K₁ B₁ Csource₁ C0₁ C1₁ T +
        heatPotentialC2HolderGaugeConst (V := V)
          alpha K₂ B₂ Csource₂ C0₂ C1₂ T := by
  rw [heatPotentialC2HolderGaugeConst,
    heatPotentialC2HolderGaugeConst,
    heatPotentialC2HolderGaugeConst,
    d2DuhJetNormConst_add K₁ K₂ hT,
    lapDuhNormConst_add K₁ K₂ hT,
    d2DuhJetHolderConst_add halpha1 K₁ K₂,
    lapDuhParabolicHolderConst_add]
  rw [Real.toNNReal_add
    (lapDuhParabolicHolderConst_nonneg' halpha1 K₁)
    (lapDuhParabolicHolderConst_nonneg' halpha1 K₂)]
  push_cast
  ring

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatPotentialSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ Csource₁ Csource₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    heatPotentialSchauderConst (V := V) alpha
        (K₁ + K₂) (B₁ + B₂) (Csource₁ + Csource₂) T =
      heatPotentialSchauderConst (V := V) alpha K₁ B₁ Csource₁ T +
        heatPotentialSchauderConst (V := V) alpha K₂ B₂ Csource₂ T := by
  have hC0 : Real.toNNReal (T * ((B₁ + B₂ : NNReal) : Real)) =
      Real.toNNReal (T * (B₁ : Real)) +
        Real.toNNReal (T * (B₂ : Real)) := by
    rw [show T * ((B₁ + B₂ : NNReal) : Real) =
      T * (B₁ : Real) + T * (B₂ : Real) by push_cast; ring,
      Real.toNNReal_add]
    · exact mul_nonneg hT B₁.coe_nonneg
    · exact mul_nonneg hT B₂.coe_nonneg
  have hC1 : Real.toNNReal
      (2 * ((B₁ + B₂ : NNReal) : Real) * heatC1 V * Real.sqrt T) =
      Real.toNNReal (2 * (B₁ : Real) * heatC1 V * Real.sqrt T) +
        Real.toNNReal
          (2 * (B₂ : Real) * heatC1 V * Real.sqrt T) := by
    rw [show 2 * ((B₁ + B₂ : NNReal) : Real) * heatC1 V * Real.sqrt T =
      2 * (B₁ : Real) * heatC1 V * Real.sqrt T +
        2 * (B₂ : Real) * heatC1 V * Real.sqrt T by push_cast; ring,
      Real.toNNReal_add]
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) B₁.coe_nonneg)
          (heatC1_nonneg (V := V))) (Real.sqrt_nonneg T)
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) B₂.coe_nonneg)
          (heatC1_nonneg (V := V))) (Real.sqrt_nonneg T)
  unfold heatPotentialSchauderConst
  rw [hC0, hC1, heatPotentialC2HolderGaugeConst_add halpha1
    K₁ K₂ B₁ B₂ Csource₁ Csource₂
    (Real.toNNReal (T * (B₁ : Real)))
    (Real.toNNReal (T * (B₂ : Real)))
    (Real.toNNReal
      (2 * (B₁ : Real) * heatC1 V * Real.sqrt T))
    (Real.toNNReal
      (2 * (B₂ : Real) * heatC1 V * Real.sqrt T)) hT,
    ENNReal.toNNReal_add]
  · simp [heatPotentialC2HolderGaugeConst]
  · simp [heatPotentialC2HolderGaugeConst]

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatDuhConstSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ : NNReal) {T : Real} (hT : 0 ≤ T) :
    heatDuhConstSchauderConst (V := V) alpha
        (K₁ + K₂) (B₁ + B₂) T =
      heatDuhConstSchauderConst (V := V) alpha K₁ B₁ T +
        heatDuhConstSchauderConst (V := V) alpha K₂ B₂ T := by
  rw [heatDuhConstSchauderConst, heatDuhConstSchauderConst,
    heatDuhConstSchauderConst,
    heatPotentialSchauderConst_add halpha1 K₁ K₂ B₁ B₂ K₁ K₂ hT]
  ring

omit [Nontrivial V] in
theorem coe_heatPotentialSchauderConst
    (alpha K B Csource : NNReal) (T : Real) :
    (heatPotentialSchauderConst (V := V) alpha K B Csource T : ENNReal) =
      heatPotentialC2HolderGaugeConst (V := V) alpha K B Csource
        (Real.toNNReal (T * (B : Real)))
        (Real.toNNReal (2 * (B : Real) * heatC1 V * Real.sqrt T)) T := by
  apply ENNReal.coe_toNNReal
  simp [heatPotentialC2HolderGaugeConst]

omit [CompleteSpace F] in
theorem heatDuhGradientMap_norm_le
    {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) x)
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatDuhGradientMap t f x‖ ≤
      2 * (B : Real) * heatC1 V * Real.sqrt t := by
  have hint := heatDuhGradient_int (V := V) ht f hbound x hmeas
  have hmajor := heatDuhGradientMajor_intble (V := V) (t := t) B
  unfold heatDuhGradientMap
  calc
    ‖∫ s : Real in 0..t, heatSupGradient (t - s) (f s) x‖ ≤
        ∫ s : Real in 0..t, ‖heatSupGradient (t - s) (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : Real in 0..t, heatDuhGradientMajor (V := V) B t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm hmajor
      intro s hs
      have hpos : 0 < t - s := sub_pos.mpr hs.2
      calc
        ‖heatSupGradient (t - s) (f s) x‖ ≤
            (heatScale (t - s))⁻¹ * heatC1 V * ‖f s‖ :=
          heatSupGradient_norm_le hpos (f s) x
        _ ≤ (heatScale (t - s))⁻¹ * heatC1 V * (B : Real) :=
          mul_le_mul_of_nonneg_left (hbound s ⟨hs.1.le, hs.2.le⟩)
            (mul_nonneg (inv_nonneg.mpr (heatScale_pos hpos).le)
              (heatC1_nonneg (V := V)))
        _ = heatDuhGradientMajor (V := V) B t s := by
          rw [← heatScale12_eq hpos]
          unfold heatDuhGradientMajor
          ring
    _ = 2 * (B : Real) * heatC1 V * Real.sqrt t := by
      unfold heatDuhGradientMajor
      rw [intervalIntegral.integral_const_mul, timeScale12_int,
        Real.sqrt_eq_rpow]
      ring

omit [CompleteSpace F] in
theorem heatDuh_fderiv_norm_le
    {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    ‖fderiv Real (heatDuh t f) x‖ ≤
      2 * (B : Real) * heatC1 V * Real.sqrt t := by
  rw [(heatDuh_hasFDerivAt ht f hbound hmeas0 hmeas1 x).fderiv]
  exact heatDuhGradientMap_norm_le ht f hbound x (hmeas1 x)

theorem heatDuh_schauder_estimate
    {alpha K B Csource : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)))
    (hmeas0 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSup (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupGradient (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuh t f x) ≤
      heatPotentialSchauderConst (V := V) alpha K B Csource T := by
  rw [coe_heatPotentialSchauderConst]
  apply eParabolicC2HolderGaugeOn_heatDuh_le_of_lower_jets
    halpha0 halpha1 hT hTS f
  · intro p hp
    unfold parabolicSpatialJet
    rw [norm_iteratedFDeriv_zero]
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans (hp.1.2.trans hTS.le)⟩
    have hraw := heatDuh_norm hp.1.1 f hbound' p.space
      (hmeas0 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩ p.space)
    have hTB : 0 ≤ T * (B : Real) := mul_nonneg hT B.coe_nonneg
    rw [Real.coe_toNNReal _ hTB]
    exact hraw.trans
      (mul_le_mul_of_nonneg_right hp.1.2 B.coe_nonneg)
  · intro p hp
    unfold parabolicSpatialJet
    rw [norm_iteratedFDeriv_one]
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans (hp.1.2.trans hTS.le)⟩
    have hraw := heatDuh_fderiv_norm_le hp.1.1 f hbound'
      (hmeas0 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩)
      (hmeas1 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩) p.space
    have hcoef : 0 ≤ 2 * (B : Real) * heatC1 V :=
      mul_nonneg (mul_nonneg (by positivity) B.coe_nonneg)
        (heatC1_nonneg (V := V))
    have hC : 0 ≤ 2 * (B : Real) * heatC1 V * Real.sqrt T :=
      mul_nonneg hcoef (Real.sqrt_nonneg T)
    rw [Real.coe_toNNReal _ hC]
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hp.1.2) hcoef)
  · exact hbound
  · exact hf
  · exact hsource
  · exact hmeas0
  · exact hmeas1
  · exact hmeas2

theorem heatDuh_schauder_estimate_of_parabolic_holder
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuh t f x) ≤
      heatPotentialSchauderConst (V := V) alpha K B K T := by
  have hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r) :=
    fun r hr => holderWith_slice_of_parabolicCylinder
      (f := fun s x => f s x) hsource hr
  have hsource' : HolderWith K alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).restrict
        (fun p => f p.time p.space)) := by
    rw [HolderWith.restrict_iff] at hsource ⊢
    exact hsource.mono fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
  exact heatDuh_schauder_estimate halpha0 halpha1 hT hTS f hbound hf
    hsource'
    (fun t ht z =>
      heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z)
    (fun t ht z =>
      heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z)
    (fun t ht z =>
      heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z)

theorem heatDuh_isParabolicC2HolderOn
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ f p.time p.space))) :
    IsParabolicC2HolderOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x ↦ heatDuh t f x) := by
  let Q : Set (ParabolicPoint V) :=
    parabolicCylinder (Ioc (0 : Real) T) Set.univ
  let w : Real → V → F := fun t x ↦ heatDuh t f x
  let C : NNReal := heatPotentialSchauderConst (V := V) alpha K B K T
  have hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r) :=
    fun r hr ↦ holderWith_slice_of_parabolicCylinder
      (f := fun s x ↦ f s x) hsource hr
  have hsource' : HolderWith K alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).restrict
        (fun p ↦ f p.time p.space)) := by
    rw [HolderWith.restrict_iff] at hsource ⊢
    exact hsource.mono fun p hp ↦ ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
  have hmeas0 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real ↦ heatSup (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)) :=
    fun t ht z ↦
      heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z
  have hmeas1 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real ↦ heatSupGradient (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)) :=
    fun t ht z ↦
      heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z
  have hmeas2 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real ↦ heatSupHessian (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)) :=
    fun t ht z ↦
      heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z
  have hgauge : eParabolicC2HolderGaugeOn alpha Q w ≤ C :=
    heatDuh_schauder_estimate_of_parabolic_holder
      halpha0 halpha1 hT hTS f hbound hsource
  refine ⟨⟨?_, ?_⟩,
    (parabolicSpatialJet_holderWith_restrict hgauge).memHolder,
    (parabolicTimeDerivative_holderWith_restrict hgauge).memHolder⟩
  · intro p hp
    have htS : p.time ∈ Ioc (0 : Real) S :=
      ⟨hp.1.1, hp.1.2.trans hTS.le⟩
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans htS.2⟩
    have hf' : ∀ s ∈ Icc (0 : Real) p.time,
        HolderWith K alpha (f s) := by
      intro s hs
      exact hf s ⟨hs.1, hs.2.trans htS.2⟩
    have hslice := holderWith_slice_of_parabolicCylinder
      (f := fun t x ↦ parabolicSpatialJet 2 w (parabolicPoint t x))
      (parabolicSpatialJet_holderWith_restrict hgauge) hp.1
    have hhessHolder : HolderWith C alpha (heatDuhHessian p.time f) := by
      have hcomp := (hessianCurryEquiv V F).lipschitz.holderWith.comp hslice
      have hcomp' : HolderWith C alpha
          (hessianCurryEquiv V F ∘
            fun x ↦ parabolicSpatialJet 2 w (parabolicPoint p.time x)) := by
        simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
      convert hcomp' using 1
      funext x
      exact (heatDuh_hessianCurryEquiv_iteratedFDeriv_two
        halpha0 halpha1.le hp.1.1 f hbound' hf'
        (hmeas0 p.time htS) (hmeas1 p.time htS)
        (hmeas2 p.time htS) x).symm
    have hhess : Continuous (heatDuhHessian p.time f) :=
      hhessHolder.continuous halpha0
    have hgrad : ContDiff Real 1 (heatDuhGradientMap p.time f) :=
      contDiff_one_iff_hasFDerivAt.mpr
        ⟨heatDuhHessian p.time f, hhess, fun x ↦
          heatDuhGradientMap_hasFDerivAt halpha0 halpha1.le hp.1.1
            f hbound' hf' (hmeas1 p.time htS) (hmeas2 p.time htS) x⟩
    exact ((contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
      ⟨heatDuhGradientMap p.time f, hgrad, fun x ↦
        heatDuh_hasFDerivAt hp.1.1 f hbound'
          (hmeas0 p.time htS) (hmeas1 p.time htS) x⟩).contDiffAt
  · intro p hp
    have htS : p.time ∈ Ioo (0 : Real) S :=
      ⟨hp.1.1, hp.1.2.trans_lt hTS⟩
    exact (heatDuh_time halpha0 halpha1 htS f hf hsource'
      hmeas2 p.space).differentiableAt

theorem heatDuh_const_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 < T) (hTS : T < S)
    (f : BoundedContinuousFunction V F)
    (hbound : ‖f‖ ≤ B) (hholder : HolderWith K alpha f) :
    eContDiffHolderGaugeOn 2 alpha Set.univ
      (heatDuh T (fun _ => f)) ≤
      heatDuhConstSchauderConst (V := V) alpha K B T := by
  have hpar := heatDuh_schauder_estimate_of_parabolic_holder
    halpha0 halpha1 hT.le hTS (fun _ => f)
    (fun _ _ => hbound)
    (holderWith_parabolic_const_time f hholder (Icc (0 : Real) S))
  have hslice := eContDiffHolderGaugeOn_slice_le
    (t := T) (J := Ioc (0 : Real) T) ⟨hT, le_rfl⟩ hpar
  unfold heatDuhConstSchauderConst
  convert hslice using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ENNReal.coe_mul, ENNReal.coe_ofNat]
  ring

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
