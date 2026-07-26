import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SubcriticalSmallTime

/-!
# Mixed critical--subcritical forcing fixed point

This file combines two nonlinear Nemytskii arms in the forcing-space
maximal-regularity construction.  The top arm loses two derivatives and must
have a small Lipschitz constant.  The lower arm loses one derivative and gains
the short-time factor `2 * sqrt T`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : Nat}
variable {a T : Real}

/-- A uniform horizon for a mixed contraction when the critical Lipschitz
constant already satisfies `2 * L2 < 1`. -/
def mixedHorizon (L2 L1 : NNReal) : Real :=
  min 1 (((1 - 2 * (L2 : Real)) / (4 * ((L1 : Real) + 1))) ^ 2)

theorem mixedHorizon_pos {L2 L1 : NNReal}
    (hL2 : 2 * (L2 : Real) < 1) : 0 < mixedHorizon L2 L1 := by
  rw [mixedHorizon]
  refine lt_min one_pos (sq_pos_of_pos ?_)
  exact div_pos (by linarith) (by positivity)

theorem mixedHorizon_le_one (L2 L1 : NNReal) :
    mixedHorizon L2 L1 ≤ 1 := by
  rw [mixedHorizon]
  exact min_le_left _ _

/-- Every positive sub-horizon of `mixedHorizon` satisfies the combined
critical--subcritical contraction inequality. -/
theorem mixedHorizon_small {L2 L1 : NNReal}
    (hL2 : 2 * (L2 : Real) < 1) {T : Real} (_hT : 0 < T)
    (hTL : T ≤ mixedHorizon L2 L1) :
    (L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T) < 1 := by
  let gap : Real := 1 - 2 * (L2 : Real)
  let q : Real := gap / (4 * ((L1 : Real) + 1))
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hq : 0 < q := div_pos hgap (by positivity)
  have hT1 : T ≤ 1 :=
    hTL.trans (mixedHorizon_le_one L2 L1)
  have hTq : T ≤ q ^ 2 := by
    exact hTL.trans (by
      rw [mixedHorizon]
      exact min_le_right _ _)
  have hsqrt : Real.sqrt T ≤ q := by
    rw [← Real.sqrt_sq hq.le]
    exact Real.sqrt_le_sqrt hTq
  have htop : (L2 : Real) * (1 + T) ≤ 2 * (L2 : Real) := by
    nlinarith [L2.coe_nonneg]
  have hfrac : (L1 : Real) / ((L1 : Real) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hlow : (L1 : Real) * (2 * Real.sqrt T) < gap := by
    calc
      (L1 : Real) * (2 * Real.sqrt T) ≤
          (L1 : Real) * (2 * q) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) L1.coe_nonneg
      _ = ((L1 : Real) / ((L1 : Real) + 1)) * (gap / 2) := by
        dsimp [q]
        field_simp [show (L1 : Real) + 1 ≠ 0 by positivity]
        ring
      _ < 1 * (gap / 2) := by
        exact mul_lt_mul_of_pos_right hfrac (by positivity)
      _ < gap := by linarith
  nlinarith

/-- The forcing map for a critical nonlinear arm and a subcritical nonlinear
arm. -/
def mixedMap (a : Real) {T : Real} (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    {L2 : NNReal}
    (N2 : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a)
    (hN2 : LipschitzWith L2 N2)
    {L1 : NNReal}
    (N1 : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (hN1 : LipschitzWith L1 N1) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun force =>
    nemytskii (I := I) (M := M) hN2
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
      nemytskiiHa1 (I := I) (M := M) hN1
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force)

@[simp] theorem mixedMap_apply (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    {L2 : NNReal}
    (N2 : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a)
    (hN2 : LipschitzWith L2 N2)
    {L1 : NNReal}
    (N1 : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (hN1 : LipschitzWith L1 N1)
    (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1 force =
      nemytskii (I := I) (M := M) hN2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
        nemytskiiHa1 (I := I) (M := M) hN1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) :=
  rfl

/-- The mixed map has contraction modulus
`L2 * (1 + T) + L1 * (2 * sqrt T)`. -/
theorem mixedMap_dist_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    {L2 : NNReal}
    (N2 : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a)
    (hN2 : LipschitzWith L2 N2)
    {L1 : NNReal}
    (N1 : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (hN1 : LipschitzWith L1 N1)
    (force force' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1 force)
        (mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1 force') ≤
      ((L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T)) *
        dist force force' := by
  have hfield2 := maxRegDuhamelSolField_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 force force'
  have hfield1 := maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 force force'
  have h2 := (nemytskii_lipschitzWith (I := I) (M := M) hN2).dist_le_mul
    (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force)
    (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')
  have h1 := (nemytskiiHa1_lipschitzWith (I := I) (M := M) hN1).dist_le_mul
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force)
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')
  have hfield2d : dist
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force)
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force') ≤
        (1 + T) * dist force force' := by
    simpa only [dist_eq_norm] using hfield2
  have hfield1d : dist
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force)
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force') ≤
        2 * Real.sqrt T * dist force force' := by
    simpa only [dist_eq_norm] using hfield1
  rw [dist_eq_norm, dist_eq_norm]
  unfold mixedMap
  have hsplit :
      (nemytskii (I := I) (M := M) hN2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
          nemytskiiHa1 (I := I) (M := M) hN1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force)) -
        (nemytskii (I := I) (M := M) hN2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force') +
          nemytskiiHa1 (I := I) (M := M) hN1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')) =
      (nemytskii (I := I) (M := M) hN2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) -
          nemytskii (I := I) (M := M) hN2
            (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')) +
        (nemytskiiHa1 (I := I) (M := M) hN1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) -
          nemytskiiHa1 (I := I) (M := M) hN1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')) := by
    abel
  rw [hsplit]
  calc
    _ ≤
        ‖nemytskii (I := I) (M := M) hN2
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) -
            nemytskii (I := I) (M := M) hN2
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force')‖ +
          ‖nemytskiiHa1 (I := I) (M := M) hN1
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) -
            nemytskiiHa1 (I := I) (M := M) hN1
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force')‖ :=
        norm_add_le _ _
    _ ≤ (L2 : Real) * ((1 + T) * ‖force - force'‖) +
          (L1 : Real) * ((2 * Real.sqrt T) * ‖force - force'‖) := by
      apply add_le_add
      · have hx := h2.trans
          (mul_le_mul_of_nonneg_left hfield2d L2.coe_nonneg)
        simpa only [dist_eq_norm] using hx
      · have hx := h1.trans
          (mul_le_mul_of_nonneg_left hfield1d L1.coe_nonneg)
        simpa only [dist_eq_norm] using hx
    _ = ((L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T)) *
          ‖force - force'‖ := by ring

/-- The mixed forcing map is a contraction under its transparent combined
smallness condition. -/
theorem mixedMap_contract
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    {L2 : NNReal}
    (N2 : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a)
    (hN2 : LipschitzWith L2 N2)
    {L1 : NNReal}
    (N1 : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (hN1 : LipschitzWith L1 N1)
    (hsmall :
      (L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T) < 1) :
    ContractingWith
      ⟨(L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T),
        add_nonneg
          (mul_nonneg L2.coe_nonneg (by linarith [hT.le]))
          (mul_nonneg L1.coe_nonneg (by positivity))⟩
      (mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1) := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa only [NNReal.coe_mk] using hsmall
  · refine LipschitzWith.of_dist_le_mul (fun force force' => ?_)
    have h := mixedMap_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u0 N2 hN2 N1 hN1
      force force'
    simpa only [NNReal.coe_mk] using h

/-- Strong existence for the fixed reference heat equation with a mixed
critical--subcritical nonlinear forcing. -/
theorem mixed_strong_exists
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    {L2 : NNReal}
    (N2 : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a)
    (hN2 : LipschitzWith L2 N2)
    {L1 : NNReal}
    (N1 : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (hN1 : LipschitzWith L1 N1)
    (hsmall :
      (L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T) < 1) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
      (force : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
      u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u0 force ∧
        force =
          nemytskii (I := I) (M := M) hN2
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
            nemytskiiHa1 (I := I) (M := M) hN1
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force) ∧
        TimeSobolev.timeH1.trace0 _ T u =
          tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a ≤ a + 2 by linarith) u0 ∧
        TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) a
              (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
            (nemytskii (I := I) (M := M) hN2
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force) +
              nemytskiiHa1 (I := I) (M := M) hN1
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0
                  force)) := by
  have hcontr := mixedMap_contract (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 N2 hN2 N1 hN1 hsmall
  set forceStar := ContractingWith.fixedPoint
    (mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1) hcontr
    with hforceStar_def
  have hfix :
      mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1 forceStar =
        forceStar := ContractingWith.fixedPoint_isFixedPt hcontr
  have hforce : forceStar =
      nemytskii (I := I) (M := M) hN2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 forceStar) +
        nemytskiiHa1 (I := I) (M := M) hN1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0
            forceStar) := by
    rw [← mixedMap_apply (I := I) (M := M) (a := a) hT hT1 u0
      N2 hN2 N1 hN1 forceStar, hfix]
  refine ⟨maxRegDuhamelMap (I := I) (M := M) a hT hT1 u0 forceStar,
    forceStar, rfl, hforce, ?_, ?_⟩
  · exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u0 forceStar
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT hT1 u0 forceStar]
    exact congrArg₂ (fun x y => x + y) rfl hforce

/-- Uniqueness of forcing-space fixed points for the same mixed nonlinear
equation. -/
theorem mixed_strong_unique
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : tensorHs (I := I) (M := M) g r s (a + 2))
    {L2 : NNReal}
    (N2 : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a)
    (hN2 : LipschitzWith L2 N2)
    {L1 : NNReal}
    (N1 : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (hN1 : LipschitzWith L1 N1)
    (hsmall :
      (L2 : Real) * (1 + T) + (L1 : Real) * (2 * Real.sqrt T) < 1)
    {force₁ force₂ : timeL2 (tensorHs (I := I) (M := M) g r s a) T}
    (hfix₁ : force₁ =
      nemytskii (I := I) (M := M) hN2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force₁) +
        nemytskiiHa1 (I := I) (M := M) hN1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force₁))
    (hfix₂ : force₂ =
      nemytskii (I := I) (M := M) hN2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u0 force₂) +
        nemytskiiHa1 (I := I) (M := M) hN1
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u0 force₂)) :
    force₁ = force₂ ∧
      maxRegDuhamelMap (I := I) (M := M) a hT hT1 u0 force₁ =
        maxRegDuhamelMap (I := I) (M := M) a hT hT1 u0 force₂ := by
  have hcontr := mixedMap_contract (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 N2 hN2 N1 hN1 hsmall
  have hf₁ : Function.IsFixedPt
      (mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1) force₁ := by
    change mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1 force₁ =
      force₁
    rw [mixedMap_apply (I := I) (M := M) (a := a) hT hT1 u0
      N2 hN2 N1 hN1 force₁]
    exact hfix₁.symm
  have hf₂ : Function.IsFixedPt
      (mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1) force₂ := by
    change mixedMap (I := I) (M := M) a hT hT1 u0 N2 hN2 N1 hN1 force₂ =
      force₂
    rw [mixedMap_apply (I := I) (M := M) (a := a) hT hT1 u0
      N2 hN2 N1 hN1 force₂]
    exact hfix₂.symm
  have heq : force₁ = force₂ := by
    rw [ContractingWith.fixedPoint_unique hcontr hf₁,
      ContractingWith.fixedPoint_unique hcontr hf₂]
  exact ⟨heq, by rw [heq]⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
