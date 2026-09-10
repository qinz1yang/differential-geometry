import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovNonpositiveLocal

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace Poincare.Geometry.Riemannian.VolumeComparison

def doublingConstant (n : ℕ) (a : ℝ) : ℝ :=
  modelVolume (-a / (n - 1 : ℕ)) n 1 /
    modelVolume (-a / (n - 1 : ℕ)) n (1 / 2)

theorem modelVolume_doubling_scale (q r θ : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hr : 0 < r) (hn : 1 ≤ n) :
    modelVolume (-((q / r) ^ 2)) n (θ * r) =
      r ^ n * modelVolume (-(q ^ 2)) n θ := by
  simpa only [mul_comm] using modelVolume_neg_sq_scale q r θ n hq hr hn

theorem modelVolume_doubling_scale_of_nonneg (a r θ : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hr : 0 < r) (hn : 2 ≤ n) :
    modelVolume (-a / (((n - 1 : ℕ) : ℝ) * r ^ 2)) n (θ * r) =
      r ^ n * modelVolume (-a / (n - 1 : ℕ)) n θ := by
  let q := Real.sqrt (a / (n - 1 : ℕ))
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hn
  have hfrac : 0 ≤ a / ((n - 1 : ℕ) : ℝ) := div_nonneg ha hn1.le
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = a / ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt hfrac
  have hleft : -((q / r) ^ 2) = -a / (((n - 1 : ℕ) : ℝ) * r ^ 2) := by
    rw [div_pow, hq2]
    field_simp
  have hright : -(q ^ 2) = -a / (n - 1 : ℕ) := by
    rw [hq2]
    ring
  rw [← hleft, ← hright]
  exact modelVolume_doubling_scale q r θ n hq hr (le_trans (by omega) hn)

theorem doublingConstant_eq_scaled_modelRatio (n : ℕ) (a r : ℝ)
    (hn : 2 ≤ n) (ha : 0 ≤ a) (hr : 0 < r) :
    doublingConstant n a =
      modelVolume (-a / (((n - 1 : ℕ) : ℝ) * r ^ 2)) n r /
        modelVolume (-a / (((n - 1 : ℕ) : ℝ) * r ^ 2)) n (r / 2) := by
  have hscaleOne :=
    modelVolume_doubling_scale_of_nonneg a r 1 n ha hr hn
  have hscaleHalf :=
    modelVolume_doubling_scale_of_nonneg a r (1 / 2) n ha hr hn
  have hrpow : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
  rw [doublingConstant]
  norm_num only [one_mul] at hscaleOne
  have hhalf : (1 / 2 : ℝ) * r = r / 2 := by ring
  rw [hhalf] at hscaleHalf
  rw [hscaleOne, hscaleHalf]
  field_simp

theorem doublingConstant_den_pos (n : ℕ) (a : ℝ)
    (hn : 2 ≤ n) (ha : 0 ≤ a) :
    0 < modelVolume (-a / (n - 1 : ℕ)) n (1 / 2) := by
  have hK : -a / ((n - 1 : ℕ) : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _)
  apply modelVolume_pos (le_trans (by omega) hn) (by norm_num)
  exact ⟨by norm_num, fun hKpos => (not_lt_of_ge hK hKpos).elim⟩

theorem doublingConstant_pos (n : ℕ) (a : ℝ)
    (hn : 2 ≤ n) (ha : 0 ≤ a) : 0 < doublingConstant n a := by
  have hK : -a / ((n - 1 : ℕ) : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _)
  have hnum : 0 < modelVolume (-a / (n - 1 : ℕ)) n 1 := by
    apply modelVolume_pos (le_trans (by omega) hn) one_pos
    exact ⟨zero_le_one, fun hKpos => (not_lt_of_ge hK hKpos).elim⟩
  exact div_pos hnum (doublingConstant_den_pos n a hn ha)

theorem doublingConstant_zero (n : ℕ) (hn : 1 ≤ n) :
    doublingConstant n 0 = (2 : ℝ) ^ n := by
  have hω : euclideanUnitBallVolume n ≠ 0 :=
    (euclideanUnitBallVolume_pos n).ne'
  rw [doublingConstant]
  norm_num only [zero_div, neg_zero]
  rw [modelVolume_zero n 1 hn, modelVolume_zero n (1 / 2) hn]
  field_simp
  rw [← mul_pow]
  norm_num

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem localDoubling
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (hn : 2 ≤ Module.finrank ℝ E)
    {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal r}
      (-a / r ^ 2)) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal r} ≤
      ENNReal.ofReal (doublingConstant (Module.finrank ℝ E) a) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)} := by
  let n : ℕ := Module.finrank ℝ E
  let d : ℕ := n - 1
  let q0 : ℝ := Real.sqrt (a / (d : ℝ))
  let q : ℝ := q0 / r
  have hdNat : 0 < d := Nat.sub_pos_of_lt hn
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hfrac : 0 ≤ a / (d : ℝ) := div_nonneg ha hd.le
  have hq0 : 0 ≤ q0 := Real.sqrt_nonneg _
  have hq : 0 ≤ q := div_nonneg hq0 hr.le
  have hq0sq : q0 ^ 2 = a / (d : ℝ) := Real.sq_sqrt hfrac
  have hcurv : -((d : ℝ) * q ^ 2) = -a / r ^ 2 := by
    dsimp only [q]
    rw [div_pow, hq0sq]
    field_simp
  have hRic' : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal r}
      (-((d : ℝ) * q ^ 2)) := by
    simpa only [hcurv] using hRic
  have hs : 0 < r / 2 := half_pos hr
  have hcross := segmentBall_vol_rel_endpoint_of_ricciBoundedBelowOn
    (I := I) g hEnorm x hq hs (by linarith : r / 2 ≤ r) hRic'
  let K : ℝ := -a / ((d : ℝ) * r ^ 2)
  let VR : ℝ := modelVolume K n r
  let Vs : ℝ := modelVolume K n (r / 2)
  have hK : K = -(q ^ 2) := by
    dsimp only [K, q]
    rw [div_pow, hq0sq]
    field_simp
  have hVsPos : 0 < Vs := by
    dsimp only [Vs]
    have hKnonpos : K ≤ 0 := by
      dsimp only [K]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
        (mul_nonneg hd.le (sq_nonneg r))
    apply modelVolume_pos (le_trans (by omega) hn) hs
    exact ⟨hs.le, fun hKpos => (not_lt_of_ge hKnonpos hKpos).elim⟩
  have hcrossModel :
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal r} *
          ENNReal.ofReal Vs ≤
        ENNReal.ofReal VR *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)} := by
    have hmodelR := ofReal_modelVolume_neg_sq q r n
      (le_trans (by omega) hn) hq
    have hmodels := ofReal_modelVolume_neg_sq q (r / 2) n
      (le_trans (by omega) hn) hq
    rw [← hK] at hmodelR hmodels
    change ENNReal.ofReal VR = _ at hmodelR
    change ENNReal.ofReal Vs = _ at hmodels
    rw [hmodelR, hmodels]
    calc
      riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal r} *
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
            ENNReal.ofReal (hyperbolicRadialVolume q (n - 1) (r / 2))) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
            (riemannianVolumeMeasure (I := I) (M := M) g
                {y : M | riemannianEDist I x y < ENNReal.ofReal r} *
              ENNReal.ofReal (hyperbolicRadialVolume q (n - 1) (r / 2))) := by ac_rfl
      _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
          (ENNReal.ofReal (hyperbolicRadialVolume q (n - 1) r) *
            riemannianVolumeMeasure (I := I) (M := M) g
              {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)}) := by
        exact mul_le_mul_right (by simpa only [n, d] using hcross) _
      _ = ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
          ENNReal.ofReal (hyperbolicRadialVolume q (n - 1) r)) *
            riemannianVolumeMeasure (I := I) (M := M) g
              {y : M | riemannianEDist I x y < ENNReal.ofReal (r / 2)} := by ac_rfl
  have hdiv := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 hVsPos).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2 hcrossModel
  have hD : doublingConstant n a = VR / Vs := by
    simpa only [K, VR, Vs, n, d] using
      doublingConstant_eq_scaled_modelRatio n a r hn ha hr
  rw [ENNReal.mul_div_right_comm] at hdiv
  rw [← ENNReal.ofReal_div_of_pos hVsPos, ← hD] at hdiv
  simpa only [n] using hdiv

end Poincare.Geometry.Riemannian.VolumeComparison
