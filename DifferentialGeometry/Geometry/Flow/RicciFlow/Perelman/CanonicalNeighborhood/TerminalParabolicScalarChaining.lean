import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarComparison
import DifferentialGeometry.Geometry.Metric.Distance.Basic

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_le_sum_range_of_chain (g : SmoothRiemannianMetric I M) {p : ℕ → M}
    {r : ℕ → Real}
    (hchain : ∀ k : ℕ, riemannianEDistOf (I := I) g (p k) (p (k + 1)) ≤
      ENNReal.ofReal (r k)) :
    ∀ n : ℕ, riemannianEDistOf (I := I) g (p 0) (p n) ≤
      ∑ k ∈ Finset.range n, ENNReal.ofReal (r k) := by
  intro n
  induction n with
  | zero => simp [riemannianEDistOf_self]
  | succ n ih =>
    calc riemannianEDistOf (I := I) g (p 0) (p (n + 1))
        ≤ riemannianEDistOf (I := I) g (p 0) (p n) +
            riemannianEDistOf (I := I) g (p n) (p (n + 1)) :=
          riemannianEDistOf_triangle (I := I) g (p 0) (p n) (p (n + 1))
      _ ≤ (∑ k ∈ Finset.range n, ENNReal.ofReal (r k)) + ENNReal.ofReal (r n) :=
          add_le_add ih (hchain n)
      _ = ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (r k) := by
          rw [Finset.sum_range_succ]

theorem sum_range_one_div_sqrt_mul_lt {D Q : Real} (hD : 1 < D) (hQ : 0 < Q) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / Real.sqrt (D ^ k * Q) <
      1 / Real.sqrt Q * (1 - 1 / Real.sqrt D)⁻¹ := by
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  have hupos : 0 < (Real.sqrt D)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hDpos)
  have hult : (Real.sqrt D)⁻¹ < 1 := by
    rw [inv_lt_one₀ (Real.sqrt_pos.2 hDpos)]
    simpa using Real.sqrt_lt_sqrt (by norm_num) hD
  have hterm : ∀ k : ℕ, (Real.sqrt (D ^ k * Q))⁻¹ =
      (Real.sqrt Q)⁻¹ * (Real.sqrt D)⁻¹ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpow : D ^ (k + 1) * Q = D * (D ^ k * Q) := by ring
      rw [hpow, Real.sqrt_mul hDpos.le, mul_inv, ih, pow_succ]
      ring
  have hgeom : (∑ k ∈ Finset.range n, (Real.sqrt D)⁻¹ ^ k) <
      (1 - (Real.sqrt D)⁻¹)⁻¹ := by
    have hne : (1 : Real) - (Real.sqrt D)⁻¹ ≠ 0 := by linarith
    have hmul := geom_sum_mul_neg (Real.sqrt D)⁻¹ n
    have hsum_eq : (∑ k ∈ Finset.range n, (Real.sqrt D)⁻¹ ^ k) =
        (1 - (Real.sqrt D)⁻¹ ^ n) / (1 - (Real.sqrt D)⁻¹) := by
      rw [eq_div_iff hne]
      exact hmul
    have hlt : 1 - (Real.sqrt D)⁻¹ ^ n < 1 := by
      have hp := pow_pos hupos n
      linarith
    have hpos : 0 < 1 - (Real.sqrt D)⁻¹ := by linarith
    have hconv : (1 - (Real.sqrt D)⁻¹)⁻¹ = 1 / (1 - (Real.sqrt D)⁻¹) :=
      (one_div (1 - (Real.sqrt D)⁻¹)).symm
    rw [hsum_eq, hconv]
    exact div_lt_div_of_pos_right hlt hpos
  have hmain : ∑ k ∈ Finset.range n, (Real.sqrt (D ^ k * Q))⁻¹ <
      (Real.sqrt Q)⁻¹ * (1 - (Real.sqrt D)⁻¹)⁻¹ :=
    calc ∑ k ∈ Finset.range n, (Real.sqrt (D ^ k * Q))⁻¹
        = ∑ k ∈ Finset.range n, (Real.sqrt Q)⁻¹ * (Real.sqrt D)⁻¹ ^ k :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = (Real.sqrt Q)⁻¹ * ∑ k ∈ Finset.range n, (Real.sqrt D)⁻¹ ^ k :=
          (Finset.mul_sum _ _ _).symm
      _ < (Real.sqrt Q)⁻¹ * (1 - (Real.sqrt D)⁻¹)⁻¹ :=
          mul_lt_mul_of_pos_left hgeom (inv_pos.2 (Real.sqrt_pos.2 hQ))
  simpa only [one_div] using hmain

theorem riemannianEDistOf_lt_geomSeries_of_chain (g : SmoothRiemannianMetric I M)
    {p : ℕ → M} {Q D : Real} (hD : 1 < D) (hQ : 0 < Q)
    (hchain : ∀ k : ℕ, riemannianEDistOf (I := I) g (p k) (p (k + 1)) ≤
      ENNReal.ofReal (1 / Real.sqrt (D ^ k * Q))) :
    ∀ n : ℕ, riemannianEDistOf (I := I) g (p 0) (p n) <
      ENNReal.ofReal (1 / Real.sqrt Q * (1 - 1 / Real.sqrt D)⁻¹) := by
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  have htermpos : ∀ k : ℕ, 0 ≤ 1 / Real.sqrt (D ^ k * Q) := by
    intro k
    rw [one_div]
    exact (inv_pos.2 (Real.sqrt_pos.2 (mul_pos (pow_pos hDpos k) hQ))).le
  have hgeom : 0 < 1 / Real.sqrt Q * (1 - 1 / Real.sqrt D)⁻¹ := by
    have h1 : 0 < 1 / Real.sqrt Q := by
      rw [one_div]
      exact inv_pos.2 (Real.sqrt_pos.2 hQ)
    have h2 : 0 < 1 - 1 / Real.sqrt D := by
      have hlt : 1 / Real.sqrt D < 1 := by
        rw [one_div, inv_lt_one₀ (Real.sqrt_pos.2 hDpos)]
        simpa [Real.sqrt_one] using
          Real.sqrt_lt_sqrt (by norm_num : (0 : Real) ≤ 1) hD
      linarith
    exact mul_pos h1 (inv_pos.2 h2)
  intro n
  refine lt_of_le_of_lt
    (riemannianEDistOf_le_sum_range_of_chain (I := I) g hchain n) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => htermpos k)]
  exact (ENNReal.ofReal_lt_ofReal_iff hgeom).2 (sum_range_one_div_sqrt_mul_lt hD hQ n)

end Chain

section Promotion

theorem exists_scalar_le_mul_pow_of_modelCurvatureBound_chain {kappa : Real}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar D : Real, 0 < epsStar ∧ 1 < D ∧
      ∀ eps : Real, 0 < eps → eps ≤ epsStar → ∀ sigma : Real, 0 < sigma →
        ∀ Phi : Real → Real, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
            ∀ t ∈ Set.Icc (-(X.depth i)) 0, ∀ x : (X.term i).M,
              2 ≤ (X.term i).S.scalar t x → ∀ p : ℕ → (X.term i).M, p 0 = x →
                (∀ k : ℕ, 2 ≤ (X.term i).S.scalar t (p k)) →
                  (∀ k : ℕ, riemannianEDistOf (I := I3) ((X.term i).S.base.metric t)
                      (p k) (p (k + 1)) ≤
                    ENNReal.ofReal (1 / Real.sqrt (D ^ k * (X.term i).S.scalar t x))) →
                  ∀ n : ℕ, (X.term i).S.scalar t (p n) ≤ D ^ n * (X.term i).S.scalar t x := by
  obtain ⟨e, D₀, he, hD₀, hcmp⟩ :=
    exists_scalar_le_mul_scalar_of_modelCurvatureBound (kappa := kappa) hmod
  refine ⟨e, max D₀ 2, he, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X i t ht x hx p hp0 hbig hchain n
  have hD₀le : D₀ ≤ max D₀ 2 := le_max_left _ _
  have hDpos : (0 : Real) < max D₀ 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hQpos : 0 < (X.term i).S.scalar t x := lt_of_lt_of_le (by norm_num) hx
  induction n with
  | zero => rw [hp0]; simp
  | succ n ih =>
    have hpnp : 0 < (X.term i).S.scalar t (p n) := lt_of_lt_of_le (by norm_num) (hbig n)
    have hrad : 1 / Real.sqrt ((max D₀ 2) ^ n * (X.term i).S.scalar t x) ≤
        1 / Real.sqrt ((X.term i).S.scalar t (p n)) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.2 hpnp) (Real.sqrt_le_sqrt ih)
    have hbound : riemannianEDistOf (I := I3) ((X.term i).S.base.metric t)
        (p n) (p (n + 1)) ≤
        ENNReal.ofReal (1 / Real.sqrt ((X.term i).S.scalar t (p n))) :=
      le_trans (hchain n) (ENNReal.ofReal_le_ofReal hrad)
    have hstep := hcmp eps heps hle sigma hsigma Phi hPhi X i t ht (p n) (hbig n)
      (p (n + 1)) hbound
    calc (X.term i).S.scalar t (p (n + 1))
        ≤ D₀ * (X.term i).S.scalar t (p n) := hstep
      _ ≤ (max D₀ 2) * ((max D₀ 2) ^ n * (X.term i).S.scalar t x) :=
          mul_le_mul hD₀le ih hpnp.le hDpos.le
      _ = (max D₀ 2) ^ (n + 1) * (X.term i).S.scalar t x := by
          rw [pow_succ]
          ring

theorem riemannianEDistOf_lt_geomSeries_of_modelCurvatureBound_chain {kappa : Real}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar D : Real, 0 < epsStar ∧ 1 < D ∧
      ∀ eps : Real, 0 < eps → eps ≤ epsStar → ∀ sigma : Real, 0 < sigma →
        ∀ Phi : Real → Real, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
            ∀ t ∈ Set.Icc (-(X.depth i)) 0, ∀ x : (X.term i).M,
              2 ≤ (X.term i).S.scalar t x → ∀ p : ℕ → (X.term i).M, p 0 = x →
                  (∀ k : ℕ, riemannianEDistOf (I := I3) ((X.term i).S.base.metric t)
                      (p k) (p (k + 1)) ≤
                    ENNReal.ofReal (1 / Real.sqrt (D ^ k * (X.term i).S.scalar t x))) →
                  ∀ n : ℕ, riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) x (p n) <
                    ENNReal.ofReal (1 / Real.sqrt ((X.term i).S.scalar t x) *
                      (1 - 1 / Real.sqrt D)⁻¹) := by
  obtain ⟨e, D₀, he, hD₀, _hcmp⟩ :=
    exists_scalar_le_mul_scalar_of_modelCurvatureBound (kappa := kappa) hmod
  refine ⟨e, max D₀ 2, he, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X i t ht x hx p hp0 hchain n
  have hQpos : 0 < (X.term i).S.scalar t x := lt_of_lt_of_le (by norm_num) hx
  have hD1 : (1 : Real) < max D₀ 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hmain := riemannianEDistOf_lt_geomSeries_of_chain (I := I3)
    ((X.term i).S.base.metric t) (p := p) (Q := (X.term i).S.scalar t x)
    (D := max D₀ 2) hD1 hQpos hchain n
  rwa [hp0] at hmain

theorem scalar_le_mul_on_parabolicBall_of_modelCurvatureBound {kappa : Real}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar D : Real, 0 < epsStar ∧ 0 < D ∧
      ∀ eps : Real, 0 < eps → eps ≤ epsStar → ∀ sigma : Real, 0 < sigma →
        ∀ Phi : Real → Real, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
            ∀ t ∈ Set.Icc (-(X.depth i)) 0, ∀ z : (X.term i).M, ∀ A : Real,
              2 ≤ (X.term i).S.scalar t z → (X.term i).S.scalar t z ≤ A →
                ∀ y : (X.term i).M,
                  riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) z y ≤
                    ENNReal.ofReal (1 / Real.sqrt A) →
                  (X.term i).S.scalar t y ≤ D * A := by
  obtain ⟨e, D, he, hD, hcmp⟩ :=
    exists_scalar_le_mul_scalar_of_modelCurvatureBound (kappa := kappa) hmod
  refine ⟨e, D, he, hD, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X i t ht z A hz hzA y hy
  have hzpos : 0 < (X.term i).S.scalar t z := lt_of_lt_of_le (by norm_num) hz
  have hrad : 1 / Real.sqrt A ≤ 1 / Real.sqrt ((X.term i).S.scalar t z) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hzpos) (Real.sqrt_le_sqrt hzA)
  refine le_trans (hcmp eps heps hle sigma hsigma Phi hPhi X i t ht z hz y
    (le_trans hy (ENNReal.ofReal_le_ofReal hrad))) ?_
  exact mul_le_mul_of_nonneg_left hzA hD.le

end Promotion

section Sharpness

noncomputable def parabolicScalarModel (Q c : Real) (r : Real) : Real := Q / (1 - c * r) ^ 2

theorem parabolicScalarModel_step_le {Q c r δ : Real} (hQ : 0 < Q) (hc : 0 < c)
    (hclt : c < Real.sqrt Q) (hr : c * r < 1)
    (hstep : δ ≤ 1 / Real.sqrt (parabolicScalarModel Q c r)) :
    parabolicScalarModel Q c (r + δ) ≤
      (1 - c / Real.sqrt Q)⁻¹ ^ 2 * parabolicScalarModel Q c r := by
  have ha : 0 < 1 - c * r := by linarith
  have hspos : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hs : 0 < 1 - c / Real.sqrt Q := by
    have h := (div_lt_one hspos).2 hclt
    linarith
  have hroot : 1 / Real.sqrt (parabolicScalarModel Q c r) = (1 - c * r) / Real.sqrt Q := by
    have hsq : Real.sqrt ((1 - c * r) ^ 2) = 1 - c * r := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
    rw [parabolicScalarModel, one_div, Real.sqrt_div hQ.le ((1 - c * r) ^ 2), hsq]
    rw [inv_div]
  have hδ : δ ≤ (1 - c * r) / Real.sqrt Q := by rw [← hroot]; exact hstep
  have hprod : 0 < (1 - c * r) * (1 - c / Real.sqrt Q) := mul_pos ha hs
  have hkey : (1 - c * r) * (1 - c / Real.sqrt Q) ≤ 1 - c * (r + δ) := by
    have h1 : (1 - c * r) * (c / Real.sqrt Q) = c * ((1 - c * r) / Real.sqrt Q) := by
      field_simp
    have h2 : c * δ ≤ c * ((1 - c * r) / Real.sqrt Q) :=
      mul_le_mul_of_nonneg_left hδ hc.le
    nlinarith [h1, h2]
  have hsq2 : ((1 - c * r) * (1 - c / Real.sqrt Q)) ^ 2 ≤ (1 - c * (r + δ)) ^ 2 :=
    pow_le_pow_left₀ hprod.le hkey 2
  calc parabolicScalarModel Q c (r + δ)
      = Q / (1 - c * (r + δ)) ^ 2 := rfl
    _ ≤ Q / ((1 - c * r) * (1 - c / Real.sqrt Q)) ^ 2 :=
        div_le_div_of_nonneg_left hQ.le (pow_pos hprod 2) hsq2
    _ = (1 - c / Real.sqrt Q)⁻¹ ^ 2 * parabolicScalarModel Q c r := by
        rw [parabolicScalarModel]
        field_simp

theorem parabolicScalarModel_unbounded {Q c B : Real} (hQ : 0 < Q) (hc : 0 < c)
    (hB : 0 < B) :
    ∃ δ : Real, 0 ≤ δ ∧ c * δ < 1 ∧ B < parabolicScalarModel Q c δ := by
  have hBQ : 0 < Q / B := div_pos hQ hB
  have htpos : 0 < min (1 / 2) (Real.sqrt (Q / B) / 2) :=
    lt_min (by norm_num) (by positivity)
  have ht1 : min (1 / 2) (Real.sqrt (Q / B) / 2) ≤ 1 / 2 := min_le_left _ _
  have ht3 : min (1 / 2) (Real.sqrt (Q / B) / 2) ≤ Real.sqrt (Q / B) / 2 := min_le_right _ _
  refine ⟨(1 - min (1 / 2) (Real.sqrt (Q / B) / 2)) / c, ?_, ?_, ?_⟩
  · exact div_nonneg (by linarith [ht1]) hc.le
  · rw [mul_div_cancel₀ _ (ne_of_gt hc)]
    linarith
  · have hval : parabolicScalarModel Q c ((1 - min (1 / 2) (Real.sqrt (Q / B) / 2)) / c) =
        Q / (min (1 / 2) (Real.sqrt (Q / B) / 2)) ^ 2 := by
      rw [parabolicScalarModel]
      congr 2
      field_simp
      ring
    rw [hval]
    have hsqt : (min (1 / 2) (Real.sqrt (Q / B) / 2)) ^ 2 ≤ Q / (4 * B) := by
      have h4 : (Real.sqrt (Q / B)) ^ 2 = Q / B := Real.sq_sqrt hBQ.le
      have h : (Real.sqrt (Q / B) / 2) ^ 2 = Q / (4 * B) := by
        rw [div_pow, h4]
        ring
      calc (min (1 / 2) (Real.sqrt (Q / B) / 2)) ^ 2
          ≤ (Real.sqrt (Q / B) / 2) ^ 2 := pow_le_pow_left₀ htpos.le ht3 2
        _ = Q / (4 * B) := h
    have hpos2 : 0 < (min (1 / 2) (Real.sqrt (Q / B) / 2)) ^ 2 := pow_pos htpos 2
    have hmul : (min (1 / 2) (Real.sqrt (Q / B) / 2)) ^ 2 * (4 * B) ≤ Q :=
      (le_div_iff₀ (by positivity : (0 : Real) < 4 * B)).mp hsqt
    rw [lt_div_iff₀ hpos2]
    nlinarith [hmul, hB, hQ, hpos2]

theorem parabolicScalarModel_reach {Q c : Real} (hQ : 0 < Q) (hclt : c < Real.sqrt Q) :
    (1 - (Real.sqrt ((1 - c / Real.sqrt Q)⁻¹ ^ 2))⁻¹)⁻¹ = Real.sqrt Q / c := by
  have hspos : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hs : 0 < 1 - c / Real.sqrt Q := by
    have h := (div_lt_one hspos).2 hclt
    linarith
  have hroot : Real.sqrt ((1 - c / Real.sqrt Q)⁻¹ ^ 2) = (1 - c / Real.sqrt Q)⁻¹ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.2 hs)]
  rw [hroot, inv_inv]
  have hsub : 1 - (1 - c / Real.sqrt Q) = c / Real.sqrt Q := by ring
  rw [hsub, inv_div]

theorem parabolicScalarModel_sharp {Q c : Real} (hQ : 0 < Q) (hc : 0 < c)
    (hclt : c < Real.sqrt Q) :
    (∀ r δ : Real, c * r < 1 → δ ≤ 1 / Real.sqrt (parabolicScalarModel Q c r) →
        parabolicScalarModel Q c (r + δ) ≤
          (1 - c / Real.sqrt Q)⁻¹ ^ 2 * parabolicScalarModel Q c r) ∧
      (1 - (Real.sqrt ((1 - c / Real.sqrt Q)⁻¹ ^ 2))⁻¹)⁻¹ = Real.sqrt Q / c ∧
        ∀ A : Real, Real.sqrt Q / c ≤ A →
          ¬ ∃ C : Real, ∀ δ : Real, 0 ≤ δ → δ < A / Real.sqrt Q →
            parabolicScalarModel Q c δ ≤ C := by
  refine ⟨fun r δ hr hstep => parabolicScalarModel_step_le hQ hc hclt hr hstep,
    parabolicScalarModel_reach hQ hclt, ?_⟩
  intro A hA ⟨C, hC⟩
  have hspos : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hAc : Real.sqrt Q ≤ A * c := (div_le_iff₀ hc).mp hA
  have hmul : A / Real.sqrt Q * c = A * c / Real.sqrt Q := by field_simp
  have h1c : 1 / c ≤ A / Real.sqrt Q := by
    rw [div_le_iff₀ hc, hmul]
    exact (le_div_iff₀ hspos).mpr (by simpa using hAc)
  obtain ⟨δ, hδ0, hδc, hδB⟩ :=
    parabolicScalarModel_unbounded (B := max C 0 + 1) hQ hc
      (by have h : (0 : Real) ≤ max C 0 := le_max_right C 0; linarith)
  have hδlt : δ < A / Real.sqrt Q := by
    have hlt : δ < 1 / c := by
      rw [lt_div_iff₀ hc]
      linarith
    linarith
  exact absurd (hC δ hδ0 hδlt)
    (not_le.2 (lt_of_le_of_lt (le_trans (le_max_left C 0) (by linarith)) hδB))

end Sharpness

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
