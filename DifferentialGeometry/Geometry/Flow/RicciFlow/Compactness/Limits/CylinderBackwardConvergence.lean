import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.CylinderReset
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Cylindrical
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

private theorem exists_nat_mul_bounds_of_pos {h a b : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a + 2 * h ≤ b) :
    ∃ N : ℕ, 0 < N ∧ a ≤ (N : ℝ) * h ∧ ((N : ℝ) + 1) * h < b := by
  refine ⟨⌈a / h⌉₊, Nat.ceil_pos.mpr (div_pos ha hh), ?_, ?_⟩
  · exact (div_le_iff₀ hh).mp (Nat.le_ceil (a / h))
  · have hc := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg ha.le hh.le)) hh
    have hcancel : a / h * h = a := div_mul_cancel₀ a hh.ne'
    nlinarith

private theorem exists_nat_mul_step_bounds_of_lt (C : ℝ≥0) {L T : ℝ}
    (hL : 0 < L) (hLT : L < T) :
    ∃ C' : ℝ≥0, C ≤ C' ∧
      let h : ℝ := (12 * ((C' : ℝ) + 1))⁻¹ / 2
      ∃ N : ℕ, 0 < N ∧ L ≤ (N : ℝ) * h ∧ ((N : ℝ) + 1) * h < T ∧
        ∀ n : ℕ, n < N → -T ≤ -((n : ℝ) * h) - 2 * h := by
  have hgap : 0 < T - L := sub_pos.mpr hLT
  let C' : ℝ≥0 := C + ⟨(T - L)⁻¹, (inv_pos.mpr hgap).le⟩
  have hCC' : C ≤ C' := le_add_of_nonneg_right zero_le
  have hC' : (T - L)⁻¹ ≤ (C' : ℝ) := by
    change (T - L)⁻¹ ≤ (C : ℝ) + (T - L)⁻¹
    exact le_add_of_nonneg_left C.coe_nonneg
  let h : ℝ := (12 * ((C' : ℝ) + 1))⁻¹ / 2
  have hh : 0 < h := by dsimp only [h]; positivity
  have hwidth : 2 * h ≤ T - L := by
    have hi : (12 * ((C' : ℝ) + 1))⁻¹ ≤ ((T - L)⁻¹)⁻¹ :=
      inv_anti₀ (inv_pos.mpr hgap) (by nlinarith [C'.coe_nonneg])
    simp only [inv_inv] at hi
    dsimp only [h]
    linarith
  obtain ⟨N, hN, hlower, hupper⟩ :=
    exists_nat_mul_bounds_of_pos hh hL (show L + 2 * h ≤ T by linarith)
  refine ⟨C', hCC', N, hN, hlower, hupper, ?_⟩
  intro n hn
  have hn' : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have hmul := mul_le_mul_of_nonneg_right hn' hh.le
  change -T ≤ -((n : ℝ) * h) - 2 * h
  nlinarith

private theorem cylinder_reset_bounds_on_subinterval
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {T : ℝ} (hslab : Icc (-T) 0 ⊆ D.carrier) (hreg : Ioo (-T) 0 ⊆ D.regular)
    (C : ℝ≥0) (q Q : ℕ → ℝ) (hq : ∀ᶠ i in atTop, q i ≤ 1)
    (hQ : Tendsto Q atTop atTop)
    (hderiv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q i < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
          C * (S n i).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ i in atTop, PhiAlmostNonnegative (S n i)
      (Icc (-T) 0) (rescalePinchingFunction (Q i) Phi))
    {h : ℝ} (he : (12 * ((C : ℝ) + 1))⁻¹ = 2 * h)
    (rho : ℕ → ℕ) (hrho : StrictMono rho) (b : ℝ) (hb : b ≤ 0)
    (hbT : -T ≤ b - 2 * h)
    (hc : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → MetricCPConvergenceOn K 2
      (fun i => (S n (rho i)).base.metric b)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) b).restrictOpen
        (neckBuffer (δ n))) (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))) :
    ∀ n,
      (∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
        ∀ t ∈ Icc (b - 2 * h) b, ∀ x ∈ K,
          curvDerivNormSq 0 ((S n (rho i)).base.metric t) x ≤ (12 * Real.sqrt 3) ^ 2) ∧
      (∀ K : Set (neckBuffer (δ n)), IsCompact K → ∃ B : ℕ → ℝ, (∀ p, 0 ≤ B p) ∧
        ∀ᶠ i in atTop, ∀ p : ℕ, ∀ t ∈ Icc (b - h) b,
          ∀ x ∈ K, curvDerivNorm p ((S n (rho i)).base.metric t) x ≤ B p) := by
  intro n
  have ht : Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ Icc (-T) 0 := by
    rw [he]
    intro t ht
    exact ⟨hbT.trans ht.1, ht.2.trans hb⟩
  have htreg : Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ Ioo (-T) 0 := by
    rw [he]
    intro t ht
    exact ⟨hbT.trans_lt ht.1, ht.2.trans_le hb⟩
  have hd : ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b,
        q (rho i) < (S n (rho i)).scalar t x →
        |derivWithin (fun s => (S n (rho i)).scalar s x) (Iic t) t| ≤
          C * (S n (rho i)).scalar t x ^ 2 := by
    intro K hK
    exact (hrho.tendsto_atTop.eventually (hderiv n K hK)).mono
      fun i hi x hx t ht hq => hi x hx t (htreg ht) hq
  have hp : ∀ᶠ i in atTop, PhiAlmostNonnegative (S n (rho i))
      (Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b) (rescalePinchingFunction (Q (rho i)) Phi) :=
    (hrho.tendsto_atTop.eventually (hpinch n)).mono fun i hi t htt x => hi t (ht htt) x
  have hr := exists_curvature_derivative_bounds_before_time_of_cylinder_convergence
    (hδ n) hb (fun i => S n (rho i)) (fun i => hS n (rho i)) C
    (ht.trans hslab) (fun t hti => hreg (htreg hti))
    (hc n) (fun i => q (rho i)) (fun i => Q (rho i))
    (hrho.tendsto_atTop.eventually hq) (hQ.comp hrho.tendsto_atTop) hd hPhi hp
  simpa only [he, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hr

private theorem exists_subsequence_cylinder_convergence_on_finite_steps
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {T : ℝ} (hslab : Icc (-T) 0 ⊆ D.carrier) (hreg : Ioo (-T) 0 ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hcompat : ∀ n m t, t ∈ Icc (-T) 0 →
      (fun i => ((S n i).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
      (fun i => ((S m i).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    (C : ℝ≥0) (q Q : ℕ → ℝ) (hq : ∀ᶠ i in atTop, q i ≤ 1)
    (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hderiv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q i < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
          C * (S n i).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ i in atTop, PhiAlmostNonnegative (S n i)
      (Icc (-T) 0) (rescalePinchingFunction (Q i) Phi))
    {h : ℝ} (hh : h = (12 * ((C : ℝ) + 1))⁻¹ / 2)
    {N : ℕ} (hNpos : 0 < N) (hN : ((N : ℝ) + 1) * h ≤ T) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-(N : ℝ) * h) 0,
          metricDerivNormSupOn K p ((S n (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer (δ n)))
            (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η := by
  have hhpos : 0 < h := by rw [hh]; positivity
  have he : (12 * ((C : ℝ) + 1))⁻¹ = 2 * h := by rw [hh]; ring
  have hsource : 2 * h ≤ T := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    nlinarith
  let Conv := fun (rho : ℕ → ℕ) (a : ℝ) =>
    ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc a 0,
        metricDerivNormSupOn K p ((S n (rho i)).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
            (neckBuffer (δ n)))
          (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η
  let Curv := fun (rho : ℕ → ℕ) (a : ℝ) =>
    ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc a 0, ∀ x ∈ K, curvDerivNorm p ((S n (rho i)).base.metric t) x ≤ B
  let Bound := fun (rho : ℕ → ℕ) (a : ℝ) =>
    ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ t ∈ Icc a 0, ∀ x ∈ K,
        curvDerivNormSq 0 ((S n (rho i)).base.metric t) x ≤ (12 * Real.sqrt 3) ^ 2
  have hreset := cylinder_reset_bounds_on_subinterval hδ S hS hslab hreg C q Q hq hQ
    hderiv hPhi hpinch he
  have hind : ∀ k : ℕ, k ≤ N → ∃ rho : ℕ → ℕ, StrictMono rho ∧
      Conv rho (-(k : ℝ) * h) ∧ Curv rho (-(k : ℝ) * h) ∧ Bound rho (-(k : ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hc : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → MetricCPConvergenceOn K 2
          (fun i => (S n i).base.metric 0)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0).restrictOpen
            (neckBuffer (δ n))) (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) := by
        intro n K hK
        simpa only [PDE.RicciFlow.shrinkingCylinderMetric_zero,
          ← roundCylinderMetric_eq_geometry] using hterminal n K hK 2
      have hr := hreset id strictMono_id 0 le_rfl (by linarith) hc
      refine ⟨id, strictMono_id, ?_, ?_, ?_⟩
      · intro n K hK p η hη
        obtain ⟨j, hj⟩ := hterminal n K hK p η hη
        refine ⟨j, fun i hi t ht => ?_⟩
        have ht0 : t = 0 := by simpa using ht
        subst t
        simpa only [PDE.RicciFlow.shrinkingCylinderMetric_zero,
          ← roundCylinderMetric_eq_geometry, id_eq] using hj i hi
      · intro n K hK p
        obtain ⟨B, hB, hbound⟩ := (hr n).2 K hK
        refine ⟨B p, hB p, hbound.mono ?_⟩
        intro i hi t ht x hx
        have ht0 : t = 0 := by simpa using ht
        subst t
        exact hi p 0 ⟨by linarith, le_rfl⟩ x hx
      · intro n K hK
        apply ((hr n).1 K hK).mono
        intro i hi t ht x hx
        have ht0 : t = 0 := by simpa using ht
        subst t
        exact hi 0 ⟨by linarith, le_rfl⟩ x hx
    | succ k ih =>
      intro hk
      obtain ⟨rho, hrho, hconv, hcurv, hbound⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hkreal : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hb : -(k : ℝ) * h ≤ 0 := by nlinarith
      have hbT : -T ≤ -(k : ℝ) * h - 2 * h := by nlinarith
      have hc : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → MetricCPConvergenceOn K 2
          (fun i => (S n (rho i)).base.metric (-(k : ℝ) * h))
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) (-(k : ℝ) * h)).restrictOpen
            (neckBuffer (δ n))) (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) := by
        intro n K hK η hη
        obtain ⟨j, hj⟩ := hconv n K hK 2 η hη
        exact ⟨j, fun i hi => hj i hi _ ⟨le_rfl, hb⟩⟩
      have hr := hreset rho hrho _ hb hbT hc
      have hnew : -(k + 1 : ℝ) * h < 0 := by nlinarith
      have hnewT : -T < -(k + 1 : ℝ) * h := by nlinarith
      have hcurv' : Curv rho (-(k + 1 : ℝ) * h) := by
        intro n K hK p
        obtain ⟨B, hB, hBbound⟩ := (hr n).2 K hK
        obtain ⟨A, hA, hAbound⟩ := hcurv n K hK p
        refine ⟨max A (B p), le_max_of_le_left hA, ?_⟩
        filter_upwards [hAbound, hBbound] with i hiA hiB t ht x hx
        by_cases htk : t ≤ -(k : ℝ) * h
        · exact (hiB p t ⟨by linarith [ht.1], htk⟩ x hx).trans (le_max_right _ _)
        · exact (hiA t ⟨(lt_of_not_ge htk).le, ht.2⟩ x hx).trans (le_max_left _ _)
      have hbound' : Bound rho (-(k + 1 : ℝ) * h) := by
        intro n K hK
        filter_upwards [hbound n K hK, (hr n).1 K hK] with i hiA hiB t ht x hx
        by_cases htk : t ≤ -(k : ℝ) * h
        · exact hiB t ⟨by linarith [ht.1], htk⟩ x hx
        · exact hiA t ⟨(lt_of_not_ge htk).le, ht.2⟩ x hx
      have hcompat' : ∀ n m t, t ∈ Icc (-(k + 1 : ℝ) * h) 0 →
          (fun i => ((S n (rho (i - 0))).base.metric t).restrictOpenOfSubset
            (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
          (fun i => ((S m (rho (i - 0))).base.metric t).restrictOpenOfSubset
            (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))) := by
        intro n m t ht
        filter_upwards [hrho.tendsto_atTop.eventually
          (hcompat n m t ⟨hnewT.le.trans ht.1, ht.2⟩)] with i hi
        exact hi
      have hpinch' : ∀ n, ∀ t ∈ Icc (-(k + 1 : ℝ) * h) 0, ∀ᶠ i in atTop,
          ∀ x : neckBuffer (δ n), curvatureOperatorLowerBoundAt ((S n (rho i)).base.metric t) x
            (metricAlgebraicCurvatureTensorAt ((S n (rho i)).base.metric t) x)
            (rescalePinchingFunction (Q (rho (i + 0))) Phi
              (metricScalarAt ((S n (rho i)).base.metric t) x)) := by
        intro n t ht
        exact (hrho.tendsto_atTop.eventually (hpinch n)).mono
          fun i hi x => hi t ⟨hnewT.le.trans ht.1, ht.2⟩ x
      have hbound'' : ∀ n, ∀ t ∈ Icc (-(k + 1 : ℝ) * h) 0,
          ∀ x : neckBuffer (δ n), ∀ᶠ i in atTop,
            normSq0S ((S n (rho i)).base.metric t) x 4
              (metricRm04At ((S n (rho i)).base.metric t) x) ≤ (12 * Real.sqrt 3) ^ 2 := by
        intro n t ht x
        exact (hbound' n {x} isCompact_singleton).mono
          fun i hi => hi t ht x (mem_singleton x)
      obtain ⟨psi, hpsi, hpsiConv⟩ :=
        exists_subsequence_converges_to_shrinkingCylinder_of_neck_terminal_convergence
          hδ hδlim (fun n i => S n (rho i)) (fun n i => hS n (rho i)) hnew
          (fun t ht => hslab ⟨hnewT.le.trans ht.1, ht.2⟩)
          (fun t ht => hreg ⟨hnewT.trans_le ht.1, ht.2⟩)
          (fun n => (hterminal n).comp_subseq hrho) hcurv' (fun _ => 0) hcompat'
          hPhi (fun i => Q (rho i)) (fun i => hQpos (rho i))
          (hQ.comp hrho.tendsto_atTop) hpinch' hbound''
      refine ⟨rho ∘ psi, hrho.comp hpsi, ?_, ?_, ?_⟩
      · dsimp only [Conv]
        simpa only [Nat.cast_succ, Nat.sub_zero, Function.comp_apply] using hpsiConv
      · intro n K hK p
        obtain ⟨B, hB, hBb⟩ := hcurv' n K hK p
        refine ⟨B, hB, ?_⟩
        simpa only [Nat.cast_succ, Function.comp_apply] using hpsi.tendsto_atTop.eventually hBb
      · intro n K hK
        simpa only [Nat.cast_succ, Function.comp_apply] using
          hpsi.tendsto_atTop.eventually (hbound' n K hK)
  obtain ⟨rho, hrho, hconv, _, _⟩ := hind N le_rfl
  exact ⟨rho, hrho, hconv⟩

private theorem exists_subsequence_cylinder_convergence_on_subinterval_of_aligned_sources
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {L T : ℝ} (hL : 0 < L) (hLT : L < T)
    (hslab : Icc (-T) 0 ⊆ D.carrier) (hreg : Ioo (-T) 0 ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hcompat : ∀ n m t, t ∈ Icc (-T) 0 →
      (fun i => ((S n i).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
      (fun i => ((S m i).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    (C : ℝ≥0) (q Q : ℕ → ℝ) (hq : ∀ᶠ i in atTop, q i ≤ 1)
    (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hderiv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q i < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
          C * (S n i).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ i in atTop, PhiAlmostNonnegative (S n i)
      (Icc (-T) 0) (rescalePinchingFunction (Q i) Phi)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-L) 0,
          metricDerivNormSupOn K p ((S n (rho i)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer (δ n)))
            (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η := by
  obtain ⟨C', hCC', N, hNpos, hNL, hNT, _⟩ := exists_nat_mul_step_bounds_of_lt C hL hLT
  let h : ℝ := (12 * ((C' : ℝ) + 1))⁻¹ / 2
  have hderiv' : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q i < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
          C' * (S n i).scalar t x ^ 2 := by
    intro n K hK
    apply (hderiv n K hK).mono
    intro i hi x hx t ht hqi
    exact (hi x hx t ht hqi).trans
      (mul_le_mul_of_nonneg_right (show (C : ℝ) ≤ C' from hCC') (sq_nonneg _))
  obtain ⟨rho, hrho, hconv⟩ := exists_subsequence_cylinder_convergence_on_finite_steps
    hδ hδlim S hS hslab hreg hterminal hcompat C' q Q hq hQpos hQ hderiv' hPhi hpinch
    (h := h) rfl hNpos hNT.le
  refine ⟨rho, hrho, ?_⟩
  intro n K hK p η hη
  obtain ⟨j, hj⟩ := hconv n K hK p η hη
  refine ⟨j, fun i hi t ht => hj i hi t ⟨?_, ht.2⟩⟩
  change -(N : ℝ) * h ≤ t
  change L ≤ (N : ℝ) * h at hNL
  linarith [ht.1]

theorem exists_subsequence_converges_to_shrinkingCylinder_on_subinterval_of_scalar_deriv_bound
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {L T : ℝ} (hL : 0 < L) (hLT : L < T)
    (hslab : Icc (-T) 0 ⊆ D.carrier) (hreg : Ioo (-T) 0 ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc (-T) 0 →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    (C : ℝ≥0) (q Q : ℕ → ℝ) (hq : ∀ᶠ i in atTop, q i ≤ 1)
    (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hderiv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q (i + N n) < (S n i).scalar t x →
        |derivWithin (fun s => (S n i).scalar s x) (Iic t) t| ≤
          C * (S n i).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n, ∀ᶠ i in atTop, PhiAlmostNonnegative (S n i)
      (Icc (-T) 0) (rescalePinchingFunction (Q (i + N n)) Phi)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (-L) 0,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
              (neckBuffer (δ n)))
            (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η := by
  let S' := fun n i => S n (i - N n)
  have hterminal' : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S' n i).base.metric 0)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) := by
    intro n K hK p η hη
    obtain ⟨j, hj⟩ := hterminal n K hK p η hη
    exact ⟨j + N n, fun i hi => hj (i - N n) (by omega)⟩
  have hderiv' : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ᶠ i in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (-T) 0,
        q i < (S' n i).scalar t x →
        |derivWithin (fun s => (S' n i).scalar s x) (Iic t) t| ≤
          C * (S' n i).scalar t x ^ 2 := by
    intro n K hK
    filter_upwards [(tendsto_sub_atTop_nat (N n)).eventually (hderiv n K hK),
      eventually_ge_atTop (N n)] with i hi hNi
    rwa [Nat.sub_add_cancel hNi] at hi
  have hpinch' : ∀ n, ∀ᶠ i in atTop, PhiAlmostNonnegative (S' n i)
      (Icc (-T) 0) (rescalePinchingFunction (Q i) Phi) := by
    intro n
    filter_upwards [(tendsto_sub_atTop_nat (N n)).eventually (hpinch n),
      eventually_ge_atTop (N n)] with i hi hNi
    rwa [Nat.sub_add_cancel hNi] at hi
  exact exists_subsequence_cylinder_convergence_on_subinterval_of_aligned_sources
    hδ hδlim S' (fun n i => hS n (i - N n)) hL hLT hslab hreg hterminal'
    hcompat C q Q hq hQpos hQ hderiv' hPhi hpinch'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
