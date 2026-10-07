import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegralGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.AdaptedCutoffTrace
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH

/-- The trace of the linear-cutoff index form along finitely many regularized
geodesic pieces. Matching scalar curvature and Lagrangian values cancel the
interior boundary terms; the final velocity is retained. -/
theorem sum_lRegularizedIndex_trace_linear_cutoff_eq_energy
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (s : Fin (n + 2) → ℝ) (hs : Monotone s) (ha : 0 < s 0)
    (hav : s 0 < s (Fin.last (n + 1)))
    (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) →
      ∀ t, TangentSpace I (alpha i t))
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i)
      (Ioo (s i.castSucc) (s i.succ)))
    (hLag : ∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (alpha i))
      (Icc (s i.castSucc) (s i.succ)))
    (hHam : ∀ i, IntervalIntegrable (lHamSq (S i) T (alpha i)) volume
      (s i.castSucc) (s i.succ))
    (hreg : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ), T - t ^ 2 ∈ (D i).regular)
    (halpha : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (alpha i) t)
    (hP : ∀ i k t, t ∈ Icc (s i.castSucc) (s i.succ) →
      DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (P i k) t) t)
    (hDP : ∀ i k, IsLAdapted (S i) T (alpha i) (P i k)
      (Icc (s i.castSucc) (s i.succ)))
    (hON : ∀ i k l,
      ((S i).base.metric (T - (s i.succ) ^ 2)).inner (alpha i (s i.succ))
        (P i k (s i.succ)) (P i l (s i.succ)) = if k = l then 1 else 0)
    (hindexInt : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand (S i) T (alpha i)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t))
      volume (s i.castSucc) (s i.succ))
    (hscalar : ∀ i : Fin n,
      (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
          (alpha i.castSucc (s i.castSucc.succ)) =
        (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
          (alpha i.succ (s i.succ.castSucc)))
    (hlag : ∀ i : Fin n,
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (s i.castSucc.succ) =
        lRegularizedLagrangian (S i.succ) T (alpha i.succ) (s i.succ.castSucc)) :
    let a := s 0;
    let v := s (Fin.last (n + 1));
    2 * (∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
      lRegularizedIndex (S i) T (alpha i)
        (fun t => ((t - a) / (v - a)) • P i k t)
        (fun t => ((t - a) / (v - a)) • P i k t)
        (s i.castSucc) (s i.succ)) =
      (Module.finrank ℝ E : ℝ) / (v - a) -
        v * (S (Fin.last n)).scalar (T - v ^ 2) (alpha (Fin.last n) v) -
        (∑ i : Fin (n + 1), ∫ t in (s i.castSucc)..(s i.succ),
          (1 - a ^ 2 / t ^ 2) * lRegularizedLagrangian (S i) T (alpha i) t) /
            (2 * (v - a) ^ 2) +
        ((S (Fin.last n)).base.metric (T - v ^ 2)).inner (alpha (Fin.last n) v)
          (lVelocity (I := I) (alpha (Fin.last n)) v)
          (lVelocity (I := I) (alpha (Fin.last n)) v) / (4 * v) := by
  classical
  let a := s 0
  let v := s (Fin.last (n + 1))
  let delta := v - a
  let chi : ℝ → ℝ := fun t => (t - a) / delta
  let L (i : Fin (n + 1)) := lRegularizedLagrangian (S i) T (alpha i)
  let R (i : Fin (n + 1)) (t : ℝ) := (S i).scalar (T - t ^ 2) (alpha i t)
  let J (i : Fin (n + 1)) := ∑ k : Fin (Module.finrank ℝ E),
    lRegularizedIndex (S i) T (alpha i) (fun t => chi t • P i k t)
      (fun t => chi t • P i k t) (s i.castSucc) (s i.succ)
  let A (i : Fin (n + 1)) := ∫ t in (s i.castSucc)..(s i.succ),
    (1 - a ^ 2 / t ^ 2) * L i t
  let Q (i : Fin (n + 1)) (t : ℝ) := t * (t - a) ^ 2 * R i t
  let F (i : Fin (n + 1)) (t : ℝ) := ((t - a) ^ 2 / t) * L i t
  have hd : 0 < delta := sub_pos.mpr hav
  have hv : 0 < v := ha.trans hav
  have hleft (i : Fin (n + 1)) : a ≤ s i.castSucc := hs (Fin.zero_le _)
  have hordered (i : Fin (n + 1)) : s i.castSucc ≤ s i.succ :=
    hs i.castSucc_le_succ
  have hpos (i : Fin (n + 1)) : 0 < s i.castSucc := ha.trans_le (hleft i)
  have hpiece (i : Fin (n + 1)) :
      4 * delta ^ 2 * J i =
        2 * (Module.finrank ℝ E : ℝ) * (s i.succ - s i.castSucc) -
          4 * (Q i (s i.succ) - Q i (s i.castSucc)) - A i +
          (F i (s i.succ) - F i (s i.castSucc)) := by
    have hnonzero (t : ℝ) (ht : t ∈ Icc (s i.castSucc) (s i.succ)) : t ≠ 0 :=
      ((hpos i).trans_le ht.1).ne'
    have hweight : ContinuousOn (fun t => (chi t / t) ^ 2)
        (uIcc (s i.castSucc) (s i.succ)) := by
      rw [uIcc_of_le (hordered i)]
      exact (((continuousOn_id.sub continuousOn_const).div_const delta).div
        continuousOn_id hnonzero).pow 2
    have hHamChi := (hHam i).continuousOn_mul hweight
    have hchi (t : ℝ) (_ht : t ∈ Icc (s i.castSucc) (s i.succ)) :
        HasDerivAt chi (1 / delta) t :=
      ((hasDerivAt_id t).sub_const a).div_const delta
    have htrace := lRegularizedIndex_trace_smul_function (S i) (hS i) T (alpha i)
      (P i) chi (fun _ => 1 / delta) (s i.castSucc) (s i.succ) (hpos i) (hordered i)
      hchi (hreg i) (halpha i) (hP i) (hDP i) (hON i) (hindexInt i)
      intervalIntegrable_const hHamChi
    have hHamEq :
        (∫ t in (s i.castSucc)..(s i.succ), (chi t / t) ^ 2 * lHamSq (S i) T (alpha i) t) =
          (∫ t in (s i.castSucc)..(s i.succ),
            ((t - a) / t) ^ 2 * lHamSq (S i) T (alpha i) t) / delta ^ 2 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 := hnonzero t (by simpa only [uIcc_of_le (hordered i)] using ht)
      dsimp only [chi]
      field_simp [hd.ne', ht0]
    have ht : 4 * delta ^ 2 * J i =
        2 * (Module.finrank ℝ E : ℝ) * (s i.succ - s i.castSucc) -
          4 * (Q i (s i.succ) - Q i (s i.castSucc)) -
          4 * (∫ t in (s i.castSucc)..(s i.succ),
            ((t - a) / t) ^ 2 * lHamSq (S i) T (alpha i) t) := by
      change J i = _ at htrace
      rw [htrace, hHamEq, intervalIntegral.integral_const]
      dsimp only [Q, R, chi]
      simp only [smul_eq_mul]
      field_simp [hd.ne']
      ring
    have he := integral_lHamSq_mul_eq_of_geodesic (S i) (hS i) T (alpha i) (a := a)
      (ha.trans_le (hleft i)) (hordered i) (hgeo i) (hLag i) (hHam i)
    change 4 * (∫ t in (s i.castSucc)..(s i.succ),
      ((t - a) / t) ^ 2 * lHamSq (S i) T (alpha i) t) =
        A i - (F i (s i.succ) - F i (s i.castSucc)) at he
    linarith
  have telescope (f g : Fin (n + 1) → ℝ)
      (hmatch : ∀ i : Fin n, f i.castSucc = g i.succ) :
      (∑ i : Fin (n + 1), (f i - g i)) = f (Fin.last n) - g 0 := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc f, Fin.sum_univ_succ g]
    have hmid : (∑ i : Fin n, f i.castSucc) = ∑ i : Fin n, g i.succ :=
      Finset.sum_congr rfl (fun i _ => hmatch i)
    rw [hmid]
    ring
  have ht : (∑ i : Fin (n + 1), (s i.succ - s i.castSucc)) = delta := by
    exact telescope (fun i => s i.succ) (fun i => s i.castSucc) (fun _ => rfl)
  have hQ : (∑ i : Fin (n + 1), (Q i (s i.succ) - Q i (s i.castSucc))) =
      v * delta ^ 2 * R (Fin.last n) v := by
    have hh := telescope (fun i => Q i (s i.succ)) (fun i => Q i (s i.castSucc))
      (fun i => by dsimp only [Q, R]; rw [hscalar i]; simp only [Fin.castSucc_succ])
    simpa only [Q, a, v, delta, Fin.succ_last, Fin.castSucc_zero, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, sub_zero] using hh
  have hF : (∑ i : Fin (n + 1), (F i (s i.succ) - F i (s i.castSucc))) =
      (delta ^ 2 / v) * L (Fin.last n) v := by
    have hh := telescope (fun i => F i (s i.succ)) (fun i => F i (s i.castSucc))
      (fun i => by dsimp only [F, L]; rw [hlag i]; simp only [Fin.castSucc_succ])
    simpa only [F, a, v, delta, Fin.succ_last, Fin.castSucc_zero, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_mul, sub_zero] using hh
  have hsum := congrArg (fun f : Fin (n + 1) → ℝ => ∑ i, f i) (funext hpiece)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib] at ht hQ hF
  rw [ht, hQ, hF] at hsum
  let speedSq := ((S (Fin.last n)).base.metric (T - v ^ 2)).inner
    (alpha (Fin.last n) v) (lVelocity (I := I) (alpha (Fin.last n)) v)
      (lVelocity (I := I) (alpha (Fin.last n)) v)
  have hLv : L (Fin.last n) v =
      (1 / 2 : ℝ) * speedSq + 2 * v ^ 2 * R (Fin.last n) v := by
    rfl
  rw [hLv] at hsum
  have hden : (2 : ℝ) * delta ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hd.ne')
  change 2 * (∑ i : Fin (n + 1), J i) =
    (Module.finrank ℝ E : ℝ) / delta - v * R (Fin.last n) v -
      (∑ i : Fin (n + 1), A i) / (2 * delta ^ 2) + speedSq / (4 * v)
  calc
    2 * (∑ i : Fin (n + 1), J i) =
        (2 * (Module.finrank ℝ E : ℝ) * delta -
          4 * (v * delta ^ 2 * R (Fin.last n) v) -
          (∑ i : Fin (n + 1), A i) +
          (delta ^ 2 / v) * ((1 / 2 : ℝ) * speedSq +
            2 * v ^ 2 * R (Fin.last n) v)) / (2 * delta ^ 2) := by
      apply (eq_div_iff hden).2
      calc
        (2 * (∑ i : Fin (n + 1), J i)) * (2 * delta ^ 2) =
            4 * delta ^ 2 * (∑ i : Fin (n + 1), J i) := by ring
        _ = _ := hsum
    _ = _ := by
      field_simp [hd.ne', hv.ne'] <;> ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
