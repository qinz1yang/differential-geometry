import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSegmentNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_strongNeck_of_long_minimizing_segment (kappa : ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ i : ℕ, ∀ t ∈ Icc (-X.depth i) 0,
          ∀ (γ : ℝ → (X.term i).M) (a b tau : ℝ),
            (∀ s ∈ Icc a b, ∀ r ∈ Icc a b,
              metricDistance ((X.term i).S.base.metric t) (γ s) (γ r) = |s - r|) →
            2 ≤ (X.term i).S.scalar t (γ tau) →
            A ≤ Real.sqrt ((X.term i).S.scalar t (γ tau)) * (tau - a) →
            A ≤ Real.sqrt ((X.term i).S.scalar t (γ tau)) * (b - tau) →
            Nonempty (StrongNeck (X.term i).S (2 * alpha) (γ tau) t) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_windowed_strongNeck_of_minimizing_segment.{u} kappa ha hsmall
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro eps sigma Phi X heps i t ht γ a b tau hsegment hQ hleft hright
  obtain ⟨W, o, _⟩ := X.higher_good i t ht (γ tau) hQ
  let Q := (X.term i).S.scalar t (γ tau)
  have hQpos : 0 < Q := W.scalar_pos
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hreg : ∀ s ∈ Ioo (-modelDepth eps) 0,
      parabolicTime t Q s ∈ (X.interval i).regular := by
    intro s hs
    have hstart := W.window_mem (left_mem_Icc.mpr
      (sub_le_self t (inv_nonneg.mpr (mul_nonneg W.eps_pos.le hQpos.le))))
    rw [X.carrier_eq i] at hstart
    rw [X.regular_eq i]
    have hdivide : -(eps * Q)⁻¹ < s / Q := by
      have hh := (div_lt_div_iff_of_pos_right hQpos).mpr hs.1
      simpa only [modelDepth, neg_div, div_eq_mul_inv, mul_inv_rev, mul_comm, neg_mul] using hh
    exact ⟨by dsimp only [parabolicTime]; linarith [hstart.1],
      by dsimp only [parabolicTime]; linarith [div_neg_of_neg_of_pos hs.2 hQpos, ht.2]⟩
  apply hneck (X.term i).M (X.interval i) (X.term i).S (X.term i).isSolution
    eps (γ tau) t W heps hreg ⟨o⟩ (fun s => γ (tau + s / Real.sqrt Q)) (by simp)
  have hmem (s : ℝ) (hs : s ∈ Icc (-A) A) : tau + s / Real.sqrt Q ∈ Icc a b := by
    have hlow : -(tau - a) ≤ s / Real.sqrt Q := by
      apply (le_div_iff₀ hsqrt).mpr
      nlinarith [hs.1]
    have hhigh : s / Real.sqrt Q ≤ b - tau := by
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith [hs.2]
    exact ⟨by linarith, by linarith⟩
  intro s hs r hr
  let _ : ConnectedSpace (X.term i).M := X.connected i
  have hd : riemannianEDistOf ((X.term i).S.base.metric t)
      (γ (tau + s / Real.sqrt Q)) (γ (tau + r / Real.sqrt Q)) =
      ENNReal.ofReal |(tau + s / Real.sqrt Q) - (tau + r / Real.sqrt Q)| := by
    rw [← hsegment _ (hmem s hs) _ (hmem r hr)]
    exact (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)).symm
  simp only [rescaledMetric, parabolicTime_zero]
  rw [edistOf_scale, hd, ← ENNReal.ofReal_mul hsqrt.le]
  congr 1
  have hdiff : tau + s / Real.sqrt Q - (tau + r / Real.sqrt Q) =
      (s - r) / Real.sqrt Q := by ring
  rw [hdiff, abs_div, abs_of_pos hsqrt]
  field_simp

theorem exists_eventually_strongNeck_of_minimizing_segment_limits (kappa : ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ (f : ℕ → ℕ) (γ : ∀ n, ℝ → (X.term (f n)).M)
          (ell : ℕ → ℝ) (rho tau R : ℝ),
          Tendsto ell atTop (𝓝 rho) → 0 < tau → tau < rho → 2 < R →
          (∀ n, ∀ s ∈ Icc 0 (ell n), ∀ r ∈ Icc 0 (ell n),
            metricDistance ((X.term (f n)).S.base.metric 0) (γ n s) (γ n r) = |s - r|) →
          Tendsto (fun n => (X.term (f n)).S.scalar 0 (γ n tau)) atTop (𝓝 R) →
          A ^ 2 < R * tau ^ 2 → A ^ 2 < R * (rho - tau) ^ 2 →
          ∀ᶠ n in atTop, Nonempty (StrongNeck (X.term (f n)).S (2 * alpha) (γ n tau) 0) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_strongNeck_of_long_minimizing_segment.{u} kappa ha hsmall
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro eps sigma Phi X heps f γ ell rho tau R hell htau htr hR hsegment hscalar hleft hright
  have hRpos : 0 < R := by linarith
  have hroot := Real.sqrt_pos.mpr hRpos
  have hleft' : A < Real.sqrt R * tau := by
    nlinarith [Real.sq_sqrt hRpos.le, mul_pos hroot htau]
  have hright' : A < Real.sqrt R * (rho - tau) := by
    nlinarith [Real.sq_sqrt hRpos.le, mul_pos hroot (sub_pos.mpr htr)]
  have hsqrt := (Real.continuous_sqrt.tendsto R).comp hscalar
  have hleft_lim := hsqrt.mul_const tau
  have hright_lim := hsqrt.mul (hell.sub_const tau)
  filter_upwards [hscalar.eventually (eventually_gt_nhds hR),
    hleft_lim.eventually (eventually_gt_nhds hleft'),
    hright_lim.eventually (eventually_gt_nhds hright')] with n hn hl hr
  apply hneck eps sigma Phi X heps (f n) 0
    ⟨by linarith [X.depth_pos (f n)], le_rfl⟩ (γ n) 0 (ell n) tau
    (hsegment n) hn.le
  · simpa only [sub_zero, Function.comp_def] using hl.le
  · exact hr.le

theorem exists_eventually_strongNeck_near_scalar_blowup_endpoint (kappa : ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ (f : ℕ → ℕ) (γ : ∀ n, ℝ → (X.term (f n)).M)
          (ell : ℕ → ℝ) (rho : ℝ), 0 < rho → Tendsto ell atTop (𝓝 rho) →
          ∀ R : Ico 0 rho → ℝ,
            (∀ n, ∀ s ∈ Icc 0 (ell n), ∀ r ∈ Icc 0 (ell n),
              metricDistance ((X.term (f n)).S.base.metric 0) (γ n s) (γ n r) = |s - r|) →
            (∀ tau : Ico 0 rho,
              Tendsto (fun n => (X.term (f n)).S.scalar 0 (γ n tau)) atTop (𝓝 (R tau))) →
            Tendsto R (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop →
            (∀ tau : Ico 0 rho, 2 < R tau → A ^ 2 ≤ R tau * (rho - tau) ^ 2) →
            ∀ᶠ (tau : Ico 0 rho) in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
              ∀ᶠ n in atTop,
                Nonempty (StrongNeck (X.term (f n)).S (2 * alpha) (γ n tau) 0) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_eventually_strongNeck_of_minimizing_segment_limits.{u} kappa ha hsmall
  refine ⟨2 * A, epsStar, by positivity, hepsStar, ?_⟩
  intro eps sigma Phi X heps f γ ell rho hrho hell R hsegment hscalar hblow hquant
  have htime : Tendsto (Subtype.val : Ico 0 rho → ℝ)
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 rho) := tendsto_comap
  have hleft := hblow.atTop_mul_pos (sq_pos_of_pos hrho) (htime.pow 2)
  filter_upwards [htime.eventually (eventually_gt_nhds hrho),
    hblow.eventually (eventually_gt_atTop 2),
    hleft.eventually (eventually_gt_atTop (A ^ 2))] with tau ht hR hl
  have hr : A ^ 2 < R tau * (rho - tau) ^ 2 := by
    have hh := hquant tau hR
    nlinarith [sq_pos_of_pos hA]
  exact hneck eps sigma Phi X heps f γ ell rho tau (R tau) hell ht tau.property.2
    hR hsegment (hscalar tau) hl hr

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
