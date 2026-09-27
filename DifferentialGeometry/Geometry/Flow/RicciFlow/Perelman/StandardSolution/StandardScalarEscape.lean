import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMaximalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarBlowup
import DifferentialGeometry.Analysis.Asymptotics.RadiusEscape

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_standard_terminal_radius_escape
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    {tau : ℝ} (htau : 0 < tau)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    {A : ℝ} (hbase : ∀ i, metricScalarAt ((S i).metric (time i)) (point i) ≤ A)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ C : ℝ,
      ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) y ≤ C) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), 0 < R ∧ StrictMono ind ∧
      (∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ,
        ∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
          metricScalarAt ((S i).metric (time i)) y ≤ C) ∧
      ∃ y : ℕ → E3,
        Tendsto (fun i => (riemannianEDistOf ((S (ind i)).metric (time (ind i)))
          (point (ind i)) (y i)).toReal) atTop (𝓝 R) ∧
        Tendsto (fun i => metricScalarAt ((S (ind i)).metric (time (ind i))) (y i)) atTop atTop := by
  obtain ⟨r₀, B, hr₀, _, hbound⟩ := exists_standard_scalar_bound_on_ball_of_scalar_le htau A
  obtain ⟨R, ind, hR, hind, hinner, y, _, hdist, hblow⟩ :=
    DifferentialGeometry.Analysis.exists_subsequence_radius_escape
      (fun i => riemannianEDistOf ((S i).metric (time i)) (point i))
      (fun i => metricScalarAt ((S i).metric (time i))) hr₀
      ⟨B, Eventually.of_forall fun i y hy =>
        hbound (S i) (time i) (htime i).1 (htime i).2.1 (htime i).2.2
          (point i) (hbase i) y hy.le⟩ hfail
  refine ⟨R, ind, hr₀.trans_le hR, hind, ?_, y, hdist, hblow⟩
  intro r hr hrR
  obtain ⟨C, hC⟩ := hinner ((r + R) / 2) (by linarith)
  refine ⟨C, hC.mono fun i hi y hy => hi y ?_⟩
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < (r + R) / 2)).mpr
    (by linarith))

theorem standard_scalar_limit_tendsto_atTop_of_endpoint_blowup
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ)
    {tau : ℝ} (htau : 0 < tau)
    (htime : ∀ᶠ i in atTop, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (rho : ℝ) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ℕ → ℝ → E3)
    (hendpoint : Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (γ i (ell i)))
      atTop atTop)
    (hdist : ∀ s : Ico 0 rho, ∀ᶠ i in atTop,
      riemannianEDistOf ((S i).metric (time i)) (γ i s) (γ i (ell i)) ≤
        ENNReal.ofReal (ell i - s))
    (R : Ico 0 rho → ℝ)
    (hscalar : ∀ s : Ico 0 rho,
      Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (γ i s)) atTop (𝓝 (R s))) :
    Tendsto R (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨r, C, hr, _, hbound⟩ :=
    exists_standard_scalar_bound_on_ball_of_scalar_le htau (B + 1)
  have hgap : Tendsto (fun s : Ico 0 rho => rho - (s : ℝ))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := rho)).sub
      (tendsto_comap : Tendsto (Subtype.val : Ico 0 rho → ℝ) _ (𝓝 rho))
  filter_upwards [hgap.eventually (Iio_mem_nhds hr)] with s hs
  by_contra hnot
  have hlow : R s < B + 1 := (lt_of_not_ge hnot).trans (lt_add_one B)
  have hcenter := (hscalar s).eventually_lt_const hlow
  have hremain := (hell.sub_const (s : ℝ)).eventually_lt_const hs
  have hhigh := hendpoint.eventually_gt_atTop C
  obtain ⟨i, hti, hdi, hci, hri, hhi⟩ :=
    (htime.and ((hdist s).and (hcenter.and (hremain.and hhigh)))).exists
  have hball : γ i (ell i) ∈ riemannianClosedBallOf ((S i).metric (time i)) (γ i s) r :=
    hdi.trans (ENNReal.ofReal_le_ofReal hri.le)
  exact hhi.not_ge (hbound (S i) (time i) hti.1 hti.2.1 hti.2.2 (γ i s) hci.le
    (γ i (ell i)) hball)

theorem standard_scalar_time_tendsto_one_of_scalar_tendsto_atTop
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ time i < 1)
    (hscalar : Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (point i)) atTop atTop) :
    Tendsto time atTop (𝓝 1) := by
  choose U hU using fun i => (S i).exists_maximal_extension
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall fun i => ha0.trans_le
        ((mem_lifetimeInterval_carrier (S i).lifetime (S i).lifetime_pos _).mp (htime i).1).1
    have hapos : 0 ≤ a := le_of_not_gt ha0
    obtain ⟨K, _hK, hcurv⟩ := (uniformStandardLifetime_slab a hapos
      (by rw [uniformStandardLifetime_eq_one]; exact ENNReal.ofReal_lt_one.mpr ha)).2
    filter_upwards [hscalar.eventually_gt_atTop (9 * K)] with i hi
    by_contra hnot
    have hia : time i ≤ a := le_of_not_gt hnot
    have hi0 := ((mem_lifetimeInterval_carrier (S i).lifetime (S i).lifetime_pos _).mp (htime i).1).1
    have hm := (hU i).2 (time i) (htime i).1
    have hrm := hcurv (U i) (time i) ⟨hi0, hia⟩ (point i)
    rw [hm] at hrm
    have hsc := scalar_abs_le_rm ((S i).metric (time i)) (point i)
    change |metricScalarAt ((S i).metric (time i)) (point i)| ≤
      (Module.finrank ℝ E3 : ℝ) ^ 2 * _ at hsc
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hsc
    have hb := (le_abs_self _).trans (hsc.trans
      (mul_le_mul_of_nonneg_left hrm (by norm_num)))
    exact (not_lt_of_ge hb) hi
  · intro a ha
    exact Eventually.of_forall fun i => (htime i).2.trans ha

end DifferentialGeometry.PDE.RicciFlow
