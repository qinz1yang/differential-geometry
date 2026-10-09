import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureEscape

noncomputable section

open Set Filter DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private exists_subsequence_radius_escape tendsto_radius_of_inner_bounds_of_escape from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureEscape

private theorem exists_closed_slice_scalar_escape_segments
    (P : ℕ → OrientedThreeStage.{u}) (g : ∀ n, (P n).Metric)
    (x : ∀ n, (P n).Carrier) (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hbase : ∀ n, metricScalarAt (g n) (x n) ≤ Q n)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hsmall : ∃ K : ℝ, ∀ᶠ n in atTop, ∀ z : (P n).Carrier,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (x n) z <
        ENNReal.ofReal r0 → metricScalarAt (g n) z ≤ K * Q n)
    (hfail : ∃ B : ℝ, 0 < B ∧ ¬ ∃ K : ℝ,
      ∀ᶠ n in atTop, ∀ z : (P n).Carrier,
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (x n) z <
          ENNReal.ofReal B → metricScalarAt (g n) z ≤ K * Q n) :
    ∃ (rho : ℝ) (ind : ℕ → ℕ), r0 ≤ rho ∧ StrictMono ind ∧
      (∀ R : ℝ, 0 < R → R < rho → ∃ K : ℝ, 4 ≤ K ∧
        ∀ᶠ n in atTop, ∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (hQ n) (g n)) (x n) R,
          metricScalarAt (g n) z ≤ K * Q n) ∧
      ∃ (A ell : ℕ → ℝ) (y : ∀ n, (P (ind n)).Carrier)
        (gamma : ∀ n, ℝ → (P (ind n)).Carrier),
        (∀ n, 2 ≤ A n) ∧ Tendsto A atTop atTop ∧
        Tendsto ell atTop (𝓝 rho) ∧ (∀ n, 0 < ell n) ∧
        (∀ n, metricScalarAt (g (ind n)) (y n) / Q (ind n) = A n) ∧
        (∀ n, riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (g (ind n)))
          (x (ind n)) (y n) = ENNReal.ofReal (ell n)) ∧
        (∀ n, gamma n 0 = x (ind n) ∧ gamma n (ell n) = y n) ∧
        (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (gamma n) (Icc 0 (ell n))) ∧
        (∀ n, ∀ t ∈ Ico 0 (ell n),
          metricScalarAt (g (ind n)) (gamma n t) / Q (ind n) < A n) ∧
        (∀ n, ∀ t ∈ Icc 0 (ell n),
          metricScalarAt (g (ind n)) (gamma n t) / Q (ind n) ≤ A n) ∧
        ∀ n, ∀ t ∈ Icc 0 (ell n), ∀ v ∈ Icc 0 (ell n),
          riemannianEDistOf
            (scaleMetric (Q (ind n)) (hQ (ind n)) (g (ind n)))
            (gamma n t) (gamma n v) = ENNReal.ofReal |t - v| := by
  classical
  let d := fun n (z : (P n).Carrier) =>
    riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (x n) z
  let f := fun n (z : (P n).Carrier) => metricScalarAt (g n) z / Q n
  have hsmall' : ∃ K : ℝ, ∀ᶠ n in atTop, ∀ z,
      d n z < ENNReal.ofReal r0 → f n z ≤ K := by
    obtain ⟨K, hK⟩ := hsmall
    exact ⟨K, hK.mono fun n hn z hz => (div_le_iff₀ (hQ n)).mpr (hn z hz)⟩
  have hfail' : ∃ B : ℝ, 0 < B ∧ ¬ ∃ K : ℝ,
      ∀ᶠ n in atTop, ∀ z, d n z < ENNReal.ofReal B → f n z ≤ K := by
    obtain ⟨B, hB, hbad⟩ := hfail
    refine ⟨B, hB, ?_⟩
    rintro ⟨K, hK⟩
    apply hbad
    exact ⟨K, hK.mono fun n hn z hz => (div_le_iff₀ (hQ n)).mp (hn z hz)⟩
  obtain ⟨rho, sigma, hrho, hsigma, hinner, escape, hfinite, hdist, hhigh⟩ :=
    exists_subsequence_radius_escape d f hr0 hsmall' hfail'
  have hrhopos : 0 < rho := hr0.trans_le hrho
  have hclosed : ∀ R : ℝ, 0 < R → R < rho → ∃ K : ℝ, 4 ≤ K ∧
      ∀ᶠ n in atTop, ∀ z ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (hQ n) (g n)) (x n) R,
        metricScalarAt (g n) z ≤ K * Q n := by
    intro R hR hRrho
    obtain ⟨K, hK⟩ := hinner ((R + rho) / 2) (by linarith)
    refine ⟨max 4 K, le_max_left _ _, hK.mono ?_⟩
    intro n hn z hz
    have hz' : d n z < ENNReal.ofReal ((R + rho) / 2) :=
      hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < (R + rho) / 2)).mpr
        (by linarith))
    exact (div_le_iff₀ (hQ n)).mp ((hn z hz').trans (le_max_right _ _))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hhigh.eventually_ge_atTop 2)
  let tail : ℕ → ℕ := fun n => n + N
  have htail : StrictMono tail := fun _ _ h => Nat.add_lt_add_right h N
  let ind : ℕ → ℕ := sigma ∘ tail
  have hind : StrictMono ind := hsigma.comp htail
  let z : ∀ n, (P (ind n)).Carrier := fun n => escape (tail n)
  let A : ℕ → ℝ := fun n => min ((n : ℝ) + 2) (f (ind n) (z n))
  have hA (n) : 2 ≤ A n :=
    le_min (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (hN (tail n) (Nat.le_add_left N n))
  have hAhigh : Tendsto A atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop B,
      (hhigh.comp htail.tendsto_atTop).eventually_ge_atTop B] with n hn hzn
    exact le_min (by linarith) hzn
  let gbar := fun n => scaleMetric (Q (ind n)) (hQ (ind n)) (g (ind n))
  let fbar := fun n (z : (P (ind n)).Carrier) => f (ind n) z
  have hf (n) : Continuous (fbar n) :=
    (metricScalar_smooth (g (ind n))).continuous.div_const _
  have hK (n) : IsCompact {z : (P (ind n)).Carrier | fbar n z ≤ A n} :=
    (isClosed_le (hf n) continuous_const).isCompact
  have hxA (n) : fbar n (x (ind n)) < A n := by
    have hb : fbar n (x (ind n)) ≤ 1 :=
      (div_le_one (hQ (ind n))).mpr (hbase (ind n))
    linarith [hA n]
  have hzA (n) : A n ≤ fbar n (z n) := min_le_right _ _
  have hfin (n) : riemannianEDistOf (gbar n) (x (ind n)) (z n) ≠ ⊤ :=
    hfinite (tail n)
  choose y gamma hlevel hfiny hle hzero hend hsmooth hbelow hbound hsegment using
    fun n => Geometry.exists_minimizing_segment_to_level_of_isCompact_sublevel
      (gbar n) (fbar n) (hf n) (hK n) (x (ind n)) (z n) (hxA n) (hzA n) (hfin n)
  let ell := fun n => (d (ind n) (y n)).toReal
  have hinner' : ∀ r : ℝ, 0 < r → r < rho → ∃ K : ℝ,
      ∀ᶠ n in atTop, ∀ z : (P (ind n)).Carrier,
        d (ind n) z < ENNReal.ofReal r → fbar n z ≤ K := by
    intro r _ hr
    obtain ⟨K, hK⟩ := hinner r hr
    exact ⟨K, hind.tendsto_atTop.eventually hK⟩
  have hYhigh : Tendsto (fun n => fbar n (y n)) atTop atTop := by
    simpa only [hlevel] using hAhigh
  have hell := (tendsto_radius_of_inner_bounds_of_escape
    (fun n z => d (ind n) z) fbar hrhopos hinner' z y hfin hle
    (hdist.comp htail.tendsto_atTop) hYhigh).2
  have hellpos (n) : 0 < ell n := by
    have hne : x (ind n) ≠ y n := by
      intro h
      have hb : fbar n (x (ind n)) ≤ 1 :=
        (div_le_one (hQ (ind n))).mpr (hbase (ind n))
      rw [h, hlevel n] at hb
      linarith [hA n]
    have hdne : d (ind n) (y n) ≠ 0 := by
      intro hzeroDist
      have he := hend n
      change gamma n (d (ind n) (y n)).toReal = y n at he
      rw [hzeroDist, ENNReal.toReal_zero, hzero n] at he
      exact hne he
    exact ENNReal.toReal_pos hdne (hfiny n)
  have heqd (n) : d (ind n) (y n) = ENNReal.ofReal (ell n) :=
    (ENNReal.ofReal_toReal (hfiny n)).symm
  exact ⟨rho, ind, hrho, hind, hclosed, A, ell, y, gamma, hA, hAhigh, hell,
    hellpos, hlevel, heqd, (fun n => ⟨hzero n, hend n⟩), hsmooth, hbelow,
    hbound, hsegment⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
