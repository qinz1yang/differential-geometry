import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_eq_of_near_minimizer_trapping
    (g g' : SmoothRiemannianMetric I M) {K : Set M} {p q : M} {delta : ℝ}
    (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (heq : ∀ x ∈ K, g'.inner x = g.inner x)
    (hle : ∀ x (v : TangentSpace I x), g.inner x v v ≤ g'.inner x v v)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    riemannianEDistOf g' p q = riemannianEDistOf g p q := by
  refine le_antisymm ?_ (edistOf_mono g g' hle p q)
  by_contra hnot
  have hgap : riemannianEDistOf g p q < riemannianEDistOf g p q + ENNReal.ofReal delta :=
    ENNReal.lt_add_right hfinite (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  obtain ⟨c, hc, hupper⟩ := exists_between (lt_min (not_le.mp hnot) hgap)
  obtain ⟨gamma, hstart, hend, hsmooth, hlength⟩ := exists_lt_of_edistOf_lt g hc
  have hmem := htrap gamma hsmooth hstart hend
    (hlength.le.trans (hupper.trans_le (min_le_right _ _)).le)
  have heqlength : metricPathELength g' gamma 0 1 = metricPathELength g gamma 0 1 :=
    metricPathELength_congr g g' (fun s hs => heq _ (hmem s ⟨hs.1.le, hs.2.le⟩))
  have hdist := edistOf_le_metricPathELength g' (by norm_num : (0 : ℝ) ≤ 1) hsmooth
  rw [hstart, hend, heqlength] at hdist
  exact (not_lt_of_ge hdist)
    (hlength.trans (hupper.trans_le (min_le_left _ _)))

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_minimizer_with_subinterval_lengths
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {p q : M} {delta : ℝ} (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) ∧
      metricPathELength g gamma 0 1 = riemannianEDistOf g p q ∧
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        metricPathELength g gamma a b = ENNReal.ofReal (b - a) * riemannianEDistOf g p q := by
  classical
  obtain ⟨g', U, hcomplete, _hUopen, hKU, heqU, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  have heqdist : riemannianEDistOf g' p q = riemannianEDistOf g p q :=
    riemannianEDistOf_eq_of_near_minimizer_trapping g g' hdelta hfinite
      (fun x hx => heqU x (hKU hx)) hle htrap
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g' :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g' x v
  have hdist' : riemannianEDistOf g' p q = Manifold.riemannianEDist I p q :=
    riemannianEDistOf_eq_riemannianEDist g' hEnorm p q
  have hfinite' : Manifold.riemannianEDist I p q ≠ ⊤ := by
    rw [← hdist', heqdist]
    exact hfinite
  obtain ⟨v, hv, hspeed⟩ := minExp_of_ne_top g' hEnorm p q hfinite'
  let gamma : ℝ → M := intrinsicGeodesic g' hEnorm p v
  have hstart : gamma 0 = p := intrinsicGeodesic_zero g' hEnorm p v
  have hend : gamma 1 = q := hv
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    isGeodesic_contMDiff g' (intrinsicGeodesic_isGeodesic g' hEnorm p v)
      (intrinsicGeodesic_continuous g' hEnorm p v)
  have hspeedAll (s : ℝ) :
      g'.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = g'.inner p v v :=
    intrinsicGeodesic_speedSq_eq g' hEnorm p v s
  have hlen' : metricPathELength g' gamma 0 1 = riemannianEDistOf g p q := by
    rw [metricPathELength_eq]
    simp_rw [hspeedAll]
    rw [setLIntegral_const, Real.volume_Ioo]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    rw [hspeed, ENNReal.ofReal_toReal hfinite', ← hdist', heqdist]
  have hlen : metricPathELength g gamma 0 1 ≤ metricPathELength g' gamma 0 1 := by
    rw [metricPathELength_eq, metricPathELength_eq]
    exact setLIntegral_mono' measurableSet_Ioo fun s _hs =>
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hle (gamma s) _))
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K := by
    apply htrap gamma (hsmooth.of_le (by simp)).contMDiffOn hstart hend
    exact (hlen.trans_eq hlen').trans
      (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal delta from bot_le))
  refine ⟨gamma, hstart, hend, hsmooth, hmem, ?_, ?_⟩
  · calc
      _ = metricPathELength g' gamma 0 1 :=
        (metricPathELength_congr g g' (fun s hs => heqU _ (hKU (hmem s ⟨hs.1.le, hs.2.le⟩)))).symm
      _ = _ := hlen'
  · intro a ha b hb
    calc
      _ = metricPathELength g' gamma a b :=
        (metricPathELength_congr g g' (fun s hs => heqU _
          (hKU (hmem s ⟨ha.1.trans hs.1.le, hs.2.le.trans hb.2⟩)))).symm
      _ = _ := by
        rw [metricPathELength_eq]
        simp_rw [hspeedAll]
        rw [setLIntegral_const, Real.volume_Ioo, hspeed, ENNReal.ofReal_toReal hfinite',
          ← hdist', heqdist, mul_comm]

theorem exists_smooth_minimizer_of_compact_trapping
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {p q : M} {delta : ℝ} (hdelta : 0 < delta) (hfinite : riemannianEDistOf g p q ≠ ⊤)
    (htrap : ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) → gamma 0 = p → gamma 1 = q →
      metricPathELength g gamma 0 1 ≤ riemannianEDistOf g p q + ENNReal.ofReal delta →
      ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ K) ∧
      metricPathELength g gamma 0 1 = riemannianEDistOf g p q := by
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, _hsub⟩ :=
    exists_smooth_minimizer_with_subinterval_lengths g hK hdelta hfinite htrap
  exact ⟨gamma, hstart, hend, hsmooth, hmem, hlength⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
