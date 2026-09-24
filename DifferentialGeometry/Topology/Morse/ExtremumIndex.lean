import DifferentialGeometry.Topology.Morse.NormalForm.Manifold
import DifferentialGeometry.Topology.Morse.ModelTransport
import DifferentialGeometry.Topology.Manifold.ModelWithCorners

open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Morse

open Set CellAttachment

section

variable {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ} {p : M}

private theorem minimum_morse_index_eq_zero_model (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p) :
    sigNeg (chartHessianAt
      (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0 := by
  classical
  let Q := chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)
  let k := sigNeg Q
  have hk : k ≤ n := by
    have hdim : Module.finrank ℝ (MorseModel n) = n := by simp [MorseModel]
    exact hdim ▸ sigPos_le_finrank (-Q)
  obtain ⟨R₀, hR₀, Φ, hΦzero, _, hΦ0, _, hnormal₀, _⟩ :=
    morse_lemma I f hf p k hk hnd rfl
  have hcont : Filter.Tendsto Φ (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt, hΦ0] using Φ.continuousAt hΦzero
  have hlocal : {y : MorseModel n | f p ≤ f (Φ y)} ∈ 𝓝 0 := hcont hmin
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hlocal
  let R := min R₀ (δ / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hδ)
  have hnormal (y : MorseModel n) (hy : morseNorm n y ≤ R) :
      f (Φ y) = morseNormalForm hk (f p) y :=
    hnormal₀ y (hy.trans (min_le_left _ _))
  have hsmall' (y : MorseModel n) (hy : morseNorm n y ≤ R) : f p ≤ f (Φ y) := by
    apply hsmall
    rw [Metric.mem_ball, dist_zero_right]
    exact ((morseNorm_piNorm_le y).trans hy).trans_lt
      ((min_le_right _ _).trans_lt (half_lt_self hδ))
  by_contra hzero
  have hkpos : 0 < k := Nat.pos_of_ne_zero hzero
  let u : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single ⟨0, hkpos⟩ 1
  have hu : ‖u‖ = 1 := by simp [u, EuclideanSpace.single, PiLp.norm_single]
  have hsqrt : Real.sqrt (2 * (R ^ 2 / 2)) = R := by
    rw [show 2 * (R ^ 2 / 2) = R ^ 2 by ring, Real.sqrt_sq hR.le]
  have hbound : morseNorm n (cellMap R u) ≤ R := by
    have h := norm_cellMap_le hk (R ^ 2 / 2) R (hsqrt.le) u hu.le
    rw [hsqrt] at h
    exact h
  have heq := hnormal (cellMap R u) hbound
  rw [morseNormalForm_cellMap, hu] at heq
  have hle := hsmall' (cellMap R u) hbound
  nlinarith [sq_pos_of_pos hR]

private theorem maximum_morse_index_eq_dimension_model (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmax : IsLocalMax f p) :
    sigNeg (chartHessianAt
      (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = n := by
  classical
  let Q := chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)
  let k := sigNeg Q
  have hk : k ≤ n := by
    have hdim : Module.finrank ℝ (MorseModel n) = n := by simp [MorseModel]
    exact hdim ▸ sigPos_le_finrank (-Q)
  obtain ⟨R₀, hR₀, Φ, hΦzero, _, hΦ0, _, hnormal₀, _⟩ :=
    morse_lemma I f hf p k hk hnd rfl
  have hcont : Filter.Tendsto Φ (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt, hΦ0] using Φ.continuousAt hΦzero
  have hlocal : {y : MorseModel n | f (Φ y) ≤ f p} ∈ 𝓝 0 := hcont hmax
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hlocal
  let R := min R₀ (δ / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hδ)
  have hnormal (y : MorseModel n) (hy : morseNorm n y ≤ R) :
      f (Φ y) = morseNormalForm hk (f p) y :=
    hnormal₀ y (hy.trans (min_le_left _ _))
  have hsmall' (y : MorseModel n) (hy : morseNorm n y ≤ R) : f (Φ y) ≤ f p := by
    apply hsmall
    rw [Metric.mem_ball, dist_zero_right]
    exact ((morseNorm_piNorm_le y).trans hy).trans_lt
      ((min_le_right _ _).trans_lt (half_lt_self hδ))
  by_contra heq
  have hpos : 0 < n - k := Nat.sub_pos_of_lt (lt_of_le_of_ne hk heq)
  let u : EuclideanSpace ℝ (Fin (n - k)) := EuclideanSpace.single ⟨0, hpos⟩ 1
  have hu : ‖u‖ = 1 := by simp [u, EuclideanSpace.single, PiLp.norm_single]
  let y := recombine hk 0 (R • u)
  have hRu : ‖R • u‖ = R := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hu, mul_one]
  have hbound : morseNorm n y ≤ R := by
    have hs := morseNorm_recombine_sq hk 0 (R • u)
    rw [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, hRu] at hs
    change morseNorm n (recombine hk 0 (R • u)) ≤ R
    nlinarith
  have he := hnormal y hbound
  rw [morseNormalForm_split, show posPart hk y = R • u from posPart_recombine hk 0 (R • u),
    show negPart hk y = 0 from negPart_recombine hk 0 (R • u), hRu, norm_zero,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at he
  have hm := hsmall' y hbound
  nlinarith [sq_pos_of_pos hR]

end

theorem minimum_morse_index_eq_zero
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p) :
    sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0 := by
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] MorseModel n := ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel, n])
  let J := I.transContinuousLinearEquiv L
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left L).mpr hf
  have hndJ : IsNondegenerateCriticalPointAt J f p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  have hindex := DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv
    I L hf BoundarylessManifold.isInteriorPoint hnd.1
  exact hindex.symm.trans (minimum_morse_index_eq_zero_model hfJ hndJ hmin)

theorem maximum_morse_index_eq_finrank
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmax : IsLocalMax f p) :
    sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) =
      Module.finrank ℝ E := by
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] MorseModel n := ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel, n])
  let J := I.transContinuousLinearEquiv L
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left L).mpr hf
  have hndJ : IsNondegenerateCriticalPointAt J f p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  have hindex := DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv
    I L hf BoundarylessManifold.isInteriorPoint hnd.1
  exact hindex.symm.trans (maximum_morse_index_eq_dimension_model hfJ hndJ hmax)

private theorem isLocalMin_of_morse_index_eq_zero_model
    {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
    [IsManifold I ∞ M] {f : M → ℝ} {p : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt
      (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0) : IsLocalMin f p := by
  obtain ⟨R, hR, Φ, hzero, hp, hΦ0, _, hnormal, _⟩ :=
    morse_lemma I f hf p 0 (Nat.zero_le n) hnd hindex
  have hsymm : Φ.symm p = 0 := hΦ0 ▸ Φ.left_inv hzero
  have hn : ContinuousAt (fun x => morseNorm n (Φ.symm x)) p :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.norm.continuousAt.comp
      (Φ.symm.continuousAt hp)
  have hn' : ∀ᶠ x in 𝓝 p, morseNorm n (Φ.symm x) < R :=
    hn.eventually (isOpen_Iio.mem_nhds (by simpa [hsymm, morseNorm] using hR))
  filter_upwards [Φ.open_target.mem_nhds hp, hn'] with x hx hxR
  have heq := hnormal (Φ.symm x) hxR.le
  rw [Φ.right_inv hx, morseNormalForm_split, negPart_bot, norm_zero,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at heq
  rw [heq]
  nlinarith [sq_nonneg (‖posPart (Nat.zero_le n) (Φ.symm x)‖)]

private theorem isLocalMax_of_morse_index_eq_dimension_model
    {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
    [IsManifold I ∞ M] {f : M → ℝ} {p : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt
      (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = n) : IsLocalMax f p := by
  obtain ⟨R, hR, Φ, hzero, hp, hΦ0, _, hnormal, _⟩ :=
    morse_lemma I f hf p n le_rfl hnd hindex
  have hsymm : Φ.symm p = 0 := hΦ0 ▸ Φ.left_inv hzero
  have hn : ContinuousAt (fun x => morseNorm n (Φ.symm x)) p :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.norm.continuousAt.comp
      (Φ.symm.continuousAt hp)
  have hn' : ∀ᶠ x in 𝓝 p, morseNorm n (Φ.symm x) < R :=
    hn.eventually (isOpen_Iio.mem_nhds (by simpa [hsymm, morseNorm] using hR))
  filter_upwards [Φ.open_target.mem_nhds hp, hn'] with x hx hxR
  have heq := hnormal (Φ.symm x) hxR.le
  rw [Φ.right_inv hx, morseNormalForm_split, posPart_top, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_sub] at heq
  rw [heq]
  nlinarith [sq_nonneg (‖negPart (le_refl n) (Φ.symm x)‖)]

theorem isLocalMin_iff_morse_index_eq_zero
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) :
    IsLocalMin f p ↔
      sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0 := by
  refine ⟨minimum_morse_index_eq_zero hf hnd, fun hindex => ?_⟩
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] MorseModel n := ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel, n])
  let J := I.transContinuousLinearEquiv L
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left L).mpr hf
  have hndJ : IsNondegenerateCriticalPointAt J f p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  have hindexJ := DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv
    I L hf BoundarylessManifold.isInteriorPoint hnd.1
  exact isLocalMin_of_morse_index_eq_zero_model hfJ hndJ (hindexJ.trans hindex)

theorem isLocalMax_iff_morse_index_eq_finrank
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) :
    IsLocalMax f p ↔
      sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) =
        Module.finrank ℝ E := by
  refine ⟨maximum_morse_index_eq_finrank hf hnd, fun hindex => ?_⟩
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] MorseModel n := ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel, n])
  let J := I.transContinuousLinearEquiv L
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left L).mpr hf
  have hndJ : IsNondegenerateCriticalPointAt J f p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  have hindexJ := DifferentialGeometry.Morse.sigNeg_chartHessianAt_transContinuousLinearEquiv
    I L hf BoundarylessManifold.isInteriorPoint hnd.1
  exact isLocalMax_of_morse_index_eq_dimension_model hfJ hndJ (hindexJ.trans hindex)

end DifferentialGeometry.Topology.Morse
