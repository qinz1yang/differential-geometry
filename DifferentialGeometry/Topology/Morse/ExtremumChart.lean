import DifferentialGeometry.Topology.Morse.ExtremumIndex
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.Morse.Affine

open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Morse

open Set CellAttachment

section

variable {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ} {p : M}

private theorem exists_quadratic_chart_of_isLocalMin_model (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p) :
    ∃ R : ℝ, 0 < R ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 R ∧ Φ 0 = p ∧
          ∀ y ∈ Φ.source, f (Φ y) = f p + ‖y‖ ^ 2 / 2 := by
  obtain ⟨R, hR, Φ, _, _, hΦ0, hsource, hnormal, _, _, R', hR', hΦ, hΦinv⟩ :=
    morse_lemma I f hf p 0 (Nat.zero_le n) hnd
      (minimum_morse_index_eq_zero hf hnd hmin)
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let e := L.toHomeomorph.toOpenPartialHomeomorph.trans Φ
  let r := min R R'
  have hr : 0 < r := lt_min hR hR'
  have hLnorm (y : EuclideanSpace ℝ (Fin n)) : morseNorm n (L y) = ‖y‖ := rfl
  have hball (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball 0 r) :
      morseNorm n (L y) < r := by simpa only [hLnorm, Metric.mem_ball, dist_zero_right] using hy
  have hsub : Metric.ball 0 r ⊆ e.source := by
    intro y hy
    exact ⟨mem_univ _, hsource (L y) ((hball y hy).le.trans (min_le_left _ _))⟩
  let e' := e.restrOpen (Metric.ball 0 r) Metric.isOpen_ball
  have he'S : e'.source = Metric.ball 0 r := inter_eq_right.mpr hsub
  have hLball : MapsTo L (Metric.ball 0 r) (Metric.ball 0 R') := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    exact (morseNorm_piNorm_le (L y)).trans_lt ((hball y hy).trans_le (min_le_right _ _))
  have hforward : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ e' e'.source := by
    rw [he'S]
    exact hΦ.comp L.contDiff.contMDiff.contMDiffOn hLball
  have hinvsub : e'.target ⊆ Φ '' Metric.ball 0 R' := by
    intro x hx
    have hy : e'.symm x ∈ Metric.ball 0 r := he'S ▸ e'.map_target hx
    exact ⟨L (e'.symm x), hLball hy, e'.right_inv hx⟩
  have hinverse : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e'.symm e'.target := by
    exact L.symm.contDiff.contMDiff.comp_contMDiffOn (hΦinv.mono hinvsub)
  refine ⟨r, hr, ⟨e'.toPartialEquiv, e'.open_source, e'.open_target, hforward, hinverse⟩,
    he'S, ?_, ?_⟩
  · change Φ (L 0) = p
    simpa only [map_zero] using hΦ0
  · intro y hy
    change f (Φ (L y)) = f p + ‖y‖ ^ 2 / 2
    have heq := hnormal (L y) ((hball y (he'S ▸ hy)).le.trans (min_le_left _ _))
    rw [morseNormalForm] at heq
    have hsum : (∑ j : Fin (n - 0), (L y (posIdx (Nat.zero_le n) j)) ^ 2) = ‖y‖ ^ 2 := by
      simpa [posIdx, L] using (EuclideanSpace.real_norm_sq_eq y).symm
    rw [hsum] at heq
    simpa [div_eq_mul_inv, mul_comm] using heq

end

theorem exists_quadratic_chart_of_isLocalMin
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p) :
    ∃ R : ℝ, 0 < R ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) I
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M ∞,
        Φ.source = Metric.ball 0 R ∧ Φ 0 = p ∧
          ∀ y ∈ Φ.source, f (Φ y) = f p + ‖y‖ ^ 2 / 2 := by
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] MorseModel n := ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel, n])
  let J := I.transContinuousLinearEquiv L
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left L).mpr hf
  have hndJ : IsNondegenerateCriticalPointAt J f p :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_transContinuousLinearEquiv_iff
      I L hf BoundarylessManifold.isInteriorPoint).mpr hnd
  obtain ⟨R, hR, Φ, hsource, hΦ0, hnormal⟩ :=
    exists_quadratic_chart_of_isLocalMin_model hfJ hndJ hmin
  let χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
      (EuclideanSpace ℝ (Fin n)) M ∞ := {
    toPartialEquiv := Φ.toPartialEquiv
    open_source := Φ.open_source
    open_target := Φ.open_target
    contMDiffOn_toFun :=
      (ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right L).mp Φ.contMDiffOn
    contMDiffOn_invFun :=
      (ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left L).mp Φ.symm.contMDiffOn }
  exact ⟨R, hR, χ, hsource, hΦ0, hnormal⟩

theorem exists_quadratic_chart_of_isLocalMax
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmax : IsLocalMax f p) :
    ∃ R : ℝ, 0 < R ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) I
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M ∞,
        Φ.source = Metric.ball 0 R ∧ Φ 0 = p ∧
          ∀ y ∈ Φ.source, f (Φ y) = f p - ‖y‖ ^ 2 / 2 := by
  have hnd' : IsNondegenerateCriticalPointAt I (fun x => -f x) p := by
    simpa only [zero_sub] using
      (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff hf
        BoundarylessManifold.isInteriorPoint 0).mpr hnd
  obtain ⟨R, hR, Φ, hsource, hΦ0, hnormal⟩ :=
    exists_quadratic_chart_of_isLocalMin hf.neg hnd' hmax.neg
  refine ⟨R, hR, Φ, hsource, hΦ0, fun y hy => ?_⟩
  have h := hnormal y hy
  linarith

end DifferentialGeometry.Topology.Morse
