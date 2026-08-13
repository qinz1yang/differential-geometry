import DifferentialGeometry.Geometry.Comparison.Variation.CovariantGronwall
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartMeasure
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]


def radialCurve (g : SmoothRiemannianMetric I M) (p : M) (x : E) (t : ℝ) : M :=
  expMap (I := I) g p (show TangentSpace I p from (t • x))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
@[simp] lemma radialCurve_apply
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (t : ℝ) :
    radialCurve (I := I) g p x t =
      expMap (I := I) g p (show TangentSpace I p from (t • x)) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
@[simp] lemma radialCurve_one
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    radialCurve (I := I) g p x 1 =
      expMap (I := I) g p (show TangentSpace I p from x) := by
  simp [radialCurve]

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma radialCurve_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    radialCurve (I := I) g p x 0 = p := by
  unfold radialCurve
  rw [zero_smul]
  exact expMap_zero (I := I) g p

omit [T2Space M] in
omit [SigmaCompactSpace M] in
theorem exists_radialJacobi_diff
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {b : ℝ}, b ≤ 1 →
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t) t) := by
  simpa [radialCurve, radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_jacobi_diff (I := I) g p

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem radial_mem_expBall
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {ρ b : Real} (hxρ : ‖x‖ < ρ) (hb : b ≤ 1) :
    ∀ t : Real, t ∈ Ioo (0 : Real) b →
      radialCurve (I := I) g p x t ∈
        (fun v : TangentSpace I p => expMap (I := I) g p v) ''
          {v : TangentSpace I p | ‖v‖ < ρ} := by
  intro t ht
  refine ⟨(show TangentSpace I p from t • x), ?_, ?_⟩
  · have ht_nonneg : 0 ≤ t := le_of_lt ht.1
    have ht_le_one : t ≤ 1 := le_trans (le_of_lt ht.2) hb
    calc
      ‖(show TangentSpace I p from t • x)‖ = ‖t • x‖ := rfl
      _ = ‖t‖ * ‖x‖ := norm_smul t x
      _ = t * ‖x‖ := by rw [Real.norm_of_nonneg ht_nonneg]
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht_le_one (norm_nonneg x)
      _ = ‖x‖ := one_mul ‖x‖
      _ < ρ := hxρ
  · rfl

omit [T2Space M] [SigmaCompactSpace M] in
omit [T2Space (TangentBundle I M)] in
lemma exists_radialFrame
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {b : ℝ} (hb : 0 < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (radialCurve (I := I) g p x)) :
    ∃ F : Fin (Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x 0))) →
        ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t),
      (∀ t ∈ Icc (0 : ℝ) b,
        Fintype.card (Fin (Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x 0)))) =
          Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) := by
  classical
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g (radialCurve (I := I) g p x 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_parallel_frame
      (I := I) g (radialCurve (I := I) g p x)
      (N := 2) (by norm_num) hγ hb basis hON0
  refine ⟨F, ?_, hFdiff, hFpar, hFON⟩
  intro t ht
  simp only [Fintype.card_fin]
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
lemma radialCurve_contMDiffAt_Icc
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : ℕ∞)
        (radialCurve (I := I) g p x) t := by
  intro t ht
  have hnorm : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ t := ht.1
    have h1 : t ≤ 1 := le_trans ht.2 hb
    have habs : |t| ≤ 1 := by
      rw [abs_of_nonneg h0]
      exact h1
    calc
      |t| * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖x‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hx
  simpa [radialCurve] using
    (DifferentialGeometry.Geometry.Riemannian.radialCurve_contMDiffAt2
      (I := I) g p x t hnorm)

omit [T2Space M] [SigmaCompactSpace M] in
lemma radialCurve_contMDiffOn_Icc
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞)
      (radialCurve (I := I) g p x) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hnorm : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ t := ht.1
    have h1 : t ≤ 1 := ht.2
    have habs : |t| ≤ 1 := by
      rw [abs_of_nonneg h0]
      exact h1
    calc
      |t| * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖x‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hx
  simpa [radialCurve] using
    (DifferentialGeometry.Geometry.Riemannian.radialCurve_contMDiffAt2
      (I := I) g p x t hnorm).contMDiffWithinAt


omit [T2Space M] [SigmaCompactSpace M] in
lemma radialC2OnBallIcc
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p) (hb : b ≤ 1) :
    ∀ w ∈ Metric.ball (0 : E) R,
      ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞)
        (radialCurve (I := I) g p w) (Icc (0 : ℝ) b) := by
  intro w hw
  have hwR : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  exact (radialCurve_contMDiffOn_Icc (I := I) g p w (hwR.trans_le hR)).mono
    (by
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hb⟩)

omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_radial_clip
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ tau : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) tau ∧
      Set.EqOn tau id (Set.Icc 0 b) ∧
      ∀ t : ℝ, ‖tau t • x‖ < expMapC2Radius (I := I) g p := by
  classical
  let R := expMapC2Radius (I := I) g p
  have hRpos : 0 < R := DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
    (I := I) g p
  by_cases hxzero : ‖x‖ = 0
  · set lam : ℝ := b + 1 with hlam_def
    have hblam : b < lam := by rw [hlam_def]; linarith
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_clip
        (L := b) (lam := lam) hb0 hblam
    refine ⟨tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, hxzero, mul_zero]
    exact hRpos
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxzero)
    have hratio : 1 < R / ‖x‖ := by
      rw [one_lt_div hxpos]
      simpa [R] using hx
    set lam : ℝ := (1 + R / ‖x‖) / 2 with hlam_def
    have h1lam : 1 < lam := by rw [hlam_def]; linarith
    have hblam : b < lam := lt_of_le_of_lt hb1 h1lam
    have hprod : lam * ‖x‖ < R := by
      have hprod_eq : lam * ‖x‖ = (‖x‖ + R) / 2 := by
        rw [hlam_def]
        field_simp [hxpos.ne']
      rw [hprod_eq]
      linarith [show ‖x‖ < R by simpa [R] using hx]
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_clip
        (L := b) (lam := lam) hb0 hblam
    refine ⟨tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (htau_bound t) (norm_nonneg x)) hprod

omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rclip_nbhd
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ tau : ℝ → ℝ,
      ContDiff ℝ (∞ : WithTop ℕ∞) tau ∧
      Set.EqOn tau id (Set.Icc (-eps) (b + eps)) ∧
      ∀ t : ℝ, ‖tau t • x‖ < expMapC2Radius (I := I) g p := by
  classical
  let R := expMapC2Radius (I := I) g p
  have hRpos : 0 < R := DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
    (I := I) g p
  by_cases hxzero : ‖x‖ = 0
  · set lam : ℝ := 2 with hlam_def
    set eps : ℝ := (1 / 2 : ℝ) with heps_def
    have heps_pos : 0 < eps := by rw [heps_def]; norm_num
    have hlam_pos : 0 < lam := by rw [hlam_def]; norm_num
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
        (a := -eps) (b := b + eps) (lam := lam) hlam_pos
        (by rw [hlam_def, heps_def]; norm_num)
        (by rw [hlam_def, heps_def]; linarith)
    refine ⟨eps, heps_pos, tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, hxzero, mul_zero]
    exact hRpos
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxzero)
    have hratio : 1 < R / ‖x‖ := by
      rw [one_lt_div hxpos]
      simpa [R] using hx
    set lam : ℝ := (1 + R / ‖x‖) / 2 with hlam_def
    set eps : ℝ := (lam - 1) / 2 with heps_def
    have h1lam : 1 < lam := by rw [hlam_def]; linarith
    have hlam_pos : 0 < lam := by linarith
    have heps_pos : 0 < eps := by rw [heps_def]; linarith
    have heps_lt_lam : eps < lam := by rw [heps_def]; linarith
    have hb_eps_lt : b + eps < lam := by
      have hmid : 1 + eps < lam := by rw [heps_def]; linarith
      have hble : b + eps ≤ 1 + eps := by linarith
      exact lt_of_le_of_lt hble hmid
    have hprod : lam * ‖x‖ < R := by
      have hprod_eq : lam * ‖x‖ = (‖x‖ + R) / 2 := by
        rw [hlam_def]
        field_simp [hxpos.ne']
      rw [hprod_eq]
      linarith [show ‖x‖ < R by simpa [R] using hx]
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
        (a := -eps) (b := b + eps) (lam := lam) hlam_pos
        (by linarith [heps_lt_lam]) hb_eps_lt
    refine ⟨eps, heps_pos, tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (htau_bound t) (norm_nonneg x)) hprod

omit [T2Space M] [SigmaCompactSpace M] in
lemma radial_clip_contMDiff
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (tau : ℝ → ℝ)
    (htau : ContDiff ℝ (∞ : WithTop ℕ∞) tau)
    (hradius : ∀ t : ℝ, ‖tau t • x‖ < expMapC2Radius (I := I) g p) :
    ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞)
      (fun t : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from (tau t • x)) : M)) := by
  intro t
  have htauMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) tau := by
    rw [contMDiff_iff_contDiff]
    exact htau
  have hsmul : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (∞ : WithTop ℕ∞)
      (fun t : ℝ => tau t • x) :=
    htauMD.smul contMDiff_const
  have hexpC2 : ContMDiffAt 𝓘(ℝ, E) I (2 : ℕ∞)
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      (tau t • x) :=
    expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p (hradius t)
  simpa using hexpC2.comp t (hsmul.contMDiffAt.of_le ENat.LEInfty.out)

omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_radial_ext
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ gamma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma ∧
      Set.EqOn gamma (radialCurve (I := I) g p x) (Set.Icc 0 b) := by
  obtain ⟨tau, htau, htau_eq, hradius⟩ :=
    exists_radial_clip (I := I) g p x hb0 hb1 hx
  refine ⟨fun t : ℝ => (expMap (I := I) g p
    (show TangentSpace I p from (tau t • x)) : M), ?_, ?_⟩
  · exact radial_clip_contMDiff (I := I) g p x tau htau hradius
  · intro t ht
    change expMap (I := I) g p (show TangentSpace I p from (tau t • x)) =
      radialCurve (I := I) g p x t
    rw [htau_eq ht]
    rfl

omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rext_nbhd
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ gamma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma ∧
      Set.EqOn gamma (radialCurve (I := I) g p x) (Set.Icc (-eps) (b + eps)) := by
  obtain ⟨eps, heps, tau, htau, htau_eq, hradius⟩ :=
    exists_rclip_nbhd (I := I) g p x hb1 hx
  refine ⟨eps, heps, fun t : ℝ => (expMap (I := I) g p
    (show TangentSpace I p from (tau t • x)) : M), ?_, ?_⟩
  · exact radial_clip_contMDiff (I := I) g p x tau htau hradius
  · intro t ht
    change expMap (I := I) g p (show TangentSpace I p from (tau t • x)) =
      radialCurve (I := I) g p x t
    rw [htau_eq ht]
    rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem radial_speed_sq_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t) =
        g.inner p x x := by
  simpa [radialCurve, curveVelocity] using
    (DifferentialGeometry.Geometry.Riemannian.radialSpeedSq_eq_inner
      (I := I) g p x hx t ht)

omit [T2Space M] [SigmaCompactSpace M] in
theorem radial_speed_le
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) {Vb b : ℝ}
    (hb : b ≤ 1) (hVb : Real.sqrt (g.inner p x x) ≤ Vb) :
    ∀ t ∈ Ioo (0 : ℝ) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb := by
  intro t ht
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hb⟩
  rw [radial_speed_sq_eq (I := I) g p x hx ht01]
  exact hVb

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private theorem exists_gON_tangentBasis_E
    (g : SmoothRiemannianMetric I M) (y : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
      ∀ i j, g.inner y (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
  simpa [show Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E from rfl]
    using DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g y

omit [SigmaCompactSpace M] in
theorem exists_jacobi_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {b : ℝ}, b ≤ 1 →
      ∀ t ∈ Ioo (0 : ℝ) b,
        IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t := by
  obtain ⟨r, hr, hJac⟩ := exists_radialJacobi_radius (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw b hb t ht
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hb⟩
  simpa [radialCurve] using hJac x w hx hw t ht01

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialJacobi_ode_of_curv
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : ℝ}
    (hJac : ∀ t ∈ Ico (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t)
    (hcurv : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t)) :
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  exact ode_bound_of_isJacobiAt (I := I) g (radialCurve (I := I) g p x)
    (radialJacobiField (I := I) g p x w) (K := K) (t := t) (hJac t ht)
    (hcurv t ht)

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ode_Ico_of_Ioo_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : ℝ}
    (hJac : ∀ t ∈ Ioo (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t)
    (hcurv : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))
    (h0 :
      g.inner (radialCurve (I := I) g p x 0)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) 0)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) 0)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
        (radialJacobiField (I := I) g p x w 0)
        (radialJacobiField (I := I) g p x w 0)) :
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa using h0
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact ode_bound_of_isJacobiAt (I := I) g (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) (K := K) (t := t)
      (hJac t ⟨htpos, ht.2⟩) (hcurv t ⟨htpos, ht.2⟩)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ode_Ico_of_Ioo_d2
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : ℝ}
    (hJac : ∀ t ∈ Ioo (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t)
    (hcurv : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))
    (hD2 :
      covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) 0 = 0) :
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t) := by
  refine ode_Ico_of_Ioo_zero (I := I) g p x w hJac hcurv ?_
  rw [hD2, radialJacobi_zero]
  change
    g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) ≤
      K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
  have hz :
      g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) = 0 := by
    rw [map_zero]
  rw [hz]
  rw [mul_zero]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem d2_zero_of_jac0
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hJac0 : IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) 0) :
    covDerivAlong (I := I) g (radialCurve (I := I) g p x)
      (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s) 0 = 0 := by
  unfold IsJacobiAt at hJac0
  rw [radialJacobi_zero] at hJac0
  set D : TangentSpace I (radialCurve (I := I) g p x 0) :=
    covDerivAlong (I := I) g (radialCurve (I := I) g p x)
      (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s) 0 with hD_def
  set C : TangentSpace I (radialCurve (I := I) g p x 0) :=
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (curveVelocity (I := I) (radialCurve (I := I) g p x) 0)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) 0)) with hC_def
  change D + C = 0 at hJac0
  have hCzero : C = 0 := by
    rw [hC_def]
    rw [map_zero]
    rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
  rw [hCzero, add_zero] at hJac0
  exact hJac0

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : ℝ}, b ≤ 1 →
      (∀ t ∈ Ioo (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (radialCurve (I := I) g p x t))
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (radialCurve (I := I) g p x t))
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
          ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t)) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hJac⟩ := exists_jacobi_Ioo (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hb hcurv h0
  exact ode_Ico_of_Ioo_zero (I := I) g p x w (K := K) (b := b)
    (hJac x w hx hw hb) hcurv h0


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma inner_self_nonneg
    (g : SmoothRiemannianMetric I M) {q : M} (u : TangentSpace I q) :
    0 <= g.inner q u u := by
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · exact (g.pos q u hu).le


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma inner_sq_le_of_sqrt_le
    (g : SmoothRiemannianMetric I M) {q : M} {u v : TangentSpace I q} {K : Real}
    (hK : 0 ≤ K)
    (h : Real.sqrt (g.inner q u u) ≤ K * Real.sqrt (g.inner q v v)) :
    g.inner q u u ≤ K ^ 2 * g.inner q v v := by
  have hu_nn : 0 ≤ g.inner q u u := inner_self_nonneg (I := I) g u
  have hv_nn : 0 ≤ g.inner q v v := inner_self_nonneg (I := I) g v
  have hrhs_nn : 0 ≤ K * Real.sqrt (g.inner q v v) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (g.inner q u u)) ^ 2 ≤
        (K * Real.sqrt (g.inner q v v)) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs_nn).2 h
  calc
    g.inner q u u = (Real.sqrt (g.inner q u u)) ^ 2 := by
      rw [Real.sq_sqrt hu_nn]
    _ ≤ (K * Real.sqrt (g.inner q v v)) ^ 2 := hsq
    _ = K ^ 2 * g.inner q v v := by
      rw [mul_pow, Real.sq_sqrt hv_nn]


private def radialCurvTerm
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    TangentSpace I (radialCurve (I := I) g p x t) :=
  (DifferentialGeometry.Geometry.Curvature.riemannOp
    (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
      (radialCurve (I := I) g p x t))
    (radialJacobiField (I := I) g p x w t)
    (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
    (curveVelocity (I := I) (radialCurve (I := I) g p x) t)


private def radialCurvTermFlat
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    Tensor0SBundle.Tensor0SSpace 1 I (radialCurve (I := I) g p x t) :=
  Tensor0SBundle.dualToCotangent_gen (I := I)
    (Tensor0SBundle.tangentFlatLinear_gen (I := I) g
      (radialCurve (I := I) g p x t)
      (radialCurvTerm (I := I) g p x w t))

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_inner
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    Tensor0SBundle.cotangentInner_gen (I := I) g
      (radialCurve (I := I) g p x t)
      (radialCurvTermFlat (I := I) g p x w t)
      (radialCurvTermFlat (I := I) g p x w t) =
        g.inner (radialCurve (I := I) g p x t)
          (radialCurvTerm (I := I) g p x w t)
          (radialCurvTerm (I := I) g p x w t) := by
  simpa [radialCurvTermFlat] using
    (Tensor0SBundle.cotangentInner_dualToCotangent_tangentFlat_gen
      (I := I) g (radialCurve (I := I) g p x t)
      (radialCurvTerm (I := I) g p x w t)
      (radialCurvTerm (I := I) g p x w t))

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_apply_eq_metricRm04StdAt
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (W : TangentSpace I (radialCurve (I := I) g p x t)) :
    radialCurvTermFlat (I := I) g p x w t (fun _ : Fin 1 => W) =
      DifferentialGeometry.Geometry.Curvature.metricRm04StdAt
        (I := I) (M := M) g (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t) W := by
  have hcov :=
    DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_apply,
    DifferentialGeometry.metricRm04At_eq_riemannCurvature04At,
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const,
    DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (cov := DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
      (hcov := hcov)]
  unfold radialCurvTermFlat radialCurvTerm
  rw [Tensor0SBundle.dualToCotangent_apply_gen,
    Tensor0SBundle.tangentFlatLinear_apply_gen]
  exact g.symm (radialCurve (I := I) g p x t)
    (radialCurvTerm (I := I) g p x w t) W

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_component_eq_metricRm04StdAt
    {Idx : Type*} [Finite Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (i : Idx) :
    Tensor0SBundle.component0S (I := I) basis
        (radialCurvTermFlat (I := I) g p x w t) (fun _ : Fin 1 => i) =
      DifferentialGeometry.Geometry.Curvature.metricRm04StdAt
        (I := I) (M := M) g (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (basis i) := by
  rw [Tensor0SBundle.component0S_apply]
  exact radialCurvTermFlat_apply_eq_metricRm04StdAt (I := I) g p x w t (basis i)

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_normSq_eq_cotangentInner
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    Tensor0SBundle.normSq0S (I := I) g (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t) =
      Tensor0SBundle.cotangentInner_gen (I := I) g
        (radialCurve (I := I) g p x t)
        (radialCurvTermFlat (I := I) g p x w t)
        (radialCurvTermFlat (I := I) g p x w t) := by
  rw [Tensor0SBundle.normSq0S_eq_inner,
    Tensor0SBundle.inner0S_one_eq_cotangent]
  rfl

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abs_flat_apply_le_rm04
    {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (W : TangentSpace I (radialCurve (I := I) g p x t)) :
    |radialCurvTermFlat (I := I) g p x w t (fun _ : Fin 1 => W)| ≤
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
      ∏ a : Fin 4, Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          W) a)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          W) a)) := by
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S
    (I := I) g (radialCurve (I := I) g p x t) 4 basis hON
    (DifferentialGeometry.Geometry.Curvature.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t))
    (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
      (radialJacobiField (I := I) g p x w t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      W)
  rw [radialCurvTermFlat_apply_eq_metricRm04StdAt (I := I) g p x w t W]
  simpa [DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_apply] using hCS

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_normSq_le_card
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (B : Real) (hBnn : 0 ≤ B)
    (hB : ∀ i : Idx,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
      ∏ a : Fin 4, Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (basis i)) a)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (basis i)) a)) ≤ B) :
    Tensor0SBundle.normSq0S (I := I) g (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t) ≤
      (Fintype.card (Fin 1 -> Idx) : Real) * B ^ 2 := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) g
        (radialCurve (I := I) g p x t) basis
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
  refine Tensor0SBundle.normSq0S_le_card_of_component_bound
    (I := I) g (radialCurve (I := I) g p x t) 1 basis hinv
    (radialCurvTermFlat (I := I) g p x w t) B hBnn ?_
  intro slots
  have hslots :
      (fun a : Fin 1 => basis (slots a)) =
        (fun _ : Fin 1 => basis (slots 0)) := by
    funext a
    exact congrArg basis (congrArg slots (Subsingleton.elim a (0 : Fin 1)))
  have happly := abs_flat_apply_le_rm04
    (I := I) g p x w t basis hON (basis (slots 0))
  calc
    |Tensor0SBundle.component0S (I := I) basis
        (radialCurvTermFlat (I := I) g p x w t) slots|
        = |radialCurvTermFlat (I := I) g p x w t
            (fun _ : Fin 1 => basis (slots 0))| := by
          rw [Tensor0SBundle.component0S_apply, hslots]
    _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
        ∏ a : Fin 4, Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (basis (slots 0))) a)
          ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (basis (slots 0))) a)) := happly
    _ ≤ B := hB (slots 0)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem radialSlotProd_basis_le
    {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {q : M}
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hON : ∀ i j : Idx,
      g.inner q (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (J V : TangentSpace I q) (i : Idx) :
    ∏ a : Fin 4, Real.sqrt (g.inner q
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          J V V (basis i)) a)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          J V V (basis i)) a)) ≤
      Real.sqrt (g.inner q J J) * (Real.sqrt (g.inner q V V)) ^ 2 := by
  have hunit : Real.sqrt (g.inner q (basis i) (basis i)) = 1 := by
    rw [hON i i]
    simp
  rw [Fin.prod_univ_four]
  simp [DifferentialGeometry.Geometry.Curvature.vec4, hunit, pow_two]
  ring_nf
  exact le_rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem radialSlotBound_basis_le
    {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {q : M}
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hON : ∀ i j : Idx,
      g.inner q (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (R Jb Vb : Real) (hRnn : 0 ≤ R) (hJb : 0 ≤ Jb) (hVb : 0 ≤ Vb)
    (J V : TangentSpace I q)
    (hJ : Real.sqrt (g.inner q J J) ≤ Jb)
    (hV : Real.sqrt (g.inner q V V) ≤ Vb) (i : Idx) :
    R * (∏ a : Fin 4, Real.sqrt (g.inner q
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          J V V (basis i)) a)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          J V V (basis i)) a))) ≤
      R * Jb * Vb ^ 2 := by
  have hprod := radialSlotProd_basis_le (I := I) g basis hON J V i
  have hVsq :
      (Real.sqrt (g.inner q V V)) ^ 2 ≤ Vb ^ 2 := by
    have habs :
        |Real.sqrt (g.inner q V V)| ≤ |Vb| := by
      simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hVb] using hV
    exact sq_le_sq.mpr habs
  have hprod_bound :
      ∏ a : Fin 4, Real.sqrt (g.inner q
          ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            J V V (basis i)) a)
          ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            J V V (basis i)) a)) ≤
        Jb * Vb ^ 2 := by
    calc
      ∏ a : Fin 4, Real.sqrt (g.inner q
          ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            J V V (basis i)) a)
          ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            J V V (basis i)) a))
          ≤ Real.sqrt (g.inner q J J) *
              (Real.sqrt (g.inner q V V)) ^ 2 := hprod
      _ ≤ Jb * Vb ^ 2 := by
          exact mul_le_mul hJ hVsq (sq_nonneg _) hJb
  calc
    R * (∏ a : Fin 4, Real.sqrt (g.inner q
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          J V V (basis i)) a)
        ((DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          J V V (basis i)) a)))
        ≤ R * (Jb * Vb ^ 2) := mul_le_mul_of_nonneg_left hprod_bound hRnn
    _ = R * Jb * Vb ^ 2 := by ring

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_normSq_le_card_of_bounds
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (Jb Vb : Real) (hJb : 0 ≤ Jb) (hVb : 0 ≤ Vb)
    (hJ : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (radialJacobiField (I := I) g p x w t)
      (radialJacobiField (I := I) g p x w t)) ≤ Jb)
    (hV : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb) :
    Tensor0SBundle.normSq0S (I := I) g (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t) ≤
      (Fintype.card (Fin 1 -> Idx) : Real) *
        (Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Jb * Vb ^ 2) ^ 2 := by
  classical
  set R : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Geometry.Curvature.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t)))
  have hRnn : 0 ≤ R := by
    simp [R]
  have hBnn : 0 ≤ R * Jb * Vb ^ 2 :=
    mul_nonneg (mul_nonneg hRnn hJb) (pow_nonneg hVb 2)
  refine radialCurvTermFlat_normSq_le_card
    (I := I) g p x w t basis hON (R * Jb * Vb ^ 2) hBnn ?_
  intro i
  simpa [R] using
    radialSlotBound_basis_le (I := I) g basis hON R Jb Vb hRnn hJb hVb
      (radialJacobiField (I := I) g p x w t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t) hJ hV i


private theorem sqrt_le_sqrt_mul_of_sq_le {A C B : Real}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (h : A ≤ C * B ^ 2) :
    Real.sqrt A ≤ Real.sqrt C * B := by
  calc
    Real.sqrt A ≤ Real.sqrt (C * B ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt C * Real.sqrt (B ^ 2) := Real.sqrt_mul hC _
    _ = Real.sqrt C * B := by rw [Real.sqrt_sq hB]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_sqrt_le_card_of_velocity_bound
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (Vb : Real) (hVb : 0 ≤ Vb)
    (hV : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t)) ≤
      Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
        (Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t)) *
          Vb ^ 2) := by
  classical
  set Jb : Real := Real.sqrt (g.inner (radialCurve (I := I) g p x t)
    (radialJacobiField (I := I) g p x w t)
    (radialJacobiField (I := I) g p x w t))
  set R : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Geometry.Curvature.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t)))
  have hJb : 0 ≤ Jb := by
    simp [Jb]
  have hBnn : 0 ≤ R * Jb * Vb ^ 2 := by
    exact mul_nonneg (mul_nonneg (by simp [R]) hJb) (pow_nonneg hVb 2)
  have hsq := radialCurvTermFlat_normSq_le_card_of_bounds
    (I := I) g p x w t basis hON Jb Vb hJb hVb (by simp [Jb]) hV
  have hcard : 0 ≤ (Fintype.card (Fin 1 -> Idx) : Real) := by
    exact Nat.cast_nonneg _
  simpa [R, Jb] using
    sqrt_le_sqrt_mul_of_sq_le hcard hBnn hsq

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_sqrt_le_K
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (K Vb : Real) (hVb : 0 ≤ Vb)
    (hV : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm :
      Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
        Vb ^ 2 ≤ K) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t)) ≤
      K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) := by
  set Cn : Real := Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real))
  set Rn : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Geometry.Curvature.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t)))
  set Jn : Real := Real.sqrt (g.inner (radialCurve (I := I) g p x t)
    (radialJacobiField (I := I) g p x w t)
    (radialJacobiField (I := I) g p x w t))
  have hbase := radialCurvTermFlat_sqrt_le_card_of_velocity_bound
    (I := I) g p x w t basis hON Vb hVb hV
  have hcoef : Cn * Rn * Vb ^ 2 ≤ K := by
    simpa [Cn, Rn] using hRm
  have hJn : 0 ≤ Jn := by
    simp [Jn]
  have hstep : Cn * (Rn * Jn * Vb ^ 2) ≤ K * Jn := by
    calc
      Cn * (Rn * Jn * Vb ^ 2) = (Cn * Rn * Vb ^ 2) * Jn := by ring
      _ ≤ K * Jn := mul_le_mul_of_nonneg_right hcoef hJn
  exact hbase.trans (by simpa [Cn, Rn, Jn] using hstep)

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_flat_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo (0 : Real) b,
      Real.sqrt (Tensor0SBundle.cotangentInner_gen (I := I) g
        (radialCurve (I := I) g p x t)
        (radialCurvTermFlat (I := I) g p x w t)
        (radialCurvTermFlat (I := I) g p x w t)) ≤
        K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  exact inner_sq_le_of_sqrt_le (I := I) g hK
    (by
      have h := hcurv t ht
      rw [radialCurvTermFlat_inner] at h
      exact h)

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_fiber_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo (0 : Real) b,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t)) ≤
        K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  refine curv_sq_of_flat_Ioo (I := I) g p x w hK ?_
  intro t ht
  simpa [radialCurvTermFlat_normSq_eq_cotangentInner]
    using hcurv t ht

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_rm04_velocity_Ioo
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K Vb b : Real}
    (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (basis : ∀ t : Real, t ∈ Ioo (0 : Real) b →
      Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ t (ht : t ∈ Ioo (0 : Real) b) i j,
      g.inner (radialCurve (I := I) g p x t) (basis t ht i) (basis t ht j) =
        if i = j then (1 : Real) else 0)
    (hV : ∀ t (_ht : t ∈ Ioo (0 : Real) b),
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm : ∀ t (_ht : t ∈ Ioo (0 : Real) b),
      Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
        Vb ^ 2 ≤ K) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  refine curv_sq_of_fiber_Ioo (I := I) g p x w hK ?_
  intro t ht
  exact radialCurvTermFlat_sqrt_le_K
    (I := I) g p x w t (basis t ht) (hON t ht) K Vb hVb
    (hV t ht) (hRm t ht)

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_norm_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo (0 : Real) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)) ≤
        K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  exact inner_sq_le_of_sqrt_le (I := I) g hK (hcurv t ht)

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_curvNorm
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : Real},
      0 ≤ K → b ≤ 1 →
      (∀ t ∈ Ioo (0 : Real) b,
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialCurvTerm (I := I) g p x w t)
          (radialCurvTerm (I := I) g p x w t)) ≤
          K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t))) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hK hb hcurv h0
  exact hODE x w hx hw hb (curv_sq_of_norm_Ioo (I := I) g p x w hK hcurv) h0

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_flat
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : Real},
      0 ≤ K → b ≤ 1 →
      (∀ t ∈ Ioo (0 : Real) b,
        Real.sqrt (Tensor0SBundle.cotangentInner_gen (I := I) g
          (radialCurve (I := I) g p x t)
          (radialCurvTermFlat (I := I) g p x w t)
          (radialCurvTermFlat (I := I) g p x w t)) ≤
          K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t))) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hK hb hcurv h0
  exact hODE x w hx hw hb (curv_sq_of_flat_Ioo (I := I) g p x w hK hcurv) h0

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_fiber
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : Real},
      0 ≤ K → b ≤ 1 →
      (∀ t ∈ Ioo (0 : Real) b,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 1
          (radialCurvTermFlat (I := I) g p x w t)) ≤
          K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t))) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico_of_flat (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hK hb hcurv h0
  refine hODE x w hx hw hK hb ?_ h0
  intro t ht
  simpa [radialCurvTermFlat_normSq_eq_cotangentInner]
    using hcurv t ht

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04_velocity
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      (basis : ∀ t : Real, t ∈ Ioo (0 : Real) b →
        Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t))) →
      (∀ t (ht : t ∈ Ioo (0 : Real) b) i j,
        g.inner (radialCurve (I := I) g p x t) ((basis t ht) i) ((basis t ht) j) =
          if i = j then (1 : Real) else 0) →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb) →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Vb ^ 2 ≤ K) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K Vb b hK hVb hb basis hON hV hRm h0
  exact hODE x w hx hw hb
    (curv_sq_of_rm04_velocity_Ioo (I := I) g p x w hK hVb basis hON hV hRm) h0

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04_launch
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      (basis : ∀ t : Real, t ∈ Ioo (0 : Real) b →
        Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t))) →
      (∀ t (ht : t ∈ Ioo (0 : Real) b) i j,
        g.inner (radialCurve (I := I) g p x t) ((basis t ht) i) ((basis t ht) j) =
          if i = j then (1 : Real) else 0) →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Vb ^ 2 ≤ K) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r₀, hr₀, hODE⟩ := exists_ode_Ico_of_rm04_velocity (I := I) (Idx := Idx) g p
  refine ⟨min r₀ (expMapC2Radius (I := I) g p),
    lt_min hr₀ (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
      (I := I) g p), ?_⟩
  intro x w hx hw K Vb b hK hVb hb hlaunch basis hON hRm h0
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hw₀ : ‖w‖ < r₀ := lt_of_lt_of_le hw (min_le_left _ _)
  have hxExp : ‖x‖ < expMapC2Radius (I := I) g p :=
    lt_of_lt_of_le hx (min_le_right _ _)
  exact hODE x w hx₀ hw₀ hK hVb hb basis hON
    (radial_speed_le (I := I) g p x hxExp hb hlaunch) hRm h0

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Vb ^ 2 ≤ K) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  classical
  obtain ⟨r, hr, hODE⟩ :=
    exists_ode_Ico_of_rm04_launch (I := I) (Idx := Fin (Module.finrank ℝ E)) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K Vb b hK hVb hb hlaunch hRm h0
  have hbasis :
      ∀ t : Real, t ∈ Ioo (0 : Real) b →
        ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
            (TangentSpace I (radialCurve (I := I) g p x t)),
          ∀ i j,
            g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
              if i = j then (1 : Real) else 0 := by
    intro t _ht
    exact exists_gON_tangentBasis_E (I := I) g (radialCurve (I := I) g p x t)
  choose basis hON using hbasis
  exact hODE x w hx hw hK hVb hb hlaunch basis
    (fun t ht i j => hON t ht i j) hRm h0

omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04_norm
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico_of_rm04 (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm h0
  refine hODE x w hx hw hK hVb hb hlaunch ?_ h0
  intro t ht
  set C : Real := Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real))
    with hC_def
  set A : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Geometry.Curvature.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t))) with hA_def
  have hCnn : 0 ≤ C := by rw [hC_def]; exact Real.sqrt_nonneg _
  have hVsq : 0 ≤ Vb ^ 2 := sq_nonneg Vb
  have hA_le_R : A ≤ R := by rw [hA_def]; exact hRm t ht
  have hmul : C * A * Vb ^ 2 ≤ C * R * Vb ^ 2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA_le_R hCnn) hVsq
  exact le_trans hmul hKbound

omit [SigmaCompactSpace M] in
theorem exists_ode_rm04_d2
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) 0 = 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico_of_rm04_norm (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm hD2
  refine hODE x w hx hw hK hVb hb hlaunch hKbound hRm ?_
  rw [hD2, radialJacobi_zero]
  change
    g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) ≤
      K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
  have hz :
      g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) = 0 := by
    rw [map_zero]
  rw [hz]
  rw [mul_zero]

omit [SigmaCompactSpace M] in
theorem exists_ode_rm04_jac0
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_rm04_d2 (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm hJac0
  exact hODE x w hx hw hK hVb hb hlaunch hKbound hRm
    (d2_zero_of_jac0 (I := I) g p x w hJac0)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_ode_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r₀, hr₀, hODE⟩ := exists_ode_rm04_jac0 (I := I) g p
  obtain ⟨r₁, hr₁, hJac0⟩ :=
    exists_radialJacobi_zero_radius (I := I) g hEnorm p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hw₀ : ‖w‖ < r₀ := lt_of_lt_of_le hw (min_le_left _ _)
  have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
  have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_right _ _)
  have hJac0' :
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 := by
    simpa [radialCurve] using hJac0 x w hx₁ hw₁
  exact hODE x w hx₀ hw₀ hK hVb hb hlaunch hKbound hRm hJac0'

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_rm04_data
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t) t) ∧
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r₀, hr₀, hdiff⟩ := exists_radialJacobi_diff (I := I) g p
  obtain ⟨r₁, hr₁, hODE⟩ := exists_ode_rm04 (I := I) g hEnorm p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hw₀ : ‖w‖ < r₀ := lt_of_lt_of_le hw (min_le_left _ _)
  have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
  have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_right _ _)
  exact ⟨(hdiff x w hx₀ hw₀ hb).1, (hdiff x w hx₀ hw₀ hb).2,
    hODE x w hx₁ hw₁ hK hVb hb hlaunch hKbound hRm⟩

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_rm04_basis
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t) ∧
      (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t) ∧
      ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t) := by
  obtain ⟨r, hr, hdata⟩ := exists_rm04_data (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b hK hVb hb hsmall hlaunch hKbound hRm
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (hdata x (a • (chartModelBasis E) k) hx (hsmall k)
      hK hVb hb hlaunch hKbound hRm).1
  · intro k
    exact (hdata x (a • (chartModelBasis E) k) hx (hsmall k)
      hK hVb hb hlaunch hKbound hRm).2.1
  · intro k
    exact (hdata x (a • (chartModelBasis E) k) hx (hsmall k)
      hK hVb hb hlaunch hKbound hRm).2.2

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_rm04_pack
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧
      (∀ x : E, ‖x‖ < r →
        ∀ {a K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
        Real.sqrt (g.inner p x x) ≤ Vb →
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
            R * Vb ^ 2 ≤ K →
        (∀ t (_ht : t ∈ Ioo (0 : Real) b),
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
        (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
          DifferentiableAt ℝ
            (chartRepAt (I := I) (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t) ∧
        (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
          DifferentiableAt ℝ
            (chartRepAt (I := I) (radialCurve (I := I) g p x)
              (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t) ∧
        ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : Real) b,
          g.inner (radialCurve (I := I) g p x t)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
          ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)) ∧
      (∀ x w : E, ‖x‖ < r → ‖w‖ < r →
        (covDerivAlong (I := I) g
          (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
          (radialJacobiField (I := I) g p x w) 0 : E) = w) := by
  obtain ⟨r₀, hr₀, hdata⟩ := exists_rm04_basis (I := I) g hEnorm p
  obtain ⟨r₁, hr₁, hderiv⟩ := exists_radialJacobi_deriv_radius (I := I) g p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_, ?_⟩
  · intro x hx a K R Vb b hK hVb hb hsmall hlaunch hKbound hRm
    have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
    refine hdata x hx₀ hK hVb hb ?_ hlaunch hKbound hRm
    intro k
    exact lt_of_lt_of_le (hsmall k) (min_le_left _ _)
  · intro x w hx hw
    have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
    have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_right _ _)
    exact hderiv x w hx₁ hw₁

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem rm04_Ioo_of_region
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {R b : Real} {U : Set M}
    (hcurve : ∀ t : Real, t ∈ Ioo (0 : Real) b →
      radialCurve (I := I) g p x t ∈ U)
    (hRmU : ∀ q : M, q ∈ U →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q)) ≤ R) :
    ∀ t (_ht : t ∈ Ioo (0 : Real) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R := by
  intro t ht
  exact hRmU _ (hcurve t ht)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_ode_rm04_on
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    (∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) →
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real} {U : Set M}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t : Real, t ∈ Ioo (0 : Real) b →
        radialCurve (I := I) g p x t ∈ U) →
      (∀ q : M, q ∈ U →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ R) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  intro hEnorm
  obtain ⟨r, hr, hODE⟩ := exists_ode_rm04 (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b U hK hVb hb hlaunch hKbound hcurve hRmU
  exact hODE x w hx hw hK hVb hb hlaunch hKbound
    (rm04_Ioo_of_region (I := I) g p x hcurve hRmU)

omit [SigmaCompactSpace M] in
theorem exists_ode_expBall
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b ρ : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 → ‖x‖ < ρ →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ q : M, q ∈
        (fun v : TangentSpace I p => expMap (I := I) g p v) ''
          {v : TangentSpace I p | ‖v‖ < ρ} →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ R) →
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_rm04_jac0 (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b ρ hK hVb hb hxρ hlaunch hKbound hRm hJac0
  exact hODE x w hx hw hK hVb hb hlaunch hKbound
    (rm04_Ioo_of_region (I := I) g p x
      (radial_mem_expBall (I := I) g p x hxρ hb) hRm) hJac0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem rm04Exp_of_global
    (g : SmoothRiemannianMetric I M) (p : M) {R ρ : Real}
    (hRm : ∀ q : M,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q)) ≤ R) :
    ∀ q : M, q ∈
      (fun v : TangentSpace I p => expMap (I := I) g p v) ''
        {v : TangentSpace I p | ‖v‖ < ρ} →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q)) ≤ R := by
  intro q _hq
  exact hRm q

omit [SigmaCompactSpace M] in
theorem exists_ode_global
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b ρ : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 → ‖x‖ < ρ →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ R) →
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_expBall (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b ρ hK hVb hb hxρ hlaunch hKbound hRm hJac0
  exact hODE x w hx hw hK hVb hb hxρ hlaunch hKbound
    (rm04Exp_of_global (I := I) g p hRm) hJac0


end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
