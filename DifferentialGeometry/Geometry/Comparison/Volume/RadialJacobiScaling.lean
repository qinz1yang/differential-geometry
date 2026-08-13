import DifferentialGeometry.Geometry.Comparison.Volume.RadialJacobiBounds
open DifferentialGeometry.Geometry.Curvature

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma sqrt_inner_le_of_smul_le
    (g : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q)
    {a B : ℝ} (ha : 0 < a)
    (h : Real.sqrt (g.inner q (a • v) (a • v)) ≤ a * B) :
    Real.sqrt (g.inner q v v) ≤ B := by
  have hscale :
      g.inner q (a • v) (a • v) = a ^ 2 * g.inner q v v := by
    rw [map_smul (g.inner q), ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hsqrt :
      Real.sqrt (a ^ 2 * g.inner q v v) =
        a * Real.sqrt (g.inner q v v) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hscale, hsqrt] at h
  exact (le_of_mul_le_mul_left h ha)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma le_sqrt_inner_of_smul_ge
    (g : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q)
    {a B : ℝ} (ha : 0 < a)
    (h : a * B ≤ Real.sqrt (g.inner q (a • v) (a • v))) :
    B ≤ Real.sqrt (g.inner q v v) := by
  have hscale :
      g.inner q (a • v) (a • v) = a ^ 2 * g.inner q v v := by
    rw [map_smul (g.inner q), ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hsqrt :
      Real.sqrt (a ^ 2 * g.inner q v v) =
        a * Real.sqrt (g.inner q v v) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hscale, hsqrt] at h
  exact le_of_mul_le_mul_left h ha

omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one_le_of_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a B : ℝ} (ha : 0 < a)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hscaled :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1)) ≤ a * B) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hsmul := radialJacobi_one_smul (I := I) g p x w a hxrad
  rw [hsmul] at hscaled
  exact sqrt_inner_le_of_smul_le (I := I) g
    (expMap (I := I) g p (show TangentSpace I p from x))
    (radialJacobiField (I := I) g p x w 1) ha hscaled

omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one_ge_of_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a B : ℝ} (ha : 0 < a)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hscaled :
      a * B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1))) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hsmul := radialJacobi_one_smul (I := I) g p x w a hxrad
  rw [hsmul] at hscaled
  exact le_sqrt_inner_of_smul_ge (I := I) g
    (expMap (I := I) g p (show TangentSpace I p from x))
    (radialJacobiField (I := I) g p x w 1) ha hscaled

private noncomputable def basisNormSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma basisNormSup_nonneg : 0 ≤ basisNormSup (E := E) := by
  classical
  unfold basisNormSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  have hnn : (0 : ℝ) ≤ ‖(chartModelBasis E) k₀‖ := norm_nonneg _
  exact hnn.trans (Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma norm_basis_le_sup
    (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ basisNormSup (E := E) := by
  classical
  unfold basisNormSup
  exact Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖)
    (Finset.mem_univ _)

lemma basisScaleSmall {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r := by
  classical
  set C : ℝ := basisNormSup (E := E) with hC
  have hC_nonneg : 0 ≤ C := by
    simpa [hC] using basisNormSup_nonneg (E := E)
  have hden_pos : 0 < C + 1 := by linarith
  refine ⟨r / (C + 1), div_pos hr hden_pos, ?_⟩
  intro k
  have hscale_pos : 0 < r / (C + 1) := div_pos hr hden_pos
  have hk_le : ‖(chartModelBasis E) k‖ ≤ C := by
    simpa [hC] using norm_basis_le_sup (E := E) k
  have hk_lt : ‖(chartModelBasis E) k‖ < C + 1 := lt_of_le_of_lt hk_le (by linarith)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale_pos]
  calc
    r / (C + 1) * ‖(chartModelBasis E) k‖
        < r / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left hk_lt hscale_pos
    _ = r := by field_simp [ne_of_gt hden_pos]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma scaleSmall_of_le {a b r : ℝ} {v : E}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hsmall : ‖b • v‖ < r) :
    ‖a • v‖ < r := by
  rw [norm_smul] at hsmall
  rw [norm_smul]
  have habs : ‖a‖ ≤ ‖b‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    exact hab
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right habs (norm_nonneg v)) hsmall

lemma basisUnitScaleSmall {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) ∧
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) := by
  obtain ⟨ab, hab_pos, hbasis⟩ := basisScaleSmall (E := E) hr
  obtain ⟨ad, had_pos, hdir⟩ := unitDirScaleSmall (E := E) hr
  refine ⟨min ab ad, lt_min hab_pos had_pos, ?_, ?_⟩
  · intro k
    exact scaleSmall_of_le
      (v := (chartModelBasis E) k)
      (le_of_lt (lt_min hab_pos had_pos))
      (le_of_lt hab_pos)
      (min_le_left ab ad)
      (hbasis k)
  · intro v hv
    exact scaleSmall_of_le
      (v := ∑ i, v i • (chartModelBasis E) i)
      (le_of_lt (lt_min hab_pos had_pos))
      (le_of_lt had_pos)
      (min_le_right ab ad)
      (hdir v hv)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
lemma basisInit_smul_le
    (g : SmoothRiemannianMetric I M) (p : M) {a A : ℝ} (ha : 0 < a)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤
        a * A := by
  intro k
  let v : TangentSpace I p := (chartModelBasis E) k
  have hscale :
      g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k) =
        a ^ 2 * g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k) := by
    have hscale_v : g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v := by
      rw [map_smul (g.inner p), ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      ring
    change g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v
    exact hscale_v
  have hsqrt :
      Real.sqrt (a ^ 2 * g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) =
        a * Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hscale, hsqrt]
  exact mul_le_mul_of_nonneg_left (hbasis k) ha.le

lemma model_le_smul {a K b A B : ℝ} (ha : 0 < a)
    (hmodel : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    a * A + gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 ≤ a * B := by
  have herr :
      gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 =
        a * gronwallBound 0 (max K 1) (K * (b * A)) 1 := by
    have heps : K * (b * (a * A)) = a * (K * (b * A)) := by ring
    rw [heps, gronwallBound_zero_mul_eps]
  rw [herr]
  have hmul := mul_le_mul_of_nonneg_left hmodel ha.le
  nlinarith


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
lemma basisModel_le_smul
    (g : SmoothRiemannianMetric I M) (p : M) {a K b A B : ℝ} (ha : 0 < a)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    (∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤
        a * A) ∧
    a * A + gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 ≤ a * B := by
  exact ⟨basisInit_smul_le (I := I) g p ha hbasis, model_le_smul ha hmodel⟩


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_deriv_eq_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_init_bound_at (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    (radialJacobi_init_le_of_deriv_eq (I := I) g p x hderiv hbasis) hmodel

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_deriv_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_deriv_eq_at (I := I) g p x hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    hderiv hbasis hmodel


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_radius_deriv_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {r K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_deriv_eq_at (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    (fin_deriv_radius (I := I) g p x hderivRadius hx hbasisSmall)
    hbasis hmodel

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_radius_deriv
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {r K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_radius_deriv_at (I := I) g p x hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hbasisSmall hbasis hmodel

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_le_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hinit : Real.sqrt (g.inner p (a • w) (a • w)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hderiv :
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x (a • w)) 0 : E) = a • w := by
    simpa [radialCurve] using hderivRadius x (a • w) hx hwsmall
  have hscaled :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1)) ≤ a * B := by
    refine radialJacobi_one_le_at (I := I) g p x (a • w) hK hb h1b hγ hcard F hpar hON
      hFdiff hJdiff hDJdiff hODE ?_
    set vnorm : ℝ :=
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) 0))
    have hvA : vnorm ≤ A := by
      have hraw :
          Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • w)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • w)) 0)) ≤ A := by
        rw [radialCurve_zero (I := I) g p x]
        rw [hderiv]
        exact hinit
      simpa [vnorm] using hraw
    have heps :
        K * (b * vnorm) ≤ K * (b * A) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvA hb) hK
    have hmax : 0 ≤ max K 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
    have hgb :
        gronwallBound 0 (max K 1) (K * (b * vnorm)) 1 ≤
          gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
      gronwallBound_zero_mono_eps hmax (by norm_num) heps
    calc
      vnorm + gronwallBound 0 (max K 1) (K * (b * vnorm)) 1
          ≤ A + gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
            add_le_add hvA hgb
      _ ≤ a * B := hmodel
  exact radialJacobi_one_le_of_smul (I := I) g p x w ha hxrad hscaled

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_le_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hinit : Real.sqrt (g.inner p (a • w) (a • w)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B :=
  radialJacobi_one_le_of_scaled_radius_at (I := I) g p x w ha hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hwsmall hinit hmodel hxrad

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_ge_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hmodel :
      a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hderiv :
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x (a • w)) 0 : E) = a • w := by
    simpa [radialCurve] using hderivRadius x (a • w) hx hwsmall
  have hscaled :
      a * B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1)) := by
    refine radialJacobi_one_ge_at (I := I) g p x (a • w) hK hb h1b hγ hcard F hpar hON
      hFdiff hJdiff hDJdiff hODE ?_
    rw [radialCurve_zero (I := I) g p x]
    rw [hderiv]
    exact hmodel
  exact radialJacobi_one_ge_of_smul (I := I) g p x w ha hxrad hscaled

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_ge_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hmodel :
      a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) :=
  radialJacobi_one_ge_of_scaled_radius_at (I := I) g p x w ha hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hwsmall hmodel hxrad

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_dir_ge_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b B : ℝ} (ha : 0 < a) (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r)
    (hmodel : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) := by
  intro v hv
  set w : E := ∑ i, v i • (chartModelBasis E) i with hw
  have hsqrt :
      B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x w 1)
        (radialJacobiField (I := I) g p x w 1)) := by
    exact radialJacobi_one_ge_of_scaled_radius_at (I := I) g p x w ha hK hb h1b hγ
      hcard F hpar hON hFdiff (hJdiff v hv) (hDJdiff v hv) (hODE v hv)
      hderivRadius hx (by simpa [hw] using hscaledSmall v hv)
      (by simpa [hw] using hmodel v hv) hxrad
  set q := expMap (I := I) g p (show TangentSpace I p from x) with hq
  set J : TangentSpace I q := radialJacobiField (I := I) g p x w 1 with hJdef
  have hsq : B ^ 2 ≤ (Real.sqrt (g.inner q J J)) ^ 2 := by
    exact (sq_le_sq₀ hB_nonneg (Real.sqrt_nonneg _)).2 (by simpa [q, J] using hsqrt)
  have hJ_nonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      have hzero :
          (g.inner q) (0 : TangentSpace I q) = (0 : TangentSpace I q →L[ℝ] ℝ) :=
        map_zero (g.inner q)
      rw [hzero]
      rfl
    · exact (g.pos q J hJ).le
  simpa [q, J, hw] using hsq.trans_eq (Real.sq_sqrt hJ_nonneg)

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_dir_ge_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b B : ℝ} (ha : 0 < a) (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r)
    (hmodel : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) :=
  radialJacobi_dir_ge_of_scaled_radius_at (I := I) g p x ha hB_nonneg hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hscaledSmall hmodel hxrad

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma model_ge_of_smul
    (g : SmoothRiemannianMetric I M) (p : M) (w : E)
    {a K b B : ℝ} (ha : 0 < a)
    (hmodel :
      B ≤ Real.sqrt (g.inner p w w) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p w w))) 1) :
    a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
        gronwallBound 0 (max K 1)
          (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1 := by
  set s : ℝ := Real.sqrt (g.inner p w w) with hs
  have hsqrt :
      Real.sqrt (g.inner p (a • w) (a • w)) = a * s := by
    have hscale :
        g.inner p (a • w) (a • w) = a ^ 2 * g.inner p w w := by
      let v : TangentSpace I p := w
      have hscale_v : g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v := by
        rw [map_smul (g.inner p), ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
        ring
      change g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v
      exact hscale_v
    rw [hscale, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha, hs]
  have herr :
      gronwallBound 0 (max K 1) (K * (b * (a * s))) 1 =
        a * gronwallBound 0 (max K 1) (K * (b * s)) 1 := by
    have heps : K * (b * (a * s)) = a * (K * (b * s)) := by ring
    rw [heps, gronwallBound_zero_mul_eps]
  rw [hsqrt, herr]
  have hmul := mul_le_mul_of_nonneg_left hmodel ha.le
  nlinarith


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
lemma dirModel_ge_smul
    (g : SmoothRiemannianMetric I M) (p : M)
    {a K b B : ℝ} (ha : 0 < a)
    (hmodel : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1 := by
  intro v hv
  exact model_ge_of_smul (I := I) g p (∑ i, v i • (chartModelBasis E) i) ha
    (hmodel v hv)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
lemma dirModel_ge_of_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    {K b B₀ D B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hlo : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B₀ ≤ Real.sqrt
        (g.inner p (∑ i, v i • (chartModelBasis E) i)
          (∑ i, v i • (chartModelBasis E) i)))
    (hhi : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      Real.sqrt
        (g.inner p (∑ i, v i • (chartModelBasis E) i)
          (∑ i, v i • (chartModelBasis E) i)) ≤ D)
    (hsmall :
      B ≤ B₀ - gronwallBound 0 (max K 1) (K * (b * D)) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1 := by
  intro v hv
  set s : ℝ := Real.sqrt
    (g.inner p (∑ i, v i • (chartModelBasis E) i)
      (∑ i, v i • (chartModelBasis E) i)) with hs
  have hslo : B₀ ≤ s := by
    simpa [s] using hlo v hv
  have hshi : s ≤ D := by
    simpa [s] using hhi v hv
  have heps : K * (b * s) ≤ K * (b * D) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshi hb) hK
  have hmax : 0 ≤ max K 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
  have hgb :
      gronwallBound 0 (max K 1) (K * (b * s)) 1 ≤
        gronwallBound 0 (max K 1) (K * (b * D)) 1 :=
    gronwallBound_zero_mono_eps hmax (by norm_num) heps
  nlinarith

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
lemma exists_dirModel_ge
    (g : SmoothRiemannianMetric I M) (p : M)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1 := by
  rcases exists_unitCoeff_bounds (I := I) g p with
    ⟨B₀, D, hB₀_pos, hD_nonneg, hlo, hhi⟩
  rcases exists_gron_small hB₀_pos hK hD_nonneg with ⟨b, B, hb_pos, hB_pos, hsmall⟩
  refine ⟨b, B, hb_pos, hB_pos, ?_⟩
  exact dirModel_ge_of_bounds (I := I) g p hK hb_pos.le hlo hhi hsmall

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
lemma exists_dirModel_ge1
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ {k : ℝ}, 0 ≤ k → k ≤ K →
        ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          B ≤ Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)) -
              gronwallBound 0 (max k 1)
                (k * Real.sqrt
                  (g.inner p (∑ i, v i • (chartModelBasis E) i)
                    (∑ i, v i • (chartModelBasis E) i))) 1 := by
  rcases exists_unitCoeff_bounds (I := I) g p with
    ⟨B₀, D, hB₀_pos, hD_nonneg, hlo, hhi⟩
  rcases exists_gron_smallK hB₀_pos hD_nonneg with ⟨K, B, hK_pos, hB_pos, hsmall⟩
  refine ⟨K, B, hK_pos, hB_pos, ?_⟩
  intro k hk_nonneg hk_le v hv
  set s : ℝ := Real.sqrt
    (g.inner p (∑ i, v i • (chartModelBasis E) i)
      (∑ i, v i • (chartModelBasis E) i)) with hs
  have hslo : B₀ ≤ s := by
    simpa [s] using hlo v hv
  have hshi : s ≤ D := by
    simpa [s] using hhi v hv
  have hsmall' :
      B ≤ B₀ - gronwallBound 0 (max k 1) (k * D) 1 :=
    hsmall hk_nonneg hk_le
  have heps : k * s ≤ k * D := mul_le_mul_of_nonneg_left hshi hk_nonneg
  have hmax : 0 ≤ max k 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
  have hgb :
      gronwallBound 0 (max k 1) (k * s) 1 ≤
        gronwallBound 0 (max k 1) (k * D) 1 :=
    gronwallBound_zero_mono_eps hmax (by norm_num) heps
  nlinarith

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_fin_le_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  intro k
  exact radialJacobi_one_le_of_scaled_radius_at (I := I) g p x ((chartModelBasis E) k)
    ha hK hb h1b hγ hcard F hpar hON hFdiff (hJdiff k) (hDJdiff k) (hODE k)
    hderivRadius hx (hscaledSmall k) (hinit k) hmodel hxrad

omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_fin_le_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_scaled_radius_at (I := I) g p x ha hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hscaledSmall hinit hmodel hxrad

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_fin_le_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b → b ≤ 1 →
      (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ t ∈ Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  obtain ⟨r, hr, hdata, hderiv⟩ := exists_rm04_pack (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodel hxrad
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  obtain ⟨hJdiff, hDJdiff, hODE⟩ :=
    hdata x hx hK hVb hb1 hsmall hlaunch hKbound hRm
  exact radialJacobi_fin_le_of_scaled_radius_at (I := I) g p x ha hK hb0 h1b hγ
    hcard F hpar hON hFdiff hJdiff hDJdiff hODE hderiv hx hsmall hinit hmodel hxrad

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_fin_le_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b → b ≤ 1 →
      (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  obtain ⟨r, hr, h⟩ := exists_fin_le_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodel hxrad
  exact h x hx ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hinit hmodel hxrad

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_dir_ge_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b B : ℝ}, 0 < a → 0 ≤ B → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ t ∈ Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1) := by
  obtain ⟨r₀, hr₀, hdata⟩ := exists_rm04_data (I := I) g hEnorm p
  obtain ⟨r₁, hr₁, hderiv⟩ := exists_radialJacobi_deriv_radius (I := I) g p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro x hx a K R Vb b B ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hmodel hxrad
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
  have hderiv' : ∀ x w : E, ‖x‖ < min r₀ r₁ → ‖w‖ < min r₀ r₁ →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w := by
    intro y z hy hz
    exact hderiv y z (lt_of_lt_of_le hy (min_le_right _ _))
      (lt_of_lt_of_le hz (min_le_right _ _))
  refine radialJacobi_dir_ge_of_scaled_radius_at (I := I) g p x ha hB hK hb0 h1b hγ
    hcard F hpar hON hFdiff ?_ ?_ ?_ hderiv' hx hsmall hmodel hxrad
  · intro v hv
    exact (hdata x (a • (∑ i, v i • (chartModelBasis E) i)) hx₀
      (lt_of_lt_of_le (hsmall v hv) (min_le_left _ _))
      hK hVb hb1 hlaunch hKbound hRm).1
  · intro v hv
    exact (hdata x (a • (∑ i, v i • (chartModelBasis E) i)) hx₀
      (lt_of_lt_of_le (hsmall v hv) (min_le_left _ _))
      hK hVb hb1 hlaunch hKbound hRm).2.1
  · intro v hv
    exact (hdata x (a • (∑ i, v i • (chartModelBasis E) i)) hx₀
      (lt_of_lt_of_le (hsmall v hv) (min_le_left _ _))
      hK hVb hb1 hlaunch hKbound hRm).2.2

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_dir_ge_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b B : ℝ}, 0 < a → 0 ≤ B → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1) := by
  obtain ⟨r, hr, h⟩ := exists_dir_ge_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b B ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hmodel hxrad
  exact h x hx ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hmodel hxrad

end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
