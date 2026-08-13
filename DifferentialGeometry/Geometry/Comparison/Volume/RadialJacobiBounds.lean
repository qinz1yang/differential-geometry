import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall

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

private noncomputable def coeffModelCLM :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E :=
  (toEuclidean (E := E)).symm.toContinuousLinearMap

omit [NeZero (Module.finrank ℝ E)] in
private lemma coeffModelCLM_eq_sum
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    coeffModelCLM (E := E) v = ∑ i, v i • (chartModelBasis E) i := by
  have hvsum : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    let b := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
    simpa [b, EuclideanSpace.basisFun_apply] using (b.sum_repr v).symm
  calc
    coeffModelCLM (E := E) v =
        (toEuclidean (E := E)).symm v := rfl
    _ = (toEuclidean (E := E)).symm (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) := by
          exact congrArg (toEuclidean (E := E)).symm hvsum
    _ = ∑ i, v i • (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
          rw [map_sum]
          simp only [map_smul]
    _ = ∑ i, v i • (chartModelBasis E) i := by
          simp only [chartModelBasis_apply]

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
private lemma sqrt_coercive_mul_norm_le
    (g : SmoothRiemannianMetric I M) (p : M)
    (x : E) :
    Real.sqrt (gpCoerciveConst (I := I) g p) * ‖x‖ ≤
      Real.sqrt (g.inner p x x) := by
  have hc_pos : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  have hcoerc : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
    gpCoerciveConst_le (I := I) g p x
  have hlhs_eq : Real.sqrt (gpCoerciveConst (I := I) g p) * ‖x‖ =
      Real.sqrt (gpCoerciveConst (I := I) g p * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul hc_pos.le, Real.sqrt_sq (norm_nonneg x)]
  rw [hlhs_eq]
  exact Real.sqrt_le_sqrt hcoerc

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma inner_le_opNorm_sq
    (g : SmoothRiemannianMetric I M) (p : M)
    (x : E) :
    g.inner p x x ≤ ‖g.inner p‖ * ‖x‖ ^ 2 := by
  have hlin : ‖(g.inner p) x‖ ≤ ‖g.inner p‖ * ‖x‖ :=
    (g.inner p).le_opNorm x
  have happ : ‖((g.inner p) x) x‖ ≤ ‖(g.inner p) x‖ * ‖x‖ :=
    ((g.inner p) x).le_opNorm x
  have hmul :
      ‖((g.inner p) x) x‖ ≤ (‖g.inner p‖ * ‖x‖) * ‖x‖ :=
    happ.trans (mul_le_mul_of_nonneg_right hlin (norm_nonneg x))
  have hself : g.inner p x x ≤ ‖((g.inner p) x) x‖ := by
    exact Real.le_norm_self _
  calc
    g.inner p x x ≤ ‖((g.inner p) x) x‖ := hself
    _ ≤ (‖g.inner p‖ * ‖x‖) * ‖x‖ := hmul
    _ = ‖g.inner p‖ * ‖x‖ ^ 2 := by ring

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem exists_unitCoeff_ge
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ B : ℝ, 0 < B ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) := by
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)).toContinuousLinearMap
  let K : ℝ := ‖L‖ + 1
  let B : ℝ := Real.sqrt (gpCoerciveConst (I := I) g p) / K
  have hc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g p) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p)
  have hden_pos : 0 < K := by
    have hL_nonneg : 0 ≤ ‖L‖ := norm_nonneg L
    linarith
  refine ⟨B, div_pos hc_pos hden_pos, ?_⟩
  intro v hv
  have hanti :=
    (ContinuousLinearEquiv.antilipschitz ((toEuclidean (E := E)).symm)).le_mul_dist v 0
  have hunit_le :
      1 ≤ K * ‖coeffModelCLM (E := E) v‖ := by
    simp only [map_zero, dist_zero_right] at hanti
    rw [hv] at hanti
    have hK0_le : (↑‖L‖₊ : ℝ) ≤ K := by
      simp [K, L]
    have hanti' : 1 ≤ (↑‖L‖₊ : ℝ) * ‖coeffModelCLM (E := E) v‖ := by
      simpa [L, coeffModelCLM] using hanti
    exact hanti'.trans
      (mul_le_mul_of_nonneg_right hK0_le (norm_nonneg _))
  have hnorm_lower : 1 / K ≤ ‖coeffModelCLM (E := E) v‖ := by
    exact (div_le_iff₀ hden_pos).2 (by rwa [mul_comm])
  have hmetric := sqrt_coercive_mul_norm_le (I := I) g p (coeffModelCLM (E := E) v)
  have hB_le :
      B ≤ Real.sqrt (gpCoerciveConst (I := I) g p) * ‖coeffModelCLM (E := E) v‖ := by
    dsimp [B]
    rw [div_eq_mul_inv]
    have hnorm_inv : K⁻¹ ≤ ‖coeffModelCLM (E := E) v‖ := by
      simpa [one_div] using hnorm_lower
    exact mul_le_mul_of_nonneg_left hnorm_inv hc_pos.le
  calc
    B ≤ Real.sqrt (gpCoerciveConst (I := I) g p) * ‖coeffModelCLM (E := E) v‖ := hB_le
    _ ≤ Real.sqrt (g.inner p (coeffModelCLM (E := E) v) (coeffModelCLM (E := E) v)) :=
        hmetric
    _ = Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) := by
        rw [coeffModelCLM_eq_sum (E := E) v]
        rfl


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem exists_unitCoeff_le
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) ≤ D := by
  let C : ℝ := ‖coeffModelCLM (E := E)‖
  let D : ℝ := Real.sqrt (‖g.inner p‖ * C ^ 2)
  refine ⟨D, Real.sqrt_nonneg _, ?_⟩
  intro v hv
  have hdir_le : ‖coeffModelCLM (E := E) v‖ ≤ C := by
    have hop := (coeffModelCLM (E := E)).le_opNorm v
    simpa [C, hv] using hop
  have hsq_le : ‖coeffModelCLM (E := E) v‖ ^ 2 ≤ C ^ 2 := by
    have hC_nonneg : 0 ≤ C := by
      exact norm_nonneg (coeffModelCLM (E := E))
    exact (sq_le_sq₀ (norm_nonneg _) hC_nonneg).2 hdir_le
  have hinner_le :
      g.inner p (coeffModelCLM (E := E) v) (coeffModelCLM (E := E) v) ≤
        ‖g.inner p‖ * C ^ 2 := by
    exact (inner_le_opNorm_sq (I := I) g p (coeffModelCLM (E := E) v)).trans
      (mul_le_mul_of_nonneg_left hsq_le (norm_nonneg (g.inner p)))
  calc
    Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i))
        = Real.sqrt (g.inner p (coeffModelCLM (E := E) v) (coeffModelCLM (E := E) v)) := by
          rw [coeffModelCLM_eq_sum (E := E) v]
          rfl
    _ ≤ D := Real.sqrt_le_sqrt hinner_le

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem exists_unitCoeff_bounds
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ B₀ D : ℝ, 0 < B₀ ∧ 0 ≤ D ∧
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B₀ ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i))) ∧
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) ≤ D) := by
  rcases exists_unitCoeff_ge (I := I) g p with ⟨B₀, hB₀_pos, hB₀⟩
  rcases exists_unitCoeff_le (I := I) g p with ⟨D, hD_nonneg, hD⟩
  exact ⟨B₀, D, hB₀_pos, hD_nonneg, hB₀, hD⟩

omit [NeZero (Module.finrank ℝ E)] in
lemma unitDirScaleSmall {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r := by
  set C : ℝ := ‖coeffModelCLM (E := E)‖ with hC
  have hC_nonneg : 0 ≤ C := by
    simp [hC]
  have hden_pos : 0 < C + 1 := by linarith
  refine ⟨r / (C + 1), div_pos hr hden_pos, ?_⟩
  intro v hv
  have ha_pos : 0 < r / (C + 1) := div_pos hr hden_pos
  have hdir_le : ‖∑ i, v i • (chartModelBasis E) i‖ ≤ C := by
    have hop := (coeffModelCLM (E := E)).le_opNorm v
    rw [hv, mul_one] at hop
    rw [← coeffModelCLM_eq_sum (E := E) v]
    simpa [hC] using hop
  have hdir_lt : ‖∑ i, v i • (chartModelBasis E) i‖ < C + 1 := by
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha_pos]
  calc
    r / (C + 1) * ‖∑ i, v i • (chartModelBasis E) i‖
        < r / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left hdir_lt ha_pos
    _ = r := by field_simp [ne_of_gt hden_pos]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
lemma dir_deriv_radius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (x : E)
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hdirSmall : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖∑ i, v i • (chartModelBasis E) i‖ < r) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i)) 0 : E) =
        ∑ i, v i • (chartModelBasis E) i := by
  intro v hv
  simpa [radialCurve] using
    hderivRadius x (∑ i, v i • (chartModelBasis E) i) hx (hdirSmall v hv)

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dir_init_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {B : ℝ}
    (hB : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
        (g.inner p (∑ i, v i • (chartModelBasis E) i)
          (∑ i, v i • (chartModelBasis E) i)))
    (hderiv : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i)) 0 : E) =
        ∑ i, v i • (chartModelBasis E) i) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
        (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)) := by
  intro v hv
  rw [radialCurve_zero (I := I) g p x]
  rw [hderiv v hv]
  exact hB v hv

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_dirInit_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hderiv : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i)) 0 : E) =
        ∑ i, v i • (chartModelBasis E) i) :
    ∃ B : ℝ, 0 < B ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
          (g.inner (radialCurve (I := I) g p x 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) 0)) := by
  rcases exists_unitCoeff_ge (I := I) g p with ⟨B, hBpos, hB⟩
  exact ⟨B, hBpos, dir_init_ge (I := I) g p x hB hderiv⟩

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_bounds_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) ≤
        t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) := by
  simpa [radialCurve] using
    covGronwall_bounds_at (I := I) g (radialCurve (I := I) g p x) hγ hcard F
      (radialJacobiField (I := I) g p x w) hK hb hpar hON hFdiff hJdiff
      hDJdiff hODE (radialJacobi_zero (I := I) g p x w) rfl

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_bounds
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) ≤
        t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) := by
  refine radialJacobi_bounds_at (I := I) g p x w hK hb (fun t _ => ?_) hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  exact hγ.contMDiffAt

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_bounds_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) ∧
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1))) := by
  have hbounds := radialJacobi_bounds_at (I := I) g p x w hK hb hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) b := ⟨by norm_num, h1b⟩
  constructor
  · simpa using hbounds.1 1 h1
  · simpa using hbounds.2 1 h1

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_bounds
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) ∧
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1))) := by
  refine radialJacobi_one_bounds_at (I := I) g p x w hK hb h1b
    (fun t _ => ?_) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
  exact hγ.contMDiffAt


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_le_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤ B) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hbounds := radialJacobi_one_bounds_at (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hupper :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x w 1)
        (radialJacobiField (I := I) g p x w 1)) ≤
          Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)) +
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)))) 1 := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.1
  exact hupper.trans hB

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_le
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤ B) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hbounds := radialJacobi_one_bounds (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hupper :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x w 1)
        (radialJacobiField (I := I) g p x w 1)) ≤
          Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)) +
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)))) 1 := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.1
  exact hupper.trans hB


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_ge_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hbounds := radialJacobi_one_bounds_at (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hlower :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1)) := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.2
  exact hB.trans hlower

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hbounds := radialJacobi_one_bounds (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hlower :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1)) := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.2
  exact hB.trans hlower


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_sq_ge_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
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
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1) := by
  set q := radialCurve (I := I) g p x 1 with hq
  set J : TangentSpace I q := radialJacobiField (I := I) g p x w 1 with hJdef
  have hsqrt : B ≤ Real.sqrt (g.inner q J J) := by
    rw [hq, radialCurve_one]
    exact
      radialJacobi_one_ge_at (I := I) g p x w hK hb h1b hγ hcard F hpar hON
        hFdiff hJdiff hDJdiff hODE hB
  have hsq : B ^ 2 ≤ (Real.sqrt (g.inner q J J)) ^ 2 :=
    (sq_le_sq₀ hB_nonneg (Real.sqrt_nonneg _)).2 hsqrt
  have hJ_nonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      have hzero :
          (g.inner q) (0 : TangentSpace I q) = (0 : TangentSpace I q →L[ℝ] ℝ) :=
        map_zero (g.inner q)
      rw [hzero]
      rfl
    · exact (g.pos q J hJ).le
  rw [← radialCurve_one (I := I) g p x]
  simpa [hq, hJdef] using hsq.trans_eq (Real.sq_sqrt hJ_nonneg)

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_sq_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
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
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1) := by
  set q := radialCurve (I := I) g p x 1 with hq
  set J : TangentSpace I q := radialJacobiField (I := I) g p x w 1 with hJdef
  have hsqrt : B ≤ Real.sqrt (g.inner q J J) := by
    rw [hq, radialCurve_one]
    exact
      radialJacobi_one_ge (I := I) g p x w hK hb h1b hγ hcard F hpar hON
        hFdiff hJdiff hDJdiff hODE hB
  have hsq : B ^ 2 ≤ (Real.sqrt (g.inner q J J)) ^ 2 :=
    (sq_le_sq₀ hB_nonneg (Real.sqrt_nonneg _)).2 hsqrt
  have hJ_nonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      have hzero :
          (g.inner q) (0 : TangentSpace I q) = (0 : TangentSpace I q →L[ℝ] ℝ) :=
        map_zero (g.inner q)
      rw [hzero]
      rfl
    · exact (g.pos q J hJ).le
  rw [← radialCurve_one (I := I) g p x]
  simpa [hq, hJdef] using hsq.trans_eq (Real.sq_sqrt hJ_nonneg)


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_dir_ge_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
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
              (∑ i, v i • (chartModelBasis E) i)) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t))
    (hB : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)))) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) := by
  intro v hv
  exact radialJacobi_sq_ge_at (I := I) g p x (∑ i, v i • (chartModelBasis E) i)
    hB_nonneg hK hb h1b hγ hcard F hpar hON hFdiff (hJdiff v hv)
    (hDJdiff v hv) (hODE v hv) (hB v hv)

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_dir_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
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
              (∑ i, v i • (chartModelBasis E) i)) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t))
    (hB : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)))) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) := by
  intro v hv
  exact radialJacobi_sq_ge (I := I) g p x (∑ i, v i • (chartModelBasis E) i)
    hB_nonneg hK hb h1b hγ hcard F hpar hON hFdiff (hJdiff v hv)
    (hDJdiff v hv) (hODE v hv) (hB v hv)


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
    (hB : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)))) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  intro k
  exact radialJacobi_one_le_at (I := I) g p x ((chartModelBasis E) k) hK hb h1b hγ
    hcard F hpar hON hFdiff (hJdiff k) (hDJdiff k) (hODE k) (hB k)

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
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
    (hB : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)))) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  intro k
  exact radialJacobi_one_le (I := I) g p x ((chartModelBasis E) k) hK hb h1b hγ
    hcard F hpar hON hFdiff (hJdiff k) (hDJdiff k) (hODE k) (hB k)


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_init_bound_at
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
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  refine radialJacobi_fin_le_at (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE ?_
  intro k
  set vnorm : ℝ :=
    Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0))
  have hvA : vnorm ≤ A := by
    simpa [vnorm] using hinit k
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
    _ ≤ B := hmodel

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_init_bound
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
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  refine radialJacobi_fin_le (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE ?_
  intro k
  set vnorm : ℝ :=
    Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0))
  have hvA : vnorm ≤ A := by
    simpa [vnorm] using hinit k
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
    _ ≤ B := hmodel

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma radialJacobi_init_le_of_deriv_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {A : ℝ}
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A := by
  intro k
  rw [radialCurve_zero (I := I) g p x]
  rw [hderiv k]
  exact hbasis k

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
lemma fin_deriv_radius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (x : E)
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r) :
    ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k := by
  intro k
  simpa [radialCurve] using hderivRadius x ((chartModelBasis E) k) hx (hbasisSmall k)

end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
