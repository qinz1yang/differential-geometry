import DifferentialGeometry.Analysis.Sobolev.DirichletHs.Defs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma dirichletSobolevWeight_mono {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    dirichletSobolevWeight i τ ≤
      dirichletSobolevWeight i σ := by
  unfold dirichletSobolevWeight
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_one_add_dirichletLaplacianEigenvalue i) hτσ

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M}

lemma weighted_summable_of_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      dirichletSobolevWeight i τ * (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.weighted_summable
  · intro i
    have hw : 0 ≤ dirichletSobolevWeight i τ :=
      dirichletSobolevWeight_nonneg i τ
    positivity
  · intro i
    have hmono : dirichletSobolevWeight i τ ≤
        dirichletSobolevWeight i σ :=
      dirichletSobolevWeight_mono i hτσ
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

def inclusionFun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    dirichletHs g τ where
  coeff := T.coeff
  weighted_summable := weighted_summable_of_le hτσ T

@[simp] lemma inclusionFun_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    (inclusionFun hτσ T).coeff = T.coeff := rfl

lemma inclusionFun_add {τ σ : ℝ} (hτσ : τ ≤ σ)
    (S T : dirichletHs g σ) :
    inclusionFun hτσ (S + T) =
      inclusionFun hτσ S +
        inclusionFun hτσ T := by
  ext i
  simp only [inclusionFun_coeff, add_coeff]

lemma inclusionFun_smul {τ σ : ℝ} (hτσ : τ ≤ σ) (c : ℝ)
    (T : dirichletHs g σ) :
    inclusionFun hτσ (c • T) =
      c • inclusionFun hτσ T := by
  ext i
  simp only [inclusionFun_coeff, smul_coeff]

lemma norm_inclusionFun_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    ‖inclusionFun hτσ T‖ ≤ ‖T‖ := by
  have h_t_sq : ‖inclusionFun hτσ T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i τ * (T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum
      (inclusionFun hτσ T)
    rwa [inclusionFun_coeff] at h
  have h_s_sq : ‖T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum T
  have h_le_terms : ∀ i : DirichletLaplacianEigenindex g,
      dirichletSobolevWeight i τ * (T.coeff i) ^ 2 ≤
        dirichletSobolevWeight i σ * (T.coeff i) ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right
      (dirichletSobolevWeight_mono i hτσ) (sq_nonneg _)
  have h_tsum_le :
      ∑' i, dirichletSobolevWeight i τ * (T.coeff i) ^ 2 ≤
        ∑' i, dirichletSobolevWeight i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms
      (weighted_summable_of_le hτσ T) T.weighted_summable
  have h_sq_le : ‖inclusionFun hτσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_t_sq, h_s_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖inclusionFun hτσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end dirichletHs

def dirichletHsInclusion {g : SmoothRiemannianMetric (I_half n) M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    dirichletHs g σ →L[ℝ]
      dirichletHs g τ :=
  LinearMap.mkContinuous
    { toFun := dirichletHs.inclusionFun hτσ
      map_add' := dirichletHs.inclusionFun_add hτσ
      map_smul' := fun c T =>
        dirichletHs.inclusionFun_smul hτσ c T }
    1
    (fun T => by
      change ‖dirichletHs.inclusionFun hτσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact dirichletHs.norm_inclusionFun_le hτσ T)

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M}

@[simp] lemma dirichletHsInclusion_apply {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    dirichletHsInclusion (g := g) hτσ T =
      inclusionFun hτσ T := rfl

@[simp] theorem dirichletHsInclusion_coeff_fun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    (dirichletHsInclusion (g := g) hτσ T).coeff =
      T.coeff := rfl

@[simp] theorem dirichletHsInclusion_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ)
    (i : DirichletLaplacianEigenindex g) :
    (dirichletHsInclusion (g := g) hτσ T).coeff i =
      T.coeff i := rfl

theorem dirichletHsInclusion_opNorm_le_one {τ σ : ℝ} (hτσ : τ ≤ σ) :
    ‖dirichletHsInclusion (g := g) hτσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem dirichletHsInclusion_norm_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    ‖dirichletHsInclusion (g := g) hτσ T‖ ≤ ‖T‖ :=
  norm_inclusionFun_le hτσ T

theorem dirichletHsInclusion_injective {τ σ : ℝ} (hτσ : τ ≤ σ) :
    Function.Injective
      (dirichletHsInclusion (g := g) hτσ) := by
  intro S T hST
  ext i
  have h := congrArg (fun U => dirichletHs.coeff U i) hST
  simpa only [dirichletHsInclusion_coeff] using h

@[simp] theorem dirichletHsInclusion_refl {σ : ℝ} :
    dirichletHsInclusion (g := g) (le_refl σ) =
      ContinuousLinearMap.id ℝ
        (dirichletHs g σ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine dirichletHs.ext ?_
  funext i
  rw [dirichletHsInclusion_coeff, ContinuousLinearMap.id_apply]

theorem dirichletHsInclusion_refl_apply {σ : ℝ}
    (T : dirichletHs g σ) :
    dirichletHsInclusion (g := g) (le_refl σ) T = T := by
  ext i
  simp only [dirichletHsInclusion_coeff]

theorem dirichletHsInclusion_trans {τ₁ σ τ₂ : ℝ}
    (h₁ : τ₁ ≤ σ) (h₂ : σ ≤ τ₂) :
    dirichletHsInclusion (g := g) (h₁.trans h₂) =
      (dirichletHsInclusion (g := g) h₁).comp
        (dirichletHsInclusion (g := g) h₂) := by
  ext T i
  simp only [dirichletHsInclusion_coeff, ContinuousLinearMap.coe_comp,
    Function.comp_apply]

theorem dirichletHsInclusion_trans_apply {τ₁ σ τ₂ : ℝ}
    (h₁ : τ₁ ≤ σ) (h₂ : σ ≤ τ₂)
    (T : dirichletHs g τ₂) :
    dirichletHsInclusion (g := g) (h₁.trans h₂) T =
      dirichletHsInclusion (g := g) h₁
        (dirichletHsInclusion (g := g) h₂ T) := by
  ext i
  simp only [dirichletHsInclusion_coeff]

lemma coeff_summable_sq_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ) :
    Summable (fun i : DirichletLaplacianEigenindex g =>
      (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) ?_
    T.weighted_summable
  intro i
  have hw : 1 ≤ dirichletSobolevWeight i σ :=
    one_le_dirichletSobolevWeight i hσ
  have hsq : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
  nlinarith [hw, hsq]

def toL2Seq {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ) :
    lp (fun _ : DirichletLaplacianEigenindex g => ℝ) 2 :=
  ⟨T.coeff, by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : DirichletLaplacianEigenindex g =>
          ‖T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => (T.coeff i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [h_eq]
    exact coeff_summable_sq_of_nonneg hσ T⟩

@[simp] lemma toL2Seq_apply {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ)
    (i : DirichletLaplacianEigenindex g) :
    (toL2Seq hσ T : _ → ℝ) i = T.coeff i := rfl

def toL2Fun {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (dirichletLaplacianHilbertBasis g).repr.symm
    (toL2Seq hσ T)

@[simp] lemma dirichletL2Coeff_toL2Fun {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ)
    (i : DirichletLaplacianEigenindex g) :
    dirichletL2Coeff
        (toL2Fun hσ T) i = T.coeff i := by
  unfold dirichletL2Coeff toL2Fun
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma toL2Seq_add {σ : ℝ} (hσ : 0 ≤ σ)
    (S T : dirichletHs g σ) :
    toL2Seq hσ (S + T) =
      toL2Seq hσ S + toL2Seq hσ T := by
  apply lp.ext
  funext i
  simp only [toL2Seq_apply, lp.coeFn_add, Pi.add_apply, add_coeff]

lemma toL2Seq_smul {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ)
    (T : dirichletHs g σ) :
    toL2Seq hσ (c • T) =
      c • toL2Seq hσ T := by
  apply lp.ext
  funext i
  simp only [toL2Seq_apply, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
    smul_eq_mul]

lemma toL2Fun_add {σ : ℝ} (hσ : 0 ≤ σ)
    (S T : dirichletHs g σ) :
    toL2Fun hσ (S + T) =
      toL2Fun hσ S + toL2Fun hσ T := by
  set b := dirichletLaplacianHilbertBasis g
  have h_seq : toL2Seq hσ (S + T) =
      toL2Seq hσ S + toL2Seq hσ T :=
    toL2Seq_add hσ S T
  have h_map :
      b.repr.symm (toL2Seq hσ S +
          toL2Seq hσ T) =
        b.repr.symm (toL2Seq hσ S) +
          b.repr.symm (toL2Seq hσ T) :=
    b.repr.symm.map_add _ _
  calc toL2Fun hσ (S + T)
      = b.repr.symm (toL2Seq hσ (S + T)) := rfl
    _ = b.repr.symm (toL2Seq hσ S +
          toL2Seq hσ T) :=
      congrArg (fun x => b.repr.symm x) h_seq
    _ = b.repr.symm (toL2Seq hσ S) +
          b.repr.symm (toL2Seq hσ T) := h_map
    _ = toL2Fun hσ S +
          toL2Fun hσ T := rfl

lemma toL2Fun_smul {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ)
    (T : dirichletHs g σ) :
    toL2Fun hσ (c • T) =
      c • toL2Fun hσ T := by
  set b := dirichletLaplacianHilbertBasis g
  have h_seq : toL2Seq hσ (c • T) =
      c • toL2Seq hσ T :=
    toL2Seq_smul hσ c T
  have h_map :
      b.repr.symm (c • toL2Seq hσ T) =
        c • b.repr.symm (toL2Seq hσ T) :=
    b.repr.symm.map_smul _ _
  calc toL2Fun hσ (c • T)
      = b.repr.symm (toL2Seq hσ (c • T)) := rfl
    _ = b.repr.symm (c • toL2Seq hσ T) :=
      congrArg (fun x => b.repr.symm x) h_seq
    _ = c • b.repr.symm (toL2Seq hσ T) := h_map
    _ = c • toL2Fun hσ T := rfl

private lemma dirichletParseval_norm_sq
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    ‖u‖ ^ 2 =
      ∑' i : DirichletLaplacianEigenindex g,
        ‖⟪dirichletLaplacianHilbertBasis g i,
            u⟫_ℝ‖ ^ 2 := by
  set b := dirichletLaplacianHilbertBasis g
  have h_par := b.tsum_inner_mul_inner u u
  have h_sq : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have h_eq : (fun i : DirichletLaplacianEigenindex g =>
        ⟪u, b i⟫_ℝ * ⟪b i, u⟫_ℝ) =
      (fun i => ‖⟪b i, u⟫_ℝ‖ ^ 2) := by
    funext i
    rw [show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _,
        Real.norm_eq_abs, sq_abs, sq]
  rw [h_eq] at h_par
  linarith [h_par, h_sq]

lemma norm_toL2Fun_le {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ) :
    ‖toL2Fun hσ T‖ ≤ ‖T‖ := by
  have h_l2_sq : ‖toL2Fun hσ T‖ ^ 2 =
      ∑' i, (T.coeff i) ^ 2 := by
    have h_par := dirichletParseval_norm_sq
      (toL2Fun hσ T)
    have h_eq :
        (fun i : DirichletLaplacianEigenindex g =>
          ‖⟪dirichletLaplacianHilbertBasis g i,
            toL2Fun hσ T⟫_ℝ‖ ^ 2) =
        (fun i => (T.coeff i) ^ 2) := by
      funext i
      have h_coeff : dirichletL2Coeff
          (toL2Fun hσ T) i = T.coeff i :=
        dirichletL2Coeff_toL2Fun hσ T i
      have h_inner : (⟪dirichletLaplacianHilbertBasis g i,
          toL2Fun hσ T⟫_ℝ : ℝ) =
          dirichletL2Coeff
            (toL2Fun hσ T) i := by
        unfold dirichletL2Coeff
        exact (HilbertBasis.repr_apply_apply _ _ _).symm
      rw [h_inner, h_coeff, Real.norm_eq_abs, sq_abs]
    rwa [h_eq] at h_par
  have h_hs_sq : ‖T‖ ^ 2 =
      ∑' i, dirichletSobolevWeight i σ *
        (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum T
  have h_summ_unweighted :
      Summable (fun i : DirichletLaplacianEigenindex g =>
        (T.coeff i) ^ 2) :=
    coeff_summable_sq_of_nonneg hσ T
  have h_le_terms : ∀ i : DirichletLaplacianEigenindex g,
      (T.coeff i) ^ 2 ≤
        dirichletSobolevWeight i σ * (T.coeff i) ^ 2 := by
    intro i
    have hw : 1 ≤ dirichletSobolevWeight i σ :=
      one_le_dirichletSobolevWeight i hσ
    nlinarith [hw, sq_nonneg (T.coeff i)]
  have h_tsum_le :
      ∑' i, (T.coeff i) ^ 2 ≤
        ∑' i, dirichletSobolevWeight i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms h_summ_unweighted T.weighted_summable
  have h_sq_le : ‖toL2Fun hσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_l2_sq, h_hs_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖toL2Fun hσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end dirichletHs

def dirichletHsToL2 {g : SmoothRiemannianMetric (I_half n) M} {σ : ℝ} (hσ : 0 ≤ σ) :
    dirichletHs g σ →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  LinearMap.mkContinuous
    { toFun := dirichletHs.toL2Fun hσ
      map_add' := dirichletHs.toL2Fun_add hσ
      map_smul' := fun c T => dirichletHs.toL2Fun_smul hσ c T }
    1
    (fun T => by
      change ‖dirichletHs.toL2Fun hσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact dirichletHs.norm_toL2Fun_le hσ T)

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M}

@[simp] lemma dirichletHsToL2_apply {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ) :
    dirichletHsToL2 (g := g) hσ T =
      toL2Fun hσ T := rfl

theorem dirichletHsToL2_opNorm_le_one {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖dirichletHsToL2 (g := g) hσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem dirichletL2Coeff_dirichletHsToL2 {σ : ℝ} (hσ : 0 ≤ σ)
    (T : dirichletHs g σ)
    (i : DirichletLaplacianEigenindex g) :
    dirichletL2Coeff
        (dirichletHsToL2 (g := g) hσ T) i = T.coeff i := by
  rw [dirichletHsToL2_apply]
  exact dirichletL2Coeff_toL2Fun hσ T i

theorem dirichletHsToL2_injective {σ : ℝ} (hσ : 0 ≤ σ) :
    Function.Injective
      (dirichletHsToL2 (g := g) hσ) := by
  intro S T hST
  ext i
  have hS := dirichletL2Coeff_dirichletHsToL2 hσ S i
  have hT := dirichletL2Coeff_dirichletHsToL2 hσ T i
  rw [← hS, ← hT, hST]

end dirichletHs

def dirichletHsZeroEquivL2 (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletHs g 0 ≃ₗᵢ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (dirichletHs.rescaleEquivL2
    (g := g) (σ := 0)).trans
    (dirichletLaplacianHilbertBasis g).repr.symm

namespace dirichletHs

variable {g : SmoothRiemannianMetric (I_half n) M}

theorem dirichletHsZeroEquivL2_dirichletL2Coeff
    (T : dirichletHs g 0)
    (i : DirichletLaplacianEigenindex g) :
    dirichletL2Coeff
        (dirichletHsZeroEquivL2 g T) i =
      T.coeff i := by
  unfold dirichletHsZeroEquivL2 dirichletL2Coeff
  rw [LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change (dirichletHs.rescaleEquivL2 T : _ → ℝ) i = T.coeff i
  rw [dirichletHs.rescaleEquivL2_apply]
  simp only [dirichletSobolevWeight_zero, Real.sqrt_one, one_mul]

@[simp] theorem dirichletHsZeroEquivL2_symm_coeff
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (i : DirichletLaplacianEigenindex g) :
    ((dirichletHsZeroEquivL2 g).symm u).coeff i =
      dirichletL2Coeff u i := by
  have h := dirichletHsZeroEquivL2_dirichletL2Coeff
    ((dirichletHsZeroEquivL2 g).symm u) i
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

end dirichletHs

theorem dirichletHsToL2_comp_dirichletHsInclusion
    {g : SmoothRiemannianMetric (I_half n) M} {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    (dirichletHsToL2 (g := g) hτ).comp
        (dirichletHsInclusion (g := g) hτσ) =
      dirichletHsToL2 (g := g) (hτ.trans hτσ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine (dirichletLaplacianHilbertBasis g).repr.injective ?_
  ext i
  have hlhs : ((dirichletLaplacianHilbertBasis g).repr
      ((dirichletHsToL2 (g := g) hτ).comp
        (dirichletHsInclusion (g := g) hτσ) T)) i =
      T.coeff i := by
    have h := dirichletHs.dirichletL2Coeff_dirichletHsToL2 hτ
      (dirichletHsInclusion (g := g) hτσ T) i
    rw [dirichletHs.dirichletHsInclusion_coeff] at h
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      dirichletL2Coeff] using h
  have hrhs : ((dirichletLaplacianHilbertBasis g).repr
      (dirichletHsToL2 (g := g) (hτ.trans hτσ) T)) i =
      T.coeff i := by
    have h := dirichletHs.dirichletL2Coeff_dirichletHsToL2
      (hτ.trans hτσ) T i
    simpa only [dirichletL2Coeff] using h
  rw [hlhs, hrhs]

theorem dirichletHsToL2_dirichletHsInclusion
    {g : SmoothRiemannianMetric (I_half n) M} {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (T : dirichletHs g σ) :
    dirichletHsToL2 (g := g) hτ
        (dirichletHsInclusion (g := g) hτσ T) =
      dirichletHsToL2 (g := g) (hτ.trans hτσ) T := by
  have h := dirichletHsToL2_comp_dirichletHsInclusion
    (g := g) hτ hτσ
  exact congrArg (fun L => L T) h

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
