import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Galerkin.DeTurckEnergy
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.TameForcing

noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

abbrev galLowView (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) :=
  tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galEmbedCombo (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    galerkinCoordEmbed (I := I) (M := M) g₀ a S w =
      finiteEigenComboHs (I := I) (M := M) g₀ S
        (fun i => if h : i ∈ S then w ⟨i, h⟩ else 0) ((a : ℝ) + 2) := by
  apply TensorHs.ext
  funext i
  rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
  · rw [if_neg hi, dif_neg hi]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galViewComboC (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    galLowView (I := I) (M := M) g₀ a
        (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)) =
      finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 1) := by
  apply TensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply, finiteEigenComboHs_coeff,
    finiteEigenComboHs_coeff]

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galViewCombo (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    galLowView (I := I) (M := M) g₀ a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w) =
      finiteEigenComboHs (I := I) (M := M) g₀ S
        (fun i => if h : i ∈ S then w ⟨i, h⟩ else 0) ((a : ℝ) + 1) := by
  rw [galEmbedCombo (I := I) (M := M) g₀ a S w,
    galViewComboC (I := I) (M := M) g₀ a S]

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galCoordNormLe (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    ‖w‖ ≤ ‖galLowView (I := I) (M := M) g₀ a
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖ := by
  classical
  set c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => if h : i ∈ S then w ⟨i, h⟩ else 0 with hc
  have hview := galViewCombo (I := I) (M := M) g₀ a S w
  have hsq : ‖galLowView (I := I) (M := M) g₀ a
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖ ^ 2 =
      ∑ i ∈ S, (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 1) *
        (c i) ^ 2 := by
    rw [hview]
    exact finiteEigenCombo_spectral_normSq (I := I) (M := M) g₀ S c _
  have hwsq : ‖w‖ ^ 2 = ∑ i ∈ S, (c i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rw [← Finset.sum_coe_sort S (fun i => (c i) ^ 2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (j : TensorEigenIdx (I := I) (M := M) g₀ 0 2) ∈ S := j.2
    simp only [hc, dif_pos hj, Subtype.coe_eta, Real.norm_eq_abs, sq_abs]
  have hle : ‖w‖ ^ 2 ≤ ‖galLowView (I := I) (M := M) g₀ a
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖ ^ 2 := by
    rw [hwsq, hsq]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hone : (1 : ℝ) ≤
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 1) :=
      Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i)
        (by positivity)
    simpa using mul_le_mul_of_nonneg_right hone (sq_nonneg (c i))
  have hfin := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hfin

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTopNormLe (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) {κ : ℝ}
    (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)‖ ≤
      Real.sqrt κ *
        ‖finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 1)‖ := by
  have htop := finiteEigenCombo_spectral_normSq (I := I) (M := M) g₀ S c
    ((a : ℝ) + 2)
  have hlow := finiteEigenCombo_spectral_normSq (I := I) (M := M) g₀ S c
    ((a : ℝ) + 1)
  have hsum : ‖finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)‖ ^ 2 ≤
      κ * ‖finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 1)‖ ^ 2 := by
    rw [htop, hlow, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
      lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
    have hsplit :
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 2) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 1) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) := by
      rw [show (a : ℝ) + 2 = ((a : ℝ) + 1) + 1 by ring,
        Real.rpow_add_one (ne_of_gt hbase)]
    have hpq : (0 : ℝ) ≤
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 1) *
          (c i) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hbase.le _) (sq_nonneg _)
    calc (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 2) *
          (c i) ^ 2
        = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 1) *
              (c i) ^ 2) := by rw [hsplit]; ring
      _ ≤ κ * ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((a : ℝ) + 1) *
            (c i) ^ 2) := mul_le_mul_of_nonneg_right (hκ i hi) hpq
  have hsqrt := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hκ0,
    Real.sqrt_sq (norm_nonneg _)] at hsqrt

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galEmbTopLe (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) {κ : ℝ}
    (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S w‖ ≤
      Real.sqrt κ * ‖galLowView (I := I) (M := M) g₀ a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖ := by
  classical
  rw [galEmbedCombo (I := I) (M := M) g₀ a S w,
    galViewComboC (I := I) (M := M) g₀ a S]
  exact galTopNormLe (I := I) (M := M) g₀ a S hκ0 hκ _

def galTameRetr (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) : EuclideanSpace ℝ {i // i ∈ S} :=
  (min 1 (R / ‖galLowView (I := I) (M := M) g₀ a
    (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖)) • w

def galTameStateC (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) :=
  (min 1 (R / ‖galLowView (I := I) (M := M) g₀ a
      (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2))‖)) •
    finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameState_eq (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    galerkinCoordEmbed (I := I) (M := M) g₀ a S
        (galTameRetr (I := I) (M := M) g₀ a R S w) =
      galTameStateC (I := I) (M := M) g₀ a R S
        (fun i => if h : i ∈ S then w ⟨i, h⟩ else 0) := by
  rw [galTameRetr, map_smul, galTameStateC,
    galEmbedCombo (I := I) (M := M) g₀ a S w]

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameStateC_emb (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    galerkinCoordEmbed (I := I) (M := M) g₀ a S
        (galTameRetr (I := I) (M := M) g₀ a R S
          ((EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c j.1))) =
      galTameStateC (I := I) (M := M) g₀ a R S c := by
  classical
  have key : ∀ c' : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ i ∈ S, c' i = c i) →
      galTameStateC (I := I) (M := M) g₀ a R S c' =
        galTameStateC (I := I) (M := M) g₀ a R S c := by
    intro c' hc'
    have hcombo : finiteEigenComboHs (I := I) (M := M) g₀ S c' ((a : ℝ) + 2) =
        finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2) := by
      apply TensorHs.ext
      funext i
      rw [finiteEigenComboHs_coeff, finiteEigenComboHs_coeff]
      by_cases hi : i ∈ S
      · rw [if_pos hi, if_pos hi, hc' i hi]
      · rw [if_neg hi, if_neg hi]
    simp only [galTameStateC, hcombo]
  rw [galTameState_eq]
  exact key _ (fun i hi => dif_pos hi)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameRetr_view (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    galLowView (I := I) (M := M) g₀ a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S
          (galTameRetr (I := I) (M := M) g₀ a R S w)) =
      ballRetraction R (galLowView (I := I) (M := M) g₀ a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)) := by
  rw [galTameRetr, map_smul, map_smul, ballRetraction]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameRetr_mem (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    galerkinCoordEmbed (I := I) (M := M) g₀ a S
        (galTameRetr (I := I) (M := M) g₀ a R S w) ∈
      lowerState (I := I) (M := M) g₀ a R := by
  change ‖galLowView (I := I) (M := M) g₀ a
    (galerkinCoordEmbed (I := I) (M := M) g₀ a S
      (galTameRetr (I := I) (M := M) g₀ a R S w))‖ ≤ R
  rw [galTameRetr_view]
  exact ballRetraction_mem_closedBall hR _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameStateC_mem (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    galTameStateC (I := I) (M := M) g₀ a R S c ∈
      lowerState (I := I) (M := M) g₀ a R := by
  change ‖galLowView (I := I) (M := M) g₀ a
    (galTameStateC (I := I) (M := M) g₀ a R S c)‖ ≤ R
  rw [galTameStateC, map_smul]
  exact ballRetraction_mem_closedBall (X :=
    TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)) hR _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameRetr_eq (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {w : EuclideanSpace ℝ {i // i ∈ S}}
    (hw : ‖galLowView (I := I) (M := M) g₀ a
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖ ≤ R) :
    galTameRetr (I := I) (M := M) g₀ a R S w = w := by
  rcases eq_or_lt_of_le (norm_nonneg (galLowView (I := I) (M := M) g₀ a
    (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))) with h0 | h0
  · have hw0 : ‖w‖ ≤ 0 :=
      le_trans (galCoordNormLe (I := I) (M := M) g₀ a S w) (le_of_eq h0.symm)
    have hzero : w = 0 := norm_le_zero_iff.mp hw0
    rw [galTameRetr, hzero, smul_zero]
  · have hone : (1 : ℝ) ≤ R / ‖galLowView (I := I) (M := M) g₀ a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)‖ :=
      (one_le_div h0).2 hw
    rw [galTameRetr, min_eq_left hone, one_smul]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameRetr_top (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S
        (galTameRetr (I := I) (M := M) g₀ a R S w)‖ ≤ Real.sqrt κ * R := by
  refine (galEmbTopLe (I := I) (M := M) g₀ a S hκ0 hκ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg κ)
  rw [galTameRetr_view]
  exact ballRetraction_mem_closedBall hR _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameState_lip (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    (w w' : EuclideanSpace ℝ {i // i ∈ S}) :
    ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S
          (galTameRetr (I := I) (M := M) g₀ a R S w) -
        galerkinCoordEmbed (I := I) (M := M) g₀ a S
          (galTameRetr (I := I) (M := M) g₀ a R S w')‖ ≤
      Real.sqrt κ * ‖(galLowView (I := I) (M := M) g₀ a).comp
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S)‖ * ‖w - w'‖ := by
  set Emb := galerkinCoordEmbed (I := I) (M := M) g₀ a S with hEmb
  set L := (galLowView (I := I) (M := M) g₀ a).comp Emb with hL
  set v : EuclideanSpace ℝ {i // i ∈ S} :=
    galTameRetr (I := I) (M := M) g₀ a R S w -
      galTameRetr (I := I) (M := M) g₀ a R S w' with hv
  have hdiff : Emb (galTameRetr (I := I) (M := M) g₀ a R S w) -
      Emb (galTameRetr (I := I) (M := M) g₀ a R S w') = Emb v := by
    rw [hv, map_sub]
  rw [hdiff]
  refine (galEmbTopLe (I := I) (M := M) g₀ a S hκ0 hκ v).trans ?_
  have hLapp : ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      L x = galLowView (I := I) (M := M) g₀ a (Emb x) := fun _ => rfl
  have hview : galLowView (I := I) (M := M) g₀ a (Emb v) =
      ballRetraction R (L w) - ballRetraction R (L w') := by
    rw [hLapp, hLapp, hv, map_sub, map_sub, galTameRetr_view, galTameRetr_view]
  rw [hview]
  have hlip := (lipschitzWith_one_ballRetraction
    (X := TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)) hR).dist_le_mul
      (L w) (L w')
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul] at hlip
  have hbound : ‖ballRetraction R (L w) - ballRetraction R (L w')‖ ≤
      ‖L‖ * ‖w - w'‖ := by
    refine hlip.trans ?_
    rw [← map_sub]
    exact L.le_opNorm _
  calc Real.sqrt κ * ‖ballRetraction R (L w) - ballRetraction R (L w')‖
      ≤ Real.sqrt κ * (‖L‖ * ‖w - w'‖) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg κ)
    _ = Real.sqrt κ * ‖L‖ * ‖w - w'‖ := by ring

def galTameField (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} → EuclideanSpace ℝ {i // i ∈ S} :=
  fun w => galerkinCoordDiag (I := I) (M := M) g₀ S w +
    galerkinCoordRestrict (I := I) (M := M) g₀ a S
      (Nfun ⟨galerkinCoordEmbed (I := I) (M := M) g₀ a S
          (galTameRetr (I := I) (M := M) g₀ a R S w),
        galTameRetr_mem (I := I) (M := M) g₀ a hR S w⟩)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp] theorem galTameField_apply (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) (j : {i // i ∈ S}) :
    (galTameField (I := I) (M := M) g₀ a hR Nfun S w) j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j +
        (Nfun ⟨galerkinCoordEmbed (I := I) (M := M) g₀ a S
            (galTameRetr (I := I) (M := M) g₀ a R S w),
          galTameRetr_mem (I := I) (M := M) g₀ a hR S w⟩).coeff j.1 := by
  change (galerkinCoordDiag (I := I) (M := M) g₀ S w) j +
    (galerkinCoordRestrict (I := I) (M := M) g₀ a S _) j = _
  rw [galerkinCoordDiag_apply, galerkinCoordRestrict_apply]

def galTameBall (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R κ : ℝ) :
    Set (lowerState (I := I) (M := M) g₀ a R) :=
  {x : lowerState (I := I) (M := M) g₀ a R |
    dist (x : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) ≤ Real.sqrt κ * R}

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameRetr_ball (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    (w : EuclideanSpace ℝ {i // i ∈ S}) :
    (⟨galerkinCoordEmbed (I := I) (M := M) g₀ a S
        (galTameRetr (I := I) (M := M) g₀ a R S w),
      galTameRetr_mem (I := I) (M := M) g₀ a hR S w⟩ :
        lowerState (I := I) (M := M) g₀ a R) ∈
      galTameBall (I := I) (M := M) g₀ a R κ := by
  change dist (galerkinCoordEmbed (I := I) (M := M) g₀ a S
      (galTameRetr (I := I) (M := M) g₀ a R S w))
    (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) ≤ Real.sqrt κ * R
  rw [dist_zero_right]
  exact galTameRetr_top (I := I) (M := M) g₀ a hR S hκ0 hκ w

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameField_lip (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    {K : ℝ≥0}
    (hK : LipschitzOnWith K Nfun (galTameBall (I := I) (M := M) g₀ a R κ)) :
    ∃ K' : ℝ≥0,
      LipschitzWith K' (galTameField (I := I) (M := M) g₀ a hR Nfun S) := by
  set Emb := galerkinCoordEmbed (I := I) (M := M) g₀ a S with hEmb
  set Rst := galerkinCoordRestrict (I := I) (M := M) g₀ a S with hRst
  set Dg := galerkinCoordDiag (I := I) (M := M) g₀ S with hDg
  set L := (galLowView (I := I) (M := M) g₀ a).comp Emb with hL
  refine ⟨Real.toNNReal (‖Dg‖ + ‖Rst‖ * ((K : ℝ) * (Real.sqrt κ * ‖L‖))), ?_⟩
  refine LipschitzWith.of_dist_le_mul (fun w w' => ?_)
  set uw : lowerState (I := I) (M := M) g₀ a R :=
    ⟨Emb (galTameRetr (I := I) (M := M) g₀ a R S w),
      galTameRetr_mem (I := I) (M := M) g₀ a hR S w⟩ with huw
  set uw' : lowerState (I := I) (M := M) g₀ a R :=
    ⟨Emb (galTameRetr (I := I) (M := M) g₀ a R S w'),
      galTameRetr_mem (I := I) (M := M) g₀ a hR S w'⟩ with huw'
  have hN : ‖Nfun uw - Nfun uw'‖ ≤ (K : ℝ) *
      ‖Emb (galTameRetr (I := I) (M := M) g₀ a R S w) -
        Emb (galTameRetr (I := I) (M := M) g₀ a R S w')‖ := by
    have h := hK.dist_le_mul uw
      (galTameRetr_ball (I := I) (M := M) g₀ a hR S hκ0 hκ w) uw'
      (galTameRetr_ball (I := I) (M := M) g₀ a hR S hκ0 hκ w')
    rwa [dist_eq_norm, Subtype.dist_eq, dist_eq_norm] at h
  have hst := galTameState_lip (I := I) (M := M) g₀ a hR S hκ0 hκ w w'
  have hdecomp : galTameField (I := I) (M := M) g₀ a hR Nfun S w -
      galTameField (I := I) (M := M) g₀ a hR Nfun S w' =
      Dg (w - w') + Rst (Nfun uw - Nfun uw') := by
    simp only [galTameField, hEmb, hRst, hDg, huw, huw', map_sub]
    abel
  rw [dist_eq_norm, dist_eq_norm, hdecomp]
  have hstep : ‖Dg (w - w') + Rst (Nfun uw - Nfun uw')‖ ≤
      (‖Dg‖ + ‖Rst‖ * ((K : ℝ) * (Real.sqrt κ * ‖L‖))) * ‖w - w'‖ := by
    have h1 : ‖Dg (w - w')‖ ≤ ‖Dg‖ * ‖w - w'‖ := Dg.le_opNorm _
    have h2 : ‖Rst (Nfun uw - Nfun uw')‖ ≤ ‖Rst‖ * ‖Nfun uw - Nfun uw'‖ :=
      Rst.le_opNorm _
    have h3 : ‖Nfun uw - Nfun uw'‖ ≤
        (K : ℝ) * (Real.sqrt κ * ‖L‖ * ‖w - w'‖) := by
      refine hN.trans ?_
      exact mul_le_mul_of_nonneg_left hst K.coe_nonneg
    have h4 : ‖Rst‖ * ‖Nfun uw - Nfun uw'‖ ≤
        ‖Rst‖ * ((K : ℝ) * (Real.sqrt κ * ‖L‖ * ‖w - w'‖)) :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg Rst)
    have h5 := norm_add_le (Dg (w - w')) (Rst (Nfun uw - Nfun uw'))
    nlinarith only [h1, h2, h4, h5]
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Real.coe_toNNReal']
  exact le_max_left _ _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameField_aff (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    {K : ℝ≥0}
    (hK : LipschitzOnWith K Nfun (galTameBall (I := I) (M := M) g₀ a R κ)) :
    ∃ (Cst : ℝ) (K' : ℝ≥0), 0 ≤ Cst ∧
      ∀ w : EuclideanSpace ℝ {i // i ∈ S},
        ‖galTameField (I := I) (M := M) g₀ a hR Nfun S w‖ ≤
          Cst + (K' : ℝ) * ‖w‖ := by
  set Emb := galerkinCoordEmbed (I := I) (M := M) g₀ a S with hEmb
  set Rst := galerkinCoordRestrict (I := I) (M := M) g₀ a S with hRst
  set Dg := galerkinCoordDiag (I := I) (M := M) g₀ S with hDg
  set N0 : TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR⟩ with hN0
  have hsqR : 0 ≤ Real.sqrt κ * R := mul_nonneg (Real.sqrt_nonneg κ) hR
  have hzeroMem : (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ a hR⟩ :
      lowerState (I := I) (M := M) g₀ a R) ∈
      galTameBall (I := I) (M := M) g₀ a R κ := by
    change dist (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) ≤ Real.sqrt κ * R
    rw [dist_self]
    exact hsqR
  refine ⟨‖Rst‖ * (‖N0‖ + (K : ℝ) * (Real.sqrt κ * R)), ‖Dg‖₊, by positivity, ?_⟩
  intro w
  set uw : lowerState (I := I) (M := M) g₀ a R :=
    ⟨Emb (galTameRetr (I := I) (M := M) g₀ a R S w),
      galTameRetr_mem (I := I) (M := M) g₀ a hR S w⟩ with huw
  have hNdiff : ‖Nfun uw - N0‖ ≤ (K : ℝ) * (Real.sqrt κ * R) := by
    have h := hK.dist_le_mul uw
      (galTameRetr_ball (I := I) (M := M) g₀ a hR S hκ0 hκ w) _ hzeroMem
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    exact galTameRetr_top (I := I) (M := M) g₀ a hR S hκ0 hκ w
  have hNbd : ‖Nfun uw‖ ≤ ‖N0‖ + (K : ℝ) * (Real.sqrt κ * R) := by
    have htri : ‖Nfun uw‖ ≤ ‖Nfun uw - N0‖ + ‖N0‖ := by
      simpa using norm_add_le (Nfun uw - N0) N0
    linarith
  have hdecomp : galTameField (I := I) (M := M) g₀ a hR Nfun S w =
      Dg w + Rst (Nfun uw) := rfl
  rw [hdecomp]
  have h1 : ‖Dg w‖ ≤ ‖Dg‖ * ‖w‖ := Dg.le_opNorm _
  have h2 : ‖Rst (Nfun uw)‖ ≤ ‖Rst‖ * ‖Nfun uw‖ := Rst.le_opNorm _
  have h3 : ‖Rst‖ * ‖Nfun uw‖ ≤
      ‖Rst‖ * (‖N0‖ + (K : ℝ) * (Real.sqrt κ * R)) :=
    mul_le_mul_of_nonneg_left hNbd (norm_nonneg Rst)
  have h4 := norm_add_le (Dg w) (Rst (Nfun uw))
  have hcoe : ((‖Dg‖₊ : ℝ≥0) : ℝ) = ‖Dg‖ := coe_nnnorm Dg
  rw [hcoe]
  linarith

open scoped Classical in
def galTameForce (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  if i ∈ S then
    (Nfun ⟨galTameStateC (I := I) (M := M) g₀ a R S c,
      galTameStateC_mem (I := I) (M := M) g₀ a hR S c⟩).coeff i
  else 0

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameStateC_eq (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ}
    (hc : ‖galLowView (I := I) (M := M) g₀ a
      (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2))‖ ≤ R) :
    galTameStateC (I := I) (M := M) g₀ a R S c =
      finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2) := by
  rcases eq_or_lt_of_le (norm_nonneg (galLowView (I := I) (M := M) g₀ a
    (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)))) with h0 | h0
  · have hview : galLowView (I := I) (M := M) g₀ a
        (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)) = 0 :=
      norm_eq_zero.mp h0.symm
    have hzero : finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2) = 0 := by
      refine tensorHsInclusion_injective (I := I) (M := M) (g := g₀) (r := 0)
        (s := 2) (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ?_
      rw [map_zero]
      exact hview
    rw [galTameStateC, hzero, smul_zero]
  · have hone : (1 : ℝ) ≤ R / ‖galLowView (I := I) (M := M) g₀ a
        (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2))‖ :=
      (one_le_div h0).2 hc
    rw [galTameStateC, min_eq_left hone, one_smul]

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameForce_eq (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    {c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ}
    (hc : ‖galLowView (I := I) (M := M) g₀ a
      (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2))‖ ≤ R)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galTameForce (I := I) (M := M) g₀ a hR Nfun S c i =
      if i ∈ S then
        (Nfun ⟨finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2), hc⟩).coeff i
      else 0 := by
  have hsub : (⟨galTameStateC (I := I) (M := M) g₀ a R S c,
      galTameStateC_mem (I := I) (M := M) g₀ a hR S c⟩ :
        lowerState (I := I) (M := M) g₀ a R) =
      ⟨finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2), hc⟩ :=
    Subtype.ext (galTameStateC_eq (I := I) (M := M) g₀ a S hc)
  rw [galTameForce, hsub]

open scoped Classical in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem galTameForce_apply (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galTameForce (I := I) (M := M) g₀ a hR Nfun S c i =
      if i ∈ S then
        (Nfun ⟨galTameStateC (I := I) (M := M) g₀ a R S c,
          galTameStateC_mem (I := I) (M := M) g₀ a hR S c⟩).coeff i
      else 0 := rfl

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameForce_contOn (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) {κ : ℝ}
    (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    {K : ℝ≥0}
    (hK : LipschitzOnWith K Nfun (galTameBall (I := I) (M := M) g₀ a R κ))
    {T : ℝ} (c : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hc : ∀ i ∈ S, ContinuousOn (fun t => c t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => galTameForce (I := I) (M := M) g₀ a hR Nfun S (c t) i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  by_cases hi : i ∈ S
  · obtain ⟨K', hK'⟩ :=
      galTameField_lip (I := I) (M := M) g₀ a hR Nfun S hκ0 hκ hK
    have hwcont : ContinuousOn (fun t : ℝ =>
        (EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c t j.1))
        (Set.Icc (0 : ℝ) T) := by
      refine (EuclideanSpace.equiv {i // i ∈ S} ℝ).symm.continuous.comp_continuousOn ?_
      exact continuousOn_pi.2 (fun j => hc j.1 j.2)
    have hproj : Continuous (fun y : EuclideanSpace ℝ {i // i ∈ S} =>
        y (⟨i, hi⟩ : {i // i ∈ S})) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (⟨i, hi⟩ : {i // i ∈ S})).continuous
    have hfield : ContinuousOn (fun t : ℝ =>
        (galTameField (I := I) (M := M) g₀ a hR Nfun S
            ((EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c t j.1)))
          (⟨i, hi⟩ : {i // i ∈ S})) (Set.Icc (0 : ℝ) T) :=
      (hproj.comp hK'.continuous).comp_continuousOn hwcont
    have hlin : ContinuousOn
        (fun t => TensorEigenIdx.lambda (I := I) (M := M) i * c t i)
        (Set.Icc (0 : ℝ) T) := continuousOn_const.mul (hc i hi)
    refine (hfield.add hlin).congr (fun t _ => ?_)
    simp only [Pi.add_apply]
    have hsub : (⟨galerkinCoordEmbed (I := I) (M := M) g₀ a S
          (galTameRetr (I := I) (M := M) g₀ a R S
            ((EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c t j.1))),
        galTameRetr_mem (I := I) (M := M) g₀ a hR S
          ((EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c t j.1))⟩ :
            lowerState (I := I) (M := M) g₀ a R) =
        ⟨galTameStateC (I := I) (M := M) g₀ a R S (c t),
          galTameStateC_mem (I := I) (M := M) g₀ a hR S (c t)⟩ :=
      Subtype.ext (galTameStateC_emb (I := I) (M := M) g₀ a R S (c t))
    have hval : (galTameField (I := I) (M := M) g₀ a hR Nfun S
          ((EuclideanSpace.equiv {i // i ∈ S} ℝ).symm (fun j => c t j.1)))
          (⟨i, hi⟩ : {i // i ∈ S}) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * c t i +
          (Nfun ⟨galTameStateC (I := I) (M := M) g₀ a R S (c t),
            galTameStateC_mem (I := I) (M := M) g₀ a hR S (c t)⟩).coeff i := by
      rw [galTameField_apply, hsub]
      rfl
    rw [galTameForce_apply, if_pos hi, hval]
    ring
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun t _ => ?_)
    rw [galTameForce_apply, if_neg hi]

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTameSolOne (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    {A B C Rt : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hRt : 0 ≤ Rt)
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ a R,
      ‖Nfun u - Nfun v‖ ≤
        A * Rt * ‖(u : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (v : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
          B * ‖galLowView (I := I) (M := M) g₀ a
            ((u : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (v : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)))‖ +
          C * (‖(u : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ +
              ‖(v : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ a
              ((u : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
                (v : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)))‖)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) {κ : ℝ}
    (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    {T : ℝ} (hT : 0 < T) :
    ∃ V : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => V r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
            galTameForce (I := I) (M := M) g₀ a hR Nfun S (V t) i)
          (Set.Ici t) t) ∧
      (∀ i, V 0 i = 0) ∧
      (∀ t, ∀ i, i ∉ S → V t i = 0) := by
  classical
  obtain ⟨K, hK⟩ :=
    tame_lip_balls (X := TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (D := lowerState (I := I) (M := M) g₀ a R) Nfun
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) id isometry_id rfl
      (galLowView (I := I) (M := M) g₀ a) A B C Rt hA hB hC hRt htame
      (Real.sqrt κ * R)
  have hKball : LipschitzOnWith K Nfun
      (galTameBall (I := I) (M := M) g₀ a R κ) := hK
  obtain ⟨Klip, hKlip⟩ :=
    galTameField_lip (I := I) (M := M) g₀ a hR Nfun S hκ0 hκ hKball
  obtain ⟨Cst, Kaff, hCst, hAff⟩ :=
    galTameField_aff (I := I) (M := M) g₀ a hR Nfun S hκ0 hκ hKball
  set Kmax : ℝ≥0 := max Klip Kaff with hKmax
  have hlip_t : ∀ t ∈ Set.Icc (0 : ℝ) T,
      LipschitzWith Kmax (galTameField (I := I) (M := M) g₀ a hR Nfun S) :=
    fun _ _ => hKlip.weaken (le_max_left _ _)
  have hcont_t : ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      ContinuousOn (fun _ : ℝ => galTameField (I := I) (M := M) g₀ a hR Nfun S x)
        (Set.Icc (0 : ℝ) T) := fun _ => continuousOn_const
  have haff_t : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      ‖galTameField (I := I) (M := M) g₀ a hR Nfun S x‖ ≤
        Cst + (Kmax : ℝ) * ‖x‖ := by
    intro _ _ x
    have h1 := hAff x
    have h2 : (Kaff : ℝ) * ‖x‖ ≤ (Kmax : ℝ) * ‖x‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
      exact_mod_cast le_max_right Klip Kaff
    linarith
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound
      (E := EuclideanSpace ℝ {i // i ∈ S})
      (f := fun _ => galTameField (I := I) (M := M) g₀ a hR Nfun S) hT hCst
      hlip_t hcont_t haff_t (0 : EuclideanSpace ℝ {i // i ∈ S})
  refine ⟨fun t i => if h : i ∈ S then (γ t) ⟨i, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hcoord : ContinuousOn (fun t => (γ t).ofLp ⟨i, hi⟩)
        (Set.Icc (0 : ℝ) T) := by
      have hproj : Continuous (fun y : EuclideanSpace ℝ {i // i ∈ S} =>
          y.ofLp (⟨i, hi⟩ : {i // i ∈ S})) :=
        (EuclideanSpace.proj (𝕜 := ℝ) (⟨i, hi⟩ : {i // i ∈ S})).continuous
      exact hproj.comp_continuousOn hγcont
    refine hcoord.congr (fun t _ => ?_)
    simp only [dif_pos hi]
  · intro t ht i hi
    have hderiv_proj := ((EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩).hasFDerivAt
      (x := γ t)).comp_hasDerivWithinAt t (hγderiv t ht)
    have hderiv_proj' :
        HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
          ((EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩)
            (galTameField (I := I) (M := M) g₀ a hR Nfun S (γ t)))
          (Set.Ici (0 : ℝ)) t := hderiv_proj
    have hstate : galerkinCoordEmbed (I := I) (M := M) g₀ a S
        (galTameRetr (I := I) (M := M) g₀ a R S (γ t)) =
        galTameStateC (I := I) (M := M) g₀ a R S
          (fun i => if h : i ∈ S then (γ t) ⟨i, h⟩ else 0) :=
      galTameState_eq (I := I) (M := M) g₀ a R S (γ t)
    have hRHS : (EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩)
        (galTameField (I := I) (M := M) g₀ a hR Nfun S (γ t)) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (if h : i ∈ S then (γ t) ⟨i, h⟩ else 0) +
          galTameForce (I := I) (M := M) g₀ a hR Nfun S
            (fun i => if h : i ∈ S then (γ t) ⟨i, h⟩ else 0) i := by
      rw [EuclideanSpace.coe_proj]
      change (galTameField (I := I) (M := M) g₀ a hR Nfun S (γ t)) ⟨i, hi⟩ = _
      have hsub : (⟨galerkinCoordEmbed (I := I) (M := M) g₀ a S
            (galTameRetr (I := I) (M := M) g₀ a R S (γ t)),
          galTameRetr_mem (I := I) (M := M) g₀ a hR S (γ t)⟩ :
            lowerState (I := I) (M := M) g₀ a R) =
          ⟨galTameStateC (I := I) (M := M) g₀ a R S
              (fun i => if h : i ∈ S then (γ t) ⟨i, h⟩ else 0),
            galTameStateC_mem (I := I) (M := M) g₀ a hR S
              (fun i => if h : i ∈ S then (γ t) ⟨i, h⟩ else 0)⟩ :=
        Subtype.ext hstate
      rw [galTameField_apply, galTameForce_apply, if_pos hi, dif_pos hi, hsub]
    have hfinal : HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (if h : i ∈ S then (γ t) ⟨i, h⟩ else 0) +
          galTameForce (I := I) (M := M) g₀ a hR Nfun S
            (fun i => if h : i ∈ S then (γ t) ⟨i, h⟩ else 0) i)
        (Set.Ici (0 : ℝ)) t := hRHS ▸ hderiv_proj'
    have hIci : HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩) _ (Set.Ici t) t :=
      DifferentialGeometry.Analysis.ODE.hasDerivWithinAt_Ici_of_Ici_zero hfinal
        ht.1
    have hcongr : (fun r => if h : i ∈ S then (γ r) ⟨i, h⟩ else 0) =
        (fun r => (γ r).ofLp ⟨i, hi⟩) := by
      funext r; rw [dif_pos hi]
    rw [hcongr]
    convert hIci using 2
  · intro i
    by_cases hi : i ∈ S
    · simp only [dif_pos hi, hγ0]
      rfl
    · simp only [dif_neg hi]
  · intro t i hi
    simp only [dif_neg hi]

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galTamePerMode (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (Nfun : lowerState (I := I) (M := M) g₀ a R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) {κ : ℝ}
    (hκ0 : 0 ≤ κ)
    (hκ : ∀ i ∈ S, 1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ κ)
    {K : ℝ≥0}
    (hK : LipschitzOnWith K Nfun (galTameBall (I := I) (M := M) g₀ a R κ))
    {T : ℝ} (hT : 0 < T) (c : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hcont : ∀ i ∈ S, ContinuousOn (fun t => c t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => c r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * c t i +
          galTameForce (I := I) (M := M) g₀ a hR Nfun S (c t) i)
        (Set.Ici t) t)
    (hzero : ∀ i ∈ S, c 0 i = 0)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (hi : i ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    c t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          galTameForce (I := I) (M := M) g₀ a hR Nfun S (c p.1) i)) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set fForce : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      galTameForce (I := I) (M := M) g₀ a hR Nfun S (c p.1) i) with hfForce_def
  have hfForce_cont : Continuous fForce := by
    refine Continuous.Icc_extend' ?_
    exact (galTameForce_contOn (I := I) (M := M) g₀ a hR Nfun S hκ0 hκ hK c
      hcont i).domRestrict
  have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      fForce x = galTameForce (I := I) (M := M) g₀ a hR Nfun S (c x) i := by
    intro x hx
    rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
  set v : ℝ → ℝ → ℝ := fun s y => -lam * y + fForce s with hv_def
  have hv_lip : ∀ s ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith ⟨|lam|, abs_nonneg lam⟩
      (v s) (Set.univ : Set ℝ) := by
    intro s _
    have hlip : LipschitzWith ⟨|lam|, abs_nonneg lam⟩
        (fun y : ℝ => -lam * y + fForce s) := by
      refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
      rw [Real.dist_eq, Real.dist_eq]
      have heq : -lam * y₁ + fForce s - (-lam * y₂ + fForce s) =
          -lam * (y₁ - y₂) := by ring
      rw [heq, abs_mul, abs_neg]
      change |lam| * |y₁ - y₂| ≤ |lam| * |y₁ - y₂|
      exact le_rfl
    exact hlip.lipschitzOnWith
  set gG : ℝ → ℝ := fun s => c s i with hgG_def
  set gP : ℝ → ℝ := fun s => perModeConv lam fForce s with hgP_def
  have hgG_cont : ContinuousOn gG (Set.Icc (0 : ℝ) T) := hcont i hi
  have hgP_cont : ContinuousOn gP (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hfForce_cont).continuousOn
  have hgG_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt gG (v s (gG s)) (Set.Ici s) s := by
    intro s hs
    have hd := hderiv s hs i hi
    have hforce_eq : fForce s =
        galTameForce (I := I) (M := M) g₀ a hR Nfun S (c s) i :=
      hfForce_mem ⟨hs.1, le_of_lt hs.2⟩
    have hval : v s (gG s) =
        -lam * c s i + galTameForce (I := I) (M := M) g₀ a hR Nfun S (c s) i := by
      simp only [hv_def, hgG_def, hforce_eq]
    rw [hval]
    exact hd
  have hgP_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt gP (v s (gP s)) (Set.Ici s) s := by
    intro s _
    have hd := (perModeConv_hasDerivAt lam hfForce_cont s).hasDerivWithinAt
      (s := Set.Ici s)
    have hval : v s (gP s) = fForce s - lam * perModeConv lam fForce s := by
      simp only [hv_def, hgP_def]; ring
    rw [hval]
    exact hd
  have hinit : gG 0 = gP 0 := by
    simp only [hgG_def, hgP_def, hzero i hi, perModeConv_zero_left]
  have heqOn : Set.EqOn gG gP (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hgG_cont
      (fun s hs => hgG_deriv s hs) (fun s _ => Set.mem_univ _)
      hgP_cont (fun s hs => hgP_deriv s hs) (fun s _ => Set.mem_univ _) hinit
  exact heqOn ht

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
