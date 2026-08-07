import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSSectionCalculus
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def NormalFormFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (p rr : ℕ) : Prop :=
  ∃ Q : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + k) (rr + d + p) I,
    ∀ W : SmoothCcTensor g r rr,
      op p rr W =
        ∑ k ∈ Finset.range (p + 1),
          homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
            (iteratedCovGrad g r rr k W)


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalForm_zeroFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (rr : ℕ) (Q₀ : HomTensorRSField (E := E) (M := M) r (rr + 0) (rr + d + 0) I)
    (hbase : ∀ W : SmoothCcTensor g r rr,
      op 0 rr W = homTensorRSFieldApply (I := I) (M := M) g r (rr + 0) (rr + d + 0) Q₀ W) :
    NormalFormFull (E := E) (I := I) (M := M) g r d op 0 rr := by
  refine ⟨fun k => match k with | 0 => Q₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_normalFormFull_sum (g : SmoothRiemannianMetric I M) (r d p rr : ℕ)
    (Q : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + k) (rr + d + p) I)
    (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + d + p)
        (∑ k ∈ Finset.range (p + 1),
          homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
            (iteratedCovGrad g r rr k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + (p + 1))
            (homTensorRSCovGradSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k))
            (iteratedCovGrad g r rr k W) +
          homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
            (slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k))
            (iteratedCovGrad g r rr (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appFullSec_eq (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
    (iteratedCovGrad g r rr k W)]
  rw [show covGrad (I := I) (M := M) g r (rr + k) (iteratedCovGrad g r rr k W) =
      iteratedCovGrad g r rr (k + 1) W from (iteratedCovGrad_succ g r rr k W).symm]
  rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem castRankCc_appFullSec_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M)
    (r d p rr k : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r ((rr + 1) + k) ((rr + 1) + d + p) I)
    (W : SmoothCcTensor g r rr) :
    castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
        (homTensorRSFieldApply (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + d + p) Q
          (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))) =
      homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
        (castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1))
          (by omega : (rr + 1) + k = rr + (k + 1))
          (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
            (by omega : (rr + 1) + d + p = rr + d + (p + 1)) Q))
        (iteratedCovGrad g r rr (k + 1) W) := by
  rw [appFullSec_castRankCc_db (E := E) g r (by omega : (rr + 1) + k = rr + (k + 1))
    (by omega : (rr + 1) + d + p = rr + d + (p + 1)) Q
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g r rr k W)
  exact castRankCc_db_heq g r (by omega : (rr + 1) + k = rr + (k + 1))
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))


omit [NeZero (Module.finrank ℝ E)] in
theorem normalFormFull_succ (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + d + p) (op p rr W) =
        op (p + 1) rr W +
          castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (p : ℕ) (hp : ∀ rr, NormalFormFull (E := E) (I := I) (M := M) g r d op p rr) (rr : ℕ) :
    NormalFormFull (E := E) (I := I) (M := M) g r d op (p + 1) rr := by
  classical
  obtain ⟨Qr, hQr⟩ := hp rr
  obtain ⟨Qr1, hQr1⟩ := hp (rr + 1)
  set Tk : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + (k + 1)) (rr + d + (p + 1)) I := fun
    k =>
    slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k) -
      castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1))
        (by omega : (rr + 1) + k = rr + (k + 1))
        (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
          (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (rr + 0) (rr + d + p) (Qr 0)
    | (k + 1) =>
        (if h : k + 1 < p + 1 then
          homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
          else 0) + Tk k, ?_⟩
  intro W
  have hrec : op (p + 1) rr W =
      covGrad g r (rr + d + p) (op p rr W) -
        castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
          (op p (rr + 1) (covGrad g r rr W)) := by
    rw [covGrad_op p rr W]; abel
  rw [hrec, hQr W]
  rw [covGrad_normalFormFull_sum (I := I) (M := M) g r d p rr Qr W]
  rw [hQr1 (covGrad g r rr W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
          (homTensorRSFieldApply (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + d + p) (Qr1 k)
            (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W)))) =
      ∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1))
            (by omega : (rr + 1) + k = rr + (k + 1))
            (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
              (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k)))
          (iteratedCovGrad g r rr (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appFullSec_iteratedCovGrad_covGrad (E := E) (I := I) (M := M) g r d p rr k (Qr1 k)
        W)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun j =>
    homTensorRSFieldApply (I := I) (M := M) g r (rr + j) (rr + d + (p + 1))
      ((match j with
        | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (rr + 0) (rr + d + p) (Qr 0)
        | (k + 1) =>
            (if h : k + 1 < p + 1 then
              homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g r rr j W)) (p + 1)]
  rw [show (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          ((if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appFullSec_add_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k))
          (iteratedCovGrad g r rr (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1))
            (by omega : (rr + 1) + k = rr + (k + 1))
            (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
              (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k)))
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appFullSec_sub_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1)))
          (iteratedCovGrad g r rr (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [dif_neg (by omega : ¬ (p + 1 < p + 1)), appFullSec_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [dif_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
  rw [Finset.sum_range_succ' (fun k =>
    homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + (p + 1))
      (homTensorRSCovGradSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k))
      (iteratedCovGrad g r rr k W)) p]
  abel


omit [NeZero (Module.finrank ℝ E)] in
theorem normalFormFull_of_base (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + d + p) (op p rr W) =
        op (p + 1) rr W +
          castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (Q₀ : ∀ rr : ℕ, HomTensorRSField (E := E) (M := M) r (rr + 0) (rr + d + 0) I)
    (hbase : ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
      op 0 rr W = homTensorRSFieldApply (I := I) (M := M) g r (rr + 0) (rr + d + 0) (Q₀ rr) W)
    (p : ℕ) : ∀ rr : ℕ, NormalFormFull (E := E) (I := I) (M := M) g r d op p rr := by
  induction p with
  | zero => exact fun rr => normalForm_zeroFull (E := E) (I := I) (M := M) g r d op rr (Q₀ rr)
                              (hbase rr)
  | succ p ih =>
      exact fun rr => normalFormFull_succ (E := E) (I := I) (M := M) g r d op covGrad_op p ih rr

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_jet_bound_of_normalFormFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (p rr : ℕ) (hNF : NormalFormFull (E := E) (I := I) (M := M) g r d op p rr) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + d + p) x ((op p rr W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨Q, hQ⟩ := hNF
  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (rr + k) (rr + d + p)
      (fun x : M => Q k x) (Q k).contMDiff
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g r (rr + k) x
    ((iteratedCovGrad g r rr k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + k) x _
  rw [hQ W, SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (rr + d + p) x
    (Finset.range (p + 1))
    (fun k => (homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
      (iteratedCovGrad g r rr k W)).toSection x)) ?_
  rw [Finset.card_range]
  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + d + p) x
          ((homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
            (iteratedCovGrad g r rr k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_
  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring
end Connection
end Geometry
end DifferentialGeometry
end
