import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ForcedTimeH1Energy
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergEstimate
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergSourceIntegral
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalNirenbergEstimate
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem integral_time_shift_weight
    (a b : ℝ) (ζ g : ℝ → ℝ) :
    (∫ s, ζ s * g (a + s) ∂timeMeasure (b - a)) =
      ∫ t in Icc a b, ζ (t - a) * g t := by
  have hshift : MeasurePreserving (fun s : ℝ => a + s)
      (timeMeasure (b - a)) (volume.restrict (Icc a b)) := by
    have h := (measurePreserving_add_right volume a).restrict_image_emb
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
    simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm a] using h
  simpa only [add_sub_cancel_left] using
    hshift.integral_comp (Homeomorph.addLeft a).isClosedEmbedding.measurableEmbedding
      (fun t => ζ (t - a) * g t)

private theorem integral_time_shift
    (a b : ℝ) (g : ℝ → ℝ) :
    (∫ s, g (a + s) ∂timeMeasure (b - a)) = ∫ t in Icc a b, g t := by
  simpa only [one_mul] using integral_time_shift_weight a b (fun _ => 1) g

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

private theorem integral_neg_bilinear_comp_le_on
    {a b : ℝ} (hab : a ≤ b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) μ)
    {CF : ℝ} (hCF : ∀ᵐ t ∂μ, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (u : Lp X 2 μ)
    (ℓ β : Lp (X →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (hwmass : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (u (a + s)))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp X 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, F t (u t) (z t) ∂μ)
    (L : X →L[ℝ] X)
    (hBL : (-(B.bilinearComp (ContinuousLinearMap.id ℝ X) L)).flip =
      -(B.bilinearComp (ContinuousLinearMap.id ℝ X) L))
    (hBLpos : ∀ x, 0 ≤ -(B x (L x)))
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζb : ζ (b - a) = 0) :
    (∫ t, ζ (t - a) * -(F t (u t) (L (u t))) ∂μ) ≤
      (3 * (K : ℝ) / 2) * (∫ t, -(B (u t) (L (u t))) ∂μ) +
        ∫ t, ζ (t - a) * -(β t (L (u t))) ∂μ := by
  have he := integral_neg_bilinear_comp_le_of_timeH1_mass_dual_integral_on hab μ hμ
    F hF hCF B u ℓ β w hwmass hwderiv hpair L hBL hBLpos
    hζsmooth hζ hζpos hζlip hζ0 hζb
  rw [integral_time_shift_weight a b ζ (fun t => -(F t (u t) (L (u t)))),
    integral_time_shift a b (fun t => -(B (u t) (L (u t)))),
    integral_time_shift_weight a b ζ (fun t => -(β t (L (u t))))] at he
  simpa only [hμ] using he

private theorem integral_energy_le_of_coercivity
    {a b : ℝ} (hab : a ≤ b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) μ)
    {CF : ℝ} (hCF : ∀ᵐ t ∂μ, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (u : Lp X 2 μ)
    (ℓ β : Lp (X →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (hwmass : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (u (a + s)))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp X 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, F t (u t) (z t) ∂μ)
    (L : X →L[ℝ] X)
    (hBL : (-(B.bilinearComp (ContinuousLinearMap.id ℝ X) L)).flip =
      -(B.bilinearComp (ContinuousLinearMap.id ℝ X) L))
    (hBLpos : ∀ x, 0 ≤ -(B x (L x)))
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζb : ζ (b - a) = 0)
    {E P : ℝ → ℝ} (hE : Integrable E μ) {lam C0 C1 Cf Cr : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ᵐ t ∂μ, lam / 2 * E t ≤ -(F t (u t) (L (u t))) + C0 * ‖u t‖^2)
    (hmass : ∀ x, -(B x (L x)) ≤ C1 * ‖x‖^2)
    (hsource : |∫ t, ζ (t - a) * β t (L (u t)) ∂μ| ≤
      lam / 4 * (∫ t, ζ (t - a) * E t ∂μ) +
        Cf * (∫ t, ζ (t - a) * P t ∂μ) + Cr * (∫ t, ζ (t - a) * ‖u t‖^2 ∂μ)) :
    (∫ t, ζ (t - a) * E t ∂μ) ≤ (4 / lam) *
      ((3 * (K : ℝ) / 2) * C1 * (∫ t, ‖u t‖^2 ∂μ) +
        (C0 + Cr) * (∫ t, ζ (t - a) * ‖u t‖^2 ∂μ) +
          Cf * (∫ t, ζ (t - a) * P t ∂μ)) := by
  have he := integral_neg_bilinear_comp_le_on hab μ hμ F hF hCF B u ℓ β w
    hwmass hwderiv hpair L hBL hBLpos hζsmooth hζ hζpos hζlip hζ0 hζb
  have hshift : MeasurePreserving (fun t : ℝ => t - a) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-a)
  have hχ : MemLp (fun t => ζ (t - a)) ∞ μ := by
    rw [hμ]
    exact (hζ.comp_measurePreserving hshift).restrict _
  have hχpos : ∀ᵐ t ∂μ, 0 ≤ ζ (t - a) := by
    rw [hμ]
    exact (hshift.quasiMeasurePreserving.ae hζpos).filter_mono (ae_mono Measure.restrict_le_self)
  have huI : Integrable (fun t => ‖u t‖^2) μ := (Lp.memLp u).norm.integrable_sq
  have hLE : MemLp (fun t => L (u t)) 2 μ := (Lp.memLp u).continuousLinearMap_comp L
  have hFI : Integrable (fun t => -(F t (u t) (L (u t)))) μ :=
    (integrable_bilinear_of_apply_aestronglyMeasurable F hF hCF
      (Lp.memLp u) hLE).neg
  have hBI : Integrable (fun t => -(B (u t) (L (u t)))) μ :=
    (integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      (Lp.memLp u) hLE).neg
  have hmassI := integral_mono_ae hBI (huI.const_mul C1)
    (Eventually.of_forall fun t => hmass (u t))
  rw [integral_const_mul] at hmassI
  have hcoerI := integral_mono_ae ((hE.mul_of_top_right hχ).const_mul (lam / 2))
    ((hFI.mul_of_top_right hχ).add ((huI.mul_of_top_right hχ).const_mul C0))
      (by
        filter_upwards [hcoer, hχpos] with t ht hζt
        simpa only [Pi.mul_apply, Pi.add_apply, mul_add, mul_assoc, mul_left_comm (ζ (t - a))]
          using mul_le_mul_of_nonneg_left ht hζt)
  simp only [Pi.mul_apply, Pi.add_apply] at hcoerI
  have hsum : (∫ t, ζ (t - a) * -(F t (u t) (L (u t))) +
      C0 * (ζ (t - a) * ‖u t‖^2) ∂μ) =
      (∫ t, ζ (t - a) * -(F t (u t) (L (u t))) ∂μ) +
        C0 * (∫ t, ζ (t - a) * ‖u t‖^2 ∂μ) := by
    rw [integral_add (show Integrable (fun t => ζ (t - a) * -(F t (u t) (L (u t)))) μ from
      hFI.mul_of_top_right hχ)
      (show Integrable (fun t => C0 * (ζ (t - a) * ‖u t‖^2)) μ from
        (huI.mul_of_top_right hχ).const_mul C0), integral_const_mul]
  rw [hsum, integral_const_mul] at hcoerI
  have hnegative : (∫ t, ζ (t - a) * -(β t (L (u t))) ∂μ) ≤
      |∫ t, ζ (t - a) * β t (L (u t)) ∂μ| := by
    simpa only [mul_neg, integral_neg] using
      neg_le_abs (∫ t, ζ (t - a) * β t (L (u t)) ∂μ)
  have hmassbound := mul_le_mul_of_nonneg_left hmassI (show 0 ≤ 3 * (K : ℝ) / 2 by positivity)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlam).mpr
  have hb : lam * (∫ t, ζ (t - a) * E t ∂μ) ≤
      4 * ((3 * (K : ℝ) / 2) * C1 * (∫ t, ‖u t‖^2 ∂μ) +
        (C0 + Cr) * (∫ t, ζ (t - a) * ‖u t‖^2 ∂μ) +
          Cf * (∫ t, ζ (t - a) * P t ∂μ)) := by
    nlinarith only [he, hcoerI, hnegative, hsource, hmassbound]
  nlinarith only [hb]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev


open Bundle
namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))


omit [NeZero n] in
private theorem cutoff_diffQuot_integral_le_restrict
    {f η : EuStd → ℝ} (hη : Continuous η) (hfmeas : AEStronglyMeasurable f (volume.restrict (tsupport η))) (hηb : ∀ z, |η z| ≤ 1)
    (hf : Integrable (fun z => f z ^ 2) (volume.restrict (tsupport η))) :
    (∫ z, (η z * f z)^2) ≤ ∫ z in tsupport η, f z^2 := by
  have hsq (z) : (η z)^2 ≤ 1 := by nlinarith [sq_nonneg (η z), hηb z, neg_abs_le (η z), le_abs_self (η z)]
  have heq : (∫ z, (η z * f z)^2) = ∫ z in tsupport η, (η z * f z)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_pow (by decide)]
  rw [heq]
  have hg : Integrable (fun z => (η z*f z)^2) (volume.restrict (tsupport η)) := by
    apply hf.mono' ?_ ?_
    · exact (hη.aestronglyMeasurable.mul hfmeas).pow 2
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_sq, mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (hsq z)
  apply integral_mono_ae hg hf
  filter_upwards [] with z
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (hsq z)



private theorem exists_cutoff_diffQuot_integral_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      Metric.cthickening δ (tsupport η) ⊆ Ω ∧
      ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ), |h| ≤ δ → ∀ u : H1ComplDirichlet q,
      let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
      (∫ z, (η z * Sobolev.diffQuot k h (fun z => H1ComplDirichletToLp q u (x z)) z)^2) ≤
        C * ‖u‖^2 := by
  obtain ⟨δ, hδ, C, hC, hroom, hbound⟩ :=
    exists_integral_sq_weakPartial_diffQuot_chartInverse_le q α hΩ hΩc hΩs hηc hηs
  refine ⟨δ, hδ, C, hC, hroom, ?_⟩
  intro k h hh u x
  let U := fun z => H1ComplDirichletToLp q u (x z)
  have hU : MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hD := Sobolev.memLp_diffQuot_restrict hΩ.measurableSet (isClosed_tsupport η).measurableSet
    hU k h ((Metric.cthickening_mono hh _).trans hroom)
  have hb := hbound k h hh u
  have hnonneg : 0 ≤ ∑ i, ∫ z in tsupport η,
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z)^2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  exact (cutoff_diffQuot_integral_le_restrict hη hD.aestronglyMeasurable hηb hD.integrable_sq).trans
    (le_trans (le_add_of_nonneg_left hnonneg) hb)

end DifferentialGeometry.Analysis.Parabolic.Dirichlet


namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))
private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

private theorem integral_mul_chart_source_dual_comp_eq
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ : ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) = ∫ t, (∫ y in Ω, f (t, y) * H1ComplDirichletToLp q (z t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ)
    (L : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q)
    (v : Lp (H1ComplDirichlet q) 2 μ)
    {ζ : Z → ℝ} (hζ : MemLp ζ ∞ μ) :
    (∫ t, ζ t * β t (L (v t)) ∂μ) =
      ∫ t, ζ t * (∫ y in Ω, f (t, y) * H1ComplDirichletToLp q (L (v t))
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ := by
  have hz : MemLp (fun t => ζ t • L (v t)) 2 μ :=
    ((Lp.memLp v).continuousLinearMap_comp L).smul hζ
  let z := hz.toLp (fun t => ζ t • L (v t))
  have hzeq : (z : Z → H1ComplDirichlet q) =ᵐ[μ] fun t => ζ t • L (v t) := hz.coeFn_toLp
  calc
    (∫ t, ζ t * β t (L (v t)) ∂μ) = ∫ t, β t (z t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hzeq] with t ht
      rw [ht, map_smul, smul_eq_mul]
    _ = _ := (hβ z).trans (by
      apply integral_congr_ae
      filter_upwards [hzeq] with t ht
      rw [ht, map_smul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset))
        (Lp.coeFn_smul (ζ t) (H1ComplDirichletToLp q (L (v t))))] with y hy
      rw [hy, Pi.smul_apply, smul_eq_mul]
      ring)


private theorem abs_integral_mul_chart_source_dual_dirichletNirenbergTest_le
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (v : Lp (H1ComplDirichlet q) 2 μ)
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ : ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) = ∫ t, (∫ y in Ω, f (t, y) * H1ComplDirichletToLp q (z t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ)
    {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    {ζ : Z → ℝ} (hζ : MemLp ζ ∞ μ) (hζpos : ∀ᵐ t ∂μ, 0 ≤ ζ t) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun t z => H1ComplDirichletToLp q (v t) (x z)
    |∫ t, ζ t * β t (smoothMulH1ComplDirichlet q φ
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom (v t))) ∂μ| ≤
      ε * (∫ t, ζ t * (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (v t)) z)^2) ∂μ) +
      (2 * ε)⁻¹ * (phiSupBound q φ)^2 * (∫ t, ζ t * (∫ z in Ω, (f (t, z))^2) ∂μ) +
      4 * ε * N^2 * (∫ t, ζ t * (∫ z in tsupport η, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (U t) z)^2) ∂μ) := by
  intro x U
  let L := (smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom)
  have hp := integral_mul_chart_source_dual_comp_eq q α hΩ hΩc hΩs f β hβ L v hζ
  dsimp only [L, ContinuousLinearMap.comp_apply] at hp
  rw [hp]
  exact abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le
    q α hΩ hΩc hΩs φ v f hη hηc hηb k hηd hε h hroom hζ hζpos

private theorem exists_abs_integral_mul_chart_source_dual_dirichletNirenbergTest_sum_le
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (hηs : tsupport η ⊆ Ω)
    {N lam : ℝ} (hηd : ∀ k x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    (hlam : 0 < lam) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ Metric.cthickening δ (tsupport η) ⊆ Ω ∧
      ∀ (v : Lp (H1ComplDirichlet q) 2 μ) (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
        (β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ),
      (∀ z : Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, β t (z t) ∂μ) = ∫ t, (∫ y in Ω, f (t, y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ) →
      ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ), |h| ≤ δ →
        ∀ ζ : Z → ℝ, MemLp ζ ∞ μ → (∀ᵐ t ∂μ, 0 ≤ ζ t) →
      ∀ hroom : Metric.cthickening |h| (tsupport η) ⊆ Ω,
      |∫ t, ζ t * β t (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom (v t))) ∂μ| ≤
        lam / 4 * (∫ t, ζ t * (∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z)^2) ∂μ) +
        (2 / lam) * (phiSupBound q φ)^2 * (∫ t, ζ t * (∫ z in Ω, (f (t, z))^2) ∂μ) +
        lam * N^2 * C * (∫ t, ζ t * ‖v t‖^2 ∂μ) := by
  obtain ⟨δ, hδ, C, hC, hroom, hbound⟩ :=
    exists_integral_sq_weakPartial_diffQuot_chartInverse_le q α hΩ hΩc hΩs hηc hηs
  refine ⟨δ, C, hδ, hC, hroom, ?_⟩
  intro v f β hβ k h hh ζ hζ hζpos hroomh
  let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
  let U := fun t z => H1ComplDirichletToLp q (v t) (x z)
  let Ei := fun i t => ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z)^2
  let R := fun t => ∫ z in tsupport η, (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (U t) z)^2
  have hEi (i) : Integrable (Ei i) μ :=
    DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
      hΩ.measurableSet (hη.continuous.memLp_of_hasCompactSupport hηc) k h
        ((Metric.cthickening_mono hh _).trans hroom)
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp v)
  have hsum : Integrable (fun t => ∑ i, Ei i t) μ := integrable_finsetSum _ (fun i _ => hEi i)
  have hsingle : (∫ t, ζ t * Ei k t ∂μ) ≤ ∫ t, ζ t * (∑ i, Ei i t) ∂μ := by
    apply integral_mono_ae ((hEi k).mul_of_top_right hζ) (hsum.mul_of_top_right hζ)
    filter_upwards [hζpos] with t ht
    apply mul_le_mul_of_nonneg_left _ ht
    exact Finset.single_le_sum (f := fun i => Ei i t) (fun i _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ k)
  have hRbound (t) : R t ≤ C * ‖v t‖^2 := by
    have hb := hbound k h hh (v t)
    have hnonneg : 0 ≤ ∑ i, ∫ z in tsupport η,
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) z)^2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
    exact (le_add_of_nonneg_left hnonneg).trans hb
  have hRmeas : AEStronglyMeasurable R μ := by
    have hK := (isClosed_tsupport η).measurableSet
    let A := (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
    have hi := DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_diffQuot_on_comp
      hΩ.measurableSet hK k h ((Metric.cthickening_mono hh _).trans hroom) A (Lp.memLp v)
    apply hi.aestronglyMeasurable.congr
    filter_upwards [] with t
    apply integral_congr_ae
    apply (DifferentialGeometry.Analysis.Sobolev.diffQuot_congr_ae_on hΩ.measurableSet hK k h
      ((Metric.cthickening_mono hh _).trans hroom)
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q (v t)))).fun_comp (· ^ 2)
  have hRint : Integrable R μ := ((Lp.memLp v).norm.integrable_sq.const_mul C).mono'
    hRmeas (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact hRbound t)
  have hRI := integral_mono_ae (hRint.mul_of_top_right hζ)
    (((Lp.memLp v).norm.integrable_sq.mul_of_top_right hζ).const_mul C) (by
      filter_upwards [hζpos] with t ht
      change ζ t * R t ≤ C * (ζ t * ‖v t‖^2)
      nlinarith only [mul_le_mul_of_nonneg_left (hRbound t) ht])
  rw [integral_const_mul] at hRI
  have hs := abs_integral_mul_chart_source_dual_dirichletNirenbergTest_le
    q α hΩ hΩc hΩs φ v f β hβ hη hηc hηb k (hηd k)
      (show 0 < lam / 4 by positivity) h ((Metric.cthickening_mono hh _).trans hroom) hζ hζpos
  have hcoeff : (2 * (lam / 4))⁻¹ = 2 / lam := by field_simp; norm_num
  rw [hcoeff] at hs
  dsimp only [Ei, R, U, x, Pi.mul_apply] at hsingle hRI hs
  have hm := mul_le_mul_of_nonneg_left hsingle (show 0 ≤ lam / 4 by positivity)
  have hr := mul_le_mul_of_nonneg_left hRI (show 0 ≤ lam * N^2 by positivity)
  nlinarith only [hs, hm, hr]

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem exists_local_dirichlet_nirenberg_time_energy_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc a b, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ Metric.cthickening δ (tsupport η) ⊆ Ω ∧
      ∀ (v : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)))
        (f : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
        (ℓ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (volume.restrict (Icc a b)))
        (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a)),
      (∀ᵐ s ∂timeMeasure (b - a), ∀ z,
        w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z)) →
      (w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s)) →
      (∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
        (∫ t in Icc a b, ℓ t (z t)) = (∫ t in Icc a b, β t (z t)) -
          ∫ t in Icc a b, (∑ i, ∑ j, ∫ y in Ω,
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
              (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
              dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y)) →
      (∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
        (∫ t in Icc a b, β t (z t)) = ∫ t in Icc a b, (∫ y in Ω,
          f (t,y) * H1ComplDirichletToLp q (z t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y)))) →
      ∀ k h, |h| ≤ δ → ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ (b - a) = 0 →
        (∫ t in Icc a b, ζ (t - a) * (∑ i, ∫ z, (η z * Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z)^2)) ≤
          C * ((K:ℝ) * (∫ t in Icc a b, ‖v t‖^2) +
            (∫ t in Icc a b, ζ (t - a) * ‖v t‖^2) +
            (∫ t in Icc a b, ζ (t - a) * (∫ z in Ω, (f (t,z))^2))) := by
  let μ := volume.restrict (Icc a b)
  have he₀ := exists_local_dirichlet_nirenberg_lower_bound
    hG isCompact_Icc hreg q α hΩ hΩc hΩs φ hφ hη hηc hηs hηb hlam hcoer
  let δ₀ := he₀.choose
  have hδ₀ := he₀.choose_spec.1
  let C₀ := he₀.choose_spec.2.choose
  have hC₀ := he₀.choose_spec.2.choose_spec.1
  have hroom₀ := he₀.choose_spec.2.choose_spec.2.choose
  have hc₀ := he₀.choose_spec.2.choose_spec.2.choose_spec
  have he₁ := exists_cutoff_diffQuot_integral_le q α hΩ hΩc hΩs hη.continuous hηc hηs hηb
  let δ₁ := he₁.choose
  have hδ₁ := he₁.choose_spec.1
  let C₁ := he₁.choose_spec.2.choose
  have hC₁ := he₁.choose_spec.2.choose_spec.1
  have hroom₁ := he₁.choose_spec.2.choose_spec.2.1
  have hc₁ := he₁.choose_spec.2.choose_spec.2.2
  obtain ⟨N, hN⟩ := (hηc.fderiv ℝ).exists_bound_of_continuous (hη.continuous_fderiv (by simp))
  have hNbound k z : |fderiv ℝ η z (EuclideanSpace.single k 1)| ≤ N := by
    calc
      _ = ‖fderiv ℝ η z (EuclideanSpace.single k 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ η z‖ * ‖EuclideanSpace.single k (1:ℝ)‖ := (fderiv ℝ η z).le_opNorm _
      _ = ‖fderiv ℝ η z‖ := by rw [PiLp.norm_single, norm_one, mul_one]
      _ ≤ N := hN z
  have he₂ := exists_abs_integral_mul_chart_source_dual_dirichletNirenbergTest_sum_le
    (μ := μ) q α hΩ hΩc hΩs φ hη hηc hηb hηs hNbound hlam
  let δ₂ := he₂.choose
  let C₂ := he₂.choose_spec.choose
  have hδ₂ := he₂.choose_spec.choose_spec.1
  have hC₂ := he₂.choose_spec.choose_spec.2.1
  have hroom₂ := he₂.choose_spec.choose_spec.2.2.1
  have hc₂ := he₂.choose_spec.choose_spec.2.2.2
  let δ := min δ₀ (min δ₁ δ₂)
  let Cf := (2 / lam) * (Laplacian.phiSupBound q φ)^2
  let Cr := lam * N^2 * C₂
  let C := (4 / lam) * max (3 / 2 * C₁) (max (C₀ + Cr) Cf)
  have hCr : 0 ≤ Cr := by dsimp only [Cr]; positivity
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hd0 : δ ≤ δ₀ := min_le_left _ _
  have hd1 : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hd2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hroom : Metric.cthickening δ (tsupport η) ⊆ Ω := (Metric.cthickening_mono hd0 _).trans hroom₀
  refine ⟨δ, lt_min hδ₀ (lt_min hδ₁ hδ₂), C, hC, hroom, ?_⟩
  intro v f ℓ β w hwmass hwderiv hpair hsource k h hh ζ K hζsmooth hζ hζpos hζlip hζ0 hζb
  have hh0 := hh.trans hd0
  have hh1 := hh.trans hd1
  have hh2 := hh.trans hd2
  have hroomh := (Metric.cthickening_mono hh _).trans hroom
  let L := (smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroomh)
  let J := H1ComplDirichletToLp q
  let B := (innerSL ℝ).bilinearComp J J
  have hmass : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (v (a + s)) := by
    filter_upwards [hwmass] with s hs
    ext z
    exact hs z
  have hφ' : ∀ z ∈ Metric.cthickening |h| (tsupport η),
      chartDensity (I := I_hs) q α ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1 := by
    intro z hz
    exact hφ z (hroomh hz)
  obtain ⟨hsymm, hpos, hval⟩ := dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity
    q α hΩ hΩc hΩs hη hηc φ k h hroomh hφ'
  have hBL : (-(B.bilinearComp (ContinuousLinearMap.id ℝ (H1ComplDirichlet q)) L)).flip =
      -(B.bilinearComp (ContinuousLinearMap.id ℝ (H1ComplDirichlet q)) L) := by
    have heq : -(B.bilinearComp (ContinuousLinearMap.id ℝ (H1ComplDirichlet q)) L) =
        -(innerSL ℝ).bilinearComp J (J.comp L) := by ext x z; rfl
    rw [heq]
    exact hsymm
  have hBLpos (x : H1ComplDirichlet q) : 0 ≤ -(B x (L x)) := hpos x
  have hmassbound (x : H1ComplDirichlet q) : -(B x (L x)) ≤ C₁ * ‖x‖^2 := by
    have heq : -(B x (L x)) = ∫ z, (η z * Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q x
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) z)^2 := by
      change (-(innerSL ℝ).bilinearComp J (J.comp L)) x x = _
      rw [hval x x]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    rw [heq]
    exact hc₁ k h hh1 x
  have hexF := exists_local_dirichlet_bilinear_form_family q hG isCompact_Icc hreg α hΩ hΩc hΩs
  let F := hexF.choose
  have hF (t) (x z : H1ComplDirichlet q) : F t x z = ∑ i, ∑ j, ∫ y in Ω,
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i x y *
        (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z y := hexF.choose_spec.1 t x z
  have hFm := hexF.choose_spec.2.1
  let CF := hexF.choose_spec.2.2.choose
  have hCF := hexF.choose_spec.2.2.choose_spec.2
  have hpairF (z : Lp (H1ComplDirichlet q) 2 μ) :
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) - ∫ t, F t (v t) (z t) ∂μ := by
    simpa only [hF] using hpair z
  let Ei := fun i t => ∫ z, (η z * Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z)^2
  let E := fun t => ∑ i, Ei i t
  have hEi (i) : Integrable (Ei i) μ :=
    Sobolev.integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet
      (hη.continuous.memLp_of_hasCompactSupport hηc) k h hroomh
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp v)
  have hEI : Integrable E μ := integrable_finsetSum _ (fun i _ => hEi i)
  have hcoercF : ∀ᵐ t ∂μ, lam / 2 * E t ≤ -(F t (v t) (L (v t))) + C₀ * ‖v t‖^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [E, Ei, hF, L, ContinuousLinearMap.comp_apply] using hc₀ t ht k h hh0 (v t)
  have hshift : MeasurePreserving (fun t : ℝ => t - a) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-a)
  have hχ : MemLp (fun t => ζ (t - a)) ∞ μ := (hζ.comp_measurePreserving hshift).restrict _
  have hχpos : ∀ᵐ t ∂μ, 0 ≤ ζ (t - a) :=
    (hshift.quasiMeasurePreserving.ae hζpos).filter_mono (ae_mono Measure.restrict_le_self)
  have hs := hc₂ v f β hsource k h hh2 (fun t => ζ (t - a)) hχ hχpos hroomh
  have he := integral_energy_le_of_coercivity hab μ rfl F hFm hCF B v ℓ β w hmass hwderiv
    hpairF L hBL hBLpos hζsmooth hζ hζpos hζlip hζ0 hζb hEI hlam hcoercF hmassbound hs
  let A := (K:ℝ) * (∫ t, ‖v t‖^2 ∂μ)
  let U := ∫ t, ζ (t - a) * ‖v t‖^2 ∂μ
  let P := ∫ t, ζ (t - a) * (∫ z in Ω, (f (t,z))^2) ∂μ
  have hA : 0 ≤ A := mul_nonneg K.coe_nonneg (integral_nonneg fun _ => sq_nonneg _)
  have hU : 0 ≤ U := integral_nonneg_of_ae (hχpos.mono fun t ht => mul_nonneg ht (sq_nonneg _))
  have hP : 0 ≤ P := integral_nonneg_of_ae
    (hχpos.mono fun t ht => mul_nonneg ht (integral_nonneg fun _ => sq_nonneg _))
  have hb0 := mul_le_mul_of_nonneg_right (le_max_left (3/2*C₁) (max (C₀+Cr) Cf)) hA
  have hb1 := mul_le_mul_of_nonneg_right
    ((le_max_left (C₀+Cr) Cf).trans (le_max_right (3/2*C₁) (max (C₀+Cr) Cf))) hU
  have hb2 := mul_le_mul_of_nonneg_right
    ((le_max_right (C₀+Cr) Cf).trans (le_max_right (3/2*C₁) (max (C₀+Cr) Cf))) hP
  apply he.trans
  dsimp only [C, A, U, P, Cr, Cf] at hb0 hb1 hb2 ⊢
  have hx := add_le_add (add_le_add hb0 hb1) hb2
  nlinarith only [mul_le_mul_of_nonneg_left hx (show 0 ≤ 4 / lam by positivity)]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
