import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Integrability
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated
import DifferentialGeometry.External.DeGiorgi.Localization
import DifferentialGeometry.Analysis.Integration.Measure.ContinuousRepresentative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import DifferentialGeometry.Analysis.Elliptic.Coefficients.Extension

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem contDiffOn_matMulE_smoothGradField
    {Ω : Set V} (hΩ : IsOpen Ω) {n : ℕ∞ω}
    {a : V → Matrix (Fin d) (Fin d) ℝ} {u : V → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ n (fun x => a x i j) Ω)
    (hu : ContDiffOn ℝ (n + 1) u Ω) :
    ContDiffOn ℝ n (fun x => matMulE (a x) (smoothGradField u x)) Ω := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  change ContDiffOn ℝ n (fun x => ∑ j,
    a x i j * fderiv ℝ u x (EuclideanSpace.single j 1)) Ω
  apply ContDiffOn.sum
  intro j _
  exact (ha i j).mul ((hu.fderiv_of_isOpen hΩ le_rfl).clm_apply contDiffOn_const)

theorem IsSolution.hasWeakDiv_smooth_representative
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u v : V → ℝ}
    (hu : IsSolution A u) (hv : ContDiffOn ℝ 1 v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    HasWeakDiv 0 (fun x => matMulE (A.a x) (smoothGradField v x)) Ω := by
  let hw := hu.1.1.someWitness
  let hwv : MemW1pWitness 2 v Ω :=
    { memLp := hw.memLp.ae_eq huv
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := hw.weakGrad_component_memLp
      isWeakGrad := fun i => (hw.isWeakGrad i).congr_ae huv EventuallyEq.rfl }
  have hgrad := hwv.weakGrad_ae_eq_smoothGradField (by norm_num) hΩ hv
  have hdiv := (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hΩ hw
    (MemLp.zero : MemLp (0 : V → ℝ) 2 (volume.restrict Ω))).mp
    (fun φ hφ hwφ => by
      simpa only [Pi.zero_apply, zero_mul, integral_zero] using
        hu.bilinFormOfCoeff_eq_zero hΩ hw hφ hwφ)
  apply hdiv.congr_ae (Eventually.of_forall fun _ => neg_zero)
  filter_upwards [hgrad] with x hx
  change matMulE (A.a x) (hwv.weakGrad x) = _
  rw [hx]

end DeGiorgi

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.exists_smooth_representative_hasWeakDiv
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hcoeff : EqOn A.a B.a Ω) {c : V} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ Ω) :
    ∃ v : V → ℝ, ContDiffOn ℝ ∞ v (Metric.ball c r) ∧
      u =ᵐ[volume.restrict (Metric.ball c r)] v ∧
      HasWeakDiv 0 (fun x => matMulE (A.a x) (smoothGradField v x)) (Metric.ball c r) := by
  obtain ⟨v, hv, huv⟩ := EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two
    Metric.isOpen_ball (fun k => hu.memWkp k hΩ Metric.isOpen_ball
      (by rw [closure_ball c hr.ne']; exact isCompact_closedBall _ _)
      (by rwa [closure_ball c hr.ne']) B (rho := 1) one_ne_zero
      (by
        intro x hx i j
        rw [hcoeff hx, one_mul]))
  have hsol := hu.restrict_ball hΩ hr hsub
  exact ⟨v, hv, huv, hsol.hasWeakDiv_smooth_representative Metric.isOpen_ball
    (hv.of_le (by norm_cast)) huv⟩

end DeGiorgi

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.exists_contDiffOn_ae_eq
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hcoeff : EqOn A.a B.a Ω) :
    ∃ v : V → ℝ, ContDiffOn ℝ ∞ v Ω ∧ u =ᵐ[volume.restrict Ω] v := by
  have hlocal : ∀ x ∈ Ω, ∃ (U : Set V) (f : V → ℝ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ContDiffOn ℝ ∞ f U ∧ f =ᵐ[volume.restrict U] u := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
    have hhalf : Metric.closedBall x (r / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hsub
    obtain ⟨f, hf, huf, _⟩ := hu.exists_smooth_representative_hasWeakDiv hΩ B hcoeff
      (half_pos hr) hhalf
    exact ⟨Metric.ball x (r / 2), f, Metric.isOpen_ball, Metric.mem_ball_self (half_pos hr),
      Metric.ball_subset_closedBall.trans hhalf, hf, huf.symm⟩
  obtain ⟨v, hvc, hvu⟩ := exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq volume
    (fun x hx => by
      obtain ⟨U, f, hU, hxU, hUΩ, hf, hfu⟩ := hlocal x hx
      exact ⟨U, f, hU, hxU, hUΩ, hf.continuousOn, hfu⟩)
  refine ⟨v, ?_, hvu.symm⟩
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨U, f, hU, hxU, hUΩ, hf, hfu⟩ := hlocal x hx
  have hvuU : v =ᵐ[volume.restrict U] u :=
    hvu.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono hUΩ le_rfl))
  have heq : EqOn v f U := Measure.eqOn_open_of_ae_eq
    (hvuU.trans hfu.symm) hU
    (hvc.mono hUΩ) hf.continuousOn
  exact ⟨U, hU, hxU, (hf.mono inter_subset_right).congr (fun y hy => heq hy.2)⟩

end DeGiorgi

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsSolution.divergence_smooth_representative_eq_zero
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u v : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hAB : EqOn A.a B.a Ω) (hv : ContDiffOn ℝ 2 v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    ∀ x ∈ Ω, (∑ i, fderiv ℝ (fun y => matMulE (B.a y) (smoothGradField v y) i) x
      (EuclideanSpace.single i 1)) = 0 := by
  have hd := hu.hasWeakDiv_smooth_representative hΩ (hv.of_le (by norm_num)) huv
  have hdB : HasWeakDiv 0 (fun y => matMulE (B.a y) (smoothGradField v y)) Ω := by
    apply hd.congr_ae EventuallyEq.rfl
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hAB hx]
  exact hdB.sum_fderiv_eq_zero hΩ (contDiffOn_matMulE_smoothGradField hΩ
    (fun i j => (B.smooth_a i j).contDiffOn.of_le (by norm_cast)) hv)

end DeGiorgi

end

end
