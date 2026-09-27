import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.LocalDiffeomorphism
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.AlternatingCross
import DifferentialGeometry.Analysis.Complex.Beltrami.CriticalCross
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.StreamFunction

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

private theorem IsSolution.fderiv_ne_zero_of_coordinate_boundary_of_stream
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (hv : ContDiffOn ℝ ∞ v (Metric.ball (0 : V) R))
    (hs : ContDiffOn ℝ ∞ s (Metric.ball (0 : V) R))
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (hstream : ∀ x ∈ Metric.ball (0 : V) R,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v x ≠ 0 := by
  let L := Complex.orthonormalBasisOneI.repr
  let W := fun z : ℂ => (v (L z) : ℂ) + (s (L z) : ℂ) * Complex.I
  let D := Metric.ball (0 : ℂ) R
  let P := fun z : ℂ => A.a (L z)
  let μ := fun z => beltramiCoefficient (P z 1 1) (P z 0 0) (-P z 0 1)
  have hLD {z : ℂ} (hz : z ∈ D) : L z ∈ Metric.ball (0 : V) R := by simpa [D] using hz
  have hPs (i j : Fin 2) : ContDiffOn ℝ ∞ (fun z => P z i j) D := by
    have hA : ContDiffOn ℝ ∞ (fun x => A.a x i j) (Metric.ball (0 : V) R) :=
      (B.smooth_a i j).contDiffOn.congr (fun x hx => congrFun (congrFun (hAB hx) i) j)
    exact hA.comp L.contDiff.contDiffOn (fun z hz => hLD hz)
  have hPpos (z : ℂ) (hz : z ∈ D) : (P z).PosDef := by
    change (A.a (L z)).PosDef
    rw [hAB (hLD hz)]
    exact B.posDef (mem_univ _)
  have hPdet (z : ℂ) (hz : z ∈ D) : (P z).det = 1 := hdet _ (hLD hz)
  have hW : ContDiffOn ℝ ∞ W D :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hv.comp L.contDiff.contDiffOn (fun z hz => hLD hz))).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hs.comp L.contDiff.contDiffOn (fun z hz => hLD hz))).mul contDiffOn_const)
  have hWB : ∀ z ∈ D, complexAntilinearPart (fderiv ℝ W z) =
      μ z * complexLinearPart (fderiv ℝ W z) := by
    intro z hz
    exact beltrami_fderiv_of_unit_determinant_conductivity_stream (hPpos z hz) (hPdet z hz)
      ((hv.differentiableOn (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds (hLD hz)))
      (hstream _ (hLD hz))
  have hnon : ¬ ∃ c : ℂ, EqOn W (fun _ => c) D :=
    not_constant_complex_stream_of_coordinate_boundary hR hc hbd
  intro x hx hzero
  let p := L.symm x
  have hp : p ∈ D := by simpa [p, D] using hx
  have hLp : L p = x := L.apply_symm_apply x
  have hcrit : fderiv ℝ W p = 0 :=
    fderiv_complex_stream_eq_zero_of_fderiv_eq_zero (A := A.a) (v := v) (s := s) (z := p)
    (by
      rw [hLp]
      exact (hv.differentiableOn (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hx))
    (by
      change HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y)
        (smoothGradField v y)) (L p)) (L p)
      rw [hLp]
      exact hstream x hx)
    (by change fderiv ℝ v (L p) = 0; rw [hLp]; exact hzero)
  obtain ⟨E, hE0, hEp, η, hη, hpos, hneg⟩ := exists_alternating_cross_of_beltrami_critical
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected P hPs hPpos hPdet
    (hW.differentiableOn (by simp)) hWB hnon hp hcrit
  let F := E.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hF0 : (0 : ℝ × ℝ) ∈ F.source := ⟨hE0, mem_univ _⟩
  have hFp : F (0, 0) = x := by change L (E (0, 0)) = x; rw [hEp, hLp]
  apply hu.not_local_alternating_cross_of_coordinate_boundary hR B hAB
    (hv.of_le (by norm_cast)) hc huv hbd F hF0 (by rwa [hFp]) hη
  · intro t ht htr
    have hh := hpos t ht htr
    change v (F (0, 0)) < v (F (t, 0))
    rw [hFp]
    change v x < v (L (E (t, 0)))
    simpa only [W, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, hLp] using hh
  · intro t ht htr
    have hh := hneg t ht htr
    change v (F (0, t)) < v (F (0, 0))
    rw [hFp]
    change v (L (E (0, t))) < v x
    simpa only [W, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, hLp] using hh


theorem IsSolution.fderiv_ne_zero_of_coordinate_boundary
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0) :
    ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v x ≠ 0 := by
  obtain ⟨w, hw, huw⟩ := hu.exists_contDiffOn_ae_eq Metric.isOpen_ball B hAB
  have heq : EqOn v w (Metric.ball (0 : V) R) := Measure.eqOn_open_of_ae_eq
    (huv.symm.trans huw) Metric.isOpen_ball (hc.mono Metric.ball_subset_closedBall) hw.continuousOn
  have hv : ContDiffOn ℝ ∞ v (Metric.ball (0 : V) R) := hw.congr heq
  obtain ⟨s, hs, hds⟩ := exists_smooth_stream_of_smooth_representative
    Metric.isOpen_ball (convex_ball (0 : V) R) hu B hAB hv huv
  exact hu.fderiv_ne_zero_of_coordinate_boundary_of_stream hR B hAB hdet hv hs hc huv hbd hds

theorem IsSolution.exists_continuous_noncritical_coordinate_representative
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (ht : MemH01 (fun x => u x - x 0) (Metric.ball (0 : V) R)) :
    ∃ v : V → ℝ, ContDiffOn ℝ ∞ v (Metric.ball (0 : V) R) ∧
      ContinuousOn v (Metric.closedBall (0 : V) R) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v ∧
      (∀ x ∈ Metric.sphere (0 : V) R, v x = x 0) ∧
      ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v x ≠ 0 := by
  obtain ⟨v, hv, hc, huv, hbd⟩ :=
    hu.exists_continuous_closedBall_representative_of_coordinate_trace (by norm_num) hR B hAB 0 ht
  exact ⟨v, hv, hc, huv, hbd,
    hu.fderiv_ne_zero_of_coordinate_boundary hR B hAB hdet hc huv hbd⟩

end DeGiorgi

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi

variable {d : ℕ}
local notation "Vd" => EuclideanSpace ℝ (Fin d)

theorem smoothGradField_eq_zero_iff {u : Vd → ℝ} {x : Vd} :
    smoothGradField u x = 0 ↔ fderiv ℝ u x = 0 := by
  constructor
  · intro hg
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ i : Fin d, v i • EuclideanSpace.single i 1 := by
      ext j
      simp [Pi.single_apply, Finset.sum_ite_eq]
    rw [hv, map_sum]
    simp only [map_smul, smul_eq_mul, zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congrArg (fun w : Vd => w i) hg
    change fderiv ℝ u x (EuclideanSpace.single i 1) = 0 at hi
    rw [hi, mul_zero]
  · intro hd
    ext i
    change fderiv ℝ u x (EuclideanSpace.single i 1) = 0
    rw [hd, zero_apply]

end DeGiorgi

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem IsSolution.det_fderiv_pos_of_coordinate_boundary_stream
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (hstream : ∀ x ∈ Metric.ball (0 : V) R,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    ∀ z ∈ Metric.ball (0 : ℂ) R,
      0 < (fderiv ℝ (fun w => (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det := by
  intro z hz
  have hzm : Complex.orthonormalBasisOneI.repr z ∈ Metric.ball (0 : V) R := by simpa using hz
  have hpos : (A.a (Complex.orthonormalBasisOneI.repr z)).PosDef := by
    rw [hAB hzm]
    exact B.posDef (mem_univ _)
  have hnon := hu.fderiv_ne_zero_of_coordinate_boundary hR B hAB hdet hc huv hbd _ hzm
  have hdiff : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z) := by
    by_contra h
    exact hnon (fderiv_zero_of_not_differentiableAt h)
  exact det_fderiv_pos_of_conductivity_stream hpos hdiff (hstream _ hzm)
    (fun hg => hnon (smoothGradField_eq_zero_iff.mp hg))

theorem IsSolution.exists_noncritical_dirichlet_stream_boundary_extension
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (ht : MemH01 (fun x => u x - x 0) (Metric.ball (0 : V) R))
    (hv : ContinuousOn v (Metric.ball (0 : V) r))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v)
    (hs : ∀ x ∈ Metric.ball (0 : V) r,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    ∃ v₁ s₁ : V → ℝ, ContDiffOn ℝ ∞ v₁ (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ s₁ (Metric.ball (0 : V) R) ∧
      ContinuousOn v₁ (Metric.closedBall (0 : V) R) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v₁ ∧
      EqOn v₁ v (Metric.ball (0 : V) r) ∧ EqOn s₁ s (Metric.ball (0 : V) r) ∧
      (∀ x ∈ Metric.sphere (0 : V) R, v₁ x = x 0) ∧
      (∀ x ∈ Metric.ball (0 : V) R,
        HasFDerivAt s₁ (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v₁ y)) x) x) ∧
      (∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v₁ x ≠ 0) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R,
        0 < (fderiv ℝ (fun w => (v₁ (Complex.orthonormalBasisOneI.repr w) : ℂ) +
          (s₁ (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det := by
  obtain ⟨v₁, s₁, hv₁, hs₁, hvc, huv₁, hveq, hseq, hbd, hds⟩ :=
    hu.exists_dirichlet_stream_boundary_extension hr hrR B hAB 0 ht hv huv hs
  have hR := hr.trans_le hrR
  exact ⟨v₁, s₁, hv₁, hs₁, hvc, huv₁, hveq, hseq, hbd, hds,
    hu.fderiv_ne_zero_of_coordinate_boundary hR B hAB hdet hvc huv₁ hbd,
    hu.det_fderiv_pos_of_coordinate_boundary_stream hR B hAB hdet hvc huv₁ hbd hds⟩


theorem IsSolution.det_fderiv_pos_of_coordinate_trace_stream
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R))
    (hdet : ∀ x ∈ Metric.ball (0 : V) R, (A.a x).det = 1)
    (ht : MemH01 (fun x => u x - x 0) (Metric.ball (0 : V) R))
    (hv : ContinuousOn v (Metric.ball (0 : V) r))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v)
    (hs : ∀ x ∈ Metric.ball (0 : V) r,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    ∀ z ∈ Metric.ball (0 : ℂ) r,
      0 < (fderiv ℝ (fun w => (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det := by
  obtain ⟨v₁, s₁, _, _, _, _, hveq, hseq, _, _, _, hJ⟩ :=
    hu.exists_noncritical_dirichlet_stream_boundary_extension hr hrR B hAB hdet ht hv huv hs
  intro z hz
  have heq : (fun w => (v₁ (Complex.orthonormalBasisOneI.repr w) : ℂ) +
      (s₁ (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) =ᶠ[𝓝 z]
      (fun w => (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    have hwm : Complex.orthonormalBasisOneI.repr w ∈ Metric.ball (0 : V) r := by simpa using hw
    rw [hveq hwm, hseq hwm]
  rw [← heq.fderiv_eq]
  exact hJ z (Metric.ball_subset_ball hrR hz)

end DeGiorgi

end

end
