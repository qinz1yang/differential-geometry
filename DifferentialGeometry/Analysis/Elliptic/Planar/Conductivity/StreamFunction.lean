import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SmoothRepresentative
import DifferentialGeometry.Analysis.Elliptic.Planar.StreamFunction
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Coefficients
import DifferentialGeometry.Analysis.Complex.Beltrami.LinearParts
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Dirichlet.AffineBoundary

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem IsSolution.exists_smooth_representative_stream_function
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff 2 Ω} {u : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hcoeff : EqOn A.a B.a Ω) {c : V} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ Ω) :
    ∃ v s : V → ℝ, ContDiffOn ℝ ∞ v (Metric.ball c r) ∧
      ContDiffOn ℝ ∞ s (Metric.ball c r) ∧
      u =ᵐ[volume.restrict (Metric.ball c r)] v ∧
      HasWeakDiv 0 (fun x => matMulE (A.a x) (smoothGradField v x)) (Metric.ball c r) ∧
      ∀ x ∈ Metric.ball c r,
        HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x := by
  obtain ⟨v, hv, huv, hdiv⟩ := hu.exists_smooth_representative_hasWeakDiv hΩ B hcoeff hr hsub
  have hflux : ContDiffOn ℝ ∞ (fun x => matMulE (A.a x) (smoothGradField v x))
      (Metric.ball c r) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℝ ∞ (fun x => ∑ j, A.a x i j *
      fderiv ℝ v x (EuclideanSpace.single j 1)) (Metric.ball c r)
    apply ContDiffOn.sum
    intro j _
    have hc : ContDiffOn ℝ ∞ (fun x => A.a x i j) (Metric.ball c r) :=
      (B.smooth_a i j).contDiffOn.congr (fun x hx =>
        congrFun (congrFun (hcoeff (hsub (Metric.ball_subset_closedBall hx))) i) j)
    exact hc.mul
      ((hv.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const)
  obtain ⟨s, hs, hds⟩ := exists_stream_function_of_hasWeakDiv_zero Metric.isOpen_ball
    (convex_ball c r) hflux hdiv
  exact ⟨v, s, hv, hs, huv, hdiv, hds⟩

end DeGiorgi

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

theorem beltrami_eq_of_conductivity_conjugate
    {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2)
    (L : ℂ →L[ℝ] ℂ)
    (hx : (L 1).im = -((planarConductivity a b c).mulVec ![(L 1).re, (L Complex.I).re]) 1)
    (hy : (L Complex.I).im =
      ((planarConductivity a b c).mulVec ![(L 1).re, (L Complex.I).re]) 0) :
    complexAntilinearPart L = beltramiCoefficient a b c * complexLinearPart L := by
  have hb : 0 < b := by nlinarith [sq_nonneg c]
  have hd := Real.sqrt_pos.mpr hdet
  have hd2 := Real.sq_sqrt hdet.le
  have ht : 0 < a + b + 2 * Real.sqrt (a * b - c ^ 2) := by positivity
  have hx' : (L 1).im = (c * (L 1).re - a * (L Complex.I).re) /
      Real.sqrt (a * b - c ^ 2) := by
    rw [hx]
    simp [planarConductivity, Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
    ring
  have hy' : (L Complex.I).im = (b * (L 1).re - c * (L Complex.I).re) /
      Real.sqrt (a * b - c ^ 2) := by
    rw [hy]
    simp [planarConductivity, Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
    ring
  have he : (a + b + 2 * Real.sqrt (a * b - c ^ 2) : ℂ) * complexAntilinearPart L =
      ((a - b : ℝ) + (2 * c : ℝ) * Complex.I) * complexLinearPart L := by
    apply Complex.ext <;>
      simp [complexAntilinearPart, complexLinearPart, Complex.mul_re, Complex.mul_im, hx', hy'] <;>
      field_simp [hd.ne']
    · linear_combination 2 * (L 1).re * hd2
    · linear_combination 2 * (L Complex.I).re * hd2
  have htC : (a + b + 2 * Real.sqrt (a * b - c ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast ht.ne'
  apply (mul_left_cancel₀ htC)
  rw [he]
  simp only [beltramiCoefficient, div_eq_mul_inv, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [htC]

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem beltrami_fderiv_of_conductivity_stream
    {v s : V → ℝ} {z : ℂ} {a b c : ℝ}
    (ha : 0 < a) (hdet : 0 < a * b - c ^ 2)
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z))
    (hs : HasFDerivAt s
      (planarFluxForm (fun x => DeGiorgi.matMulE (planarConductivity a b c)
        (DeGiorgi.smoothGradField v x)) (Complex.orthonormalBasisOneI.repr z))
      (Complex.orthonormalBasisOneI.repr z)) :
    complexAntilinearPart (fderiv ℝ (fun w =>
      (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) =
      beltramiCoefficient a b c * complexLinearPart (fderiv ℝ (fun w =>
        (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
          (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) := by
  let e := Complex.orthonormalBasisOneI.repr
  have he := e.toContinuousLinearEquiv.hasFDerivAt (x := z)
  have hU := (Complex.ofRealCLM.hasFDerivAt.comp (e z) hv.hasFDerivAt).comp z he
  have hS := (Complex.ofRealCLM.hasFDerivAt.comp (e z) hs).comp z he
  have hW := (hU.add (hS.mul_const Complex.I)).fderiv
  change fderiv ℝ (fun w => (v (e w) : ℂ) + (s (e w) : ℂ) * Complex.I) z = _ at hW
  have he0 : e 1 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [e]
  have he1 : e Complex.I = EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp [e]
  apply beltrami_eq_of_conductivity_conjugate ha hdet
  · rw [hW]
    simp [ContinuousLinearMap.comp_apply, planarFluxForm,
      e, DeGiorgi.matMulE_apply, DeGiorgi.smoothGradField, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Complex.real_smul, ← he0, ← he1]
  · rw [hW]
    simp [ContinuousLinearMap.comp_apply, planarFluxForm,
      e, DeGiorgi.matMulE_apply, DeGiorgi.smoothGradField, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Complex.real_smul, ← he0, ← he1]

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis
open Sobolev.NirenbergEuclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_smooth_stream_of_smooth_representative
    {Ω : Set V} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {A : DeGiorgi.EllipticCoeff 2 Ω} {u v : V → ℝ} (hu : DeGiorgi.IsSolution A u)
    (B : SmoothEllipticBilinearForm 2 (univ : Set V)) (hAB : EqOn A.a B.a Ω)
    (hv : ContDiffOn ℝ ∞ v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    ∃ s : V → ℝ, ContDiffOn ℝ ∞ s Ω ∧ ∀ x ∈ Ω,
      HasFDerivAt s (planarFluxForm (fun y => DeGiorgi.matMulE (A.a y)
        (DeGiorgi.smoothGradField v y)) x) x := by
  have hflux := DeGiorgi.contDiffOn_matMulE_smoothGradField (n := ∞) hΩ
    (fun i j => (B.smooth_a i j).contDiffOn.congr
      (fun x hx => congrFun (congrFun (hAB hx) i) j))
    (by simpa only [ENat.coe_top_add_one] using hv)
  exact exists_stream_function_of_hasWeakDiv_zero hΩ hc hflux
    (hu.hasWeakDiv_smooth_representative hΩ (hv.of_le (by norm_cast)) huv)

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem IsSolution.exists_dirichlet_stream_boundary_extension
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v s : V → ℝ} (hu : IsSolution A u)
    (B : SmoothEllipticBilinearForm 2 (univ : Set V))
    (hAB : EqOn A.a B.a (Metric.ball (0 : V) R)) (j : Fin 2)
    (ht : MemH01 (fun x => u x - x j) (Metric.ball (0 : V) R))
    (hv : ContinuousOn v (Metric.ball (0 : V) r))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v)
    (hs : ∀ x ∈ Metric.ball (0 : V) r,
      HasFDerivAt s (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v y)) x) x) :
    ∃ v₁ s₁ : V → ℝ, ContDiffOn ℝ ∞ v₁ (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ s₁ (Metric.ball (0 : V) R) ∧
      ContinuousOn v₁ (Metric.closedBall (0 : V) R) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v₁ ∧
      EqOn v₁ v (Metric.ball (0 : V) r) ∧ EqOn s₁ s (Metric.ball (0 : V) r) ∧
      (∀ x ∈ Metric.sphere (0 : V) R, v₁ x = x j) ∧
      ∀ x ∈ Metric.ball (0 : V) R,
        HasFDerivAt s₁ (planarFluxForm (fun y => matMulE (A.a y) (smoothGradField v₁ y)) x) x := by
  have hR : 0 < R := hr.trans_le hrR
  have hsub : Metric.ball (0 : V) r ⊆ Metric.ball (0 : V) R := Metric.ball_subset_ball hrR
  obtain ⟨v₁, hv₁, hvc, huv₁, heq, hvbd⟩ :=
    hu.exists_continuous_boundary_extension_of_representative (by norm_num) hR B hAB j ht
      Metric.isOpen_ball hsub hv huv
  let F := fun x => matMulE (A.a x) (smoothGradField v₁ x)
  have hF := contDiffOn_matMulE_smoothGradField (n := ∞) Metric.isOpen_ball
    (fun i l => (B.smooth_a i l).contDiffOn.congr
      (fun x hx => congrFun (congrFun (hAB hx) i) l))
    (by simpa only [ENat.coe_top_add_one] using hv₁)
  have hFs : ∀ x ∈ Metric.ball (0 : V) r, HasFDerivAt s (planarFluxForm F x) x := by
    intro x hx
    have hnear : v₁ =ᶠ[𝓝 x] v :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Metric.ball (0 : V) r from Metric.isOpen_ball.mem_nhds hx).mono
        (fun y hy => heq hy)
    have hgrad : smoothGradField v₁ x = smoothGradField v x := by
      ext l
      exact congrArg (fun L : V →L[ℝ] ℝ => L (EuclideanSpace.single l 1)) hnear.fderiv_eq
    have hh := hs x hx
    simpa only [planarFluxForm, F, hgrad] using hh
  obtain ⟨s₁, hs₁, hseq, hds₁⟩ := exists_stream_function_extension_of_hasWeakDiv_zero
    Metric.isOpen_ball (convex_ball (0 : V) R) Metric.isOpen_ball
    (convex_ball (0 : V) r).isPreconnected hsub (Metric.mem_ball_self hr) hF
    (hu.hasWeakDiv_smooth_representative Metric.isOpen_ball (hv₁.of_le (by norm_cast)) huv₁) hFs
  exact ⟨v₁, s₁, hv₁, hs₁, hvc, huv₁, heq, hseq, hvbd, hds₁⟩

end DeGiorgi

end

end
