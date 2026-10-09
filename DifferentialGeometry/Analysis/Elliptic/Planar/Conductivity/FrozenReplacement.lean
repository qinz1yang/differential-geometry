import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.FrozenComparison
import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.Analysis.Elliptic.Euclidean.DivergenceOperator
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Decay

noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff InnerProductSpace

namespace DifferentialGeometry.Analysis

open DeGiorgi Laplacian.MetricExtension Sobolev.NirenbergEuclidean Parabolic.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_constant_smooth_elliptic_form
    (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosDef) :
    ∃ S : SmoothEllipticBilinearForm d (univ : Set E), S.a = fun _ => K := by
  obtain ⟨lam, _, hlam, _, hcoer, _⟩ :=
    exists_uniform_matrix_and_inverse_quadratic_lower_bound
      (isCompact_singleton : IsCompact ({(0 : E)} : Set E)) (fun _ : E => K)
      (fun _ _ => continuousOn_const) (fun _ _ => hK)
  let S : SmoothEllipticBilinearForm d (univ : Set E) := {
    a := fun _ => K
    c := fun _ => 0
    symm := fun _ i j => (Matrix.isHermitian_iff_isSymm.mp hK.isHermitian).apply j i
    smooth_a := fun _ _ => contDiff_const
    smooth_c := contDiff_const
    lam := lam
    capLam := lam
    ellipticity_pos := hlam
    ellipticity_le_upper := le_rfl
    coercive := fun _ _ v => hcoer 0 (by simp) v }
  exact ⟨S, rfl⟩

omit [NeZero d] in
private theorem laplacian_comp_spdSqrt
    (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosDef) (v : E → ℝ) (x : E) :
    Laplacian.laplacian (v ∘ spdSqrtEquiv K hK) x =
      matrixLap K (fderiv ℝ (fderiv ℝ v) (spdSqrtEquiv K hK x)) := by
  let L := spdSqrtEquiv K hK
  have he := L.iteratedFDerivWithin_comp_right v
    (s := univ) uniqueDiffOn_univ (x := x) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  change iteratedFDeriv ℝ 2 (v ∘ L) x =
    (iteratedFDeriv ℝ 2 v (L x)).compContinuousLinearMap
      (fun _ => L.toContinuousLinearMap) at he
  calc
    Laplacian.laplacian (v ∘ L) x =
        factorLap L (fderiv ℝ (fderiv ℝ v) (L x)) := by
      rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
      dsimp only
      rw [he]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    _ = _ := spd_factorLap K hK _

omit [NeZero d] in
private theorem harmonicOnNhd_comp_spdSqrt_of_hasWeakDiv
    {Ω : Set E} (hΩ : IsOpen Ω)
    (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosDef) {v : E → ℝ}
    (hv : ContDiffOn ℝ 2 v Ω)
    (hdiv : HasWeakDiv 0 (fun x => matMulE K (smoothGradField v x)) Ω) :
    HarmonicOnNhd (v ∘ spdSqrtEquiv K hK) (spdSqrtEquiv K hK ⁻¹' Ω) := by
  have hclass := hdiv.sum_fderiv_eq_zero hΩ
    (contDiffOn_matMulE_smoothGradField hΩ (fun _ _ => contDiffOn_const) hv)
  have hmat (x : E) (hx : x ∈ Ω) :
      matrixLap K (fderiv ℝ (fderiv ℝ v) x) = 0 := by
    have hh := hclass x hx
    rw [divergence_matMulE_smoothGradField_eq_scalarEllipticOperator
      (fun _ : E => K) (fun _ _ => differentiableAt_const _)
      (hv.contDiffAt (hΩ.mem_nhds hx))] at hh
    simpa [scalarEllipticOperator, matrixLap, EuclideanSpace.basisFun_apply] using hh
  let L := spdSqrtEquiv K hK
  have hpre : IsOpen (L ⁻¹' Ω) := hΩ.preimage L.continuous
  intro x hx
  refine ⟨(hv.contDiffAt (hΩ.mem_nhds hx)).comp x L.contDiff.contDiffAt, ?_⟩
  filter_upwards [hpre.mem_nhds hx] with y hy
  change Laplacian.laplacian (v ∘ L) y = 0
  rw [laplacian_comp_spdSqrt]
  exact hmat (L y) hy

/-- Freeze the actual coefficient at the chosen center and construct its actual
weak Dirichlet replacement. Only the constant-coefficient comparator receives a
smooth representative; the original solution keeps its given weak regularity.
The trace, gradient comparison and a.e. identifications all concern this same
chosen replacement and representative. -/
theorem exists_frozen_harmonic_replacement_with_gradient_comparison
    (hd : 2 ≤ d) {c : E} {R : ℝ}
    (A : EllipticCoeff d (Metric.ball c R)) (hAc : (A.a c).PosDef)
    {u : E → ℝ} (hu : IsHomogeneousWeakSolution A u)
    (wu : MemW1pWitness 2 u (Metric.ball c R))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ᵐ x ∂volume.restrict (Metric.ball c R), ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (A.a c) ξ‖ ≤ ε * ‖ξ‖) :
    ∃ (B : EllipticCoeff d (Metric.ball c R)) (h : E → ℝ)
      (wh : MemW1pWitness 2 h (Metric.ball c R)) (v : E → ℝ),
      B.a = (fun _ => A.a c) ∧ IsHomogeneousWeakSolution B h ∧
      MemW01p 2 (fun x => h x - u x) (Metric.ball c R) ∧
      (∫ x, ‖wh.weakGrad x - wu.weakGrad x‖ ^ (2 : ℝ)
        ∂volume.restrict (Metric.ball c R)) ^ (1 / (2 : ℝ)) ≤
        (ε / B.lam) * (∫ x, ‖wu.weakGrad x‖ ^ (2 : ℝ)
          ∂volume.restrict (Metric.ball c R)) ^ (1 / (2 : ℝ)) ∧
      ContDiffOn ℝ ∞ v (Metric.ball c R) ∧
      h =ᵐ[volume.restrict (Metric.ball c R)] v ∧
      wh.weakGrad =ᵐ[volume.restrict (Metric.ball c R)] smoothGradField v ∧
      HasWeakDiv 0 (fun x => matMulE (A.a c) (smoothGradField v x))
        (Metric.ball c R) ∧
      HarmonicOnNhd (v ∘ spdSqrtEquiv (A.a c) hAc)
        (spdSqrtEquiv (A.a c) hAc ⁻¹' Metric.ball c R) := by
  obtain ⟨B, hB⟩ := ellipticCoeff_of_continuous_posDef_on_compact
    Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall
    (isCompact_closedBall c R) (fun _ : E => A.a c)
    (fun _ _ => measurable_const) (fun _ _ => continuousOn_const) (fun _ _ => hAc)
  obtain ⟨h, hh, htrace⟩ := aHarmonic_replacement_exists hd
    Metric.isOpen_ball Metric.isBounded_ball B hu.1
  let wh := hh.1.someWitness
  have hoscB : ∀ᵐ x ∂volume.restrict (Metric.ball c R), ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖ := by
    simpa only [hB] using hosc
  have hcompare := weakGrad_l2_sub_le_of_coefficient_oscillation
    Metric.isOpen_ball A B hu hh htrace wu wh hε hoscB
  obtain ⟨S, hS⟩ := exists_constant_smooth_elliptic_form (A.a c) hAc
  have hBS : EqOn B.a S.a (Metric.ball c R) := by
    intro x _
    rw [hB, hS]
  have hhsol := isHomogeneousWeakSolution_isSolution hh
  obtain ⟨v, hv, hhv⟩ := hhsol.exists_contDiffOn_ae_eq Metric.isOpen_ball S hBS
  let wv : MemW1pWitness 2 v (Metric.ball c R) := {
    memLp := wh.memLp.ae_eq hhv
    weakGrad := wh.weakGrad
    weakGrad_component_memLp := wh.weakGrad_component_memLp
    isWeakGrad := fun i => (wh.isWeakGrad i).congr_ae hhv EventuallyEq.rfl }
  have hv1 : ContDiffOn ℝ 1 v (Metric.ball c R) := hv.of_le (by norm_cast)
  have hgrad := wv.weakGrad_ae_eq_smoothGradField (by norm_num) Metric.isOpen_ball hv1
  have hdiv := hhsol.hasWeakDiv_smooth_representative Metric.isOpen_ball hv1 hhv
  have hdivK : HasWeakDiv 0 (fun x => matMulE (A.a c) (smoothGradField v x))
      (Metric.ball c R) := by
    simpa only [hB] using hdiv
  exact ⟨B, h, wh, v, hB, hh, htrace, hcompare, hv, hhv, hgrad, hdivK,
    harmonicOnNhd_comp_spdSqrt_of_hasWeakDiv Metric.isOpen_ball (A.a c) hAc
      (hv.of_le (by norm_cast)) hdivK⟩

omit [NeZero d] in
/-- The actual smooth representative of a frozen planar replacement obeys the
paid fourth-power harmonic gradient-excess estimate after the literal square-root
change of variables. The closed-ball inclusion supplies integrability. This does
not yet transport the estimate back to the original variable-coefficient solution. -/
theorem frozen_harmonic_transformed_gradient_excess
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef)
    {v : EuclideanSpace ℝ (Fin 2) → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hdiv : HasWeakDiv 0 (fun x => matMulE K (smoothGradField v x)) Ω)
    {c : EuclideanSpace ℝ (Fin 2)} {r R : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 4)
    (hsub : Metric.closedBall c R ⊆ spdSqrtEquiv K hK ⁻¹' Ω)
    (p : EuclideanSpace ℝ (Fin 2)) :
    (∫ x in Metric.ball c r, ∑ j : Fin 2,
      (fderiv ℝ (v ∘ spdSqrtEquiv K hK) x (EuclideanSpace.single j 1) -
        fderiv ℝ (v ∘ spdSqrtEquiv K hK) c (EuclideanSpace.single j 1)) ^ 2) ≤
      256 * (r / R) ^ 4 * ∫ x in Metric.ball c R, ∑ j : Fin 2,
        (fderiv ℝ (v ∘ spdSqrtEquiv K hK) x (EuclideanSpace.single j 1) - p j) ^ 2 := by
  let L := spdSqrtEquiv K hK
  have hpre : IsOpen (L ⁻¹' Ω) := hΩ.preimage L.continuous
  have hvc : ContDiffOn ℝ 2 (v ∘ L) (L ⁻¹' Ω) :=
    hv.comp L.contDiff.contDiffOn (fun _ hx => hx)
  have hD (j : Fin 2) : ContinuousOn
      (fun x => fderiv ℝ (v ∘ L) x (EuclideanSpace.single j 1)) (L ⁻¹' Ω) :=
    (hvc.continuousOn_fderiv_of_isOpen hpre (by norm_num)).clm_apply continuousOn_const
  have hc : ContinuousOn (fun x => ∑ j : Fin 2,
      (fderiv ℝ (v ∘ L) x (EuclideanSpace.single j 1) - p j) ^ 2) (L ⁻¹' Ω) := by
    simpa only [Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.pow_apply] using!
      (((hD 0).sub continuousOn_const).pow 2).add
        (((hD 1).sub continuousOn_const).pow 2)
  have hi := ((hc.mono hsub).integrableOn_compact
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) (isCompact_closedBall c R)).mono_set
    Metric.ball_subset_closedBall
  have hharm := harmonicOnNhd_comp_spdSqrt_of_hasWeakDiv hΩ K hK hv hdiv
  exact harmonic_integral_gradient_sub_center_sq_le_radius_ratio_pow_four hR hr hrR
    (hharm.mono (Metric.ball_subset_closedBall.trans hsub)) p hi

end DifferentialGeometry.Analysis
