import DifferentialGeometry.Analysis.Elliptic.Euclidean.Supersolution
import DifferentialGeometry.Analysis.Elliptic.Euclidean.LaplaceCoefficient
import DifferentialGeometry.External.DeGiorgi.StrongMinimum
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian

/-!
# Strong minimum principle in the plane via a lift to `ℝ³` (S-W-EIG, G2)

For `v ≥ 0` of class `C²` on a connected open `Ω ⊂ ℝ²` with `Δv = c v`, `c ≤ M`: if `v` vanishes
at a point of `Ω` then `v ≡ 0`.  The De Giorgi weak Harnack machinery in the tree needs `d ≥ 3`; the
lift `(x,y,z) ↦ v(x,y) cos (k z)`, `k² ≥ M`, is a nonnegative `C²` superharmonic function on a slab
in `ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Projection of `ℝ³` onto its first two coordinates. -/
def projL_EG : E3 →L[ℝ] E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 => EuclideanSpace.proj (Fin.castSucc i))

theorem projL_apply_EG (p : E3) (i : Fin 2) : projL_EG p i = p (Fin.castSucc i) := rfl

theorem projL_single_EG (i : Fin 2) :
    projL_EG (EuclideanSpace.single (Fin.castSucc i) (1 : ℝ)) = EuclideanSpace.single i 1 := by
  ext j
  simp [projL_apply_EG, Fin.castSucc_inj]

theorem projL_single_two_EG : projL_EG (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = 0 := by
  ext j
  fin_cases j <;> simp [projL_apply_EG]

/-- The cosine factor of the lift. -/
def cosFac_EG (k : ℝ) (p : E3) : ℝ := Real.cos (k * p 2)

theorem hasFDerivAt_cosFac_EG (k : ℝ) (z : E3) :
    HasFDerivAt (cosFac_EG k)
      ((-(k * Real.sin (k * z 2))) • (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ)) z := by
  have h1 : HasFDerivAt (fun p : E3 => k * p 2)
      (k • (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ)) z :=
    ((EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt).const_mul k
  have h2 := (Real.hasDerivAt_cos (k * z 2)).comp_hasFDerivAt z h1
  have h3 : (-(k * Real.sin (k * z 2))) • (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ) =
      (-Real.sin (k * z 2)) • (k • (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ)) := by
    rw [smul_smul]
    congr 1
    ring
  rw [h3]
  exact h2

/-- The lift `p ↦ v(π p) cos (k p₂)` of a planar function to `ℝ³`. -/
def lift_EG (v : E2 → ℝ) (k : ℝ) (p : E3) : ℝ := v (projL_EG p) * Real.cos (k * p 2)

theorem fderiv_lift_apply_EG {v : E2 → ℝ} {k : ℝ} {z : E3}
    (hv : DifferentiableAt ℝ v (projL_EG z)) (w : E3) :
    fderiv ℝ (lift_EG v k) z w =
      v (projL_EG z) * (-(k * Real.sin (k * z 2)) * w 2) +
        Real.cos (k * z 2) * fderiv ℝ v (projL_EG z) (projL_EG w) := by
  have h1 : HasFDerivAt (fun p : E3 => v (projL_EG p))
      ((fderiv ℝ v (projL_EG z)).comp projL_EG) z :=
    hv.hasFDerivAt.comp z projL_EG.hasFDerivAt
  have h3 := h1.mul (hasFDerivAt_cosFac_EG k z)
  have h5 : fderiv ℝ (lift_EG v k) z =
      v (projL_EG z) • (-(k * Real.sin (k * z 2))) •
          (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ) +
        cosFac_EG k z • (fderiv ℝ v (projL_EG z)).comp projL_EG := h3.fderiv
  rw [h5]
  simp [cosFac_EG, mul_comm, add_comm]

theorem hasFDerivAt_fderiv_lift_apply_EG {Ω : Set E2} (hΩ : IsOpen Ω) {v : E2 → ℝ}
    (hv : ContDiffOn ℝ 2 v Ω) (k : ℝ) {x : E3} (hx : projL_EG x ∈ Ω) (w : E3) :
    HasFDerivAt (fun z : E3 => fderiv ℝ (lift_EG v k) z w)
      (v (projL_EG x) • (-(k * (Real.cos (k * x 2) * k)) * w 2) •
          (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ) +
        (-(k * Real.sin (k * x 2)) * w 2) • (fderiv ℝ v (projL_EG x)).comp projL_EG +
        (fderiv ℝ v (projL_EG x) (projL_EG w)) •
          ((-Real.sin (k * x 2)) • k • (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ)) +
        Real.cos (k * x 2) • ((fderiv ℝ (fderiv ℝ v) (projL_EG x)).flip (projL_EG w)).comp
          projL_EG) x := by
  have hvx : ContDiffAt ℝ 2 v (projL_EG x) := hv.contDiffAt (hΩ.mem_nhds hx)
  have hdv : DifferentiableAt ℝ v (projL_EG x) := hvx.differentiableAt (by norm_num)
  have hddv : DifferentiableAt ℝ (fderiv ℝ v) (projL_EG x) :=
    (hvx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hN : IsOpen (projL_EG ⁻¹' Ω) := hΩ.preimage projL_EG.continuous
  have hev : (fun z : E3 => fderiv ℝ (lift_EG v k) z w) =ᶠ[𝓝 x] fun z : E3 =>
      v (projL_EG z) * (-(k * Real.sin (k * z 2)) * w 2) +
        Real.cos (k * z 2) * fderiv ℝ v (projL_EG z) (projL_EG w) := by
    filter_upwards [hN.mem_nhds hx] with z hz
    exact fderiv_lift_apply_EG ((hv.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by norm_num)) w
  refine HasFDerivAt.congr_of_eventuallyEq ?_ hev
  let L₂ : E3 →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have h1 : HasFDerivAt (fun p : E3 => k * p 2) (k • L₂) x := L₂.hasFDerivAt.const_mul k
  have hs : HasFDerivAt (fun p : E3 => Real.sin (k * p 2)) (Real.cos (k * x 2) • (k • L₂)) x :=
    h1.sin
  have hc : HasFDerivAt (fun p : E3 => Real.cos (k * p 2)) ((-Real.sin (k * x 2)) • (k • L₂)) x :=
    h1.cos
  have hA : HasFDerivAt (fun p : E3 => v (projL_EG p))
      ((fderiv ℝ v (projL_EG x)).comp projL_EG) x :=
    hdv.hasFDerivAt.comp x projL_EG.hasFDerivAt
  have hT := (hs.const_mul k).neg.mul_const (w 2)
  have hS0 : HasFDerivAt (fun y : E2 => fderiv ℝ v y (projL_EG w))
      ((fderiv ℝ (fderiv ℝ v) (projL_EG x)).flip (projL_EG w)) (projL_EG x) := by
    have := hddv.hasFDerivAt.clm_apply (hasFDerivAt_const (projL_EG w) (projL_EG x))
    simpa using this
  have hS : HasFDerivAt (fun p : E3 => fderiv ℝ v (projL_EG p) (projL_EG w))
      (((fderiv ℝ (fderiv ℝ v) (projL_EG x)).flip (projL_EG w)).comp projL_EG) x :=
    hS0.comp x projL_EG.hasFDerivAt
  have h := (hA.mul hT).add (hc.mul hS)
  refine h.congr_fderiv ?_
  ext u
  simp [L₂]
  ring

theorem projL_single_zero_EG :
    projL_EG (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (0 : Fin 2) 1 := by
  ext j
  fin_cases j <;> simp [projL_apply_EG]

theorem projL_single_one_EG :
    projL_EG (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (1 : Fin 2) 1 := by
  ext j
  fin_cases j <;> simp [projL_apply_EG]

theorem fderiv_apply_const_EG {v : E2 → ℝ} {y : E2}
    (hddv : DifferentiableAt ℝ (fderiv ℝ v) y) (c h : E2) :
    fderiv ℝ (fun z => fderiv ℝ v z c) y h = fderiv ℝ (fderiv ℝ v) y h c := by
  have h1 := hddv.hasFDerivAt.clm_apply (hasFDerivAt_const c y)
  have h3 : fderiv ℝ (fun z => fderiv ℝ v z c) y = (fderiv ℝ (fderiv ℝ v) y).flip c := by
    simpa using h1.fderiv
  rw [h3]
  rfl

theorem laplacian_lift_EG {Ω : Set E2} (hΩ : IsOpen Ω) {v : E2 → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (k : ℝ) {x : E3} (hx : projL_EG x ∈ Ω) :
    Laplacian.laplacian (lift_EG v k) x =
      (Laplacian.laplacian v (projL_EG x) - k ^ 2 * v (projL_EG x)) * Real.cos (k * x 2) := by
  have hvx : ContDiffAt ℝ 2 v (projL_EG x) := hv.contDiffAt (hΩ.mem_nhds hx)
  have hlift : ContDiffAt ℝ 2 (lift_EG v k) x := by
    have h1 : ContDiffAt ℝ 2 (fun p : E3 => v (projL_EG p)) x :=
      hvx.comp x projL_EG.contDiff.contDiffAt
    have h2 : ContDiffAt ℝ 2 (fun p : E3 => Real.cos (k * p 2)) x :=
      Real.contDiff_cos.contDiffAt.comp x
        ((contDiff_const.mul (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).contDiff).contDiffAt)
    exact h1.mul h2
  rw [laplacian_eq_sum_euclidean_fderiv hlift, laplacian_eq_sum_euclidean_fderiv hvx,
    Fin.sum_univ_three, Fin.sum_univ_two]
  rw [(hasFDerivAt_fderiv_lift_apply_EG hΩ hv k hx (EuclideanSpace.single 0 1)).fderiv,
    (hasFDerivAt_fderiv_lift_apply_EG hΩ hv k hx (EuclideanSpace.single 1 1)).fderiv,
    (hasFDerivAt_fderiv_lift_apply_EG hΩ hv k hx (EuclideanSpace.single 2 1)).fderiv]
  have hddv : DifferentiableAt ℝ (fderiv ℝ v) (projL_EG x) :=
    (hvx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_apply_const_EG hddv, fderiv_apply_const_EG hddv]
  simp [projL_single_zero_EG, projL_single_one_EG, projL_single_two_EG]
  ring

/-- The inclusion `ℝ² → ℝ³`, `y ↦ (y₀, y₁, 0)`. -/
def incl_EG (y : E2) : E3 := WithLp.toLp 2 ![y 0, y 1, 0]

theorem projL_incl_EG (y : E2) : projL_EG (incl_EG y) = y := by
  ext j
  fin_cases j <;> simp [projL_apply_EG, incl_EG]

theorem incl_apply_two_EG (y : E2) : incl_EG y 2 = 0 := by
  simp [incl_EG]

theorem dist_incl_EG (y y' : E2) : dist (incl_EG y) (incl_EG y') = dist y y' := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_three, Fin.sum_univ_two, incl_EG]

theorem dist_projL_le_EG (q q' : E3) : dist (projL_EG q) (projL_EG q') ≤ dist q q' := by
  simp only [EuclideanSpace.dist_eq, Fin.sum_univ_three, Fin.sum_univ_two, projL_apply_EG]
  apply Real.sqrt_le_sqrt
  simp

theorem local_zero_EG {Ω : Set E2} (hΩ : IsOpen Ω) {v : E2 → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hv0 : ∀ x ∈ Ω, 0 ≤ v x) {c : E2 → ℝ} {M : ℝ} (hcM : ∀ x ∈ Ω, c x ≤ M)
    (hlap : ∀ x ∈ Ω, Laplacian.laplacian v x = c x * v x)
    {p : E2} (hp : p ∈ Ω) (hz : v p = 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ Ω ∧ ∀ x ∈ Metric.ball p r, v x = 0 := by
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.mp hΩ p hp
  set k : ℝ := Real.sqrt (max M 0 + 1) with hk
  have hk2 : k ^ 2 = max M 0 + 1 := Real.sq_sqrt (by positivity)
  have hkpos : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hkM : M ≤ k ^ 2 := by rw [hk2]; linarith [le_max_left M 0]
  set R : ℝ := min (r₀ / 2) (Real.pi / (2 * k)) with hR
  have hRpos : 0 < R := lt_min (half_pos hr₀) (by positivity)
  have hRr : R < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hkR : k * R ≤ Real.pi / 2 := by
    calc k * R ≤ k * (Real.pi / (2 * k)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hkpos.le
      _ = Real.pi / 2 := by field_simp
  let c₃ : E3 := incl_EG p
  let N : Set E3 := projL_EG ⁻¹' Ω
  have hN : IsOpen N := hΩ.preimage projL_EG.continuous
  have hball : Metric.closedBall c₃ R ⊆ N := by
    intro q hq
    have h1 := dist_projL_le_EG q c₃
    rw [projL_incl_EG] at h1
    have h2 : dist (projL_EG q) p ≤ R := h1.trans (Metric.mem_closedBall.mp hq)
    exact hsub (Metric.mem_ball.mpr (h2.trans_lt hRr))
  have hcos : ∀ q ∈ Metric.closedBall c₃ R, 0 ≤ Real.cos (k * q 2) := by
    intro q hq
    have h1 : |q 2| ≤ R := by
      have h2 := PiLp.norm_apply_le (q - c₃) 2
      have h3 : ‖q - c₃‖ ≤ R := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hq
      have h4 : (q - c₃) 2 = q 2 := by simp [c₃, incl_apply_two_EG]
      rw [h4, Real.norm_eq_abs] at h2
      exact h2.trans h3
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [abs_le.mp h1, Real.pi_pos]
    · nlinarith [abs_le.mp h1, Real.pi_pos]
  have hGsm : ContDiffOn ℝ 2 (lift_EG v k) N := by
    have h1 : ContDiffOn ℝ 2 (fun q : E3 => v (projL_EG q)) N :=
      hv.comp projL_EG.contDiff.contDiffOn (fun q hq => hq)
    have h2 : ContDiffOn ℝ 2 (fun q : E3 => Real.cos (k * q 2)) N :=
      (Real.contDiff_cos.comp
        (contDiff_const.mul (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).contDiff)).contDiffOn
    exact h1.mul h2
  have hdiv : ∀ x ∈ Metric.ball c₃ R, (∑ i : Fin 3, fderiv ℝ (fun y => DeGiorgi.matMulE
      (1 : Matrix (Fin 3) (Fin 3) ℝ) (DeGiorgi.smoothGradField (lift_EG v k) y) i) x
        (EuclideanSpace.single i 1)) ≤ 0 := by
    intro x hx
    have hxN : x ∈ N := hball (Metric.ball_subset_closedBall hx)
    have hxΩ : projL_EG x ∈ Ω := hxN
    have hat : ContDiffAt ℝ 2 (lift_EG v k) x := hGsm.contDiffAt (hN.mem_nhds hxN)
    have hlapx := laplacian_eq_sum_euclidean_fderiv hat
    have hsum : (∑ i : Fin 3, fderiv ℝ (fun y => DeGiorgi.matMulE
        (1 : Matrix (Fin 3) (Fin 3) ℝ) (DeGiorgi.smoothGradField (lift_EG v k) y) i) x
          (EuclideanSpace.single i 1)) = Laplacian.laplacian (lift_EG v k) x := by
      rw [hlapx]
      apply Finset.sum_congr rfl
      intro i _
      simp [DeGiorgi.matMulE_one, DeGiorgi.smoothGradField]
    rw [hsum, laplacian_lift_EG hΩ hv k hxΩ, hlap _ hxΩ]
    have hcx := hcos x (Metric.ball_subset_closedBall hx)
    have h1 : (c (projL_EG x) * v (projL_EG x) - k ^ 2 * v (projL_EG x)) =
        (c (projL_EG x) - k ^ 2) * v (projL_EG x) := by ring
    rw [h1]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hcM _ hxΩ]) (hv0 _ hxΩ)) hcx
  have hsuper : DeGiorgi.IsSupersolution (DeGiorgi.EllipticCoeff.identity 3 (Metric.ball c₃ R))
      (lift_EG v k) :=
    DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos hN hball
      (DeGiorgi.EllipticCoeff.identity 3 (Metric.ball c₃ R)) (fun _ => 1)
      (fun i j => contDiffOn_const) (fun x _ => rfl) hGsm hdiv
  have hGnonneg : ∀ q ∈ Metric.ball c₃ R, 0 ≤ lift_EG v k q := by
    intro q hq
    exact mul_nonneg (hv0 _ (hball (Metric.ball_subset_closedBall hq)))
      (hcos q (Metric.ball_subset_closedBall hq))
  have hGcont : ContinuousOn (lift_EG v k) (Metric.ball c₃ R) :=
    (hGsm.continuousOn).mono ((Metric.ball_subset_closedBall).trans hball)
  have hG0 : lift_EG v k c₃ = 0 := by
    simp [lift_EG, c₃, projL_incl_EG, incl_apply_two_EG, hz]
  have hquarter := DeGiorgi.IsSupersolution.eq_zero_on_quarter_ball (d := 3) (by norm_num) hRpos
    ⟨DeGiorgi.EllipticCoeff.identity 3 (Metric.ball c₃ R), rfl⟩ hGcont hGnonneg hsuper
    (Metric.mem_ball_self (by positivity)) hG0
  refine ⟨R / 4, by positivity, ?_, ?_⟩
  · intro x hx
    apply hsub
    rw [Metric.mem_ball] at hx ⊢
    nlinarith [hRr, hRpos]
  · intro x hx
    have hmem : incl_EG x ∈ Metric.ball c₃ (R / 4) := by
      rw [Metric.mem_ball, dist_incl_EG]
      exact Metric.mem_ball.mp hx
    have h := hquarter hmem
    simpa [lift_EG, projL_incl_EG, incl_apply_two_EG] using h

theorem eq_zero_of_nonneg_EG {Ω : Set E2} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) {v : E2 → ℝ}
    (hv : ContDiffOn ℝ 2 v Ω) (hv0 : ∀ x ∈ Ω, 0 ≤ v x) {c : E2 → ℝ} {M : ℝ}
    (hcM : ∀ x ∈ Ω, c x ≤ M) (hlap : ∀ x ∈ Ω, Laplacian.laplacian v x = c x * v x)
    {p : E2} (hp : p ∈ Ω) (hz : v p = 0) : ∀ x ∈ Ω, v x = 0 := by
  let O : Set E2 := {x | ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Ω ∧ ∀ y ∈ Metric.ball x r, v y = 0}
  have hO : IsOpen O := by
    rw [isOpen_iff_forall_mem_open]
    intro x ⟨r, hr, hsub, hzero⟩
    refine ⟨Metric.ball x r, fun y hy => ?_, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
    refine ⟨r - dist y x, by linarith [Metric.mem_ball.mp hy], ?_, ?_⟩
    · intro z hz'
      apply hsub
      rw [Metric.mem_ball] at hz' ⊢
      linarith [dist_triangle z y x]
    · intro z hz'
      apply hzero
      rw [Metric.mem_ball] at hz' ⊢
      linarith [dist_triangle z y x]
  have hP : IsOpen (Ω ∩ v ⁻¹' {y | y ≠ 0}) :=
    hv.continuousOn.isOpen_inter_preimage hΩ isOpen_ne
  have hOz : ∀ y ∈ O, v y = 0 := by
    rintro y ⟨r, hr, _, hzero⟩
    exact hzero y (Metric.mem_ball_self hr)
  have hpO : p ∈ O := local_zero_EG hΩ hv hv0 hcM hlap hp hz
  have hdisj : Disjoint O (Ω ∩ v ⁻¹' {y | y ≠ 0}) := by
    rw [Set.disjoint_left]
    intro x hxO hxP
    exact hxP.2 (hOz x hxO)
  have hsub : Ω ⊆ O := by
    refine IsPreconnected.subset_left_of_subset_union hO hP hdisj ?_ ⟨p, hp, hpO⟩ hΩc
    intro x hx
    by_cases hvx : v x = 0
    · exact Or.inl (local_zero_EG hΩ hv hv0 hcM hlap hx hvx)
    · exact Or.inr ⟨hx, hvx⟩
  exact fun x hx => hOz x (hsub hx)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
