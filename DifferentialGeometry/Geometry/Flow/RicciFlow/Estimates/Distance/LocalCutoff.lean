import DifferentialGeometry.Geometry.Comparison.DistanceCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Laplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Barrier
import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem mul_sqrt_div_eq_sqrt_mul {n Λ : ℝ} (hn : 0 ≤ n) (hΛ : 0 ≤ Λ) :
    n * Real.sqrt (Λ / n) = Real.sqrt (n * Λ) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hsq : (n * Real.sqrt (Λ / n)) ^ 2 = n * Λ := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hΛ hn)]
    field_simp
  have hleft := mul_nonneg hn (Real.sqrt_nonneg (Λ / n))
  have hright := Real.sqrt_nonneg (n * Λ)
  have hsqr := Real.sq_sqrt (mul_nonneg hn hΛ)
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem eventually_finite_of_calabi_tail
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r : ℝ} (tail : CalabiTail (I := I) g hEnorm O x r) :
    ∀ᶠ y in 𝓝 x, ∀ g' : SmoothRiemannianMetric I M,
      riemannianEDistOf (I := I) g' O y ≠ ⊤ := by
  have hleft_fin : Manifold.riemannianEDist I O tail.splitPoint ≠ ⊤ := by
    rw [tail.initial_edist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨v, hv, _⟩ := minExp_of_ne_top (I := I) g hEnorm O tail.splitPoint hleft_fin
  let γ := intrinsicGeodesic (I := I) g hEnorm O v
  let δ := fun y => intrinsicGeodesic (I := I) g hEnorm tail.splitPoint
    ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm (tail.branch.inv y))
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ :=
    contMDiffOn_univ.mp (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm O v)
  have hδ (y : M) : ContMDiff 𝓘(ℝ, ℝ) I 1 (δ y) :=
    contMDiffOn_univ.mp (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm tail.splitPoint _)
  have hγzero : γ 0 = O := intrinsicGeodesic_zero (I := I) g hEnorm O v
  have hγone : γ 1 = tail.splitPoint := by simpa only [γ, expMapIntrinsic_def] using hv
  have hδzero (y : M) : δ y 0 = tail.splitPoint := intrinsicGeodesic_zero (I := I) g hEnorm _ _
  filter_upwards [tail.branch.hom.open_target.mem_nhds tail.target_mem] with y hy
  have hδone : δ y 1 = y := by
    simpa only [δ, expMapIntrinsic_def] using tail.branch.right_inv hy
  intro g'
  have hdist := edistOf_le_two_arcs (I := I) g' zero_le_one zero_le_one
    hγ.contMDiffOn (hδ y).contMDiffOn (hγone.trans (hδzero y).symm)
  rw [hγzero, hδone] at hdist
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_scaled_distance_upper_support_of_ricci_bound_on_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (O : M)
    {T t Λ R : ℝ} (hT : 0 < T)
    (hreg : Ioc 0 T ⊆ D.regular) (ht : t ∈ Icc 0 T) (htpos : 0 < t)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    (hΛ : 0 ≤ Λ)
    (hRic : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, |ricciTensor (I := I) (S.base.metric t) y v v| ≤
        Λ * (S.base.metric t).inner y v v)
    (x : M) (hOx : O ≠ x)
    (hx : riemannianEDistOf (I := I) (S.base.metric t) O x < ENNReal.ofReal R) :
    let d : ℝ := Module.finrank ℝ E
    let r := (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    (∀ᶠ y in 𝓝 x, ∀ s : ℝ, riemannianEDistOf (I := I) (S.base.metric s) O y ≠ ⊤) ∧
    ∃ ρ : ℝ → M → ℝ,
      ρ t x = Real.exp (Λ * t) * r ∧
      (∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
        Real.exp (Λ * p.1) *
          (riemannianEDistOf (I := I) (S.base.metric p.1) O p.2).toReal ≤ ρ p.1 p.2) ∧
      DifferentiableWithinAt ℝ (fun s => ρ s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ρ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (ρ t) y) x ∧
      (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (ρ t) x)
        (gradientFun (I := I) (S.base.metric t) (ρ t) x) ≤ Real.exp (2 * Λ * t) ∧
      -Real.exp (Λ * t) * (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) ≤
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y)) ρ t x := by
  classical
  let d : ℝ := Module.finrank ℝ E
  let n : ℝ := ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
  let q := Real.sqrt (Λ / n)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hd : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdn : d - 1 = n := by
    dsimp only [d, n]
    rw [Nat.cast_sub hd]
    norm_num
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hnq : n * q = Real.sqrt ((d - 1) * Λ) := by
    rw [hdn]
    exact mul_sqrt_div_eq_sqrt_mul hn hΛ
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨(S.base.metric t).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨(S.base.metric t).inner, (S.base.metric t).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t) := by
    intro y w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hricBall : ∀ y ∈ Metric.eball O (ENNReal.ofReal R),
      ∀ v : TangentSpace I y, |ricciTensor (I := I) (S.base.metric t) y v v| ≤
        Λ * (S.base.metric t).inner y v v := by
    intro y hy v
    have hball : Manifold.riemannianEDist I O y < ENNReal.ofReal R := by
      rw [Metric.mem_eball', IsRiemannianManifold.out (I := I) O y] at hy
      exact hy
    exact hRic y hball v
  have hx' : Manifold.riemannianEDist I O x < ENNReal.ofReal R := hx
  have hfin : Manifold.riemannianEDist I O x ≠ ⊤ := ne_top_of_lt hx'
  have hRpos : 0 < R := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hx')
  have hR : (Manifold.riemannianEDist I O x).toReal < R :=
    (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hx' |>.trans_eq
      (ENNReal.toReal_ofReal hRpos.le)
  have hlower : 0 < Module.finrank ℝ E - 1 →
      ∀ y ∈ Metric.eball O (ENNReal.ofReal R), ∀ w : TangentSpace I y,
        -(n * q ^ 2) * (S.base.metric t).inner y w w ≤
          ricciTensor (I := I) (S.base.metric t) y w w := by
    intro hnpos y hy w
    have hnreal : 0 < n := by
      dsimp only [n]
      exact_mod_cast hnpos
    have hqsq : q ^ 2 = Λ / n := Real.sq_sqrt (div_nonneg hΛ hn)
    rw [hqsq, mul_div_cancel₀ Λ hnreal.ne']
    simpa only [neg_mul] using neg_le_of_abs_le (hricBall y hy w)
  obtain ⟨tail, hreach, _⟩ := exists_calabiData_lt
    (I := I) (S.base.metric t) hEnorm q hq hlower hOx hfin hR
  have htail : 0 < Module.finrank ℝ E - 1 →
      let γ := intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint tail.endpointVector
      ∀ u ∈ Ioo (0 : ℝ) tail.conjugateScale,
        -(n * q ^ 2) * (S.base.metric t).inner (γ u)
          (Variation.curveVelocity (I := I) γ u) (Variation.curveVelocity (I := I) γ u) ≤
        ricciTensor (I := I) (S.base.metric t) (γ u)
          (Variation.curveVelocity (I := I) γ u) (Variation.curveVelocity (I := I) γ u) := by
    intro hnpos
    dsimp only
    intro u hu
    exact hlower hnpos _ (tail.mem_eball hreach ⟨hu.1.le, hu.2.le⟩) _
  have hcoef : 2 * (d - 1) / (Manifold.riemannianEDist I O x).toReal +
      Real.sqrt ((d - 1) * Λ) =
      2 * n / (Manifold.riemannianEDist I O x).toReal + n * q := by rw [← hnq, hdn]
  obtain ⟨h⟩ := DistanceBarrier.exists_scaled_distance_support_of_calabi_tail
    (I := I) (d := d) S hS O hT hreg ht htpos x hEnorm tail hreach hq htail hricBall hcoef
  refine ⟨?_, h.exists_support_function⟩
  filter_upwards [eventually_finite_of_calabi_tail (I := I) (S.base.metric t) hEnorm tail]
    with y hy s
  exact hy (S.base.metric s)

private theorem cutoff_parabolic_bound
    {B D H K a : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hH : 0 ≤ H) (hHle : H ≤ K) {p e e' : ℝ}
    (hp : -B ≤ p) (he : e ≤ 0) (hebound : |e| ≤ D) (he'bound : |e'| ≤ D)
    (hB : 0 ≤ B) :
    e * (a * p) - e' * H ≤ D * (a * B + K) := by
  have hp' : -(a * B) ≤ a * p := by nlinarith [mul_le_mul_of_nonneg_left hp ha]
  have hfirst := mul_le_mul_of_nonpos_left hp' he
  have heb := (abs_le.mp hebound).1
  have he'b := (abs_le.mp he'bound).1
  have h1 : e * (a * p) ≤ D * (a * B) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ D + e) (mul_nonneg ha hB)]
  have h2 : -e' * H ≤ D * K := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ D + e') hH,
      mul_nonneg hD (sub_nonneg.mpr hHle)]
  nlinarith

theorem exists_distance_cutoff_lower_support_of_ricci_bound_on_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (O : M)
    {T t Λ R : ℝ} (hT : 0 < T)
    (hreg : Ioc 0 T ⊆ D.regular) (ht : t ∈ Icc 0 T) (htpos : 0 < t)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    (hΛ : 0 ≤ Λ)
    (hRic : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, |ricciTensor (I := I) (S.base.metric t) y v v| ≤
        Λ * (S.base.metric t).inner y v v)
    (a : ℝ) (ha : 0 ≤ a)
    (x : M) (hOx : O ≠ x)
    (hx : riemannianEDistOf (I := I) (S.base.metric t) O x < ENNReal.ofReal R) :
    let d : ℝ := Module.finrank ℝ E
    let r := (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    let z := a * Real.exp (Λ * t) * r
    let χ := fun s y => Analysis.CutoffProfile.evalue
      (ENNReal.ofReal (a * Real.exp (Λ * s)) *
        riemannianEDistOf (I := I) (S.base.metric s) O y)
    ∃ φ : ℝ → M → ℝ,
      φ t x = χ t x ∧
      (∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
        0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2) ∧
      DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (φ t) y) x ∧
      (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (φ t) x)
        (gradientFun (I := I) (S.base.metric t) (φ t) x) ≤
          (deriv Analysis.CutoffProfile.value z) ^ 2 * a ^ 2 * Real.exp (2 * Λ * t) ∧
      parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y)) φ t x ≤
          Analysis.CutoffProfile.derivBound *
            (a * Real.exp (Λ * t) * (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) +
              a ^ 2 * Real.exp (2 * Λ * t)) := by
  obtain ⟨hfinite, ρ, hρeq, hρupper, hρtime, hρspace, hρgrad, hρsq, hρpar⟩ :=
    exists_scaled_distance_upper_support_of_ricci_bound_on_ball
      (I := I) S hS O hT hreg ht htpos hcomplete hΛ hRic x hOx hx
  let u : ℝ → M → ℝ := fun s y => a * ρ s y
  let φ : ℝ → M → ℝ := fun s y => Analysis.CutoffProfile.value (u s y)
  have hvalue : Differentiable ℝ Analysis.CutoffProfile.value :=
    Analysis.CutoffProfile.contDiff.differentiable (by simp)
  have hvalueC2 : ContDiff ℝ 2 Analysis.CutoffProfile.value :=
    Analysis.CutoffProfile.contDiff.of_le (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hvalue' : Differentiable ℝ (deriv Analysis.CutoffProfile.value) :=
    (hvalueC2.deriv' (n := 1)).differentiable (by simp)
  have hlin : Differentiable ℝ (fun q : ℝ => a * q) := fun q =>
    (hasDerivAt_const_mul (x := q) a).differentiableAt
  have hlin' : Differentiable ℝ (deriv fun q : ℝ => a * q) := by
    have hder : (deriv fun q : ℝ => a * q) = fun _ => a :=
      funext fun q => (hasDerivAt_const_mul (x := q) a).deriv
    rw [hder]
    exact differentiable_const a
  have hutime : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t :=
    hρtime.const_mul a
  have huspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y := by
    filter_upwards [hρspace] with y hy
    exact hy.const_smul a
  have hugrad : MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (u t) y) x :=
    grad_comp_mdiffAt (I := I) (S.base.metric t) hlin (hlin' (ρ t x)) hρspace hρgrad
  have hftime : DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 T) t := by
    with_unfolding_all exact
      (hvalue (u t x)).comp_differentiableWithinAt t hutime
  have hfspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y := by
    filter_upwards [huspace] with y hy
    exact (hvalue (u t y)).mdifferentiableAt.comp y hy
  have hfgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (φ t) y) x :=
    grad_comp_mdiffAt (I := I) (S.base.metric t) hvalue (hvalue' (u t x)) huspace hugrad
  have hfinite' : ∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
      riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 ≠ ⊤ := by
    have h := (continuous_snd.continuousAt :
      ContinuousAt (fun p : ℝ × M => p.2) (t, x)).eventually hfinite
    filter_upwards [h.filter_mono inf_le_left] with p hp
    exact hp p.1
  have hχreal (s : ℝ) (y : M)
      (hfin : riemannianEDistOf (I := I) (S.base.metric s) O y ≠ ⊤) :
      Analysis.CutoffProfile.evalue
        (ENNReal.ofReal (a * Real.exp (Λ * s)) *
          riemannianEDistOf (I := I) (S.base.metric s) O y) =
      Analysis.CutoffProfile.value (a * (Real.exp (Λ * s) *
        (riemannianEDistOf (I := I) (S.base.metric s) O y).toReal)) := by
    rw [Analysis.CutoffProfile.evalue_eq_value (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg ha (Real.exp_pos _).le)]
    congr 1
    ring
  have heq : φ t x = Analysis.CutoffProfile.evalue
      (ENNReal.ofReal (a * Real.exp (Λ * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) O x) := by
    rw [hχreal t x (ne_top_of_lt hx)]
    change Analysis.CutoffProfile.value (a * ρ t x) = _
    rw [hρeq]
  have hlower : ∀ᶠ p in 𝓝[Icc 0 T ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ Analysis.CutoffProfile.evalue
        (ENNReal.ofReal (a * Real.exp (Λ * p.1)) *
          riemannianEDistOf (I := I) (S.base.metric p.1) O p.2) := by
    filter_upwards [hρupper, hfinite'] with p hp hfin
    refine ⟨(Analysis.CutoffProfile.mem_Icc _).1, ?_⟩
    rw [hχreal p.1 p.2 hfin]
    exact Analysis.CutoffProfile.antitone_value (mul_le_mul_of_nonneg_left hp ha)
  have hgu : gradientFun (I := I) (S.base.metric t) (u t) x =
      a • gradientFun (I := I) (S.base.metric t) (ρ t) x :=
    gradientFun_const_smul (I := I) (S.base.metric t) a hρspace.self_of_nhds
  have hgf : gradientFun (I := I) (S.base.metric t) (φ t) x =
      deriv Analysis.CutoffProfile.value (u t x) • gradientFun (I := I) (S.base.metric t) (u t) x :=
    gradientFun_comp (I := I) (S.base.metric t) (hvalue (u t x)) huspace.self_of_nhds
  have husq : (S.base.metric t).inner x
      (gradientFun (I := I) (S.base.metric t) (u t) x)
      (gradientFun (I := I) (S.base.metric t) (u t) x) ≤ a ^ 2 * Real.exp (2 * Λ * t) := by
    rw [hgu]
    simpa only [map_smul, smul_apply, smul_eq_mul, pow_two, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hρsq (sq_nonneg a)
  have huz : u t x = a * Real.exp (Λ * t) *
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal := by
    dsimp only [u]
    rw [hρeq]
    ring
  refine ⟨φ, heq, hlower, hftime, hfspace, hfgrad, ?_, ?_⟩
  · rw [hgf]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← huz]
    nlinarith [mul_le_mul_of_nonneg_left husq
      (sq_nonneg (deriv Analysis.CutoffProfile.value (u t x)))]
  · have hcomp := parabolic_comp_nhds (I := I) (flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y)) u t x hvalue (hvalue' (u t x)) hutime huspace hugrad
    have hscale := parabolic_smul_nhds (I := I) (G := flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y)) a ρ t x hρspace hρgrad
    change parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y)) φ t x = _ at hcomp
    rw [hcomp, hscale]
    have hnonneg : 0 ≤ (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (u t) x)
        (gradientFun (I := I) (S.base.metric t) (u t) x) := by
      by_cases hv : gradientFun (I := I) (S.base.metric t) (u t) x = 0
      · rw [hv]
        simp
      · exact ((S.base.metric t).pos x _ hv).le
    have hd : 0 ≤ (Module.finrank ℝ E : ℝ) - 1 := by
      have hdim : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
      have hdimR : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdim
      linarith
    have hB : 0 ≤ Real.exp (Λ * t) *
        (2 * ((Module.finrank ℝ E : ℝ) - 1) /
          (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal +
            Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * Λ)) := by positivity
    have hbound := cutoff_parabolic_bound ha Analysis.CutoffProfile.derivBound_nonneg
      hnonneg husq (by simpa only [neg_mul] using hρpar)
      (Analysis.CutoffProfile.deriv_nonpos (u t x))
      (Analysis.CutoffProfile.abs_deriv_le_derivBound (u t x))
      (Analysis.CutoffProfile.abs_deriv2_le_derivBound (u t x)) hB
    simpa only [mul_assoc, gradientAt, flowG] using hbound

theorem exists_distance_cutoff_lower_support_of_ricci_le_on_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t R K : ℝ} (ht : t ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (hR : 0 < R) (hK : 0 ≤ K)
    (hRic : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v)
    (a : ℝ) (ha : 0 ≤ a)
    (x : M) (hx : R ≤ (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal) :
    let r := (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    let χ := fun s y => Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y)
    ∃ φ : ℝ → M → ℝ,
      φ t x = χ t x ∧
      (∀ᶠ y in 𝓝 x, ∀ s : ℝ, 0 ≤ φ s y ∧ φ s y ≤ χ s y) ∧
      DifferentiableAt ℝ (fun s => φ s x) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (φ t) y) x ∧
      (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (φ t) x)
        (gradientFun (I := I) (S.base.metric t) (φ t) x) ≤
          (deriv Analysis.CutoffProfile.value (a * r)) ^ 2 * a ^ 2 ∧
      deriv (fun s => φ s x) t - laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) (φ t) x ≤
        Analysis.CutoffProfile.derivBound *
          (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
            K * R) + a ^ 2) := by
  obtain ⟨ρ, hρeq, hρupper, hρtime, hρspace, hρgrad, hρsq, hρpar⟩ :=
    exists_distance_upper_support_of_ricci_le_on_ball
      (I := I) S hS ht hcomplete O hR hK hRic x hx
  let u : ℝ → M → ℝ := fun s y => a * ρ s y
  let φ : ℝ → M → ℝ := fun s y => Analysis.CutoffProfile.value (u s y)
  have hvalue : Differentiable ℝ Analysis.CutoffProfile.value :=
    Analysis.CutoffProfile.contDiff.differentiable (by simp)
  have hvalueC2 : ContDiff ℝ 2 Analysis.CutoffProfile.value :=
    Analysis.CutoffProfile.contDiff.of_le (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hvalue' : Differentiable ℝ (deriv Analysis.CutoffProfile.value) :=
    (hvalueC2.deriv' (n := 1)).differentiable (by simp)
  have hlin : Differentiable ℝ (fun q : ℝ => a * q) := fun q =>
    (hasDerivAt_const_mul (x := q) a).differentiableAt
  have hlin' : Differentiable ℝ (deriv fun q : ℝ => a * q) := by
    have hder : (deriv fun q : ℝ => a * q) = fun _ => a :=
      funext fun q => (hasDerivAt_const_mul (x := q) a).deriv
    rw [hder]
    exact differentiable_const a
  have hutime : DifferentiableAt ℝ (fun s => u s x) t := hρtime.const_mul a
  have huspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y := by
    filter_upwards [hρspace] with y hy
    exact hy.const_smul a
  have hugrad : MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (u t) y) x :=
    grad_comp_mdiffAt (I := I) (S.base.metric t) hlin (hlin' (ρ t x)) hρspace hρgrad
  have hftime : DifferentiableAt ℝ (fun s => φ s x) t := by
    with_unfolding_all exact (hvalue (u t x)).comp t hutime
  have hfspace : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y := by
    filter_upwards [huspace] with y hy
    exact (hvalue (u t y)).mdifferentiableAt.comp y hy
  have hfgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (φ t) y) x :=
    grad_comp_mdiffAt (I := I) (S.base.metric t) hvalue (hvalue' (u t x)) huspace hugrad
  have hfin : riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hρupper.self_of_nhds t)
  have heq : φ t x = Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric t) O x) := by
    rw [Analysis.CutoffProfile.evalue_eq_value
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
    change Analysis.CutoffProfile.value (a * ρ t x) = _
    rw [hρeq]
  have hlower : ∀ᶠ y in 𝓝 x, ∀ s : ℝ,
      0 ≤ φ s y ∧ φ s y ≤ Analysis.CutoffProfile.evalue
        (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y) := by
    filter_upwards [hρupper] with y hy s
    refine ⟨(Analysis.CutoffProfile.mem_Icc _).1, ?_⟩
    have h := Analysis.CutoffProfile.antitone_evalue
      (mul_le_mul_right (hy s) (ENNReal.ofReal a))
    rw [← ENNReal.ofReal_mul ha, Analysis.CutoffProfile.evalue_ofReal] at h
    exact h
  have hgu : gradientFun (I := I) (S.base.metric t) (u t) x =
      a • gradientFun (I := I) (S.base.metric t) (ρ t) x :=
    gradientFun_const_smul (I := I) (S.base.metric t) a hρspace.self_of_nhds
  have hgf : gradientFun (I := I) (S.base.metric t) (φ t) x =
      deriv Analysis.CutoffProfile.value (u t x) • gradientFun (I := I) (S.base.metric t) (u t) x :=
    gradientFun_comp (I := I) (S.base.metric t) (hvalue (u t x)) huspace.self_of_nhds
  have husq : (S.base.metric t).inner x
      (gradientFun (I := I) (S.base.metric t) (u t) x)
      (gradientFun (I := I) (S.base.metric t) (u t) x) = a ^ 2 := by
    rw [hgu, gInner_smul_self, hρsq, mul_one]
  have huz : u t x = a * (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal := by
    dsimp only [u]
    rw [hρeq]
  refine ⟨φ, heq, hlower, hftime, hfspace, hfgrad, ?_, ?_⟩
  · rw [hgf, gInner_smul_self, husq, huz]
  · have hd : deriv (fun s => φ s x) t =
        deriv Analysis.CutoffProfile.value (u t x) * (a * deriv (fun s => ρ s x) t) := by
      with_unfolding_all exact
        ((hvalue (u t x)).hasDerivAt.comp t (hρtime.hasDerivAt.const_mul a)).deriv
    have hlap := laplacian_comp_of_eventually_differentiable (I := I)
      (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t)
      (Filter.Eventually.of_forall hvalue) (hvalue' (u t x)) huspace hugrad
    have hscale := laplacian_smul_at (I := I)
      (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) a hρspace hρgrad
    change laplacian (I := I) _ _ (φ t) x = _ at hlap
    change laplacian (I := I) _ _ (u t) x = _ at hscale
    rw [hd, hlap, hscale]
    have hdimen : 0 ≤ (Module.finrank ℝ E : ℝ) - 1 := by
      have hdim : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
      have hdimR : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdim
      linarith
    have hB : 0 ≤ 2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
        K * R := by positivity
    have hbound := cutoff_parabolic_bound ha Analysis.CutoffProfile.derivBound_nonneg
      (show 0 ≤ (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (u t) x)
        (gradientFun (I := I) (S.base.metric t) (u t) x) by rw [husq]; positivity)
      husq.le hρpar (Analysis.CutoffProfile.deriv_nonpos (u t x))
      (Analysis.CutoffProfile.abs_deriv_le_derivBound (u t x))
      (Analysis.CutoffProfile.abs_deriv2_le_derivBound (u t x)) hB
    nlinarith

omit [NeZero (Module.finrank ℝ E)] in
private theorem eventually_distance_cutoff_eq_one
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t : ℝ} (ht : J ∈ nhds t)
    (hcomplete : RiemannianMetricComplete (I := I) (g t))
    (O x : M) (hfin : riemannianEDistOf (I := I) (g t) O x ≠ ⊤)
    {a : ℝ} (ha : 0 ≤ a)
    (hx : a * (riemannianEDistOf (I := I) (g t) O x).toReal < 1) :
    ∀ᶠ p in nhds (t, x), DifferentialGeometry.Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (g p.1) O p.2) = 1 := by
  obtain ⟨F, hF, hFx, hupper⟩ := exists_riemannianEDistOf_upper_support_continuousAt
    (I := I) g hg ht hcomplete O x hfin
  have hcenter : a * F (t, x) < 1 := by simpa [hFx] using hx
  have hsmall : ∀ᶠ p in nhds (t, x), a * F p < 1 := by
    exact (continuousAt_const.mul hF).eventually (Iio_mem_nhds hcenter)
  filter_upwards [hsmall, hupper] with p hp hdist
  apply DifferentialGeometry.Analysis.CutoffProfile.evalue_one_of_le
  have hmul := mul_le_mul_right hdist (ENNReal.ofReal a)
  rw [← ENNReal.ofReal_mul ha] at hmul
  exact hmul.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le)


theorem exists_distance_cutoff_lower_support_at
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t R K : ℝ} (ht : t ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (hR : 0 < R) (hK : 0 ≤ K)
    (hRic : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v)
    (a : ℝ) (ha : 0 ≤ a) (haR : a * R < 1) (x : M) :
    let r := (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    let χ := fun s y => Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y)
    ∃ φ : ℝ → M → ℝ,
      φ t x = χ t x ∧
      (∀ᶠ p : ℝ × M in 𝓝 (t, x), 0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2) ∧
      DifferentiableAt ℝ (fun s => φ s x) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (φ t) y) x ∧
      (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (φ t) x)
        (gradientFun (I := I) (S.base.metric t) (φ t) x) ≤
          (deriv Analysis.CutoffProfile.value (a * r)) ^ 2 * a ^ 2 ∧
      deriv (fun s => φ s x) t - laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) (φ t) x ≤
        Analysis.CutoffProfile.derivBound *
          (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
            K * R) + a ^ 2) := by
  let r := (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
  let χ := fun s y => Analysis.CutoffProfile.evalue
    (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y)
  dsimp only
  have hgrad_nonneg : 0 ≤ (deriv Analysis.CutoffProfile.value (a * r)) ^ 2 * a ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdim : (1 : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hpar_nonneg : 0 ≤ Analysis.CutoffProfile.derivBound *
      (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
        K * R) + a ^ 2) := by
    apply mul_nonneg Analysis.CutoffProfile.derivBound_nonneg
    exact add_nonneg (mul_nonneg ha (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hdim)) (sq_nonneg _)) hR.le)
      (mul_nonneg hK hR.le))) (sq_nonneg _)
  have hconst (c : ℝ) (hc : c = χ t x) (hc0 : 0 ≤ c)
      (hcl : ∀ᶠ p : ℝ × M in 𝓝 (t, x), c ≤ χ p.1 p.2) :
      ∃ φ : ℝ → M → ℝ,
        φ t x = χ t x ∧
        (∀ᶠ p : ℝ × M in 𝓝 (t, x), 0 ≤ φ p.1 p.2 ∧ φ p.1 p.2 ≤ χ p.1 p.2) ∧
        DifferentiableAt ℝ (fun s => φ s x) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
        MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (φ t) y) x ∧
        (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (φ t) x)
          (gradientFun (I := I) (S.base.metric t) (φ t) x) ≤
            (deriv Analysis.CutoffProfile.value (a * r)) ^ 2 * a ^ 2 ∧
        deriv (fun s => φ s x) t - laplacian (I := I)
            (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) (φ t) x ≤
          Analysis.CutoffProfile.derivBound *
            (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
              K * R) + a ^ 2) := by
    refine ⟨fun _ _ => c, hc, hcl.mono (fun p hp => ⟨hc0, hp⟩),
      differentiableAt_const c, Filter.Eventually.of_forall (fun _ => mdifferentiableAt_const), ?_, ?_, ?_⟩
    · simpa only [gradientFun_const] using!
        (contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).contMDiffAt.mdifferentiableAt one_ne_zero
    · simpa only [gradientFun_const, map_zero] using hgrad_nonneg
    · simpa only [deriv_const, laplacian_const, sub_zero] using hpar_nonneg
  by_cases ha0 : a = 0
  · have hχ : ∀ s y, χ s y = 1 := by
      intro s y
      apply Analysis.CutoffProfile.evalue_one_of_le
      simp [ha0]
    exact hconst 1 (hχ t x).symm zero_le_one
      (Filter.Eventually.of_forall (fun p => (hχ p.1 p.2).ge))
  by_cases hfin : riemannianEDistOf (I := I) (S.base.metric t) O x = ⊤
  · have hχ : χ t x = 0 := by
      dsimp only [χ]
      rw [hfin, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne ha (Ne.symm ha0))),
        Analysis.CutoffProfile.evalue_top]
    exact hconst 0 hχ.symm le_rfl (Filter.Eventually.of_forall (fun p =>
      (Analysis.CutoffProfile.evalue_mem_Icc _).1))
  by_cases hx : R ≤ r
  · obtain ⟨φ, heq, hlow, htime, hspace, hgrad, hgsq, hpar⟩ :=
      exists_distance_cutoff_lower_support_of_ricci_le_on_ball
        (I := I) S hS ht hcomplete O hR hK hRic a ha x hx
    refine ⟨φ, heq, ?_, htime, hspace, hgrad, hgsq, hpar⟩
    have hlow' : ∀ᶠ p : ℝ × M in nhds (t, x), ∀ s : ℝ,
        0 ≤ φ s p.2 ∧ φ s p.2 ≤ χ s p.2 :=
      (continuousAt_snd : ContinuousAt (fun p : ℝ × M => p.2) (t, x)).eventually hlow
    exact hlow'.mono (fun p hp => hp p.1)
  · have hinner : a * r < 1 :=
      (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hx)) ha).trans_lt haR
    have hJ : D.carrier ∈ nhds t := by
      obtain ⟨α, β, ht', hwin⟩ := D.exists_Icc_regular ht
      exact Filter.mem_of_superset (Icc_mem_nhds ht'.1 ht'.2)
        (fun _ hs => D.regular_subset (hwin hs))
    have hone := eventually_distance_cutoff_eq_one (I := I) S.base.metric
      hS.smoothMetric.metricTensor_cont hJ hcomplete O x hfin ha hinner
    exact hconst 1 hone.self_of_nhds.symm zero_le_one
      (hone.mono (fun _ hp => hp.ge))

theorem distance_cutoff_lower_support_with_gradient_ratio
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t R K : ℝ} (ht : t ∈ D.regular) (htpos : 0 < t)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (hR : 0 < R) (hK : 0 ≤ K)
    (hRic : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v)
    {a C : ℝ} (ha : 0 ≤ a) (haR : a * R < 1)
    (hC : ∀ s : ℝ, (deriv Analysis.CutoffProfile.value s) ^ 2 ≤ C * Analysis.CutoffProfile.value s)
    (x : M) :
    let χ := fun s y => Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y)
    ∃ φ : ℝ → M → ℝ,
      φ t x = χ t x ∧
      (∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2) ∧
      DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
      MDiffAt (T% fun y => gradientFun (I := I) (S.base.metric t) (φ t) y) x ∧
      parabolicOperatorWithDrift (I := I) (flowG (I := I) S) t
        (fun _ y => (0 : TangentSpace I y)) φ t x ≤
        Analysis.CutoffProfile.derivBound *
          (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
            K * R) + a ^ 2) ∧
      (S.base.metric t).inner x (gradientFun (I := I) (S.base.metric t) (φ t) x)
        (gradientFun (I := I) (S.base.metric t) (φ t) x) ≤ (C * a ^ 2) * φ t x := by
  let d := riemannianEDistOf (I := I) (S.base.metric t) O x
  obtain ⟨φ, hφeq, hφχ, hφtime, hφspace, hφgrad, hφg, hφP⟩ :=
    exists_distance_cutoff_lower_support_at S hS ht hcomplete O hR hK hRic a ha haR x
  refine ⟨φ, hφeq, (hφχ.mono fun p hp => hp.2).filter_mono nhdsWithin_le_nhds,
    hφtime.differentiableWithinAt, hφspace, hφgrad, ?_, ?_⟩
  · unfold parabolicOperatorWithDrift heatOperatorWithDrift
    rw [hφtime.hasDerivAt.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc htpos) t ⟨htpos.le, le_rfl⟩)]
    simpa only [laplacianAt, flowG, driftTerm, SolutionFamily.connection,
      LeviCivita_eq_leviCivitaConnectionOfMetric, map_zero, Pi.zero_apply,
      zero_apply, add_zero] using hφP
  · rw [hφeq]
    change _ ≤ C * a ^ 2 * Analysis.CutoffProfile.evalue (ENNReal.ofReal a * d)
    by_cases ha0 : a = 0
    · simpa only [ha0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul] using hφg
    by_cases hd : d = ⊤
    · have ha0' : ENNReal.ofReal a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne ha (Ne.symm ha0))
      change _ ≤ (deriv Analysis.CutoffProfile.value (a * d.toReal)) ^ 2 * a ^ 2 at hφg
      rw [hd, ENNReal.toReal_top, mul_zero,
        Analysis.CutoffProfile.deriv_zero_of_le (by norm_num : (0 : ℝ) ≤ 1),
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hφg
      simpa only [hd, ENNReal.mul_top ha0', Analysis.CutoffProfile.evalue_top, mul_zero] using hφg
    have hvalue : Analysis.CutoffProfile.evalue (ENNReal.ofReal a * d) =
        Analysis.CutoffProfile.value (a * d.toReal) := by
      rw [Analysis.CutoffProfile.evalue_eq_value (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
    have hscaled := mul_le_mul_of_nonneg_right (hC (a * d.toReal)) (sq_nonneg a)
    rw [hvalue]
    change _ ≤ (deriv Analysis.CutoffProfile.value (a * d.toReal)) ^ 2 * a ^ 2 at hφg
    nlinarith only [hφg, hscaled]

end DifferentialGeometry.PDE.RicciFlow
