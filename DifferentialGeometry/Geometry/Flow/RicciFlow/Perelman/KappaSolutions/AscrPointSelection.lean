import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticScalarRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialPointSelection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open scoped _root_.Topology

private def ascrPointEta (i : ℕ) : ℝ := 1 / ((i : ℝ) + 2)

private def ascrPointEpsilon (i : ℕ) : ℝ := ((1 - ascrPointEta i)⁻¹) ^ 2 - 1

private theorem ascrPointEta_pos (i : ℕ) : 0 < ascrPointEta i := by
  unfold ascrPointEta
  positivity

private theorem ascrPointEta_le_half (i : ℕ) : ascrPointEta i ≤ 1 / 2 := by
  unfold ascrPointEta
  apply (div_le_iff₀ (by positivity : 0 < (i : ℝ) + 2)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

private theorem ascrPointEta_lt_one (i : ℕ) : ascrPointEta i < 1 :=
  (ascrPointEta_le_half i).trans_lt (by norm_num)

private theorem ascrPointEpsilon_pos (i : ℕ) : 0 < ascrPointEpsilon i := by
  have hu : 0 < 1 - ascrPointEta i := sub_pos.mpr (ascrPointEta_lt_one i)
  have hv : 1 < (1 - ascrPointEta i)⁻¹ := by
    have h := one_div_lt_one_div_of_lt hu
      (by linarith [ascrPointEta_pos i] : 1 - ascrPointEta i < 1)
    simpa only [div_one, one_div] using h
  dsimp only [ascrPointEpsilon]
  nlinarith

private theorem ascrPointEpsilon_strictAnti : StrictAnti ascrPointEpsilon := by
  intro i j hij
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have heta : ascrPointEta j < ascrPointEta i := by
    exact one_div_lt_one_div_of_lt (by positivity : 0 < (i : ℝ) + 2)
      (by linarith : (i : ℝ) + 2 < (j : ℝ) + 2)
  have hi : 0 < 1 - ascrPointEta i := sub_pos.mpr (ascrPointEta_lt_one i)
  have hj : 0 < 1 - ascrPointEta j := sub_pos.mpr (ascrPointEta_lt_one j)
  have hinv : (1 - ascrPointEta j)⁻¹ < (1 - ascrPointEta i)⁻¹ :=
    (inv_lt_inv₀ hj hi).mpr (by linarith)
  have hsquare := (sq_lt_sq₀ (inv_nonneg.mpr hj.le) (inv_nonneg.mpr hi.le)).mpr hinv
  exact sub_lt_sub_right hsquare 1

private theorem ascrPointEpsilon_tendsto :
    Tendsto ascrPointEpsilon atTop (𝓝 0) := by
  have hden : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun i => by linarith)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have heta : Tendsto ascrPointEta atTop (𝓝 0) := by
    change Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 2)) atTop (𝓝 0)
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp hden
  have hinv : Tendsto (fun i => (1 - ascrPointEta i)⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero, inv_one] using
      (tendsto_const_nhds.sub heta).inv₀ (by norm_num : (1 - 0 : ℝ) ≠ 0)
  change Tendsto (fun i => ((1 - ascrPointEta i)⁻¹) ^ 2 - 1) atTop (𝓝 0)
  simpa only [one_pow, sub_self] using
    (hinv.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))

section ProperMetric

variable {X : Type*} [MetricSpace X] [ProperSpace X]

private theorem ascr_exists_weighted_maximum
    {f : X → ℝ} (hf : Continuous f) (y : X) (hy : 0 < f y)
    {R eta : ℝ} (hR : 0 < R) (heta1 : eta < 1) :
    ∃ (x : X) (sigma : ℝ), 0 < sigma ∧ sigma ≤ R ∧
      dist y x ≤ R ∧ 0 < f x ∧ f y * R ^ 2 ≤ f x * sigma ^ 2 ∧
      ∀ z : X, dist z x < eta * sigma →
        f z ≤ ((1 - eta)⁻¹) ^ 2 * f x := by
  let F : X → ℝ := fun z => f z * (R - dist y z) ^ 2
  have hF : Continuous F :=
    hf.mul ((continuous_const.sub (continuous_const.dist continuous_id)).pow 2)
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall y R).exists_isMaxOn
    ⟨y, by simpa only [Metric.mem_closedBall, dist_self] using hR.le⟩ hF.continuousOn
  let sigma : ℝ := R - dist y x
  have hxle : dist y x ≤ R := by
    simpa only [Metric.mem_closedBall, dist_comm] using hx
  have hsigma : 0 ≤ sigma := sub_nonneg.mpr hxle
  have hsigmaR : sigma ≤ R := by
    dsimp only [sigma]
    linarith [dist_nonneg (x := y) (y := x)]
  have hweight : f y * R ^ 2 ≤ f x * sigma ^ 2 := by
    have hyball : y ∈ Metric.closedBall y R := by
      simpa only [Metric.mem_closedBall, dist_self] using hR.le
    have hymax : F y ≤ F x := hmax hyball
    simpa only [F, sigma, dist_self, sub_zero] using hymax
  have hpositive : 0 < f y * R ^ 2 := mul_pos hy (sq_pos_of_pos hR)
  have hsigma_pos : 0 < sigma := by
    by_contra hn
    have hz : sigma = 0 := le_antisymm (le_of_not_gt hn) hsigma
    rw [hz, zero_pow (by decide), mul_zero] at hweight
    exact (not_le_of_gt hpositive) hweight
  have hfx : 0 < f x :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos hsigma_pos)).mp
      (hpositive.trans_le hweight)
  refine ⟨x, sigma, hsigma_pos, hsigmaR, hxle, hfx, hweight, ?_⟩
  intro z hz
  by_cases hfz : 0 ≤ f z
  · have hz' : dist x z < eta * sigma := by simpa only [dist_comm] using hz
    have htri := dist_triangle y x z
    have hslack : (1 - eta) * sigma ≤ R - dist y z := by
      dsimp only [sigma] at hz' ⊢
      nlinarith
    have hslack_pos : 0 < (1 - eta) * sigma :=
      mul_pos (sub_pos.mpr heta1) hsigma_pos
    have hzball : z ∈ Metric.closedBall y R := by
      rw [Metric.mem_closedBall, dist_comm]
      linarith
    have hsquare : ((1 - eta) * sigma) ^ 2 ≤ (R - dist y z) ^ 2 :=
      (sq_le_sq₀ hslack_pos.le (hslack_pos.le.trans hslack)).mpr hslack
    have hprod := mul_le_mul_of_nonneg_left hsquare hfz
    have hmaxz : f z * (R - dist y z) ^ 2 ≤ f x * sigma ^ 2 := hmax hzball
    have hcancel : f z * (1 - eta) ^ 2 ≤ f x := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hsigma_pos)).mp
      nlinarith [hprod, hmaxz]
    have hdiv : f z ≤ f x / (1 - eta) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr heta1))).mpr hcancel
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hdiv
  · exact (le_of_lt (lt_of_not_ge hfz)).trans
      (mul_nonneg (sq_nonneg _) hfx.le)

omit [ProperSpace X] in
private theorem ascr_disjoint_subsequence
    (p : X) (x : ℕ → X) (r : ℕ → ℝ)
    (hescape : Tendsto (fun i => dist p (x i)) atTop atTop)
    (hr : ∀ i, r i ≤ dist p (x i) / 6) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Pairwise (fun i j => Disjoint (Metric.ball (x (phi i)) (r (phi i)))
        (Metric.ball (x (phi j)) (r (phi j)))) := by
  have hex (k : ℕ) : ∃ j : ℕ, k < j ∧
      2 * dist p (x k) + 1 ≤ dist p (x j) := by
    have hevent : ∀ᶠ j in atTop, k < j ∧
        2 * dist p (x k) + 1 ≤ dist p (x j) := by
      filter_upwards [eventually_gt_atTop k,
        hescape.eventually_ge_atTop (2 * dist p (x k) + 1)] with j hj hd
      exact ⟨hj, hd⟩
    exact hevent.exists
  choose next hnext using hex
  let phi : ℕ → ℕ := fun n => Nat.rec 0 (fun _ k => next k) n
  have hstep (n : ℕ) : phi (n + 1) = next (phi n) := rfl
  have hmono : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hstep]
    exact (hnext (phi n)).1
  have hgrow (n : ℕ) :
      2 * dist p (x (phi n)) + 1 ≤ dist p (x (phi (n + 1))) := by
    rw [hstep]
    exact (hnext (phi n)).2
  have hdistmono : Monotone (fun n => dist p (x (phi n))) := by
    apply monotone_nat_of_le_succ
    intro n
    linarith [hgrow n, dist_nonneg (x := p) (y := x (phi n))]
  have hdisjoint {i j : ℕ} (hij : i < j) :
      Disjoint (Metric.ball (x (phi i)) (r (phi i)))
        (Metric.ball (x (phi j)) (r (phi j))) := by
    have hle := hdistmono (Nat.succ_le_iff.mpr hij)
    have hsep : 2 * dist p (x (phi i)) ≤ dist p (x (phi j)) := by
      linarith [hgrow i]
    apply Metric.ball_disjoint_ball
    have htri := dist_triangle p (x (phi i)) (x (phi j))
    linarith [hr (phi i), hr (phi j), dist_nonneg (x := p) (y := x (phi i))]
  refine ⟨phi, hmono, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hdisjoint hlt
  · exact (hdisjoint hgt).symm

theorem exists_ascrPointSelection
    {f : X → ℝ} (hf : Continuous f) (p : X)
    (hfar : ∀ A D : ℝ, 0 < A → 0 < D → ∃ y : X,
      D ≤ dist p y ∧ A < f y * dist p y ^ 2) :
    ∃ (x : ℕ → X) (r eps : ℕ → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ dist p (x i) / 6 ∧ 0 < f (x i)) ∧
      (∀ i, 0 < eps i) ∧ StrictAnti eps ∧ Tendsto eps atTop (𝓝 0) ∧
      Pairwise (fun i j => Disjoint (Metric.ball (x i) (r i)) (Metric.ball (x j) (r j))) ∧
      Tendsto (fun i => dist p (x i)) atTop atTop ∧
      Tendsto (fun i => f (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => dist p (x i) / r i) atTop atTop ∧
      ∀ i z, dist z (x i) < r i → f z ≤ (1 + eps i) * f (x i) := by
  have hchoose (i : ℕ) : ∃ y : X,
      4 * ((i : ℝ) + 1) ≤ dist p y ∧
      16 * ((i : ℝ) + 1) / ascrPointEta i ^ 2 < f y * dist p y ^ 2 :=
    hfar _ _ (by positivity [ascrPointEta_pos i]) (by positivity)
  choose y hy using hchoose
  have hdy (i : ℕ) : 0 < dist p (y i) := by
    linarith [(hy i).1, Nat.cast_nonneg (α := ℝ) i]
  have hfy (i : ℕ) : 0 < f (y i) := by
    have hlarge : 0 < f (y i) * dist p (y i) ^ 2 :=
      (by positivity [ascrPointEta_pos i] :
        0 < 16 * ((i : ℝ) + 1) / ascrPointEta i ^ 2).trans (hy i).2
    exact (mul_pos_iff_of_pos_right (sq_pos_of_pos (hdy i))).mp hlarge
  choose x sigma hsigma hsigmaR hxR hfx hweight hcontrol using fun i =>
    ascr_exists_weighted_maximum hf (y i) (hfy i)
      (R := dist p (y i) / 4) (eta := ascrPointEta i)
      (by positivity [hdy i]) (ascrPointEta_lt_one i)
  let r : ℕ → ℝ := fun i => ascrPointEta i * sigma i
  have hrpos (i : ℕ) : 0 < r i := mul_pos (ascrPointEta_pos i) (hsigma i)
  have hannulus (i : ℕ) : 3 * dist p (y i) / 4 ≤ dist p (x i) := by
    have ht := dist_triangle p (x i) (y i)
    rw [dist_comm (x i) (y i)] at ht
    linarith [hxR i]
  have hrscale (i : ℕ) : ((i : ℝ) + 2) * r i ≤ dist p (x i) / 3 := by
    have hcancel : ((i : ℝ) + 2) * r i = sigma i := by
      dsimp only [r, ascrPointEta]
      rw [← mul_assoc, mul_div_cancel₀ 1 (by positivity : (i : ℝ) + 2 ≠ 0), one_mul]
    rw [hcancel]
    linarith [hsigmaR i, hannulus i]
  have hrle (i : ℕ) : r i ≤ dist p (x i) / 6 := by
    nlinarith [hrscale i, hrpos i, Nat.cast_nonneg (α := ℝ) i]
  have hproduct : Tendsto (fun i => f (x i) * r i ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    have hlarge := (div_lt_iff₀ (sq_pos_of_pos (ascrPointEta_pos i))).mp (hy i).2
    have hweighted := mul_le_mul_of_nonneg_left (hweight i)
      (sq_nonneg (ascrPointEta i))
    dsimp only [r]
    nlinarith
  have hescape : Tendsto (fun i => dist p (x i)) atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    linarith [hannulus i, (hy i).1, Nat.cast_nonneg (α := ℝ) i]
  have hratio : Tendsto (fun i => dist p (x i) / r i) atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    apply (le_div_iff₀ (hrpos i)).mpr
    nlinarith [hrscale i, hrpos i, Nat.cast_nonneg (α := ℝ) i]
  obtain ⟨phi, hphi, hdisjoint⟩ := ascr_disjoint_subsequence p x r hescape hrle
  refine ⟨x ∘ phi, r ∘ phi, ascrPointEpsilon ∘ phi,
    (fun i => ⟨hrpos (phi i), hrle (phi i), hfx (phi i)⟩),
    (fun i => ascrPointEpsilon_pos (phi i)),
    (fun _ _ hij => ascrPointEpsilon_strictAnti (hphi hij)),
    ascrPointEpsilon_tendsto.comp hphi.tendsto_atTop, hdisjoint,
    hescape.comp hphi.tendsto_atTop, hproduct.comp hphi.tendsto_atTop,
    hratio.comp hphi.tendsto_atTop, ?_⟩
  intro i z hz
  calc
    f z ≤ ((1 - ascrPointEta (phi i))⁻¹) ^ 2 * f (x (phi i)) :=
      hcontrol (phi i) z hz
    _ = (1 + (ascrPointEpsilon ∘ phi) i) * f ((x ∘ phi) i) := by
      dsimp only [ascrPointEpsilon, Function.comp_def]
      ring

end ProperMetric

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_scalarAscrPointSelection
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) (hASCR : asymptoticScalarCurvatureRatio g p = ⊤) :
    let d := fun x y : M => (riemannianEDistOf (I := I) g x y).toReal
    ∃ (x : ℕ → M) (r eps : ℕ → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ d p (x i) / 6 ∧ 0 < metricScalarAt (I := I) g (x i)) ∧
      (∀ i, 0 < eps i) ∧ StrictAnti eps ∧ Tendsto eps atTop (𝓝 0) ∧
      Pairwise (fun i j =>
        Disjoint {z : M | riemannianEDistOf (I := I) g z (x i) < ENNReal.ofReal (r i)}
          {z : M | riemannianEDistOf (I := I) g z (x j) < ENNReal.ofReal (r j)}) ∧
      Tendsto (fun i => d p (x i)) atTop atTop ∧
      Tendsto (fun i => metricScalarAt (I := I) g (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => d p (x i) / r i) atTop atTop ∧
      ∀ i z, d z (x i) < r i →
        metricScalarAt (I := I) g z ≤ (1 + eps i) * metricScalarAt (I := I) g (x i) := by
  classical
  have hfar := (asymptoticScalarCurvatureRatio_eq_top_iff g p).mp hASCR
  by_cases hz : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hz
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology H := inferInstance
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    obtain ⟨y, hy, _⟩ := hfar 1 1 zero_lt_one zero_lt_one
    have hyp : y = p := Subsingleton.elim _ _
    rw [hyp, riemannianEDistOf_self, ENNReal.toReal_zero] at hy
    norm_num at hy
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hz⟩
    let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let _ : T3Space M := inferInstance
    let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let _ : CompleteSpace M := hcomplete.complete
    have hEnorm : IsMetricNorm (I := I) (M := M) g := fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
    let _ : MetricSpace M := riemMetricSpace (I := I) (M := M)
    let _ : ProperSpace M := properSpace_riemMetric (I := I) hcomplete.complete g hEnorm
    have hd (a b : M) : dist a b = (riemannianEDistOf (I := I) g a b).toReal := by
      rw [riemMetric_dist_eq (I := I),
        ← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    have hfarMetric : ∀ A D : ℝ, 0 < A → 0 < D → ∃ y : M,
        D ≤ dist p y ∧ A < metricScalarAt (I := I) g y * dist p y ^ 2 := by
      simpa only [hd] using hfar
    obtain ⟨x, r, eps, hr, heps, hanti, hlim, hdisjoint, hescape, hprod, hratio, hctrl⟩ :=
      exists_ascrPointSelection (metricScalar_smooth (I := I) g).continuous p hfarMetric
    refine ⟨x, r, eps, ?_, heps, hanti, hlim, ?_, ?_, hprod, ?_, ?_⟩
    · simpa only [hd] using hr
    · intro i j hij
      apply (hdisjoint hij).mono
      · intro z hzball
        rw [Metric.mem_ball, hd]
        exact ENNReal.toReal_lt_of_lt_ofReal hzball
      · intro z hzball
        rw [Metric.mem_ball, hd]
        exact ENNReal.toReal_lt_of_lt_ofReal hzball
    · simpa only [hd] using hescape
    · simpa only [hd] using hratio
    · simpa only [hd] using hctrl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
