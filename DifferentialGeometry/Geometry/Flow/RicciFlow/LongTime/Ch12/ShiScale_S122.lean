import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WBNLevel_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.CurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm
import DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm

set_option autoImplicit false

/-!
# CH12-S122 / G1: time-shift + scaling `parabolicSolution S' t t⁻¹`, `|Rm| ≤ 189 / r` from the Einstein defect,
Rm-tower ↔ Ric-tower bridge, and `↥(ball 2R)` is `σ`-compact.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology ENNReal
universe u
namespace GC.LongTime.Ch12

theorem sigmaCompact_ballU_S122 (H : FiniteVolumeHyperbolicModel.{u}) (R : ℝ) :
    SigmaCompactSpace (ballU_S98 H R) := by
  have : SecondCountableTopology H.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : SecondCountableTopology (ballU_S98 H R) := inferInstance
  have : LocallyCompactSpace (ballU_S98 H R) := (ballU_S98 H R).isOpen.locallyCompactSpace
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

section Rm

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ X] [T2Space X]

theorem abs_ricci_basis_le_of_quad_S122 (g : SmoothRiemannianMetric (𝓡 3) X) (x : X)
    {c : ℝ}
    (hq : ∀ V : TangentSpace (𝓡 3) x, |ricciTensor g x V V| ≤ c * g.inner x V V)
    {ι : Type} [DecidableEq ι] (e : Module.Basis ι ℝ (TangentSpace (𝓡 3) x))
    (hON : ∀ i j : ι, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) (i j : ι) :
    |ricciTensor g x (e i) (e j)| ≤ c := by
  by_cases hij : i = j
  · subst hij
    have h := hq (e i)
    simpa [hON] using h
  · have hsym := fun v w : TangentSpace (𝓡 3) x => ricciTensor_symm g x v w
    have hgs := fun v w : TangentSpace (𝓡 3) x => g.symm x v w
    have h1 := hq (e i + e j)
    have h2 := hq (e i - e j)
    have gij : g.inner x (e i) (e j) = 0 := by simp [hON, hij]
    have gji : g.inner x (e j) (e i) = 0 := by rw [← hgs, gij]
    have gii : g.inner x (e i) (e i) = 1 := by simp [hON]
    have gjj : g.inner x (e j) (e j) = 1 := by simp [hON]
    have gp : g.inner x (e i + e j) (e i + e j) = 2 := by
      simp [gij, gji, gii, gjj]; norm_num
    have gm : g.inner x (e i - e j) (e i - e j) = 2 := by
      simp [gij, gji, gii, gjj]; norm_num
    have rp : ricciTensor g x (e i + e j) (e i + e j) =
        ricciTensor g x (e i) (e i) + 2 * ricciTensor g x (e i) (e j) + ricciTensor g x (e j) (e j) := by
      simp only [map_add, add_apply]
      rw [hsym (e j) (e i)]; ring
    have rm : ricciTensor g x (e i - e j) (e i - e j) =
        ricciTensor g x (e i) (e i) - 2 * ricciTensor g x (e i) (e j) + ricciTensor g x (e j) (e j) := by
      simp only [map_sub, sub_apply]
      rw [hsym (e j) (e i)]; ring
    rw [gp] at h1
    rw [gm] at h2
    rw [rp] at h1
    rw [rm] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem sqrt_normSq0S_ricci_le_of_quad_S122 (g : SmoothRiemannianMetric (𝓡 3) X)
    (x : X) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ V : TangentSpace (𝓡 3) x, |ricciTensor g x V V| ≤ c * g.inner x V V) :
    Real.sqrt (normSq0S g x 2 (metricRicci g x)) ≤ 3 * c := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := 𝓡 3) g x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
  have hinv : MetricInverseInBasis (I := 𝓡 3) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have h := sqrt_normSq0S_le_card_of_component_bound (I := 𝓡 3) g x 2 basis hinv
    (metricRicci g x) c hc (fun slots => by
      rw [component0S_apply]
      have e1 : (fun a : Fin 2 => basis (slots a)) = vec2 (basis (slots 0)) (basis (slots 1)) := by
        funext a; fin_cases a <;> rfl
      rw [e1]
      change |metricRicciAt (I := 𝓡 3) g x (vec2 (basis (slots 0)) (basis (slots 1)))| ≤ c
      rw [metricRicciAt_apply_eq_ricciTensor]
      exact abs_ricci_basis_le_of_quad_S122 g x hq basis hON _ _)
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) : ℝ) = 9 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hdim]; norm_num
  rw [hcard] at h
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h9] at h

/-- generic-3-manifold form of `sqrt_normSq0S_rm_le_of_defect_S70`: `|Rm| ≤ 189 / t`. -/
theorem sqrt_normSq0S_rm_le_of_defect_S122 (g : SmoothRiemannianMetric (𝓡 3) X)
    (x : X) {t η : ℝ} (ht : 0 < t) (hη : η ≤ 1)
    (hdef : ∀ V : TangentSpace (𝓡 3) x,
      |2 * t * ricciTensor g x V V + g.inner x V V| ≤ η * g.inner x V V) :
    Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ 189 / t := by
  have hq : ∀ V : TangentSpace (𝓡 3) x, |ricciTensor g x V V| ≤ (1 / t) * g.inner x V V := by
    intro V
    have h1 := hdef V
    have hg : 0 ≤ g.inner x V V := metric_inner_self_nonneg _ _ _
    have h2 : |2 * t * ricciTensor g x V V| ≤ 2 * g.inner x V V := by
      have := abs_sub_abs_le_abs_sub (2 * t * ricciTensor g x V V) (-(g.inner x V V))
      rw [abs_neg, abs_of_nonneg hg] at this
      have h3 : |2 * t * ricciTensor g x V V - -g.inner x V V| =
          |2 * t * ricciTensor g x V V + g.inner x V V| := by
        rw [sub_neg_eq_add]
      nlinarith [h1, h3]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)] at h2
    rw [show 1 / t * g.inner x V V = g.inner x V V / t by ring, le_div_iff₀ ht]
    nlinarith [h2]
  have hRic := sqrt_normSq0S_ricci_le_of_quad_S122 g x (by positivity) hq
  have hthree := sqrt_normSq_metricRm04_le_ricci_three g x finrank_euclideanSpace_fin
  calc Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ 63 * (3 * (1 / t)) := hthree.trans (by linarith)
    _ = 189 / t := by ring

end Rm

section Scale

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ X] [T2Space X]

theorem nablaK_scaled_S122 {D : RealTimeInterval} (S' : SolutionOn (I := 𝓡 3) (M := X) D)
    {t : ℝ} (ht : 0 < t) (hz : t ∈ D.carrier) (k : ℕ) (τ : ℝ) (y : X) :
    nablaKRm04NormSqIntrinsic (parabolicSolution (I := 𝓡 3) S' t t⁻¹ (inv_pos.2 ht) hz) k τ y =
      t ^ (2 + k) * nablaKRm04NormSqIntrinsic S' k (t + τ * t) y := by
  rw [parabolicNablaKRmNormSq, inv_inv]
  congr 2
  unfold parabolicTime
  rw [div_inv_eq_mul]

theorem nablaK_zero_eq_S122 {D : RealTimeInterval} (S' : SolutionOn (I := 𝓡 3) (M := X) D)
    (r : ℝ) (y : X) :
    nablaKRm04NormSqIntrinsic S' 0 r y = normSq0S (S'.base.metric r) y 4 (metricRm04 (S'.base.metric r) y) := by
  rw [← curvNormSq_eq]
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]
  rfl

theorem rm_scaled_le_S122 {D : RealTimeInterval} (S' : SolutionOn (I := 𝓡 3) (M := X) D)
    {t η : ℝ} (ht : 0 < t) (hη : η ≤ 1) (hz : t ∈ D.carrier)
    (hdef : ∀ r ∈ Icc t (2 * t), ∀ (y : X) (V : TangentSpace (𝓡 3) y),
      |2 * r * ricciTensor (S'.base.metric r) y V V + (S'.base.metric r).inner y V V| ≤
        η * (S'.base.metric r).inner y V V)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (y : X) :
    nablaKRm04NormSqIntrinsic (parabolicSolution (I := 𝓡 3) S' t t⁻¹ (inv_pos.2 ht) hz) 0 τ y ≤
      189 ^ 2 := by
  rw [nablaK_scaled_S122 S' ht hz 0 τ y, nablaK_zero_eq_S122]
  have hr : t + τ * t ∈ Icc t (2 * t) :=
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hr0 : 0 < t + τ * t := by nlinarith [hτ.1]
  have h := sqrt_normSq0S_rm_le_of_defect_S122 (S'.base.metric (t + τ * t)) y hr0 hη
    (hdef _ hr y)
  have hsq := (Real.sqrt_le_iff.mp h).2
  have hle : t ≤ t + τ * t := hr.1
  have h1 : t ^ 2 * (189 / (t + τ * t)) ^ 2 ≤ 189 ^ 2 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [mul_div_assoc', div_le_iff₀ hr0]
    nlinarith
  calc t ^ (2 + 0) * normSq0S (S'.base.metric (t + τ * t)) y 4 (metricRm04 (S'.base.metric (t + τ * t)) y)
      ≤ t ^ (2 + 0) * (189 / (t + τ * t)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ 189 ^ 2 := by simpa using h1

theorem ricTower_normSq_le_S122 (g : SmoothRiemannianMetric (𝓡 3) X) (s : ℕ) (y : X) :
    normSq0S g y (2 + s) (ricCovTower g g s y) ≤ 3 ^ (s + 4) * curvDerivNormSq s g y := by
  have h := sqrt_normSq0S_ricCovTower_le_curvDerivNorm g s y
  have e : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [e, show 2 + s + 2 = s + 4 by omega] at h
  unfold curvDerivNorm at h
  rw [← Real.sqrt_mul (by positivity)] at h
  have hc : 0 ≤ curvDerivNormSq s g y := normSq0S_nonneg _ _ _ _
  exact (Real.sqrt_le_sqrt_iff (by positivity)).1 h

theorem ricTower_le_of_scaled_S122 {D : RealTimeInterval} (S' : SolutionOn (I := 𝓡 3) (M := X) D)
    {t : ℝ} (ht : 0 < t) (hz : t ∈ D.carrier) (s : ℕ) (B : ℝ) (y : X)
    (hB : ∀ τ ∈ Icc (0 : ℝ) 1,
      nablaKRm04NormSqIntrinsic (parabolicSolution (I := 𝓡 3) S' t t⁻¹ (inv_pos.2 ht) hz) s τ y ≤ B)
    {r : ℝ} (hr : r ∈ Icc t (2 * t)) :
    normSq0S (S'.base.metric r) y (2 + s)
        (ricCovTower (S'.base.metric r) (S'.base.metric r) s y) * r ^ (2 + s) ≤
      3 ^ (s + 4) * 2 ^ (2 + s) * B := by
  have hr0 : 0 < r := ht.trans_le hr.1
  have hτ : (r - t) / t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.2 hr.1) ht.le, (div_le_one ht).2 (by linarith [hr.2])⟩
  have hrt : t + (r - t) / t * t = r := by field_simp; ring
  have h1 := hB _ hτ
  rw [nablaK_scaled_S122 S' ht hz s _ y, hrt] at h1
  have hc : nablaKRm04NormSqIntrinsic S' s r y = curvDerivNormSq s (S'.base.metric r) y :=
    (curvNormSq_eq S' s r y).symm
  have hn : 0 ≤ nablaKRm04NormSqIntrinsic S' s r y := nablaKRm04NormSqIntrinsic_nonneg S' s r y
  have hrp : r ^ (2 + s) ≤ 2 ^ (2 + s) * t ^ (2 + s) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hr0.le (by linarith [hr.2]) _
  calc normSq0S (S'.base.metric r) y (2 + s)
        (ricCovTower (S'.base.metric r) (S'.base.metric r) s y) * r ^ (2 + s)
      ≤ 3 ^ (s + 4) * nablaKRm04NormSqIntrinsic S' s r y * r ^ (2 + s) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hc]; exact ricTower_normSq_le_S122 _ s y
    _ ≤ 3 ^ (s + 4) * nablaKRm04NormSqIntrinsic S' s r y * (2 ^ (2 + s) * t ^ (2 + s)) :=
        mul_le_mul_of_nonneg_left hrp (by positivity)
    _ = 3 ^ (s + 4) * 2 ^ (2 + s) * (t ^ (2 + s) * nablaKRm04NormSqIntrinsic S' s r y) := by ring
    _ ≤ 3 ^ (s + 4) * 2 ^ (2 + s) * B := mul_le_mul_of_nonneg_left h1 (by positivity)

end Scale

end GC.LongTime.Ch12
