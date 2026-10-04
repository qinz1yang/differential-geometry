import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import DifferentialGeometry.Topology.Covering.SimplyConnected

/-!
# Global inverse function theorem with uniform constants (Hadamard–Lévy type)

Let `φ : E → F` have an invertible derivative `φ' z` at every point, with a uniform bound
`‖(φ' z)⁻¹‖ ≤ K` and `z ↦ φ' z` uniformly continuous. Then every point has a ball on which
`φ` is injective and whose image contains a ball of uniform radius. From this we build an even
covering of every point (`IsOpen.trivializationDiscrete`), so `φ` is a covering map; if `F` is
simply connected and `E` connected, `φ` is a homeomorphism (`IsCoveringMap.bijective_sc`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section UniformInverse

variable {φ : E → F} {φ' : E → E ≃L[ℝ] F} {K δ : ℝ}

/-- On a ball where the derivative stays `c`-close to its value at the center, `φ`
approximates that value with constant `c`. -/
theorem approximatesLinearOn_ball_of_fderiv_near
    (hφ : ∀ z, HasFDerivAt φ (φ' z : E →L[ℝ] F) z) {c : ℝ≥0}
    (hδ : ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ ≤ c) (z₀ : E) :
    ApproximatesLinearOn φ (φ' z₀ : E →L[ℝ] F) (ball z₀ δ) c := by
  intro x hx y hy
  exact (convex_ball z₀ δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun w _ => (hφ w).hasFDerivWithinAt) (fun w hw => hδ w z₀ hw) hy hx

/-- The nonlinear right inverse `(φ' z)⁻¹` with the uniform bound `K`. -/
def uniformRightInverse (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K) (z : E) :
    (φ' z : E →L[ℝ] F).NonlinearRightInverse where
  toFun := (φ' z).symm
  nnnorm := K.toNNReal
  bound' y := by
    refine (((φ' z).symm : F →L[ℝ] E).le_opNorm y).trans ?_
    exact mul_le_mul_of_nonneg_right ((hK z).trans (Real.le_coe_toNNReal K)) (norm_nonneg y)
  right_inv' y := (φ' z).apply_symm_apply y

theorem norm_le_of_uniform_inverse (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K)
    (z : E) (v : E) : ‖v‖ ≤ K * ‖(φ' z : E →L[ℝ] F) v‖ := by
  have h := ((φ' z).symm : F →L[ℝ] E).le_opNorm ((φ' z) v)
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _))

/-- Uniform injectivity estimate: on every ball of radius `δ`,
`‖x - y‖ ≤ 2K ‖φ x - φ y‖`. -/
theorem norm_sub_le_of_uniform_fderiv (hφ : ∀ z, HasFDerivAt φ (φ' z : E →L[ℝ] F) z)
    (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K) (hKpos : 0 < K)
    (hδ : ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ ≤ (2 * K)⁻¹) (z₀ : E)
    {x y : E} (hx : x ∈ ball z₀ δ) (hy : y ∈ ball z₀ δ) :
    ‖x - y‖ ≤ 2 * K * ‖φ x - φ y‖ := by
  have happ := approximatesLinearOn_ball_of_fderiv_near hφ (c := ((2 * K)⁻¹).toNNReal)
    (fun z z' h => (hδ z z' h).trans (Real.le_coe_toNNReal _)) z₀ x hx y hy
  rw [Real.coe_toNNReal _ (by positivity)] at happ
  have h1 := norm_le_of_uniform_inverse hK z₀ (x - y)
  have h2 : ‖(φ' z₀ : E →L[ℝ] F) (x - y)‖ ≤ ‖φ x - φ y‖ + (2 * K)⁻¹ * ‖x - y‖ := by
    have := norm_sub_norm_le ((φ' z₀ : E →L[ℝ] F) (x - y)) (φ x - φ y)
    rw [norm_sub_rev ((φ' z₀ : E →L[ℝ] F) (x - y))] at this
    linarith
  have h3 : K * ((2 * K)⁻¹ * ‖x - y‖) = ‖x - y‖ / 2 := by field_simp
  nlinarith

theorem injOn_ball_of_uniform_fderiv (hφ : ∀ z, HasFDerivAt φ (φ' z : E →L[ℝ] F) z)
    (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K) (hKpos : 0 < K)
    (hδ : ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ ≤ (2 * K)⁻¹) (z₀ : E) :
    InjOn φ (ball z₀ δ) := by
  intro x hx y hy hxy
  have h := norm_sub_le_of_uniform_fderiv hφ hK hKpos hδ z₀ hx hy
  rw [hxy, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- Uniform local surjectivity: the image of `closedBall z₀ ε` (with `ε < δ`) contains the
closed ball of radius `ε / (2K)` around `φ z₀`. -/
theorem surjOn_closedBall_of_uniform_fderiv [CompleteSpace E]
    (hφ : ∀ z, HasFDerivAt φ (φ' z : E →L[ℝ] F) z)
    (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K) (hKpos : 0 < K)
    (hδ : ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ ≤ (2 * K)⁻¹) (z₀ : E)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεδ : ε < δ) :
    SurjOn φ (closedBall z₀ ε) (closedBall (φ z₀) (ε / (2 * K))) := by
  have happ := approximatesLinearOn_ball_of_fderiv_near hφ (c := ((2 * K)⁻¹).toNNReal)
    (fun z z' h => (hδ z z' h).trans (Real.le_coe_toNNReal _)) z₀
  have hs := happ.surjOn_closedBall_of_nonlinearRightInverse (uniformRightInverse hK z₀) hε0
    (closedBall_subset_ball hεδ)
  have hrad : (((uniformRightInverse hK z₀).nnnorm : ℝ)⁻¹ - (((2 * K)⁻¹).toNNReal : ℝ)) * ε =
      ε / (2 * K) := by
    change ((K.toNNReal : ℝ)⁻¹ - (((2 * K)⁻¹).toNNReal : ℝ)) * ε = ε / (2 * K)
    rw [Real.coe_toNNReal _ hKpos.le, Real.coe_toNNReal _ (by positivity)]
    field_simp
    ring
  rwa [hrad] at hs

/-- **Uniform inverse function theorem ⇒ covering map.** -/
theorem isCoveringMap_of_uniform_fderiv [CompleteSpace E]
    (hφ : ∀ z, HasFDerivAt φ (φ' z : E →L[ℝ] F) z)
    (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K) (hKpos : 0 < K)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ < ε) :
    IsCoveringMap φ := by
  obtain ⟨δ, hδpos, hδ'⟩ := hunif (2 * K)⁻¹ (by positivity)
  have hδ : ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ ≤ (2 * K)⁻¹ :=
    fun z z' h => (hδ' z z' h).le
  set r : ℝ := δ / 5 with hr
  have hrpos : 0 < r := by positivity
  set ρ : ℝ := r / (2 * K) with hρ
  have hρpos : 0 < ρ := by positivity
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr fun z => (hφ z).continuousAt
  have hinj := injOn_ball_of_uniform_fderiv hφ hK hKpos hδ
  have hsurj : ∀ z₀ {ε : ℝ}, 0 ≤ ε → ε < δ →
      SurjOn φ (closedBall z₀ ε) (closedBall (φ z₀) (ε / (2 * K))) :=
    fun z₀ _ h0 h1 => surjOn_closedBall_of_uniform_fderiv hφ hK hKpos hδ z₀ h0 h1
  -- `φ` is open
  have hopen : IsOpenMap φ := by
    intro W hW
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hzW, rfl⟩
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW z hzW
    set ε' := min (ε / 2) (δ / 2)
    have hε'0 : 0 < ε' := by positivity
    refine Filter.mem_of_superset (closedBall_mem_nhds _ (by positivity : 0 < ε' / (2 * K))) ?_
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hsurj z hε'0.le (by
      have : ε' ≤ δ / 2 := min_le_right _ _
      linarith) hw
    refine ⟨y, hεW ?_, rfl⟩
    have : ε' ≤ ε / 2 := min_le_left _ _
    exact closedBall_subset_ball (by linarith) hy
  -- the range is closed
  have hclosed : IsClosed (range φ) := by
    refine isClosed_iff_clusterPt.mpr fun x hx => ?_
    obtain ⟨_, hw, ⟨w, rfl⟩⟩ := (clusterPt_principal_iff.mp hx) (ball x ρ) (ball_mem_nhds x hρpos)
    obtain ⟨y, -, hy⟩ := hsurj w hrpos.le (by rw [hr]; linarith)
      (show x ∈ closedBall (φ w) ρ from by
        rw [mem_closedBall, dist_comm]; exact (mem_ball.mp hw).le)
    exact ⟨y, hy⟩
  -- discreteness of fibres
  have hdisc : ∀ x : F, DiscreteTopology (φ ⁻¹' {x}) := by
    intro x
    refine discreteTopology_iff_isOpen_singleton.mpr fun y => ?_
    refine isOpen_induced_iff.mpr ⟨ball y.1 δ, isOpen_ball, ?_⟩
    ext y'
    simp only [mem_preimage, mem_ball, mem_singleton_iff]
    constructor
    · intro h
      apply Subtype.ext
      have h1 : φ y'.1 = x := y'.2
      have h2 : φ y.1 = x := y.2
      exact hinj y.1 h (mem_ball_self hδpos) (h1.trans h2.symm)
    · rintro rfl
      exact mem_ball_self hδpos
  refine IsCoveringMap.mk' φ (fun x => ↥(φ ⁻¹' {x})) (fun x hx => ?_) hclosed
  let y₀ : E := hx.choose
  have hy₀ : φ y₀ = x := hx.choose_spec
  have hne : Nonempty (φ ⁻¹' {x}) := ⟨⟨y₀, hy₀⟩⟩
  have hne' : Nonempty (F → E) := ⟨fun _ => y₀⟩
  let U : φ ⁻¹' {x} → Set E := fun y => ball y.1 (2 * r) ∩ φ ⁻¹' ball x ρ
  have hUopen : ∀ y, IsOpen (U y) := fun y => isOpen_ball.inter (isOpen_ball.preimage hcont)
  have hUsurj : ∀ y, SurjOn φ (U y) (ball x ρ) := by
    intro y w hw
    have hyx : φ y.1 = x := y.2
    obtain ⟨z, hz, rfl⟩ := hsurj y.1 hrpos.le (by rw [hr]; linarith)
      (show w ∈ closedBall (φ y.1) ρ by rw [hyx]; exact ball_subset_closedBall hw)
    exact ⟨z, ⟨closedBall_subset_ball (by linarith) hz, hw⟩, rfl⟩
  have hUinj : ∀ y, InjOn φ (U y) := fun y =>
    (hinj y.1).mono fun w hw => ball_subset_ball (by rw [hr]; linarith) hw.1
  refine ⟨IsOpen.trivializationDiscrete (ι := φ ⁻¹' {x}) U (ball x ρ) isOpen_ball
    (fun y W hWV => ⟨fun hW => hW.preimage hcont |>.inter (hUopen y), fun hW => ?_⟩) hUinj hUsurj
    ?_ ?_, ?_⟩
  · have himage : φ '' (φ ⁻¹' W ∩ U y) = W := by
      refine Subset.antisymm (fun _ ⟨z, hz, h⟩ => h ▸ hz.1) fun w hw => ?_
      obtain ⟨z, hz, rfl⟩ := hUsurj y (hWV hw)
      exact ⟨z, ⟨hw, hz⟩, rfl⟩
    rw [← himage]
    exact hopen _ hW
  · intro y y' hyy'
    refine Set.disjoint_left.mpr fun w hw hw' => hyy' (Subtype.ext ?_)
    have hd : dist y'.1 y.1 < δ := by
      have h1 := mem_ball.mp hw.1
      have h2 := mem_ball.mp hw'.1
      calc dist y'.1 y.1 ≤ dist y'.1 w + dist w y.1 := dist_triangle _ _ _
        _ < 2 * r + 2 * r := by rw [dist_comm] at h2; linarith
        _ < δ := by rw [hr]; linarith
    have h1 : φ y.1 = x := y.2
    have h2 : φ y'.1 = x := y'.2
    exact hinj y.1 (mem_ball_self hδpos) (mem_ball.mpr hd) (h1.trans h2.symm)
  · intro w hw
    obtain ⟨z, hz, hzx⟩ := hsurj w hrpos.le (by rw [hr]; linarith)
      (show x ∈ closedBall (φ w) ρ by
        rw [mem_closedBall, dist_comm]; exact (mem_ball.mp hw).le)
    refine mem_iUnion.mpr ⟨⟨z, hzx⟩, ?_, hw⟩
    rw [mem_ball, dist_comm]
    exact lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)
  · exact mem_ball_self hρpos

/-- **Hadamard–Lévy, uniform form.** A map with invertible derivative, uniformly bounded inverse
derivative and uniformly continuous derivative, into a simply connected space, is a
homeomorphism. -/
theorem bijective_of_uniform_fderiv [CompleteSpace E]
    [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
    (hφ : ∀ z, HasFDerivAt φ (φ' z : E →L[ℝ] F) z)
    (hK : ∀ z, ‖((φ' z).symm : F →L[ℝ] E)‖ ≤ K) (hKpos : 0 < K)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ z z', dist z z' < δ → ‖(φ' z : E →L[ℝ] F) - φ' z'‖ < ε) :
    Bijective φ :=
  (isCoveringMap_of_uniform_fderiv hφ hK hKpos hunif).bijective_sc

end UniformInverse

end DifferentialGeometry.Analysis
