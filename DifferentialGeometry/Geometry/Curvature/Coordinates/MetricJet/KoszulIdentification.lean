import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientPullback
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientField
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Geometry.Connection.ConnectionForm.CurvatureOperator

set_option autoImplicit false

noncomputable section

open scoped Topology
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

namespace DifferentialGeometry.Analysis

private theorem clm_apply_eq_basis_sum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →L[ℝ] F) (X : E) :
    f X = ∑ i, (chartModelBasis E).repr X i • f (chartModelBasis E i) := by
  calc f X = f (∑ i, (chartModelBasis E).repr X i • chartModelBasis E i) := by
        rw [(chartModelBasis E).sum_repr X]
    _ = ∑ i, (chartModelBasis E).repr X i • f (chartModelBasis E i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul f _ _

private theorem clm_expand_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) (W : E) :
    f W = ∑ l, (chartModelBasis E).repr W l * f (chartModelBasis E l) :=
  (clm_apply_eq_basis_sum f W).trans (Finset.sum_congr rfl fun _ _ => smul_eq_mul _ _)

private theorem clm_expand_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] E →L[ℝ] ℝ) (Z W : E) :
    f Z W = ∑ k, ∑ l, (chartModelBasis E).repr Z k * (chartModelBasis E).repr W l *
      f (chartModelBasis E k) (chartModelBasis E l) := by
  rw [clm_apply_eq_basis_sum f Z, _root_.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [_root_.smul_apply (f (chartModelBasis E k)) ((chartModelBasis E).repr Z k) W,
    smul_eq_mul, clm_expand_one (f (chartModelBasis E k)) W, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm

private theorem clm_expand_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (Y Z W : E) :
    f Y Z W = ∑ j, ∑ k, ∑ l, (chartModelBasis E).repr Y j * (chartModelBasis E).repr Z k *
      (chartModelBasis E).repr W l *
        f (chartModelBasis E j) (chartModelBasis E k) (chartModelBasis E l) := by
  rw [clm_apply_eq_basis_sum f Y, _root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.smul_apply (f (chartModelBasis E j)) ((chartModelBasis E).repr Y j) Z,
    _root_.smul_apply (f (chartModelBasis E j) Z) ((chartModelBasis E).repr Y j) W, smul_eq_mul,
    clm_expand_two (f (chartModelBasis E j)) Z W, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

private theorem clm_expand_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (X Y Z W : E) :
    f X Y Z W = ∑ i, ∑ j, ∑ k, ∑ l, (chartModelBasis E).repr X i * (chartModelBasis E).repr Y j *
      (chartModelBasis E).repr Z k * (chartModelBasis E).repr W l *
        f (chartModelBasis E i) (chartModelBasis E j) (chartModelBasis E k)
          (chartModelBasis E l) := by
  rw [clm_apply_eq_basis_sum f X, _root_.sum_apply, _root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.smul_apply (f (chartModelBasis E i)) ((chartModelBasis E).repr X i) Y,
    _root_.smul_apply (f (chartModelBasis E i) Y) ((chartModelBasis E).repr X i) Z,
    _root_.smul_apply (f (chartModelBasis E i) Y Z) ((chartModelBasis E).repr X i) W,
    smul_eq_mul, clm_expand_three (f (chartModelBasis E i)) Y Z W, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

private theorem apply_connectionFormCurvature_eq_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (x X Y Z W : E) :
    B (Geometry.Connection.connectionFormCurvature Γ x X Y Z) W =
      ∑ i, ∑ j, ∑ k, ∑ l, (chartModelBasis E).repr X i * (chartModelBasis E).repr Y j *
        (chartModelBasis E).repr Z k * (chartModelBasis E).repr W l *
          B (Geometry.Connection.connectionFormCurvature Γ x (chartModelBasis E i)
            (chartModelBasis E j) (chartModelBasis E k)) (chartModelBasis E l) :=
  clm_expand_four (((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E →L[ℝ] ℝ))
    (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B)).comp
      (Geometry.Connection.connectionFormCurvatureCLM Γ x)) X Y Z W

private theorem lower_connectionFormCurvature {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E) (x a c d t : E) :
    B (Geometry.Connection.connectionFormCurvature Γ x a c d) t =
      B (fderiv ℝ Γ x a c d) t - B (fderiv ℝ Γ x c a d) t + B (Γ x a (Γ x c d)) t -
        B (Γ x c (Γ x a d)) t := by
  unfold Geometry.Connection.connectionFormCurvature
  rw [map_sub B, map_add B, map_sub B,
    _root_.sub_apply (B (fderiv ℝ Γ x a c d) - B (fderiv ℝ Γ x c a d) + B (Γ x a (Γ x c d)))
      (B (Γ x c (Γ x a d))) t,
    _root_.add_apply (B (fderiv ℝ Γ x a c d) - B (fderiv ℝ Γ x c a d)) (B (Γ x a (Γ x c d))) t,
    _root_.sub_apply (B (fderiv ℝ Γ x a c d)) (B (fderiv ℝ Γ x c a d)) t]

private theorem clm_eq_of_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {φ ψ : E →L[ℝ] ℝ}
    (h : ∀ q, φ (chartModelBasis E q) = ψ (chartModelBasis E q)) : φ = ψ := by
  refine ContinuousLinearMap.ext fun t => ?_
  rw [clm_apply_eq_basis_sum φ t, clm_apply_eq_basis_sum ψ t]
  exact Finset.sum_congr rfl fun q _ => by rw [h q]

private theorem bilin_sum_smul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {ι : Type*} (s : Finset ι) (α : ι → ℝ) (v : ι → E) (t : E) :
    B (∑ r ∈ s, α r • v r) t = ∑ r ∈ s, α r * B (v r) t := by
  rw [map_sum, _root_.sum_apply]
  exact Finset.sum_congr rfl fun r _ => by
    rw [map_smul, _root_.smul_apply (B (v r)) (α r) t, smul_eq_mul]

private theorem gram_mul_inv {n : ℕ} (g : Fin n → Fin n → ℝ) (hp : IsUnit (Matrix.of g).det)
    (q l : Fin n) : ∑ k, g q k * (Matrix.of g)⁻¹ k l = if q = l then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv (Matrix.of g) hp) q) l
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

private theorem sum_lower_aux {n : ℕ} (g inv : Fin n → Fin n → ℝ)
    (hgi : ∀ q l, ∑ k, g q k * inv k l = if q = l then 1 else 0) (B : Fin n → ℝ) (q : Fin n) :
    ∑ l, (∑ k, g q k * inv k l) * B l = B q := by
  calc ∑ l, (∑ k, g q k * inv k l) * B l = ∑ l, if q = l then B l else 0 :=
        Finset.sum_congr rfl fun l _ => by rw [hgi q l, boole_mul]
    _ = B q := Finset.sum_ite_eq_of_mem Finset.univ q B (Finset.mem_univ q)

private theorem sum_mul_inv_aux {n : ℕ} (g inv : Fin n → Fin n → ℝ)
    (hgi : ∀ q l, ∑ k, g q k * inv k l = if q = l then 1 else 0) (U : Fin n → ℝ) (q : Fin n) :
    ∑ k, g q k * ∑ a, inv k a * U a = U q := by
  calc ∑ k, g q k * ∑ a, inv k a * U a = ∑ k, ∑ a, g q k * inv k a * U a :=
        Finset.sum_congr rfl fun k _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => (mul_assoc _ _ _).symm
    _ = ∑ a, ∑ k, g q k * inv k a * U a := Finset.sum_comm
    _ = ∑ a, (∑ k, g q k * inv k a) * U a :=
        Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
    _ = U q := sum_lower_aux g inv hgi U q

private theorem jet_lower_aux {n : ℕ} (g inv : Fin n → Fin n → ℝ)
    (hgi : ∀ q l, ∑ k, g q k * inv k l = if q = l then 1 else 0)
    (hgs : ∀ k q, g k q = g q k) (B : Fin n → ℝ) (q : Fin n) :
    ∑ k, (1 / 2 : ℝ) * (∑ l, inv k l * B l) * g k q = (1 / 2 : ℝ) * B q := by
  calc ∑ k, (1 / 2 : ℝ) * (∑ l, inv k l * B l) * g k q =
        ∑ k, (1 / 2 : ℝ) * (g q k * ∑ l, inv k l * B l) :=
        Finset.sum_congr rfl fun k _ => by
          rw [hgs k q]
          ring
    _ = (1 / 2 : ℝ) * ∑ k, g q k * ∑ l, inv k l * B l := (Finset.mul_sum _ _ _).symm
    _ = (1 / 2 : ℝ) * B q := by rw [sum_mul_inv_aux g inv hgi B q]

private theorem jet_deriv_lower_aux {n : ℕ} (g inv d : Fin n → Fin n → ℝ)
    (hgi : ∀ q l, ∑ k, g q k * inv k l = if q = l then 1 else 0) (B dB : Fin n → ℝ)
    (q : Fin n) :
    ∑ k, g q k * ((1 / 2 : ℝ) *
        ∑ l, ((-∑ a, ∑ c, inv k a * inv c l * d a c) * B l + inv k l * dB l)) =
      (1 / 2 : ℝ) * dB q - ∑ c, d q c * ((1 / 2 : ℝ) * ∑ l, inv c l * B l) := by
  have hN : ∀ l, ∑ k, g q k * (-∑ a, ∑ c, inv k a * inv c l * d a c) =
      -∑ c, inv c l * d q c := by
    intro l
    have h1 : ∀ k, g q k * (-∑ a, ∑ c, inv k a * inv c l * d a c) =
        -(g q k * ∑ a, inv k a * ∑ c, inv c l * d a c) := by
      intro k
      rw [mul_neg]
      refine congrArg (fun z => -(g q k * z)) (Finset.sum_congr rfl fun a _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => mul_assoc _ _ _
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (sum_mul_inv_aux g inv hgi (fun a => ∑ c, inv c l * d a c) q)
  have hsplit : ∀ l, ∑ k, g q k * ((-∑ a, ∑ c, inv k a * inv c l * d a c) * B l +
      inv k l * dB l) = (-∑ c, inv c l * d q c) * B l + (∑ k, g q k * inv k l) * dB l := by
    intro l
    rw [← hN l, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hB : ∑ l, (-∑ c, inv c l * d q c) * B l = -∑ c, d q c * ∑ l, inv c l * B l := by
    calc ∑ l, (-∑ c, inv c l * d q c) * B l = -∑ l, ∑ c, d q c * (inv c l * B l) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [neg_mul, Finset.sum_mul]
          exact congrArg Neg.neg (Finset.sum_congr rfl fun c _ => by ring)
      _ = -∑ c, ∑ l, d q c * (inv c l * B l) := by rw [Finset.sum_comm]
      _ = -∑ c, d q c * ∑ l, inv c l * B l := by
          refine congrArg Neg.neg (Finset.sum_congr rfl fun c _ => ?_)
          rw [Finset.mul_sum]
  have hhalf : ∑ c, d q c * ((1 / 2 : ℝ) * ∑ l, inv c l * B l) =
      (1 / 2 : ℝ) * ∑ c, d q c * ∑ l, inv c l * B l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => mul_left_comm _ _ _
  calc ∑ k, g q k * ((1 / 2 : ℝ) *
          ∑ l, ((-∑ a, ∑ c, inv k a * inv c l * d a c) * B l + inv k l * dB l)) =
        ∑ k, (1 / 2 : ℝ) * ∑ l, g q k *
          ((-∑ a, ∑ c, inv k a * inv c l * d a c) * B l + inv k l * dB l) :=
        Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ k, ∑ l, g q k *
          ((-∑ a, ∑ c, inv k a * inv c l * d a c) * B l + inv k l * dB l) :=
        (Finset.mul_sum _ _ _).symm
    _ = (1 / 2 : ℝ) * ∑ l, ∑ k, g q k *
          ((-∑ a, ∑ c, inv k a * inv c l * d a c) * B l + inv k l * dB l) := by
        rw [Finset.sum_comm]
    _ = (1 / 2 : ℝ) * ∑ l, ((-∑ c, inv c l * d q c) * B l + (∑ k, g q k * inv k l) * dB l) :=
        congrArg (fun z => (1 / 2 : ℝ) * z) (Finset.sum_congr rfl fun l _ => hsplit l)
    _ = (1 / 2 : ℝ) * (-∑ c, d q c * ∑ l, inv c l * B l + dB q) := by
        rw [Finset.sum_add_distrib, hB, sum_lower_aux g inv hgi dB q]
    _ = (1 / 2 : ℝ) * dB q - ∑ c, d q c * ((1 / 2 : ℝ) * ∑ l, inv c l * B l) := by
        rw [hhalf]
        ring

private theorem isUnit_det_gram {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hco : IsCoercive (b w)) : IsUnit (Matrix.of (coefficientGram b w)).det := by
  obtain ⟨C, hC, hCu⟩ := hco
  have hpos : ∀ u : E, u ≠ 0 → 0 < b w u u := fun u hu =>
    lt_of_lt_of_le (mul_pos (mul_pos hC (norm_pos_iff.mpr hu)) (norm_pos_iff.mpr hu)) (hCu u)
  refine Ne.isUnit fun hdet0 => ?_
  obtain ⟨c, hc0, hcv⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of (coefficientGram b w))).2 hdet0
  set v : E := ∑ i, c i • chartModelBasis E i with hv
  have hrow0 : ∀ i, (b w (chartModelBasis E i)) v = 0 := by
    intro i
    have h1 : (b w (chartModelBasis E i)) v =
        ∑ j, Matrix.of (coefficientGram b w) i j * c j := by
      rw [hv, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      simp only [coefficientGram_apply, Matrix.of_apply]
    have h2 : (∑ j, Matrix.of (coefficientGram b w) i j * c j) = 0 := congrFun hcv i
    rw [h1, h2]
  have hinner : b w v v = 0 := by
    have hout : (b w) v = ∑ i, c i • ((b w) (chartModelBasis E i)) := by
      rw [hv, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    calc b w v v = (∑ i, c i • ((b w) (chartModelBasis E i))) v := by rw [hout]
      _ = ∑ i, c i • ((b w (chartModelBasis E i)) v) := by
          rw [_root_.sum_apply]
          exact Finset.sum_congr rfl fun i _ => by rw [_root_.smul_apply]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hrow0 i, smul_zero]
  have hvne : v ≠ 0 := by
    intro hv0
    apply hc0
    have hz : ∑ i, c i • chartModelBasis E i = 0 := hv.symm.trans hv0
    have hall := Fintype.linearIndependent_iff.1 (chartModelBasis E).linearIndependent c hz
    funext i
    exact hall i
  exact absurd hinner (ne_of_gt (hpos v hvne))

private def symmDefect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u) -
    (ContinuousLinearMap.apply ℝ ℝ u).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)

private theorem symmDefect_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (B : E →L[ℝ] E →L[ℝ] ℝ) : symmDefect u v B = B u v - B v u :=
  rfl

private theorem symmDefect_comp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v w : E) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    (symmDefect u v).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) w) D =
      D w u v - D w v u :=
  rfl

theorem clm_apply_fderiv_eq_zero {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (h : ∀ᶠ y in 𝓝 x, L (f y) = 0) (w : E) : L (fderiv ℝ f x w) = 0 := by
  have h1 : HasFDerivAt (fun y => L (f y)) (L.comp (fderiv ℝ f x)) x :=
    L.hasFDerivAt.comp x hf.hasFDerivAt
  have h2 : HasFDerivAt (fun y => L (f y)) (0 : E →L[ℝ] G) x :=
    (hasFDerivAt_const (0 : G) x).congr_of_eventuallyEq h
  exact DFunLike.congr_fun (h1.unique h2) w

theorem eventually_fderiv_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) :
    ∀ᶠ y in 𝓝 x, ∀ w u v : E, fderiv ℝ b y w u v = fderiv ℝ b y w v u := by
  filter_upwards [hbd, hsymm.eventually_nhds] with y hy hy' w u v
  have h : symmDefect u v (fderiv ℝ b y w) = 0 :=
    clm_apply_fderiv_eq_zero (symmDefect u v) hy
      (hy'.mono fun z hz => (symmDefect_apply u v (b z)).trans (sub_eq_zero.mpr (hz u v))) w
  exact sub_eq_zero.mp ((symmDefect_apply u v (fderiv ℝ b y w)).symm.trans h)

theorem fderiv_fderiv_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y)
    (hb2 : DifferentiableAt ℝ (fderiv ℝ b) x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (m w u v : E) :
    fderiv ℝ (fderiv ℝ b) x m w u v = fderiv ℝ (fderiv ℝ b) x m w v u := by
  have h := clm_apply_fderiv_eq_zero
    ((symmDefect u v).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) w)) hb2
    ((eventually_fderiv_symm hbd hsymm).mono fun y hy =>
      (symmDefect_comp_apply u v w (fderiv ℝ b y)).trans (sub_eq_zero.mpr (hy w u v))) m
  exact sub_eq_zero.mp ((symmDefect_comp_apply u v w (fderiv ℝ (fderiv ℝ b) x m)).symm.trans h)

private theorem jet2_coefficientGram_snd_fst {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hbd : DifferentiableAt ℝ b y) (w : E) (l m : Fin (Module.finrank ℝ E)) :
    (jet2 (coefficientGram b) y).2.1 w l m =
      fderiv ℝ b y w (chartModelBasis E l) (chartModelBasis E m) := by
  have h : fderiv ℝ (coefficientGram b) y = (coefficientGramCLM E).comp (fderiv ℝ b y) :=
    ((coefficientGramCLM E).hasFDerivAt.comp y hbd.hasFDerivAt).fderiv
  exact congrFun (congrFun (DFunLike.congr_fun h w) l) m

private theorem jet2_coefficientGram_snd_snd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hbd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ b z) (hb2 : DifferentiableAt ℝ (fderiv ℝ b) y)
    (d w : E) (l m : Fin (Module.finrank ℝ E)) :
    (jet2 (coefficientGram b) y).2.2 d w l m =
      fderiv ℝ (fderiv ℝ b) y d w (chartModelBasis E l) (chartModelBasis E m) := by
  have heq : (fun z => fderiv ℝ (coefficientGram b) z) =ᶠ[𝓝 y] fun z =>
      ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) (coefficientGramCLM E)
          (fderiv ℝ b z) :=
    hbd.mono fun z hz => ((coefficientGramCLM E).hasFDerivAt.comp z hz.hasFDerivAt).fderiv
  have h := (heq.fderiv_eq (𝕜 := ℝ)).trans ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
      (coefficientGramCLM E)).hasFDerivAt.comp y hb2.hasFDerivAt).fderiv
  exact congrFun (congrFun (DFunLike.congr_fun (DFunLike.congr_fun h d) w) l) m

private theorem jetChristoffel_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (e : Fin n → E) (p : MatJet E n)
    (hd : ∀ l a c, p.2.1 (e l) a c = p.2.1 (e l) c a) (i j k : Fin n) :
    jetChristoffel e p i j k = jetChristoffel e p j i k := by
  unfold jetChristoffel
  refine congrArg (fun z => (1 / 2 : ℝ) * z) (Finset.sum_congr rfl fun l _ => ?_)
  rw [hd l i j]
  ring

theorem apply_raisedKoszulOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    B (MetricKoszul.raisedKoszulOp B D u v) = MetricKoszul.koszulCov D u v := by
  rw [MetricKoszul.raisedKoszulOp_eq hB, MetricKoszul.apply_koszul_vec]

theorem raisedKoszulOp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] (B : E →L[ℝ] E →L[ℝ] ℝ) {D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hD : ∀ w u v : E, D w u v = D w v u) (u v : E) :
    MetricKoszul.raisedKoszulOp B D u v = MetricKoszul.raisedKoszulOp B D v u := by
  have hk : MetricKoszul.koszulCov D u v = MetricKoszul.koszulCov D v u := by
    refine ContinuousLinearMap.ext fun t => ?_
    rw [MetricKoszul.koszul_cov_apply, MetricKoszul.koszul_cov_apply, hD t u v]
    ring
  rw [MetricKoszul.raisedKoszulOp_apply, MetricKoszul.raisedKoszulOp_apply, hk]

theorem differentiableAt_raisedKoszulOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hb : ContDiffAt ℝ 2 b x) (hco : IsCoercive (b x)) :
    DifferentiableAt ℝ
      (fun y => (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) x := by
  have hev := (hb.eventually (by norm_num)).and
    (eventually_isCoercive_of_continuousAt hb.continuousAt hco)
  obtain ⟨U, hUP, hUo, hxU⟩ := eventually_nhds_iff.1 hev
  have hbU : ContDiffOn ℝ 2 b U := fun y hy => (hUP y hy).1.contDiffWithinAt
  have hDU : ContDiffOn ℝ 1 (fderiv ℝ b) U := hbU.fderiv_of_isOpen hUo (by norm_num)
  exact ((MetricKoszul.raisedKoszulOp_contDiffOn (hbU.of_le (by norm_num)) hDU
    fun y hy => (hUP y hy).2).contDiffAt (hUo.mem_nhds hxU)).differentiableAt (by norm_num)

theorem basis_eq_sum_jetChristoffel_of_koszul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {y : E} (hbd : DifferentiableAt ℝ b y)
    (hsymm : ∀ u v : E, b y u v = b y v u)
    (hdsymm : ∀ w u v : E, fderiv ℝ b y w u v = fderiv ℝ b y w v u)
    (hco : IsCoercive (b y))
    (hK : ∀ u v t : E, b y (Γ y u v) t = MetricKoszul.koszulCov (fderiv ℝ b y) u v t)
    (i j : Fin (Module.finrank ℝ E)) :
    Γ y (chartModelBasis E i) (chartModelBasis E j) =
      ∑ k, jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) y) i j k •
        chartModelBasis E k := by
  apply hco.bilin_injective
  refine clm_eq_of_basis fun q => ?_
  have hjl : ∑ k, jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) y) i j k *
      b y (chartModelBasis E k) (chartModelBasis E q) =
      (1 / 2 : ℝ) * ((jet2 (coefficientGram b) y).2.1 (chartModelBasis E i) q j +
        (jet2 (coefficientGram b) y).2.1 (chartModelBasis E j) q i -
          (jet2 (coefficientGram b) y).2.1 (chartModelBasis E q) i j) :=
    jet_lower_aux (coefficientGram b y)
      ((Matrix.of (coefficientGram b y))⁻¹ :
        Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      (gram_mul_inv _ (isUnit_det_gram (b := b) (w := y) hco))
      (fun k l => hsymm (chartModelBasis E k) (chartModelBasis E l))
      (fun l => (jet2 (coefficientGram b) y).2.1 (chartModelBasis E i) l j +
        (jet2 (coefficientGram b) y).2.1 (chartModelBasis E j) l i -
          (jet2 (coefficientGram b) y).2.1 (chartModelBasis E l) i j) q
  rw [hK, bilin_sum_smul_apply, hjl, jet2_coefficientGram_snd_fst hbd,
    jet2_coefficientGram_snd_fst hbd, jet2_coefficientGram_snd_fst hbd,
    MetricKoszul.koszul_cov_apply,
    hdsymm (chartModelBasis E i) (chartModelBasis E q) (chartModelBasis E j),
    hdsymm (chartModelBasis E j) (chartModelBasis E q) (chartModelBasis E i)]

private def evalThree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a c d : E) :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ d).comp ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) c).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) a))

private def koszulEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v t : E) :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (evalThree u v t + evalThree v u t - evalThree t u v)

private theorem evalThree_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a c d : E) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : evalThree a c d D = D a c d :=
  rfl

private theorem koszulEval_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v t : E) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    koszulEval u v t D = MetricKoszul.koszulCov D u v t := by
  unfold koszulEval
  rw [_root_.smul_apply (evalThree u v t + evalThree v u t - evalThree t u v) (1 / 2 : ℝ) D,
    _root_.sub_apply (evalThree u v t + evalThree v u t) (evalThree t u v) D,
    _root_.add_apply (evalThree u v t) (evalThree v u t) D, evalThree_apply, evalThree_apply,
    evalThree_apply, smul_eq_mul, MetricKoszul.koszul_cov_apply]

theorem apply_fderiv_eq_koszulCov_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hbd : DifferentiableAt ℝ b x) (hb2 : DifferentiableAt ℝ (fderiv ℝ b) x)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hK : ∀ᶠ y in 𝓝 x, ∀ u v t : E,
      b y (Γ y u v) t = MetricKoszul.koszulCov (fderiv ℝ b y) u v t)
    (w u v t : E) :
    b x (fderiv ℝ Γ x w u v) t =
      MetricKoszul.koszulCov (fderiv ℝ (fderiv ℝ b) x w) u v t -
        fderiv ℝ b x w (Γ x u v) t := by
  have hγ : HasFDerivAt (fun y => Γ y u v)
      (((ContinuousLinearMap.apply ℝ E v).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) u)).comp (fderiv ℝ Γ x)) x :=
    ((ContinuousLinearMap.apply ℝ E v).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) u)).hasFDerivAt.comp x hΓ.hasFDerivAt
  have hφ : HasFDerivAt (fun y => b y (Γ y u v) t) _ x :=
    (ContinuousLinearMap.apply ℝ ℝ t).hasFDerivAt.comp x (hbd.hasFDerivAt.clm_apply hγ)
  have hψ : HasFDerivAt (fun y => koszulEval u v t (fderiv ℝ b y))
      ((koszulEval u v t).comp (fderiv ℝ (fderiv ℝ b) x)) x :=
    (koszulEval u v t).hasFDerivAt.comp x hb2.hasFDerivAt
  have heq : (fun y => b y (Γ y u v) t) =ᶠ[𝓝 x] fun y => koszulEval u v t (fderiv ℝ b y) :=
    hK.mono fun y hy => (hy u v t).trans (koszulEval_apply u v t (fderiv ℝ b y)).symm
  have hD : b x (fderiv ℝ Γ x w u v) t + fderiv ℝ b x w (Γ x u v) t =
      MetricKoszul.koszulCov (fderiv ℝ (fderiv ℝ b) x w) u v t :=
    (DFunLike.congr_fun (hφ.unique (hψ.congr_of_eventuallyEq heq)) w).trans
      (koszulEval_apply u v t (fderiv ℝ (fderiv ℝ b) x w))
  exact eq_sub_of_add_eq hD

private theorem lower_fderiv_eq_sum_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y) (hb2 : DifferentiableAt ℝ (fderiv ℝ b) x)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hK : ∀ᶠ y in 𝓝 x, ∀ u v t : E,
      b y (Γ y u v) t = MetricKoszul.koszulCov (fderiv ℝ b y) u v t)
    (hunit : IsUnit (Matrix.of (coefficientGram b x)).det)
    (hdsx : ∀ w u v : E, fderiv ℝ b x w u v = fderiv ℝ b x w v u)
    (hd2 : ∀ m w u v : E, fderiv ℝ (fderiv ℝ b) x m w u v = fderiv ℝ (fderiv ℝ b) x m w v u)
    (hC : ∀ i j, Γ x (chartModelBasis E i) (chartModelBasis E j) =
      ∑ k, jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) i j k •
        chartModelBasis E k)
    (hCsym : ∀ a c r, jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) a c r =
      jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) c a r)
    (m a c q : Fin (Module.finrank ℝ E)) :
    b x (fderiv ℝ Γ x (chartModelBasis E m) (chartModelBasis E a) (chartModelBasis E c))
        (chartModelBasis E q) =
      ∑ r, coefficientGram b x q r *
        jetChristoffelDeriv (chartModelBasis E) (jet2 (coefficientGram b) x) m c a r := by
  have hbdx : DifferentiableAt ℝ b x := hbd.self_of_nhds
  have hjet : ∑ r, coefficientGram b x q r *
      jetChristoffelDeriv (chartModelBasis E) (jet2 (coefficientGram b) x) m c a r =
      (1 / 2 : ℝ) *
        ((jet2 (coefficientGram b) x).2.2 (chartModelBasis E m) (chartModelBasis E c) q a +
          (jet2 (coefficientGram b) x).2.2 (chartModelBasis E m) (chartModelBasis E a) q c -
            (jet2 (coefficientGram b) x).2.2 (chartModelBasis E m) (chartModelBasis E q) c a) -
        ∑ r, (jet2 (coefficientGram b) x).2.1 (chartModelBasis E m) q r *
          jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) c a r :=
    jet_deriv_lower_aux (coefficientGram b x)
      ((Matrix.of (coefficientGram b x))⁻¹ :
        Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      ((jet2 (coefficientGram b) x).2.1 (chartModelBasis E m)) (gram_mul_inv _ hunit)
      (fun l => (jet2 (coefficientGram b) x).2.1 (chartModelBasis E c) l a +
        (jet2 (coefficientGram b) x).2.1 (chartModelBasis E a) l c -
          (jet2 (coefficientGram b) x).2.1 (chartModelBasis E l) c a)
      (fun l => (jet2 (coefficientGram b) x).2.2 (chartModelBasis E m) (chartModelBasis E c) l a +
        (jet2 (coefficientGram b) x).2.2 (chartModelBasis E m) (chartModelBasis E a) l c -
          (jet2 (coefficientGram b) x).2.2 (chartModelBasis E m) (chartModelBasis E l) c a) q
  have hsum : ∑ r, (jet2 (coefficientGram b) x).2.1 (chartModelBasis E m) q r *
      jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) c a r =
      ∑ r, jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) a c r *
        fderiv ℝ b x (chartModelBasis E m) (chartModelBasis E r) (chartModelBasis E q) :=
    Finset.sum_congr rfl fun r _ => by
      rw [jet2_coefficientGram_snd_fst hbdx,
        hdsx (chartModelBasis E m) (chartModelBasis E q) (chartModelBasis E r), hCsym c a r]
      ring
  rw [hjet, hsum, jet2_coefficientGram_snd_snd hbd hb2, jet2_coefficientGram_snd_snd hbd hb2,
    jet2_coefficientGram_snd_snd hbd hb2,
    hd2 (chartModelBasis E m) (chartModelBasis E c) (chartModelBasis E q) (chartModelBasis E a),
    hd2 (chartModelBasis E m) (chartModelBasis E a) (chartModelBasis E q) (chartModelBasis E c),
    hd2 (chartModelBasis E m) (chartModelBasis E q) (chartModelBasis E c) (chartModelBasis E a),
    apply_fderiv_eq_koszulCov_sub hbdx hb2 hΓ hK, MetricKoszul.koszul_cov_apply, hC a c,
    bilin_sum_smul_apply]
  ring

private theorem lower_comp_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    {C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hsx : ∀ u v : E, b x u v = b x v u)
    (hC : ∀ i j, Γ x (chartModelBasis E i) (chartModelBasis E j) =
      ∑ k, C i j k • chartModelBasis E k)
    (hCsym : ∀ a c r, C a c r = C c a r) (a c d q : Fin (Module.finrank ℝ E)) :
    b x (Γ x (chartModelBasis E a) (Γ x (chartModelBasis E c) (chartModelBasis E d)))
        (chartModelBasis E q) =
      ∑ r, coefficientGram b x q r * ∑ m, C a m r * C d c m := by
  have h1 : Γ x (chartModelBasis E a) (Γ x (chartModelBasis E c) (chartModelBasis E d)) =
      ∑ m, C c d m • ∑ r, C a m r • chartModelBasis E r := by
    rw [hC c d, map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, hC a m]
  calc b x (Γ x (chartModelBasis E a) (Γ x (chartModelBasis E c) (chartModelBasis E d)))
          (chartModelBasis E q) =
        ∑ m, C c d m * ∑ r, C a m r * b x (chartModelBasis E r) (chartModelBasis E q) := by
        rw [h1, bilin_sum_smul_apply]
        exact Finset.sum_congr rfl fun m _ => by rw [bilin_sum_smul_apply]
    _ = ∑ m, ∑ r, coefficientGram b x q r * (C a m r * C d c m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [coefficientGram_apply, hsx (chartModelBasis E q) (chartModelBasis E r), hCsym c d m]
        ring
    _ = ∑ r, ∑ m, coefficientGram b x q r * (C a m r * C d c m) := Finset.sum_comm
    _ = ∑ r, coefficientGram b x q r * ∑ m, C a m r * C d c m :=
        Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm

theorem coefficientRm04_eq_connectionFormCurvature_of_koszul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hb : ContDiffAt ℝ 2 b x) (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u)
    (hco : IsCoercive (b x)) (hΓ : DifferentiableAt ℝ Γ x)
    (hK : ∀ᶠ y in 𝓝 x, ∀ u v t : E,
      b y (Γ y u v) t = MetricKoszul.koszulCov (fderiv ℝ b y) u v t)
    (X Y Z W : E) :
    coefficientRm04 b x X Y Z W =
      b x (Geometry.Connection.connectionFormCurvature Γ x X Y Z) W := by
  have hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y :=
    (hb.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hbdx : DifferentiableAt ℝ b x := hbd.self_of_nhds
  have hb2 : DifferentiableAt ℝ (fderiv ℝ b) x :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsx : ∀ u v : E, b x u v = b x v u := hsymm.self_of_nhds
  have hdsx : ∀ w u v : E, fderiv ℝ b x w u v = fderiv ℝ b x w v u :=
    (eventually_fderiv_symm hbd hsymm).self_of_nhds
  have hd2 := fderiv_fderiv_symm hbd hb2 hsymm
  have hunit : IsUnit (Matrix.of (coefficientGram b x)).det :=
    isUnit_det_gram (b := b) (w := x) hco
  have hC := basis_eq_sum_jetChristoffel_of_koszul hbdx hsx hdsx hco hK.self_of_nhds
  have hCsym : ∀ a c r, jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) a c r =
      jetChristoffel (chartModelBasis E) (jet2 (coefficientGram b) x) c a r :=
    jetChristoffel_symm (chartModelBasis E) (jet2 (coefficientGram b) x) fun l a c =>
      (jet2_coefficientGram_snd_fst hbdx (chartModelBasis E l) a c).trans
        ((hdsx (chartModelBasis E l) (chartModelBasis E a) (chartModelBasis E c)).trans
          (jet2_coefficientGram_snd_fst hbdx (chartModelBasis E l) c a).symm)
  rw [coefficientRm04_eq_sum, apply_connectionFormCurvature_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [lower_connectionFormCurvature, lower_fderiv_eq_sum_jet hbd hb2 hΓ hK hunit hdsx hd2 hC hCsym,
    lower_fderiv_eq_sum_jet hbd hb2 hΓ hK hunit hdsx hd2 hC hCsym,
    lower_comp_eq_sum hsx hC hCsym, lower_comp_eq_sum hsx hC hCsym, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold jetRiemann
  rw [Finset.sum_sub_distrib]
  ring

theorem coefficientRm04_eq_connectionFormCurvature {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x))
    (X Y Z W : E) :
    coefficientRm04 b x X Y Z W =
      b x (Geometry.Connection.connectionFormCurvature
        (fun y => (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E))
        x X Y Z) W :=
  coefficientRm04_eq_connectionFormCurvature_of_koszul
    (Γ := fun y => (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E))
    hb hsymm hco (differentiableAt_raisedKoszulOp hb hco)
    ((eventually_isCoercive_of_continuousAt hb.continuousAt hco).mono fun y hy u v t =>
      DFunLike.congr_fun (apply_raisedKoszulOp hy (fderiv ℝ b y) u v) t) X Y Z W

theorem coefficientRm04_eq_connectionFormCurvature_of_isOpen {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : ContDiffOn ℝ 2 b U)
    (hsymm : ∀ y ∈ U, ∀ u v : E, b y u v = b y v u) (hco : ∀ y ∈ U, IsCoercive (b y))
    {x : E} (hx : x ∈ U) (X Y Z W : E) :
    coefficientRm04 b x X Y Z W =
      b x (Geometry.Connection.connectionFormCurvature
        (fun y => (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E))
        x X Y Z) W :=
  coefficientRm04_eq_connectionFormCurvature (hb.contDiffAt (hU.mem_nhds hx))
    (Filter.eventually_of_mem (hU.mem_nhds hx) hsymm) (hco x hx) X Y Z W

end DifferentialGeometry.Analysis
