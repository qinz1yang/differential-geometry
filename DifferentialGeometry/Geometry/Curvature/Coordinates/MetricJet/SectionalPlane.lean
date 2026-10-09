import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientSectional
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.KoszulIdentification
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

set_option autoImplicit false

noncomputable section

open scoped Topology
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

namespace DifferentialGeometry.Analysis

theorem jetRiemann_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (e : Fin n → E) (p : MatJet E n) (i j k l : Fin n) :
    jetRiemann e p i k j l = -jetRiemann e p i j k l := by
  unfold jetRiemann
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

private theorem sum_jetRiemann_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (e : Fin n → E) (p : MatJet E n) (g : Fin n → ℝ) (k j i : Fin n) :
    ∑ l, g l * jetRiemann e p k j i l = -∑ l, g l * jetRiemann e p k i j l := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by rw [jetRiemann_swap e p k i j l, mul_neg]

theorem coefficientRm04_swap_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x X Y Z W : E) :
    coefficientRm04 b x Y X Z W = -coefficientRm04 b x X Y Z W := by
  rw [coefficientRm04_eq_sum, coefficientRm04_eq_sum, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sum_jetRiemann_swap]
  ring

theorem metric_compat_of_koszul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} {D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {G : E →L[ℝ] E →L[ℝ] E}
    (hB : ∀ u v : E, B u v = B v u) (hD : ∀ w u v : E, D w u v = D w v u)
    (hK : ∀ u v t : E, B (G u v) t = MetricKoszul.koszulCov D u v t) (w u v : E) :
    D w u v = B (G w u) v + B u (G w v) := by
  rw [hB u (G w v), hK w u v, hK w v u, MetricKoszul.koszul_cov_apply,
    MetricKoszul.koszul_cov_apply, hD w v u]
  ring

theorem eventually_metric_compat_raisedKoszulOp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 1 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) :
    ∀ᶠ y in 𝓝 x, ∀ w u v : E, fderiv ℝ b y w u v =
      b y (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) w u) v +
        b y u (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) w v) := by
  have hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y :=
    (hb.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  filter_upwards [hsymm, eventually_fderiv_symm hbd hsymm,
    eventually_isCoercive_of_continuousAt hb.continuousAt hco] with y hy1 hy2 hy3
  exact metric_compat_of_koszul hy1 hy2 fun u v t =>
    DFunLike.congr_fun (apply_raisedKoszulOp hy3 (fderiv ℝ b y) u v) t

theorem fderiv_fderiv_eq_of_koszul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hbd : DifferentiableAt ℝ b x) (hb2 : DifferentiableAt ℝ (fderiv ℝ b) x)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hK : ∀ᶠ y in 𝓝 x, ∀ u v t : E,
      b y (Γ y u v) t = MetricKoszul.koszulCov (fderiv ℝ b y) u v t)
    (hsx : ∀ u v : E, b x u v = b x v u)
    (hdsx : ∀ w u v : E, fderiv ℝ b x w u v = fderiv ℝ b x w v u)
    (hd2 : ∀ m w u v : E, fderiv ℝ (fderiv ℝ b) x m w u v = fderiv ℝ (fderiv ℝ b) x m w v u)
    (m w u v : E) :
    fderiv ℝ (fderiv ℝ b) x m w u v =
      fderiv ℝ b x m (Γ x w u) v + b x (fderiv ℝ Γ x m w u) v +
        fderiv ℝ b x m u (Γ x w v) + b x u (fderiv ℝ Γ x m w v) := by
  have h1 := apply_fderiv_eq_koszulCov_sub hbd hb2 hΓ hK m w u v
  have h2 := apply_fderiv_eq_koszulCov_sub hbd hb2 hΓ hK m w v u
  rw [MetricKoszul.koszul_cov_apply] at h1 h2
  rw [hsx u (fderiv ℝ Γ x m w v), hdsx m u (Γ x w v)]
  linarith [hd2 m w v u]

private theorem lower_connectionFormCurvature_fst {E : Type*} [NormedAddCommGroup E]
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

private theorem lower_connectionFormCurvature_snd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E) (x a c d t : E) :
    B t (Geometry.Connection.connectionFormCurvature Γ x a c d) =
      B t (fderiv ℝ Γ x a c d) - B t (fderiv ℝ Γ x c a d) + B t (Γ x a (Γ x c d)) -
        B t (Γ x c (Γ x a d)) := by
  unfold Geometry.Connection.connectionFormCurvature
  rw [map_sub (B t), map_add (B t), map_sub (B t)]

theorem apply_connectionFormCurvature_add_of_koszul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hb : ContDiffAt ℝ 2 b x) (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hK : ∀ᶠ y in 𝓝 x, ∀ u v t : E,
      b y (Γ y u v) t = MetricKoszul.koszulCov (fderiv ℝ b y) u v t)
    (X Y Z W : E) :
    b x (Geometry.Connection.connectionFormCurvature Γ x X Y Z) W +
      b x Z (Geometry.Connection.connectionFormCurvature Γ x X Y W) = 0 := by
  have hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y :=
    (hb.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hb2 : DifferentiableAt ℝ (fderiv ℝ b) x :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsx : ∀ u v : E, b x u v = b x v u := hsymm.self_of_nhds
  have hdsx : ∀ w u v : E, fderiv ℝ b x w u v = fderiv ℝ b x w v u :=
    (eventually_fderiv_symm hbd hsymm).self_of_nhds
  have hc := metric_compat_of_koszul hsx hdsx hK.self_of_nhds
  have hdc := fderiv_fderiv_eq_of_koszul hbd.self_of_nhds hb2 hΓ hK hsx hdsx
    (fderiv_fderiv_symm hbd hb2 hsymm)
  have hS : fderiv ℝ (fderiv ℝ b) x X Y Z W = fderiv ℝ (fderiv ℝ b) x Y X Z W :=
    DFunLike.congr_fun (DFunLike.congr_fun ((hb.isSymmSndFDerivAt (by norm_num)).eq X Y) Z) W
  rw [lower_connectionFormCurvature_fst, lower_connectionFormCurvature_snd]
  linarith [hdc X Y Z W, hdc Y X Z W, hS, hc X (Γ x Y Z) W, hc X Z (Γ x Y W),
    hc Y (Γ x X Z) W, hc Y Z (Γ x X W)]

theorem coefficientRm04_swap_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x))
    (X Y Z W : E) :
    coefficientRm04 b x X Y W Z = -coefficientRm04 b x X Y Z W := by
  let _ : ContinuousDualEquiv E := IsCoercive.continuousDualEquivOfFiniteDimensional
  have hsx : ∀ u v : E, b x u v = b x v u := hsymm.self_of_nhds
  have h := apply_connectionFormCurvature_add_of_koszul hb hsymm
    (differentiableAt_raisedKoszulOp hb hco)
    ((eventually_isCoercive_of_continuousAt hb.continuousAt hco).mono fun y hy u v t =>
      DFunLike.congr_fun (apply_raisedKoszulOp hy (fderiv ℝ b y) u v) t) X Y Z W
  rw [coefficientRm04_eq_connectionFormCurvature hb hsymm hco X Y W Z,
    coefficientRm04_eq_connectionFormCurvature hb hsymm hco X Y Z W, hsx _ Z]
  exact eq_neg_of_add_eq_zero_right h

private theorem repr_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (a c : ℝ) (p q : E) (i : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr (a • p + c • q) i =
      a * (chartModelBasis E).repr p i + c * (chartModelBasis E).repr q i := by
  rw [map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, smul_eq_mul]

private theorem sum4_add_mul {n : ℕ} (f g : Fin n → Fin n → Fin n → Fin n → ℝ) (a c : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (a * f i j k l + c * g i j k l) =
      a * (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) + c * ∑ i, ∑ j, ∑ k, ∑ l, g i j k l := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

private theorem coefficientRm04_combo_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (a c : ℝ) (p q Y Z W : E) :
    coefficientRm04 b x (a • p + c • q) Y Z W =
      a * coefficientRm04 b x p Y Z W + c * coefficientRm04 b x q Y Z W := by
  rw [coefficientRm04_eq_sum, coefficientRm04_eq_sum, coefficientRm04_eq_sum, ← sum4_add_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [repr_add_smul]
  ring

private theorem coefficientRm04_combo_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (a c : ℝ) (p q X Z W : E) :
    coefficientRm04 b x X (a • p + c • q) Z W =
      a * coefficientRm04 b x X p Z W + c * coefficientRm04 b x X q Z W := by
  rw [coefficientRm04_eq_sum, coefficientRm04_eq_sum, coefficientRm04_eq_sum, ← sum4_add_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [repr_add_smul]
  ring

private theorem coefficientRm04_combo_thd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (a c : ℝ) (p q X Y W : E) :
    coefficientRm04 b x X Y (a • p + c • q) W =
      a * coefficientRm04 b x X Y p W + c * coefficientRm04 b x X Y q W := by
  rw [coefficientRm04_eq_sum, coefficientRm04_eq_sum, coefficientRm04_eq_sum, ← sum4_add_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [repr_add_smul]
  ring

private theorem coefficientRm04_combo_fth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (a c : ℝ) (p q X Y Z : E) :
    coefficientRm04 b x X Y Z (a • p + c • q) =
      a * coefficientRm04 b x X Y Z p + c * coefficientRm04 b x X Y Z q := by
  rw [coefficientRm04_eq_sum, coefficientRm04_eq_sum, coefficientRm04_eq_sum, ← sum4_add_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [repr_add_smul]
  ring

private theorem sq_det_of_antisymm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : E → E → E → E → ℝ)
    (h1 : ∀ (a c : ℝ) (p q Y Z W : E), N (a • p + c • q) Y Z W = a * N p Y Z W + c * N q Y Z W)
    (h2 : ∀ (a c : ℝ) (p q X Z W : E), N X (a • p + c • q) Z W = a * N X p Z W + c * N X q Z W)
    (h3 : ∀ (a c : ℝ) (p q X Y W : E), N X Y (a • p + c • q) W = a * N X Y p W + c * N X Y q W)
    (h4 : ∀ (a c : ℝ) (p q X Y Z : E), N X Y Z (a • p + c • q) = a * N X Y Z p + c * N X Y Z q)
    (hA : ∀ X Y Z W : E, N Y X Z W = -N X Y Z W) (hB : ∀ X Y Z W : E, N X Y W Z = -N X Y Z W)
    (α β γ δ : ℝ) (v u : E) :
    N (α • v + β • u) (γ • v + δ • u) (γ • v + δ • u) (α • v + β • u) =
      (α * δ - β * γ) ^ 2 * N v u u v := by
  have s1 : ∀ Z W : E,
      N (α • v + β • u) (γ • v + δ • u) Z W = (α * δ - β * γ) * N v u Z W := by
    intro Z W
    have hvv : N v v Z W = 0 := by linarith [hA v v Z W]
    have huu : N u u Z W = 0 := by linarith [hA u u Z W]
    rw [h1, h2, h2, hvv, huu, hA v u Z W]
    ring
  have s2 : N v u (γ • v + δ • u) (α • v + β • u) = (α * δ - β * γ) * N v u u v := by
    have hvv : N v u v v = 0 := by linarith [hB v u v v]
    have huu : N v u u u = 0 := by linarith [hB v u u u]
    rw [h3, h4, h4, hvv, huu, hB v u u v]
    ring
  rw [s1, s2]
  ring

theorem coefficientRm04_change_of_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x))
    (α β γ δ : ℝ) (v u : E) :
    coefficientRm04 b x (α • v + β • u) (γ • v + δ • u) (γ • v + δ • u) (α • v + β • u) =
      (α * δ - β * γ) ^ 2 * coefficientRm04 b x v u u v :=
  sq_det_of_antisymm (coefficientRm04 b x) (coefficientRm04_combo_fst b x)
    (coefficientRm04_combo_snd b x) (coefficientRm04_combo_thd b x)
    (coefficientRm04_combo_fth b x) (coefficientRm04_swap_left b x)
    (coefficientRm04_swap_right hb hsymm hco) α β γ δ v u

private theorem bilin_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (α β γ δ : ℝ) (v u : E) :
    B (α • v + β • u) (γ • v + δ • u) =
      α * (γ * B v v + δ * B v u) + β * (γ * B u v + δ * B u u) := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem bilin_gram_change_of_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ u v : E, B u v = B v u) (α β γ δ : ℝ) (v u : E) :
    B (α • v + β • u) (α • v + β • u) * B (γ • v + δ • u) (γ • v + δ • u) -
        (B (α • v + β • u) (γ • v + δ • u)) ^ 2 =
      (α * δ - β * γ) ^ 2 * (B v v * B u u - (B v u) ^ 2) := by
  rw [bilin_add_smul B α β α β v u, bilin_add_smul B γ δ γ δ v u, bilin_add_smul B α β γ δ v u,
    hB u v]
  ring

theorem linearIndependent_pair_of_span_eq {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] {v u v' u' : V} (hvu' : LinearIndependent 𝕜 ![v', u'])
    (hspan : Submodule.span 𝕜 ({v', u'} : Set V) = Submodule.span 𝕜 ({v, u} : Set V)) :
    LinearIndependent 𝕜 ![v, u] := by
  have h : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range ![v', u'])) = Fintype.card (Fin 2) :=
    finrank_span_eq_card hvu'
  rw [Matrix.range_cons_cons_empty, hspan, ← Matrix.range_cons_cons_empty v u ![]] at h
  have hcard : Fintype.card (Fin 2) = (Set.range ![v, u]).finrank 𝕜 := h.symm
  exact linearIndependent_iff_card_eq_finrank_span.mpr hcard

theorem coefficientSectional_eq_of_span_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hb : ContDiffAt ℝ 2 b x) (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u)
    (hco : IsCoercive (b x)) {v u v' u' : E} (hvu' : LinearIndependent ℝ ![v', u'])
    (hspan : Submodule.span ℝ ({v', u'} : Set E) = Submodule.span ℝ ({v, u} : Set E)) :
    coefficientSectional b x v' u' = coefficientSectional b x v u := by
  have hsx : ∀ u v : E, b x u v = b x v u := hsymm.self_of_nhds
  have hv' : v' ∈ Submodule.span ℝ ({v, u} : Set E) := by
    rw [← hspan]
    exact Submodule.mem_span_of_mem (Set.mem_insert v' {u'})
  have hu' : u' ∈ Submodule.span ℝ ({v, u} : Set E) := by
    rw [← hspan]
    exact Submodule.mem_span_of_mem (Set.mem_insert_of_mem v' (Set.mem_singleton u'))
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv'
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hu'
  have hG := bilin_gram_pos_of_linearIndependent hsx hco hvu'
  rw [bilin_gram_change_of_basis hsx] at hG
  have hD : (α * δ - β * γ) ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hG
    exact lt_irrefl 0 hG
  rw [coefficientSectional_def, coefficientSectional_def,
    coefficientRm04_change_of_basis hb hsymm hco, bilin_gram_change_of_basis hsx]
  exact mul_div_mul_left _ _ hD

end DifferentialGeometry.Analysis
