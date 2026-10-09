import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable section

open Filter
open scoped InnerProductSpace
open scoped Topology

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]

theorem continuousLinearMap_kernel_eq_of_constant_on_left
    [FiniteDimensional Real E]
    {A : Real → E →L[Real] F} {K : Submodule Real E}
    {a b : Real} (hab : a < b) (hA : ContinuousAt A b)
    (hK : ∀ t ∈ Set.Ioo a b, (A t).ker = K)
    (hfin : Module.finrank Real K = Module.finrank Real (A b).ker) :
    K = (A b).ker := by
  apply Submodule.eq_of_le_of_finrank_eq ?_ hfin
  intro v hv
  have hzero : ∀ t ∈ Set.Ioo a b, A t v = 0 := by
    intro t ht
    have hv' : v ∈ (A t).ker := by
      rw [hK t ht]
      exact hv
    exact LinearMap.mem_ker.mp hv'
  have hlim : Tendsto (fun t : Real => A t v)
      (𝓝[Set.Ioo a b] b) (𝓝 (A b v)) :=
    (hA.clm_apply continuousAt_const).continuousWithinAt.tendsto
  have hev : ∀ᶠ t in 𝓝[Set.Ioo a b] b, A t v ∈ ({0} : Set F) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Set.mem_singleton_iff.mpr (hzero t ht)
  let _ : (𝓝[Set.Ioo a b] b).NeBot := right_nhdsWithin_Ioo_neBot hab
  have hmem : A b v ∈ ({0} : Set F) :=
    isClosed_singleton.mem_of_tendsto hlim hev
  simpa using hmem

theorem continuousLinearMap_kernel_annihilation_of_constant_on_left
    [FiniteDimensional Real E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
    {A : Real → E →L[Real] F} {B : Real → E →L[Real] G}
    {K : Submodule Real E} {a b : Real} (hab : a < b)
    (hA : ContinuousAt A b) (hB : ContinuousAt B b)
    (hK : ∀ t ∈ Set.Ioo a b, (A t).ker = K)
    (hfin : Module.finrank Real K = Module.finrank Real (A b).ker)
    (hzero : ∀ t ∈ Set.Ioo a b, ∀ v, v ∈ (A t).ker → B t v = 0) :
    ∀ v, v ∈ (A b).ker → B b v = 0 := by
  have hKb : K = (A b).ker :=
    continuousLinearMap_kernel_eq_of_constant_on_left hab hA hK hfin
  intro v hv
  have hvK : v ∈ K := by
    rw [hKb]
    exact hv
  have hzero' : ∀ t ∈ Set.Ioo a b, B t v = 0 := by
    intro t ht
    apply hzero t ht v
    rw [hK t ht]
    exact hvK
  have hlim : Tendsto (fun t : Real => B t v)
      (𝓝[Set.Ioo a b] b) (𝓝 (B b v)) :=
    (hB.clm_apply continuousAt_const).continuousWithinAt.tendsto
  have hev : ∀ᶠ t in 𝓝[Set.Ioo a b] b, B t v ∈ ({0} : Set G) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Set.mem_singleton_iff.mpr (hzero' t ht)
  let _ : (𝓝[Set.Ioo a b] b).NeBot := right_nhdsWithin_Ioo_neBot hab
  have hmem : B b v ∈ ({0} : Set G) :=
    isClosed_singleton.mem_of_tendsto hlim hev
  simpa using hmem

theorem hasDerivAt_apply_eq_zero_of_eventually_eq_zero
    {A : Real → E →L[Real] F} {w : Real → E}
    {A' : E →L[Real] F} {w' : E} {t : Real}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t)
    (hzero : ∀ᶠ s in nhds t, A s (w s) = 0) :
    A' (w t) + A t w' = 0 := by
  have hprod : HasDerivAt (fun s => A s (w s))
      (A' (w t) + A t w') t := hA.clm_apply hw
  have hconst : HasDerivAt (fun _ : Real => (0 : F)) 0 t :=
    hasDerivAt_const t 0
  have hzero' : HasDerivAt (fun s => A s (w s)) 0 t := by
    exact hconst.congr_of_eventuallyEq hzero
  exact hprod.unique hzero'

theorem hasDerivAt_apply_eq_zero_of_continuousLinearMap
    {A : Real → E →L[Real] F} {w : Real → E}
    {A' : E →L[Real] F} {w' : E} {t : Real}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t)
    (hzero : ∀ s, A s (w s) = 0) :
    A' (w t) + A t w' = 0 :=
  hasDerivAt_apply_eq_zero_of_eventually_eq_zero hA hw
    (Filter.Eventually.of_forall hzero)

theorem hasDerivAt_apply_eq_of_kernel_motion
    {A : Real → E →L[Real] F} {w : Real → E}
    {A' B : E →L[Real] F} {w' : E} {t : Real}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t)
    (hzero : ∀ᶠ s in nhds t, A s (w s) = 0)
    (hmotion : A t w' = -B (w t)) :
    A' (w t) = B (w t) := by
  have h := hasDerivAt_apply_eq_zero_of_eventually_eq_zero hA hw hzero
  rw [hmotion] at h
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg]
  exact h

theorem hasDerivAt_kernel_motion_of_apply_eq
    {A : Real → E →L[Real] F} {w : Real → E}
    {A' B : E →L[Real] F} {w' : E} {t : Real}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t)
    (hzero : ∀ᶠ s in nhds t, A s (w s) = 0)
    (happly : A' (w t) = B (w t)) :
    A t w' = -B (w t) := by
  have h := hasDerivAt_apply_eq_zero_of_eventually_eq_zero hA hw hzero
  rw [happly] at h
  exact eq_neg_of_add_eq_zero_right h

theorem inner_deriv_apply_eq_zero_of_eventually_mem_ker
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {A : Real → E →L[Real] E} {w : Real → E} {t : Real}
    (hA : DifferentiableAt Real A t) (hw : DifferentiableAt Real w t)
    (hzero : ∀ᶠ s in nhds t, A s (w s) = 0)
    (hsymm : (A t : E →ₗ[Real] E).IsSymmetric) :
    ⟪deriv A t (w t), w t⟫_Real = 0 := by
  have happly := hasDerivAt_apply_eq_zero_of_eventually_eq_zero
    hA.hasDerivAt hw.hasDerivAt hzero
  have hderiv : deriv A t (w t) = -A t (deriv w t) := by
    exact eq_neg_of_add_eq_zero_left happly
  rw [hderiv, inner_neg_left]
  have hswap : ⟪A t (deriv w t), w t⟫_Real =
      ⟪deriv w t, A t (w t)⟫_Real := hsymm _ _
  rw [hswap]
  have hAt : A t (w t) = 0 := hzero.self_of_nhds
  rw [hAt, inner_zero_right, neg_zero]

theorem continuousLinearMap_eq_zero_of_isPositive_inner_eq_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {B : E →L[Real] E} (hB : B.IsPositive) {w : E}
    (hw : ⟪B w, w⟫_ℝ = 0) : B w = 0 := by
  let b : LinearMap.BilinForm Real E := LinearMap.mk₂ Real
    (fun x y : E => ⟪B x, y⟫_ℝ)
    (by intros; rw [map_add, inner_add_left])
    (by intros; rw [map_smul]; simp [real_inner_smul_left])
    (by intros; rw [inner_add_right])
    (by intros; simp [real_inner_smul_right])
  have hbnonneg : ∀ x : E, 0 ≤ b x x := by
    intro x
    simpa [b] using hB.inner_nonneg_left x
  have hbsymm : LinearMap.IsSymm b := by
    refine ⟨?_⟩
    intro x y
    simpa [b, real_inner_comm] using hB.inner_left_eq_inner_right x y
  have hker : w ∈ LinearMap.ker b :=
    (b.apply_apply_same_eq_zero_iff hbnonneg hbsymm).mp (by simpa [b] using hw)
  have hbw : b w = 0 := LinearMap.mem_ker.mp hker
  apply ext_inner_left Real
  intro z
  have hz := congrArg (fun L : E →ₗ[Real] Real => L z) hbw
  change ⟪B w, z⟫_ℝ = 0 at hz
  rw [real_inner_comm]
  simpa using hz

theorem continuousLinearMap_kernel_annihilation_of_isPositive
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {A B : E →L[Real] E} (hB : B.IsPositive)
    (hzero : ∀ w : E, w ∈ A.ker → ⟪B w, w⟫_ℝ = 0) :
    ∀ w : E, w ∈ A.ker → B w = 0 := by
  intro w hw
  exact continuousLinearMap_eq_zero_of_isPositive_inner_eq_zero hB (hzero w hw)

theorem linearMap_kernel_annihilation_of_commuting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {A B : E →ₗ[Real] E} (hB : B.IsSymmetric)
    (hcomm : B.comp A = A.comp B)
    (hzero : ∀ w : E, w ∈ A.ker → ⟪B w, w⟫_ℝ = 0) :
    ∀ w : E, w ∈ A.ker → B w = 0 := by
  intro w hw
  have hBwker : B w ∈ A.ker := by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun L : E →ₗ[Real] E => L w) hcomm
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hw,
      map_zero] at h
    exact h.symm
  have hquad_plus := hzero (w + B w) (A.ker.add_mem hw hBwker)
  have hquad_minus := hzero (w - B w) (A.ker.sub_mem hw hBwker)
  have hpair : ⟪B w, B w⟫_ℝ = 0 := by
    simp only [map_add, map_sub, inner_add_left, inner_sub_left,
      inner_add_right, inner_sub_right] at hquad_plus hquad_minus
    have hsymm : ⟪B (B w), w⟫_ℝ = ⟪B w, B w⟫_ℝ := by
      simpa using hB (B w) w
    nlinarith [hquad_plus, hquad_minus, hzero w hw, hsymm]
  have hnormsq : ‖B w‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hpair
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)
