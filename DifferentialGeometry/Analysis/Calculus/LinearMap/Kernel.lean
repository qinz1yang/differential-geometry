import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

noncomputable section

open Filter
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
