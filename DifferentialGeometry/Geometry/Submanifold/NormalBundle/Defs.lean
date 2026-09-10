import DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry
namespace IsRiemannianIsometricImmersion

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def normalSpaceAt
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (_h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    Submodule ℝ (TangentSpace I (iota x)) :=
  (gM.inner (iota x)).toBilinForm.orthogonal
    (mfderiv IN I iota x).range

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem mem_normalSpaceAt_iff
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (v : TangentSpace I (iota x)) :
    v ∈ h.normalSpaceAt x ↔
      ∀ u : TangentSpace IN x,
        gM.inner (iota x) v (mfderiv IN I iota x u) = 0 := by
  rw [normalSpaceAt, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hv u
    rw [gM.symm]
    exact hv (mfderiv IN I iota x u) ⟨u, rfl⟩
  · intro hv w hw
    obtain ⟨u, rfl⟩ := hw
    change gM.inner (iota x) (mfderiv IN I iota x u) v = 0
    rw [gM.symm]
    exact hv u

abbrev NormalBundleTotalSpace
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :=
  Σ x : N, h.normalSpaceAt x

def normalBundleProjection
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    h.NormalBundleTotalSpace → N :=
  Sigma.fst

def normalZeroSection
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    N → h.NormalBundleTotalSpace :=
  fun x ↦ ⟨x, 0⟩

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
@[simp]
theorem normalBundleProjection_normalZeroSection
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    h.normalBundleProjection (h.normalZeroSection x) = x :=
  rfl

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem normalZeroSection_injective
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    Function.Injective h.normalZeroSection :=
  Function.LeftInverse.injective (h.normalBundleProjection_normalZeroSection)

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem nonempty_normalBundleTotalSpace_iff
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    Nonempty h.NormalBundleTotalSpace ↔ Nonempty N := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.1⟩
  · rintro ⟨x⟩
    exact ⟨h.normalZeroSection x⟩

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem normalSpaceAt_eq_top_of_derivative_eq_zero
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (hzero : mfderiv IN I iota x = 0) :
    h.normalSpaceAt x = ⊤ := by
  ext v
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    rw [h.mem_normalSpaceAt_iff]
    intro u
    rw [hzero]
    simp

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem range_inf_normalSpaceAt_eq_bot
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    (mfderiv IN I iota x).range ⊓ h.normalSpaceAt x = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvRange, hvNormal⟩ := hv
    obtain ⟨u, rfl⟩ := hvRange
    have huOrth := (h.mem_normalSpaceAt_iff x _).mp hvNormal u
    by_contra hv0
    have hpos := gM.pos (iota x) (mfderiv IN I iota x u) hv0
    exact hpos.ne' huOrth
  · exact bot_le

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem normalSpaceAt_eq_bot_of_surjective_derivative
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (hsurj : Function.Surjective (mfderiv IN I iota x)) :
    h.normalSpaceAt x = ⊥ := by
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_bot]
    obtain ⟨u, hu⟩ := hsurj v
    have hvv := (h.mem_normalSpaceAt_iff x v).mp hv u
    rw [hu] at hvv
    by_contra hv0
    exact (gM.pos (iota x) v hv0).ne' hvv
  · intro hv
    rw [Submodule.mem_bot] at hv
    subst v
    exact Submodule.zero_mem _

omit [FiniteDimensional ℝ E] in
theorem mfderiv_eq_zero_of_finrank_eq_zero
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (_h : IsRiemannianIsometricImmersion gN gM iota)
    (hdim : Module.finrank ℝ EN = 0) (x : N) :
    mfderiv IN I iota x = 0 := by
  let _ : Subsingleton EN := Module.finrank_zero_iff.mp hdim
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = 0 :=
    (tangentSpaceModelContinuousLinearEquiv (I := IN) x).injective
      (Subsingleton.elim _ _)
  rw [hu]
  exact ContinuousLinearMap.map_zero _

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
private def normalSpaceAtEquivTangentSpaceOfEqTop
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (htop : h.normalSpaceAt x = ⊤) :
    h.normalSpaceAt x ≃ TangentSpace I (iota x) where
  toFun v := v.1
  invFun v := ⟨v, by rw [htop]; exact Submodule.mem_top⟩
  left_inv v := Subtype.ext rfl
  right_inv _ := rfl

def normalBundleTotalSpaceEquivTangentSpaceAt
    [Subsingleton N]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota)
    (x0 : N) (hdim : Module.finrank ℝ EN = 0) :
    h.NormalBundleTotalSpace ≃ TangentSpace I (iota x0) := by
  letI : Unique N :=
    { default := x0
      uniq := fun x ↦ Subsingleton.elim x x0 }
  refine (Equiv.uniqueSigma (fun x ↦ h.normalSpaceAt x)).trans ?_
  apply normalSpaceAtEquivTangentSpaceOfEqTop h x0
  exact h.normalSpaceAt_eq_top_of_derivative_eq_zero x0
    (h.mfderiv_eq_zero_of_finrank_eq_zero hdim x0)

end IsRiemannianIsometricImmersion
end DifferentialGeometry.Geometry
