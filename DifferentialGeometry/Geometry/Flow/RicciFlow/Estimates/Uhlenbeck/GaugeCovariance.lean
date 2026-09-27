import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.MetricGauge
import DifferentialGeometry.Analysis.Calculus.FiniteDimension

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem ricci_ode_inner_self_eq_initial
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hflow : ∀ t ∈ J, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) J t)
    (x : M) (Z : ℝ → TangentSpace I x)
    (hZ : ∀ t ∈ J, HasDerivWithinAt Z (ricciSharp (I := I) (g t) x (Z t)) J t) :
    ∀ t ∈ J, (g t).inner x (Z t) (Z t) = (g t₀).inner x (Z t₀) (Z t₀) := by
  intro t ht
  let _ : ∀ y : M, NormedAddCommGroup (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
  let _ : ∀ y : M, NormedSpace ℝ (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hzero : ∀ r ∈ J, HasDerivWithinAt (fun s => (g s).inner x (Z s) (Z s)) 0 J r := by
    intro r hr
    have hgd : HasDerivWithinAt (fun s => (g s).inner x)
        ((-2 : ℝ) • ricciTensor (I := I) (g r) x) J r := by
      apply hasDerivWithinAt_clm_apply.mpr
      intro v
      apply hasDerivWithinAt_clm_apply.mpr
      intro w
      simpa only [smul_apply, smul_eq_mul] using hflow r hr x v w
    apply ((hgd.clm_apply (hZ r hr)).clm_apply (hZ r hr)).congr_deriv
    simp only [add_apply, smul_apply, smul_eq_mul, inner_ricciSharp, inner_ricciSharp_right]
    ring
  have hbound := hJ.convex.norm_image_sub_le_of_norm_hasDerivWithin_le hzero
    (fun r hr => by simp : ∀ r ∈ J, ‖(0 : ℝ)‖ ≤ (0 : ℝ)) ht₀ ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hbound))

theorem ricci_ode_unique_on_interval
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hflow : ∀ t ∈ J, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) J t)
    (x : M) (Z W : ℝ → TangentSpace I x)
    (hZ : ∀ t ∈ J, HasDerivWithinAt Z (ricciSharp (I := I) (g t) x (Z t)) J t)
    (hW : ∀ t ∈ J, HasDerivWithinAt W (ricciSharp (I := I) (g t) x (W t)) J t)
    (hinit : Z t₀ = W t₀) : Set.EqOn Z W J := by
  let _ : NormedAddCommGroup (TangentSpace I x) := Tensor0SBundle.tangentSpaceNormedAddCommGroup x
  let _ : NormedSpace ℝ (TangentSpace I x) := Tensor0SBundle.tangentSpaceNormedSpace x
  let Y := fun s => Z s - W s
  have hY : ∀ s ∈ J, HasDerivWithinAt Y (ricciSharp (I := I) (g s) x (Y s)) J s := by
    intro s hs
    exact ((hZ s hs).sub (hW s hs)).congr_deriv
      (map_sub (ricciSharp (I := I) (g s) x) _ _).symm
  have hY₀ : Y t₀ = 0 := sub_eq_zero.mpr hinit
  intro t ht
  have he := ricci_ode_inner_self_eq_initial hJ ht₀ g hflow x Y hY t ht
  simp only [hY₀, map_zero] at he
  have hzero : Y t = 0 := by
    by_contra hn
    exact (ne_of_gt ((g t).pos x (Y t) hn)) he
  exact sub_eq_zero.mp hzero

theorem ricci_ode_equiv_eq_comp_initial
    {V W : M → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hflow : ∀ t ∈ J, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) J t)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ℝ → ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (hι : ∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (g t) x (ι t x v)) J t)
    (hκ : ∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => κ s x v)
      (ricciSharp (I := I) (g t) x (κ t x v)) J t) :
    let U := fun x => (κ t₀ x).trans (ι t₀ x).symm
    ∀ t ∈ J, ∀ x, κ t x = (U x).trans (ι t x) := by
  intro U t ht x
  ext v
  exact ricci_ode_unique_on_interval hJ ht₀ g hflow x
    (fun s => κ s x v) (fun s => ι s x (U x v))
    (hκ x v) (hι x (U x v))
    ((ι t₀ x).apply_symm_apply (κ t₀ x v)).symm ht

end DifferentialGeometry.PDE.RicciFlow
