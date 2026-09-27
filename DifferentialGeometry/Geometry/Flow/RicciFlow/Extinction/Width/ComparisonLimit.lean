import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

private theorem le_liminf_of_eventually_le_mul {α : Type*} {l : Filter α} [l.NeBot]
    {a : ℝ≥0∞} {v m : α → ℝ≥0∞} (hm : Tendsto m l (𝓝 1))
    (h : ∀ᶠ s in l, a ≤ m s * v s) : a ≤ liminf v l := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc => ?_
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul]
    exact bot_le
  have hcinv : (1 : ℝ≥0∞) < c⁻¹ := ENNReal.one_lt_inv.mpr hc
  have hctop : c ≠ ⊤ := (hc.trans_le le_top).ne
  have hm' : ∀ᶠ s in l, m s ≤ c⁻¹ :=
    (hm.eventually (Iio_mem_nhds (show (1 : ℝ≥0∞) < c⁻¹ from hcinv))).mono
      fun _ hs => le_of_lt hs
  have h' : ∀ᶠ s in l, a ≤ c⁻¹ * v s :=
    (h.and hm').mono fun _ hs => hs.1.trans (mul_le_mul' hs.2 le_rfl)
  have hlim := Filter.le_liminf_of_le (f := l) (by isBoundedDefault) h'
  rw [ENNReal.liminf_const_mul_of_ne_top (ENNReal.inv_ne_top.mpr hc0)] at hlim
  calc c * a ≤ c * (c⁻¹ * liminf v l) := mul_le_mul' le_rfl hlim
    _ = (c * c⁻¹) * liminf v l := (mul_assoc _ _ _).symm
    _ = 1 * liminf v l := by rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = liminf v l := one_mul _

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
  [T2Space N] [CompactSpace N] [ConnectedSpace N]

theorem classWidth_le_liminf_of_lipschitzComparison
    (g : ℝ → SmoothRiemannianMetric ThreeModel M)
    (h : SmoothRiemannianMetric ThreeModel N)
    (ξ : FreeContractibleSphereClass M) (ξN : FreeContractibleSphereClass N)
    (f : ℝ → C(M, N)) {t : ℝ} (ell : ℝ → ℝ)
    (hell : Tendsto ell (𝓝[<] t) (𝓝 1))
    (hclass : ∀ᶠ s in 𝓝[<] t,
      FreeHomotopyClass.map (contractibleLoopPostcompose (f s)) ξ = ξN)
    (hlip : ∀ᶠ s in 𝓝[<] t, 0 ≤ ell s ∧ ∀ x y,
      riemannianEDistOf h (f s x) (f s y) ≤
        ENNReal.ofReal (ell s) * riemannianEDistOf (g s) x y) :
    ENNReal.ofReal (classWidth h ξN) ≤
      liminf (fun s => ENNReal.ofReal (classWidth (g s) ξ)) (𝓝[<] t) := by
  have hm : Tendsto (fun s => ENNReal.ofReal ((ell s) ^ 2)) (𝓝[<] t) (𝓝 1) := by
    simpa only [Function.comp_def, one_pow, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hell.pow 2)
  have hbase : ∀ᶠ s in 𝓝[<] t, ENNReal.ofReal (classWidth h ξN) ≤
      ENNReal.ofReal ((ell s) ^ 2) * ENNReal.ofReal (classWidth (g s) ξ) := by
    filter_upwards [hlip, hclass] with s hs hcls
    let L : ℝ≥0 := ⟨ell s, hs.1⟩
    have hf : ∀ x y, riemannianEDistOf h (f s x) (f s y) ≤
        (L : ℝ≥0∞) * riemannianEDistOf (g s) x y := by
      have hcast : (L : ℝ≥0∞) = ENNReal.ofReal (ell s) := ENNReal.coe_nnreal_eq L
      intro x y
      rw [hcast]
      exact hs.2 x y
    have hw := rfs_width_lipschitz (g s) h (f s) L hf ξ
    rw [hcls] at hw
    have hL : (L : ℝ) = ell s := rfl
    rw [hL] at hw
    rw [← ENNReal.ofReal_mul (sq_nonneg (ell s))]
    exact ENNReal.ofReal_le_ofReal hw
  exact le_liminf_of_eventually_le_mul hm hbase

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
