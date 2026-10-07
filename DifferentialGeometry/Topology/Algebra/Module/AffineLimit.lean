import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

open scoped Topology

theorem ContinuousMap.map_add_smul_eq_of_tendsto
    {R E F ι : Type*} [Semiring R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousConstSMul R E]
    [AddCommGroup F] [Module R F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul R F] [T2Space F]
    [LocallyCompactPair E F]
    {l : Filter ι} [l.NeBot]
    {f : ι → C(E, F)} {g : C(E, F)}
    {x v : ι → E} {x₀ v₀ : E}
    (hf : Filter.Tendsto f l (𝓝 g))
    (hx : Filter.Tendsto x l (𝓝 x₀))
    (hv : Filter.Tendsto v l (𝓝 v₀))
    (hline : ∀ t : R, ∀ᶠ i in l,
      f i (x i + t • v i) = f i (x i) + t • (f i (x i + v i) - f i (x i))) :
    ∀ t : R, g (x₀ + t • v₀) = g x₀ + t • (g (x₀ + v₀) - g x₀) := by
  intro t
  have hleft := hf.eval (hx.add (hv.const_smul t))
  have hbase := hf.eval hx
  have hstep := hf.eval (hx.add hv)
  have hright := hbase.add ((hstep.sub hbase).const_smul t)
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright (hline t)

theorem ContinuousMap.map_add_smul_eq_of_tendsto_homothety
    {E F ι : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] [T2Space F]
    [LocallyCompactPair E F]
    {l : Filter ι} [l.NeBot]
    (h : C(E, F)) (p z : E) (s : ι → ℝ)
    {f : ι → C(E, F)} {H : C(E, F)}
    (hpencil : ∀ (v : E) (t : ℝ), h (p + t • v) = h p + t • (h (p + v) - h p))
    (hs : Filter.Tendsto s l Filter.atTop)
    (hzoom : ∀ (i : ι) (w : E),
      f i w = h z + s i • (h (z + (s i)⁻¹ • (w - z)) - h z))
    (hlim : Filter.Tendsto f l (𝓝 H)) :
    ∀ (x : E) (t : ℝ), H (x + t • (z - p)) = H x + t • (H (x + (z - p)) - H x) := by
  intro x
  let v : ι → E := fun i => (z - p) + (s i)⁻¹ • (x - z)
  have hv : Filter.Tendsto v l (𝓝 (z - p)) := by
    simpa only [v, Function.comp_def, zero_smul, add_zero] using
      (tendsto_const_nhds (x := z - p)).add
        ((tendsto_inv_atTop_zero.comp hs).smul_const (x - z))
  apply ContinuousMap.map_add_smul_eq_of_tendsto hlim tendsto_const_nhds hv
  intro t
  apply Filter.Eventually.of_forall
  intro i
  change f i (x + t • v i) = f i x + t • (f i (x + v i) - f i x)
  have harg (q : ℝ) : z + (s i)⁻¹ • (x + q • v i - z) =
      p + (1 + (s i)⁻¹ * q) • v i := by
    dsimp only [v]
    module
  have hpoint (q : ℝ) : f i (x + q • v i) =
      h z + s i • (h p + (1 + (s i)⁻¹ * q) • (h (p + v i) - h p) - h z) := by
    rw [hzoom, harg, hpencil]
  have hzero := hpoint 0
  have hone := hpoint 1
  simp only [zero_smul, add_zero] at hzero
  simp only [one_smul] at hone
  rw [hpoint t, hzero, hone]
  module

theorem ContinuousMap.affine_direction_of_tendsto_homothety
    {K E F ι : Type*} [DivisionRing K]
    [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul K F] [T2Space F]
    {l : Filter ι} [l.NeBot]
    (h : E → F) (z v : E) (s : ι → K)
    {f : ι → C(E, F)} {H : C(E, F)}
    (hparallel : ∀ (x : E) (t : K),
      h (x + t • v) = h x + t • (h (x + v) - h x))
    (hzoom : ∀ (i : ι) (w : E),
      f i w = h z + s i • (h (z + (s i)⁻¹ • (w - z)) - h z))
    (hlim : Filter.Tendsto f l (𝓝 H)) :
    ∀ (x : E) (t : K), H (x + t • v) = H x + t • (H (x + v) - H x) := by
  have hline (i : ι) (x : E) (t : K) :
      f i (x + t • v) = f i x + t • (f i (x + v) - f i x) := by
    by_cases ha : s i = 0
    · simp only [hzoom, ha, zero_smul, add_zero, sub_self, smul_zero]
    · let y := z + (s i)⁻¹ • (x - z)
      let D := h (y + v) - h y
      let c := h z + s i • (h y - h z)
      have hcoef (q : K) : s i * ((s i)⁻¹ * q) = q := by
        rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      have harg (q : K) : z + (s i)⁻¹ • (x + q • v - z) =
          y + ((s i)⁻¹ * q) • v := by
        dsimp only [y]
        rw [show x + q • v - z = (x - z) + q • v by abel,
          smul_add, smul_smul, add_assoc]
      have hpoint (q : K) : f i (x + q • v) = c + q • D := by
        rw [hzoom, harg, hparallel]
        change h z + s i • (h y + ((s i)⁻¹ * q) • D - h z) = c + q • D
        rw [show h y + ((s i)⁻¹ * q) • D - h z =
          (h y - h z) + ((s i)⁻¹ * q) • D by abel,
          smul_add, smul_smul, hcoef, ← add_assoc]
      have hzero := hpoint 0
      have hone := hpoint 1
      simp only [zero_smul, add_zero] at hzero
      simp only [one_smul] at hone
      rw [hpoint t, hzero, hone, add_sub_cancel_left]
  intro x t
  exact tendsto_nhds_unique_of_eventuallyEq (hlim.eval_const (x + t • v))
    ((hlim.eval_const x).add
      (((hlim.eval_const (x + v)).sub (hlim.eval_const x)).const_smul t))
    (Filter.Eventually.of_forall (fun i => hline i x t))
