import DifferentialGeometry.Geometry.Comparison.Soul.NormalExponential
import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundleCompactness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
  {S : Set M}

local notation "FB" => (Fin (maxSliceDim I S) → ℝ)
local notation "FN" => (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
local notation "ν" => TotalSpace FN (normalBundleFiber (I := I) g S)

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem dist_normalExp_le_length (z : ν) :
    dist z.proj.1 (normalExp (I := I) g hEnorm S z) ≤
      Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm z.proj.1 z.snd.1
    (s := (0 : ℝ)) (t := 1) zero_le_one
  rw [intrinsicGeodesic_zero, ← expMapIntrinsic_def,
    ← IsRiemannianManifold.out (I := I), edist_dist] at h
  simp only [sub_zero, mul_one] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp h

theorem exists_normalExp_injOn_disk (hcompact : IsCompact S)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    ∃ ε > 0, Set.InjOn (normalExp (I := I) g hEnorm S)
      {z : ν | Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε} := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let f : ν → M := normalExp (I := I) g hEnorm S
  let L : ν → ℝ := fun z => Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)
  by_contra hnone
  have hbad : ∀ n : ℕ, ∃ z w : ν,
      L z < 1 / ((n : ℝ) + 1) ∧ L w < 1 / ((n : ℝ) + 1) ∧
        f z = f w ∧ z ≠ w := by
    intro n
    have hn : ¬Set.InjOn f {z : ν | L z < 1 / ((n : ℝ) + 1)} := by
      intro hi
      exact hnone ⟨1 / ((n : ℝ) + 1), by positivity, hi⟩
    unfold Set.InjOn at hn
    push Not at hn
    obtain ⟨z, hz, w, hw, heq, hne⟩ := hn
    exact ⟨z, w, hz, hw, heq, hne⟩
  choose z w hz hw heq hne using hbad
  have hzlen : Tendsto (fun n => L (z n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => Real.sqrt_nonneg _) (fun n => (hz n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hwlen : Tendsto (fun n => L (w n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => Real.sqrt_nonneg _) (fun n => (hw n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hdist_bound (n : ℕ) :
      dist (z n).proj.1 (w n).proj.1 ≤ L (z n) + L (w n) := by
    calc
      dist (z n).proj.1 (w n).proj.1 ≤
          dist (z n).proj.1 (f (z n)) + dist (f (z n)) (w n).proj.1 :=
        dist_triangle _ _ _
      _ ≤ L (z n) + L (w n) := by
        apply add_le_add (dist_normalExp_le_length g hEnorm (z n))
        rw [heq n, dist_comm]
        exact dist_normalExp_le_length g hEnorm (w n)
  have hdist : Tendsto (fun n => dist (z n).proj.1 (w n).proj.1) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) hdist_bound (by simpa only [zero_add] using hzlen.add hwlen)
  obtain ⟨p, hp, φ, hφ, hzp⟩ :=
    hcompact.tendsto_subseq (fun n => (z n).proj.2)
  let pS : S := ⟨p, hp⟩
  have hwp : Tendsto (fun n => (w (φ n)).proj.1) atTop (𝓝 p) :=
    hzp.congr_dist (hdist.comp hφ.tendsto_atTop)
  have hzlim : Tendsto (z ∘ φ) atTop (𝓝 (⟨pS, 0⟩ : ν)) :=
    tendsto_normal_zero_of_tendsto_length g hEnorm hcompact hconv hB
      (z ∘ φ) pS hzp (hzlen.comp hφ.tendsto_atTop)
  have hwlim : Tendsto (w ∘ φ) atTop (𝓝 (⟨pS, 0⟩ : ν)) :=
    tendsto_normal_zero_of_tendsto_length g hEnorm hcompact hconv hB
      (w ∘ φ) pS hwp (hwlen.comp hφ.tendsto_atTop)
  have hlocal : IsLocalDiffeomorphAt (𝓘(ℝ, FB).prod 𝓘(ℝ, FN)) I ∞ f
      (⟨pS, 0⟩ : ν) :=
    normalExp_isLocalDiffeomorphAt_zero g hEnorm hconv hB pS
  obtain ⟨Φ, hpΦ, hEqΦ⟩ := hlocal
  have hzΦ : ∀ᶠ n in atTop, z (φ n) ∈ Φ.source :=
    hzlim (Φ.open_source.mem_nhds hpΦ)
  have hwΦ : ∀ᶠ n in atTop, w (φ n) ∈ Φ.source :=
    hwlim (Φ.open_source.mem_nhds hpΦ)
  obtain ⟨n, hzn, hwn⟩ := (hzΦ.and hwΦ).exists
  apply hne (φ n)
  apply Φ.toPartialEquiv.injOn hzn hwn
  rw [← hEqΦ hzn, ← hEqΦ hwn]
  exact heq (φ n)

end DifferentialGeometry.Geometry.Topology

end
