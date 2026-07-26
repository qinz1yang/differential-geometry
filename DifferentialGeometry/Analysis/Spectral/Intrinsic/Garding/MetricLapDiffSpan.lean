import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffMeas
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricC1Continuity

/-!
# Compact-span moving scalar Laplacian

This file packages the fixed-scale moving scalar Laplacian on every requested
short backward interval in a compact regular-time slab.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- A compact regular-time slab has one backward radius on which the genuine
`H² → H⁰` scalar Laplacian perturbation is continuous, uniformly bounded,
and agrees with its finite spectral core on every requested interval. -/
theorem lapA20_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : Real, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : Real) ∈ Set.Icc a b →
        ∀ h : Real, 0 < h → h ≤ ρ → a ≤ (T : Real) - h →
          (∀ s ∈ Set.Icc (0 : Real) h, (T : Real) - s ∈ D.regular) ∧
          ContinuousOn
            (fun s : Real ↦ lapDiffA20 (I := I) (M := M) G T s)
            (Set.Icc (0 : Real) h) ∧
          ∃ C2 : NNReal,
            (∀ s ∈ Set.Icc (0 : Real) h,
              ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ (C2 : Real)) ∧
            ∀ s ∈ Set.Icc (0 : Real) h,
              ∀ v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)),
                tensorHsZeroEquivL2 (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) (G.metric (T : Real)) 0 0)
                    (lapDiffA20 (I := I) (M := M) G T s v.1) =
                  lapDiffCore (I := I) (M := M) (G.metric (T : Real))
                    (G.metric ((T : Real) - s)) v := by
  classical
  let d : Real := Module.finrank Real E
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  let ε : Real := 1 / (2 * d)
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  obtain ⟨ρ₀, hρ₀, hmetric⟩ :=
    HCGCompactness.metric_c1_span (I := I) G hG hab hε
  let ρ : Real := min 1 ρ₀
  have hρ : 0 < ρ := lt_min zero_lt_one hρ₀
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hρle : ρ ≤ ρ₀ := min_le_right _ _
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
        TensorL2 0 0 (G.metric (T : Real))) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
        tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hvar (s : Real) (hs : s ∈ Set.Icc (0 : Real) h) :
      (T : Real) - s ∈ Set.Icc a b := by
    constructor <;> linarith [hs.1, hs.2, hT.1, hT.2]
  have hdist (s : Real) (hs : s ∈ Set.Icc (0 : Real) h) :
      |((T : Real) - s) - (T : Real)| ≤ ρ₀ := by
    rw [show ((T : Real) - s) - (T : Real) = -s by ring, abs_neg,
      abs_of_nonneg hs.1]
    exact hs.2.trans (hhρ.trans hρle)
  have hmod (s : Real) (hs : s ∈ Set.Icc (0 : Real) h) :
      HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
          (G.metric ((T : Real) - s))
          (G.metric (T : Real)) (G.metric (T : Real)) ≤ ε :=
    hmetric (T : Real) hT (T - s) (hvar s hs) (hdist s hs)
  have hsmall (s : Real) (hs : s ∈ Set.Icc (0 : Real) h) :
      (Module.finrank Real E : Real) *
          HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
            (G.metric ((T : Real) - s))
            (G.metric (T : Real)) (G.metric (T : Real)) ≤
        (1 / 2 : Real) := by
    calc
      (Module.finrank Real E : Real) *
          HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1
            (G.metric ((T : Real) - s))
            (G.metric (T : Real)) (G.metric (T : Real)) ≤
          d * ε := by
            simpa only [d] using mul_le_mul_of_nonneg_left (hmod s hs) hd.le
      _ = 1 / 2 := by
        dsimp only [ε]
        field_simp [ne_of_gt hd]
  have hreg : ∀ s ∈ Set.Icc (0 : Real) h, (T : Real) - s ∈ D.regular := by
    intro s hs
    exact hab (hvar s hs)
  have hA2cont : ContinuousOn
      (fun s : Real ↦ lapDiffA2 (I := I) (M := M) G T s)
      (Set.Icc (0 : Real) h) :=
    lapDiffA2_cont (I := I) (M := M) G hG T hreg hsmall
  have hA20cont : ContinuousOn
      (fun s : Real ↦ lapDiffA20 (I := I) (M := M) G T s)
      (Set.Icc (0 : Real) h) :=
    lapDiffA20_cont_of (I := I) (M := M) G T hA2cont
  have hnorm : ContinuousOn
      (fun s : Real ↦ ‖lapDiffA20 (I := I) (M := M) G T s‖)
      (Set.Icc (0 : Real) h) :=
    continuous_norm.comp_continuousOn hA20cont
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hnorm
  let C2 : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hbound : ∀ s ∈ Set.Icc (0 : Real) h,
      ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ (C2 : Real) := by
    intro s hs
    change ‖lapDiffA20 (I := I) (M := M) G T s‖ ≤ max C 0
    exact (hC ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  have hcore : ∀ s ∈ Set.Icc (0 : Real) h,
      ∀ v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (G.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) G T s v.1) =
          lapDiffCore (I := I) (M := M) (G.metric (T : Real))
            (G.metric ((T : Real) - s)) v := by
    intro s hs v
    rw [lapDiffA20_apply, LinearIsometryEquiv.apply_symm_apply]
    simpa only [lapDiffA2] using
      lapDiffOp_core (I := I) (M := M)
        (G.metric (T : Real)) (G.metric ((T : Real) - s)) v (hsmall s hs)
  exact ⟨hreg, hA20cont, C2, hbound, hcore⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
