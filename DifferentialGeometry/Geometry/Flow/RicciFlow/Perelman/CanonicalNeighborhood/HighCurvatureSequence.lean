import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

noncomputable def highCurvatureInterval {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) : RealTimeInterval :=
  RealTimeInterval.closed (-(t i * S.scalar (t i) (x i))) 0
    (by
      have h1 : 0 < t i * S.scalar (t i) (x i) := mul_pos (htpos i) (hpos i)
      linarith)

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem highCurvatureInterval_carrier {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).carrier =
      Set.Icc (-(t i * S.scalar (t i) (x i))) 0 :=
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem highCurvatureInterval_regular {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).regular =
      Set.Ioo (-(t i * S.scalar (t i) (x i))) 0 :=
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem highCurvatureInterval_carrier_subset {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).carrier ⊆
      (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) (t i)
        (S.scalar (t i) (x i)) (htmem i)).carrier := by
  intro s hs
  have hQ : 0 < S.scalar (t i) (x i) := hpos i
  have htT : t i < T := (htmem i).2
  have hlow : 0 ≤ t i + s / S.scalar (t i) (x i) := by
    have h1 : -(t i * S.scalar (t i) (x i)) ≤ s := hs.1
    have h2 : -t i ≤ s / S.scalar (t i) (x i) := by
      rw [le_div_iff₀ hQ]
      nlinarith [h1]
    linarith
  have hhigh : t i + s / S.scalar (t i) (x i) < T := by
    have h1 : s ≤ 0 := hs.2
    have h2 : s / S.scalar (t i) (x i) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hQ.le
    linarith
  simpa only [parabolicInterval_carrier, parabolicTime, Set.mem_ofPred_eq,
    Set.mem_Ico] using ⟨hlow, hhigh⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem highCurvatureInterval_regular_subset {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).regular ⊆
      (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) (t i)
        (S.scalar (t i) (x i)) (htmem i)).regular := by
  intro s hs
  have hQ : 0 < S.scalar (t i) (x i) := hpos i
  have htT : t i < T := (htmem i).2
  have hlow : 0 < t i + s / S.scalar (t i) (x i) := by
    have h1 : -(t i * S.scalar (t i) (x i)) < s := hs.1
    have h2 : -t i < s / S.scalar (t i) (x i) := by
      rw [lt_div_iff₀ hQ]
      nlinarith [h1]
    linarith
  have hhigh : t i + s / S.scalar (t i) (x i) < T := by
    have h1 : s < 0 := hs.2
    have h2 : s / S.scalar (t i) (x i) < 0 := div_neg_of_neg_of_pos h1 hQ
    linarith
  simpa only [parabolicInterval_regular, parabolicTime, Set.mem_ofPred_eq,
    Set.mem_Ioo] using ⟨hlow, hhigh⟩

noncomputable def highCurvatureFlowSequence {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) : FlowSequence.{u} where
  interval i := highCurvatureInterval hT S x t htpos hpos i
  term i :=
    { M := M
      basepoint := x i
      S := (parabolicSolution (I := I3) (M := M) S (t i)
        (S.scalar (t i) (x i)) (hpos i) (htmem i)).timeRestrict
          (highCurvatureInterval hT S x t htpos hpos i)
      isSolution := isSolutionOn_timeRestrict (I := I3) (M := M)
        (parabolicSolution_isSolutionOn (I := I3) (M := M) S hS (t i)
          (S.scalar (t i) (x i)) (hpos i) (htmem i))
        (highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem i)
        (highCurvatureInterval_regular_subset hT S x t htpos hpos htmem i) }

@[simp] theorem highCurvatureFlowSequence_interval {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).interval i =
      highCurvatureInterval hT S x t htpos hpos i :=
  rfl

@[simp] theorem highCurvatureFlowSequence_basepoint {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).basepoint =
      x i :=
  rfl

@[simp] theorem highCurvatureFlowSequence_metric {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S.base.metric =
      rescaledMetric (I := I3) S (t i) (S.scalar (t i) (x i)) (hpos i) :=
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
