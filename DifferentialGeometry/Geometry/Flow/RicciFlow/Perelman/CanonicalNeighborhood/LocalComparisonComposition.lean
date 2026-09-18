import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialErrorTower
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]


private local instance localComparisonComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem MetricComparisonOn.exists_trans_on_compact
    {h : ℝ → SmoothRiemannianMetric I N} {k : ℝ → SmoothRiemannianMetric I3 P}
    {g : ℝ → SmoothRiemannianMetric I3 M}
    (Phi : PartialDiffeomorph I I3 N P ∞) (F : PartialDiffeomorph I3 I3 P M ∞)
    (U : TopologicalSpace.Opens N) {V : Set P} {times : Set ℝ}
    (hU : (U : Set N) ⊆ Phi.source) (hV : V ⊆ F.source) (hUV : MapsTo Phi U V)
    {order order' : ℕ} {alpha eps : ℝ}
    (C : MetricComparisonOn h k Phi U times order alpha)
    (C' : MetricComparisonOn k g F V times order' eps)
    (horder : order ≤ order') (heps : 0 ≤ eps) (halpha : 0 < alpha)
    (hsmall : alpha ≤ backgroundJetSmallness E order)
    (hC : ∀ b s, s ∈ times → UniqueDiffWithinAt ℝ times s → ∀ y ∈ U,
      ∀ v : Fin 2 → TangentSpace I y,
        DifferentiableWithinAt ℝ (fun a => C.jet b a y v) times s)
    (hC' : ∀ b s, s ∈ times → ∀ z ∈ Phi '' (U : Set N),
      ∀ v : Fin 2 → TangentSpace I3 z,
        DifferentiableWithinAt ℝ (fun a => C'.jet b a z v) times s)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U) :
    Nonempty (MetricComparisonOn h g (fun y => F (Phi y)) K times order
      (alpha + backgroundJetConstant E order * ((order : ℝ) + 1) * eps)) := by
  obtain ⟨chi, hchi, _hcompact, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I) hK U.isOpen hKU
  obtain ⟨W, hWopen, hKW, hWone⟩ := mem_nhdsSet_iff_exists.mp hone
  let W' : TopologicalSpace.Opens N := ⟨W ∩ U, hWopen.inter U.isOpen⟩
  have hW'U : (W' : Set N) ⊆ U := inter_subset_right
  have hKW' : K ⊆ W' := subset_inter hKW hKU
  have hone' : EqOn chi (fun _ => 1) W' := fun y hy => hWone hy.1
  obtain ⟨T⟩ := TransportedErrorTower.nonempty_of_partial_pullback C' h Phi U W'
    hU hW'U hUV chi hchi hsupp hone' (C.mono hW'U le_rfl le_rfl)
    horder heps halpha hsmall hC'
  exact ⟨((C.mono hW'U le_rfl le_rfl).trans C' T
    (fun _ hy => hUV (hW'U hy))
    (fun _ hy => Phi.mdifferentiableAt (by simp) (hU (hW'U hy)))
    (fun _ hy => F.mdifferentiableAt (by simp) (hV (hUV (hW'U hy))))
    (fun b s hs hu y hy v => hC b s hs hu y (hW'U hy) v)).mono hKW' le_rfl le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
