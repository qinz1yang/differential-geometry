import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PartialTensorPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialJetBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonJetDerivative

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance partialErrorSourceC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance partialErrorTargetC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

omit [T2Space M] [SigmaCompactSpace M] in
theorem TransportedErrorTower.nonempty_of_partial_pullback
    {k : ℝ → SmoothRiemannianMetric I3 P} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : P → M} {V : Set P} {times : Set ℝ} {order' : ℕ} {eps : ℝ}
    (c : MetricComparisonOn k g F V times order' eps)
    (h : ℝ → SmoothRiemannianMetric J N) (Phi : PartialDiffeomorph J I3 N P ∞)
    (U W : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ Phi.source)
    (hWU : (W : Set N) ⊆ U) (hUV : MapsTo Phi U V)
    (chi : N → ℝ) (hchi : ContMDiff J 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ (U : Set N)) (hone : EqOn chi (fun _ => 1) W)
    {order : ℕ} {alpha : ℝ} (c₁ : MetricComparisonOn h k Phi W times order alpha)
    (horder : order ≤ order') (heps : 0 ≤ eps)
    (halpha : 0 < alpha) (hsmall : alpha ≤ backgroundJetSmallness E order)
    (hdiff : ∀ b s, s ∈ times → ∀ z ∈ Phi '' (U : Set N),
      ∀ v : Fin 2 → TangentSpace I3 z,
        DifferentiableWithinAt ℝ (fun a => c.jet b a z v) times s) :
    Nonempty (TransportedErrorTower c h Phi W times order
      (backgroundJetConstant E order * ((order : ℝ) + 1))) := by
  have himage : Phi '' (U : Set N) ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hUV hy
  have hjet : ∀ b s, s ∈ times → ∀ z ∈ Phi '' (U : Set N),
      HasDerivWithinAt (fun a => c.jet b a z) (c.jet (b + 1) s z) times s := by
    intro b s hs z hz
    exact c.hasDerivWithinAt_jet hs (himage hz) (hdiff b s hs z hz)
  obtain ⟨B, hvalue, _hout, hderiv⟩ :=
    DifferentialGeometry.exists_partial_pullback_tensor_time_tower Phi U hU c.jet
      chi hchi hsupp times hjet
  have hvalueCore (b : ℕ) (s : ℝ) (y : N) (hy : y ∈ W)
      (v : Fin 2 → TangentSpace J y) :
      B b s y v = c.jet b s (Phi y) (fun q => mfderiv J I3 Phi y (v q)) := by
    rw [hvalue b s y (hWU hy) v, hone hy, one_mul]
  refine ⟨{
    tower := B
    zero_eq := hvalueCore 0
    succ_eq := ?_
    differentiableWithinAt := ?_
    close := ?_ }⟩
  · intro b s hs y hy v
    by_cases hu : UniqueDiffWithinAt ℝ times s
    · have hh := (tensor0SEvalCLM (I := J) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
        s (hderiv b s hs y)
      exact (hh.derivWithin hu).symm
    · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hu]
      rw [hvalueCore (b + 1) s y hy v, c.jet_succ b s hs (Phi y) (hUV (hWU hy))]
      exact derivWithin_zero_of_not_uniqueDiffWithinAt hu
  · intro b s hs _hu y _hy v
    exact ((tensor0SEvalCLM (I := J) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
      s (hderiv b s hs y)).differentiableWithinAt
  · intro a b hab s hs y hy
    have hale : a ≤ order := by omega
    have hchange := tensor02CovDerivNormWith_le_of_partial_pullback_comparison
      Phi W (hWU.trans hU) c₁ halpha hsmall hs (c.jet b s) (B b s)
      (hvalueCore b s) hale hy
    have hterm : ∀ j ∈ Finset.range (a + 1),
        tensor02CovDerivNormWith j (c.jet b s) (k s) (k s) (Phi y) ≤ eps := by
      intro j hj
      have hjle : j ≤ a := by have := Finset.mem_range.mp hj; omega
      exact c.close j b (by omega) s hs (Phi y) (hUV (hWU hy))
    have hsum : (∑ j ∈ Finset.range (a + 1),
        tensor02CovDerivNormWith j (c.jet b s) (k s) (k s) (Phi y)) ≤
          ((a : ℝ) + 1) * eps := by
      have hh := Finset.sum_le_card_nsmul (Finset.range (a + 1)) _ eps hterm
      rw [Finset.card_range, nsmul_eq_mul] at hh
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    have hcast : ((a : ℝ) + 1) * eps ≤ ((order : ℝ) + 1) * eps := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hale 1) heps
    calc
      _ ≤ backgroundJetConstant E order * ((a : ℝ) + 1) * eps := by
        exact hchange.trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
            (backgroundJetConstant_pos E order).le)
      _ ≤ backgroundJetConstant E order * ((order : ℝ) + 1) * eps := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcast
          (backgroundJetConstant_pos E order).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
