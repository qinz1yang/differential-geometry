import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessPullbackTimeTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ComparisonTimeJets


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

section ChainRule


theorem hasDerivWithinAt_rescaled_time_tower
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ℕ → ℝ → V) (t Q : ℝ) {J K : Set ℝ}
    (hmap : MapsTo (parabolicTime t Q) J K)
    (hA : ∀ q r, r ∈ K → HasDerivWithinAt (A q) (A (q + 1) r) K r)
    (q : ℕ) (s : ℝ) (hs : s ∈ J) :
    HasDerivWithinAt (fun r => (Q * Q⁻¹ ^ q) • A q (parabolicTime t Q r))
      ((Q * Q⁻¹ ^ (q + 1)) • A (q + 1) (parabolicTime t Q s)) J s := by
  have htime : HasDerivAt (parabolicTime t Q) Q⁻¹ s := by
    have hd := ((hasDerivAt_id s).div_const Q).const_add t
    simp only [one_div] at hd
    exact hd
  have hd := ((hA q (parabolicTime t Q s) (hmap hs)).scomp s
    htime.hasDerivWithinAt hmap).const_smul (Q * Q⁻¹ ^ q)
  simpa only [Function.comp_def, Pi.smul_def, smul_smul, pow_succ, mul_assoc] using hd

end ChainRule

section Fields

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private local instance normalizedTimeSourceC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance normalizedTimeTargetC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


def rescaledTensorTimeTower
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (t Q : ℝ) (q : ℕ) (s : ℝ) : Tensor0SField (I := I) (M := N) (n := ∞) 2 :=
  (Q * Q⁻¹ ^ q) • A q (parabolicTime t Q s)

omit [CompleteSpace E] [T2Space N] in
theorem hasDerivWithinAt_rescaledTensorTimeTower
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (t Q : ℝ) {J K : Set ℝ} (hmap : MapsTo (parabolicTime t Q) J K)
    (hA : ∀ q r, r ∈ K → ∀ y : N,
      HasDerivWithinAt (fun s => A q s y) (A (q + 1) r y) K r)
    (q : ℕ) (s : ℝ) (hs : s ∈ J) (y : N) :
    HasDerivWithinAt (fun r => rescaledTensorTimeTower A t Q q r y)
      (rescaledTensorTimeTower A t Q (q + 1) s y) J s := by
  have hd := hasDerivWithinAt_rescaled_time_tower (fun q r => A q r y) t Q hmap
    (fun q r hr => hA q r hr y) q s hs
  exact hd


theorem exists_uniform_rescaled_pullback_time_tower
    [I.Boundaryless] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (Phi : PartialDiffeomorph I I N M ∞)
    (chi : N → ℝ) (hchi : ContMDiff I 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ Phi.source) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2,
      (∀ t Q (hQ : 0 < Q) s, ∀ y ∈ Phi.source, ∀ v : Fin 2 → TangentSpace I y,
        rescaledTensorTimeTower A t Q 0 s y v =
          chi y * (rescaledMetric S t Q hQ s).inner (Phi y)
            (mfderiv I I Phi y (v 0)) (mfderiv I I Phi y (v 1))) ∧
      ∀ t Q (J : Set ℝ), MapsTo (parabolicTime t Q) J (Icc c b) →
        ∀ q s, s ∈ J → ∀ y : N,
          HasDerivWithinAt (fun r => rescaledTensorTimeTower A t Q q r y)
            (rescaledTensorTimeTower A t Q (q + 1) s y) J s := by
  obtain ⟨A, hzero, _hout, hA⟩ := exists_closedWindow_pullback_metric_time_tower
    S hS hac hcb hslab hreg Phi chi hchi hsupp
  refine ⟨A, ?_, ?_⟩
  · intro t Q hQ s y hy v
    simp only [rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hzero _ y hy v,
      rescaledMetric, scaleMetric_inner]
    ring
  · intro t Q J hmap q s hs y
    exact hasDerivWithinAt_rescaledTensorTimeTower A t Q hmap hA q s hs y

end Fields

section Comparison

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance comparisonTowerC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace N] in
theorem quadratic_comparison_of_error_norm
    (g : SmoothRiemannianMetric I N)
    (P A : Tensor0SField (I := I) (M := N) (n := ∞) 2) (x : N) {eps : ℝ}
    (hzero : ∀ v : Fin 2 → TangentSpace I x,
      A x v = P x v - g.inner x (v 0) (v 1))
    (hbound : tensor02CovDerivNormWith (I := I) 0 A g g x ≤ eps)
    (v : TangentSpace I x) :
    (1 - eps) * g.inner x v v ≤ P x (fun _ => v) ∧
      P x (fun _ => v) ≤ (1 + eps) * g.inner x v v := by
  have hnonneg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]; simp
    · exact (g.pos x v hv).le
  have habs := abs_apply_le_norm0S g x 2 (A x) (fun _ => v)
  have hproduct : (∏ _j : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    simp only [Fin.prod_univ_two, Real.mul_self_sqrt hnonneg]
  rw [hproduct, hzero (fun _ => v)] at habs
  have hn : Real.sqrt (normSq0S (I := I) g x 2 (A x)) ≤ eps := hbound
  have hh := abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right hn hnonneg))
  constructor <;> nlinarith [hh.1, hh.2]

omit [T2Space M] [SigmaCompactSpace M] in
theorem MetricComparisonOn.jet_eq_of_genuine_towers
    {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : N → M} {U : Set N} {J : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U J order eps) (hJ : UniqueDiffOn ℝ J)
    (A B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (hA : ∀ q s, s ∈ J → ∀ y ∈ U,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ J → ∀ y ∈ U,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) J s)
    (hzero : ∀ s ∈ J, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I y,
      C.pullback s y v - (h s).inner y (v 0) (v 1) = A 0 s y v - B 0 s y v) :
    ∀ q s, s ∈ J → ∀ y ∈ U, C.jet q s y = A q s y - B q s y := by
  intro q s hs y hy
  ext v
  apply derivWithin_tower_eq_of_genuine hJ
    (fun j r => C.jet j r y v) (fun j r => A j r y v - B j r y v)
    (fun j r hr => C.jet_succ j r hr y hy v) ?_ ?_ q s hs
  · intro j r hr
    exact ((tensor0SEvalCLM (I := I) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
      r (hA j r hr y hy)).sub
      ((tensor0SEvalCLM (I := I) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
        r (hB j r hr y hy))
  · intro r hr
    exact (C.jet_zero r y v).trans (hzero r hr y hy v)

end Comparison

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
