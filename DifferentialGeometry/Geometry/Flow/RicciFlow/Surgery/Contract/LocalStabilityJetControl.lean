import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.LocalStabilityRepair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ReducedLengthRealization
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry (SmoothRiemannianMetric)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem not_isCommonLocalRealizationOnAdmissibleStrips_of_vanishingStability :
    ¬ (IsLocalStabilityVanishingInput ∧ isBufferedControlInput.{u} ∧
        isReducedLengthRealizationInput.{u} ∧ isJacobianInput.{u} ∧
        (∃ d : OldData, isOldTubeInput.{u} d) ∧ isEnlargementInput.{u} ∧
        isRoundDegreeInput.{u}) :=
  fun h => not_isLocalStabilityVanishingInput_of_roundSphereShrink h.1

def localStabilityPointwiseVanishing
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, 4 ≤ m → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i → ∀ r : ℝ, ∀ hr : r ≤ L i,
      ∀ u ∈ Set.Icc (0 : ℝ) (v i), ∀ a : ℕ, a ≤ m →
        ∀ x : ↥(ModelBall r), (x : ThreeSpace) ∈ A →
          metricDerivNorm (I := ThreeModel) (M := ↥(ModelBall r)) a
            (((ℓ i).base.metric u).restrictOpenOfSubset (modelBall_mono hr))
            ((γ.restrictOpen (ModelBall r))) ((γ.restrictOpen (ModelBall r))) x ≤ ε

def IsLocalStabilityPointwiseVanishingInput : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 → ∀ (K : ℝ), 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
            ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityPointwiseVanishing L v hv γ ℓ

theorem isLocalStabilityInput_of_pointwiseVanishingInput
    (h : IsLocalStabilityPointwiseVanishingInput) : isLocalStabilityInput :=
  fun θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet =>
    localStabilityCauchyConclusion_of_staticJetLimit
      (h θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet)

theorem metricDerivNorm_restrictOpenOfSubset_le_of_supOn_le
    {L r : ℝ} (hr : r ≤ L) {A : Set ThreeSpace} {m : ℕ}
    {g : SmoothRiemannianMetric ThreeModel ↥(ModelBall L)}
    {γ : SmoothRiemannianMetric ThreeModel ThreeSpace} {ε : ℝ}
    (hbdd : BddAbove {s : ℝ | ∃ a : ℕ, a ≤ m ∧ ∃ x : ↥(ModelBall L),
      (x : ThreeSpace) ∈ A ∧
        metricDerivNorm (I := ThreeModel) a g (γ.restrictOpen (ModelBall L))
          (γ.restrictOpen (ModelBall L)) x = s})
    (hsup : metricDerivNormSupOn (Subtype.val ⁻¹' A) m g (γ.restrictOpen (ModelBall L))
      (γ.restrictOpen (ModelBall L)) ≤ ε) :
    ∀ a : ℕ, a ≤ m → ∀ x : ↥(ModelBall r), (x : ThreeSpace) ∈ A →
      metricDerivNorm (I := ThreeModel) a (g.restrictOpenOfSubset (modelBall_mono hr))
        (γ.restrictOpen (ModelBall r)) (γ.restrictOpen (ModelBall r)) x ≤ ε := by
  let : SigmaCompactSpace ↥(ModelBall L) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_of_isOpen ThreeModel (ModelBall L).isOpen)
  have hγ : γ.restrictOpen (ModelBall r) =
      (γ.restrictOpen (ModelBall L)).restrictOpenOfSubset (modelBall_mono hr) :=
    (SmoothRiemannianMetric.restrictOpen_flat (I := ThreeModel) γ
      (modelBall_mono hr)).symm
  intro a ha x hx
  rw [hγ, metricDerivNorm_flat (I := ThreeModel) (modelBall_mono hr) g
    (γ.restrictOpen (ModelBall L)) (γ.restrictOpen (ModelBall L)) a x]
  exact (le_csSup hbdd ⟨a, ha, TopologicalSpace.Opens.inclusion (modelBall_mono hr) x,
    hx, rfl⟩).trans hsup

def localStabilityReferenceJetBounded
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
    (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set ThreeSpace, IsCompact A → ∀ m : ℕ, ∀ i : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) (v i),
    BddAbove {s : ℝ | ∃ a : ℕ, a ≤ m ∧ ∃ x : ↥(ModelBall (L i)),
      (x : ThreeSpace) ∈ A ∧
        metricDerivNorm (I := ThreeModel) a ((ℓ i).base.metric u)
          (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) x = s}

def IsLocalStabilityReferenceJetBoundedInput : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 → ∀ (K : ℝ), 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric ThreeModel ThreeSpace)
      (ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (metricRm04At (I := ThreeModel) (M := ↥(ModelBall (L i)))
            ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityReferenceJetBounded L v hv γ ℓ

theorem localStabilityPointwiseVanishing_of_vanishing_of_referenceJetBounded
    {L : ℕ → ℝ} {v : ℕ → ℝ} {hv : ∀ i, 0 < v i}
    {γ : SmoothRiemannianMetric ThreeModel ThreeSpace}
    {ℓ : (i : ℕ) → SolutionOn (I := ThreeModel) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))}
    (hb : localStabilitySlabDerivativeBound L v hv γ ℓ)
    (hbdd : localStabilityReferenceJetBounded L v hv γ ℓ)
    (h : localStabilityConclusion L v hv γ ℓ) :
    localStabilityPointwiseVanishing L v hv γ ℓ := by
  intro A hA m hm ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((h A hA m hm).eventually (Iio_mem_nhds (half_pos hε)))
  refine ⟨N, fun i hi r hr u hu a ha x hx => ?_⟩
  have hsup : metricDerivNormSupOn (Subtype.val ⁻¹' A) m ((ℓ i).base.metric u)
      (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i))) ≤ ε :=
    (le_csSup (bddAbove_localStabilityIccValues hb A hA m hm i)
      ⟨u, hu, rfl⟩).trans ((le_of_lt (hN i hi)).trans (le_of_lt (half_lt_self hε)))
  exact metricDerivNorm_restrictOpenOfSubset_le_of_supOn_le hr (hbdd A hA m i u hu) hsup
    a ha x hx

theorem isLocalStabilityInput_of_windowSlabInput_of_slabDerivativeBoundInput_of_referenceJetBounded
    (hb : IsLocalStabilitySlabDerivativeBoundInput) {δ : ℝ} (hδ : 0 < δ)
    (hbdd : IsLocalStabilityReferenceJetBoundedInput)
    (h : IsLocalStabilityWindowSlabInput δ) : isLocalStabilityInput :=
  fun θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet =>
    localStabilityCauchyConclusion_of_staticJetLimit
      (localStabilityPointwiseVanishing_of_vanishing_of_referenceJetBounded
        (hb θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet)
        (hbdd θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet)
        (isLocalStabilityVanishingInput_of_windowSlabInput_of_slabDerivativeBoundInput
          hb hδ h θ hθ hθ1 K hK L hLpos hLtop v hv hvθ γ ℓ hsol hcurv hjet))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
