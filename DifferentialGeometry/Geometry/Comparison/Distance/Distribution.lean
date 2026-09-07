import DifferentialGeometry.Analysis.Elliptic.WeakLaplacian
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lipschitz.Basic
import DifferentialGeometry.Geometry.Comparison.Distance.RadialPairing
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DifferentialGeometry.Geometry.Operator
open Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [finiteE : FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [t2M : T2Space M]
  [sigmaM : SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional Real E] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem edist_real_tri [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (x y z : M) :
    (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal +
        (riemannianEDist I y z).toReal := by
  have hxy : riemannianEDist I x y ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x y
  have hyz : riemannianEDist I y z ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) y z
  have htri : riemannianEDist I x z ≤
      riemannianEDist I x y + riemannianEDist I y z :=
    Manifold.riemannianEDist_triangle
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  rwa [ENNReal.toReal_add hxy hyz] at hreal

omit [FiniteDimensional Real E] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem dist_pole_lip [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (p x y : M) :
    |(riemannianEDist I p x).toReal -
        (riemannianEDist I p y).toReal| ≤
      (riemannianEDist I x y).toReal := by
  have hxy := edist_real_tri (I := I) p y x
  have hyx := edist_real_tri (I := I) p x y
  have hcomm : (riemannianEDist I y x).toReal =
      (riemannianEDist I x y).toReal :=
    congrArg ENNReal.toReal Manifold.riemannianEDist_comm
  rw [hcomm] at hxy
  rw [abs_le]
  constructor <;> linarith

include finiteE t2M sigmaM in
omit [I.Boundaryless] in
private theorem dist_real_cont [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (p : M) :
    Continuous (fun y : M => (riemannianEDist I p y).toReal) := by
  have hed : Continuous (fun y : M => riemannianEDist I p y) :=
    (continuous_riemannianEDist_to (I := I) p).congr
      (fun _ => Manifold.riemannianEDist_comm)
  apply continuousOn_univ.mp
  refine ENNReal.continuousOn_toReal.comp' hed.continuousOn ?_
  intro y _
  exact riemannianEDist_ne_top (I := I) p y

omit [I.Boundaryless] in
theorem locallyIntegrable_dist [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    LocallyIntegrable (fun y : M => (riemannianEDist I p y).toReal)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let : IsLocallyFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  exact (dist_real_cont (I := I) p).locallyIntegrable

omit [I.Boundaryless] in
theorem locallyIntegrableOn_inv_dist [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (c : Real) :
    LocallyIntegrableOn
      (fun y : M => c / (riemannianEDist I p y).toReal) {p}ᶜ
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let : IsLocallyFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  have hρ := dist_real_cont (I := I) p
  have hρ0 : ∀ y ∈ ({p}ᶜ : Set M),
      (riemannianEDist I p y).toReal ≠ 0 := by
    intro y hy
    apply ne_of_gt
    apply ENNReal.toReal_pos
    · intro hzero
      have hne : y ≠ p := by simpa only [mem_compl_iff, mem_singleton_iff] using hy
      exact hne (riemannianEDist_eq_zero_imp_eq (I := I) p y hzero).symm
    · exact riemannianEDist_ne_top (I := I) p y
  have hcont : ContinuousOn
      (fun y : M => c / (riemannianEDist I p y).toReal) {p}ᶜ :=
    continuousOn_const.div hρ.continuousOn hρ0
  exact hcont.locallyIntegrableOn isClosed_singleton.measurableSet.compl

theorem dist_green_identity
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M) :
    let ρ : M → Real := fun y => (riemannianEDist I p y).toReal
    let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      gradG (I := I) g φ
    Integrable (tangentSectionAction (I := I) X ρ)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, ρ x * ΔG (I := I) g φ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        -∫ x, tangentSectionAction (I := I) X ρ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let ρ : M → Real := fun y => (riemannianEDist I p y).toReal
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradG (I := I) g φ
  have hX : HasCompactSupport X :=
    hasCompactSupport_grad_g (I := I) g φ hφ
  have hρ : ∀ x y, edist (ρ x) (ρ y) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) x y)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [ρ] using dist_pole_lip (I := I) p x y)
  have hgreen :=
    integrable_tangentSectionAction_and_integral_eq_neg_integral_smul_divergence_of_lipschitz
      (I := I) g X hX hρ
  refine ⟨hgreen.1, ?_⟩
  change (∫ x, ρ x * ΔG (I := I) g φ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    -∫ x, tangentSectionAction (I := I) X ρ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)
  have hdiv : ∀ x : M,
      divergenceG (I := I) g X x = ΔG (I := I) g φ x := by
    intro x
    change divergenceG (I := I) g (gradG (I := I) g φ) x = _
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
    congrArg (fun z : Real => ρ x * z) (hdiv x))] at hgreen
  linarith [hgreen.2]

omit [I.Boundaryless] in
theorem exists_dist_bounds_on_tsupport
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (p : M) (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφp : tsupport (φ : M → Real) ⊆ {p}ᶜ) :
    ∃ a R : Real, 0 < a ∧ a ≤ R ∧
      ∀ y ∈ tsupport (φ : M → Real),
        a ≤ (riemannianEDist I p y).toReal ∧
          (riemannianEDist I p y).toReal ≤ R := by
  let ρ : M → Real := fun y => (riemannianEDist I p y).toReal
  have hρ_cont : Continuous ρ := by
    simpa only [ρ] using dist_real_cont (I := I) p
  have hK : IsCompact (tsupport (φ : M → Real)) := hφ
  by_cases hKne : (tsupport (φ : M → Real)).Nonempty
  · obtain ⟨ymin, hymin, hmin⟩ :=
      hK.exists_isMinOn hKne hρ_cont.continuousOn
    obtain ⟨ymax, hymax, hmax⟩ :=
      hK.exists_isMaxOn hKne hρ_cont.continuousOn
    have hymin_ne : ymin ≠ p := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hφp hymin
    have hρmin : 0 < ρ ymin := by
      apply ENNReal.toReal_pos
      · intro hzero
        exact hymin_ne
          (riemannianEDist_eq_zero_imp_eq (I := I) p ymin hzero).symm
      · exact riemannianEDist_ne_top (I := I) p ymin
    refine ⟨ρ ymin, ρ ymax, hρmin, ?_, ?_⟩
    · exact (isMinOn_iff.mp hmin) ymax hymax
    · intro y hy
      exact ⟨(isMinOn_iff.mp hmin) y hy,
        (isMaxOn_iff.mp hmax) y hy⟩
  · refine ⟨1, 1, zero_lt_one, le_rfl, ?_⟩
    have hempty : tsupport (φ : M → Real) = ∅ :=
      not_nonempty_iff_eq_empty.mp hKne
    intro y hy
    rw [hempty] at hy
    have : False := (Set.mem_empty_iff_false y).mp hy
    exact this.elim

end DifferentialGeometry.Geometry.Riemannian
