import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PathLengthFlow_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Length agrees with ambient length for a path in an open submanifold. -/
theorem pathLength_restrictOpen_CX2 {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] (g : SmoothRiemannianMetric ThreeModel M)
    (U : TopologicalSpace.Opens M) (γ : ℝ → U)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) :
    metricPathELength (g.restrictOpen U) γ 0 1 =
      metricPathELength g ((Subtype.val : U → M) ∘ γ) 0 1 := by
  rw [metricPathELength_eq, metricPathELength_eq]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s _
  dsimp only
  rw [mfderiv_comp_apply s ((contMDiff_subtype_val (I := ThreeModel) (n := ∞) (U := U)).mdifferentiableAt (by simp))
    (hγ.mdifferentiableAt (by norm_num))]
  rw [DifferentialGeometry.mfderiv_subtype_val]
  rfl

/-- The terminal limit supplies a closed-interval solution on its actual
regular open; the ambient compact stage is not extended through singular points. -/
def terminalPathSolution_CX2 {P : OrientedThreeStage.{u}} {a b : ℝ}
    {G : P.IncomingSlab a b} (L : G.TerminalLimitMetric) :
    SolutionOn (I := ThreeModel) (M := G.terminalRegularOpen) (RealTimeInterval.closed a b G.lt.le) :=
  { base := { metric := L.extendedMetric } }

theorem terminalPathSolution_isSolution_CX2 {P : OrientedThreeStage.{u}} {a b : ℝ}
    {G : P.IncomingSlab a b} (L : G.TerminalLimitMetric) :
    IsSolutionOn (terminalPathSolution_CX2 L) := by
  apply isSolutionOn_of_joint_metric (RealTimeInterval.closed a b G.lt.le)
    (uniqueDiffOn_Icc G.lt) L.extendedMetric (L.extendedMetric_jointContMDiffOn le_rfl G.lt)
  intro t ht x v w
  exact (L.extendedMetric_hasDerivAt ht x v w).hasDerivWithinAt

/-- Backward path estimates with terminal-limit data at a singular top time.
Only the moving ambient R-ball is assumed controlled before the top time. -/
theorem incoming_path_estimate_CX2 {P : OrientedThreeStage.{u}} {a b : ℝ}
    (G : P.IncomingSlab a b) (L : G.TerminalLimitMetric)
    {c K ℓ R : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ)
    (γ : ℝ → G.terminalRegularOpen) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hlen : metricPathELength L.metric γ 0 1 ≤ ENNReal.ofReal ℓ)
    (hroom : Real.exp (9 * K * (b - c)) * ℓ < R)
    (hterminal : ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S L.metric (γ z) 4 (metricRm04At L.metric (γ z))) ≤ K)
    (hRm : ∀ t ∈ Ico c b, ∀ x ∈ riemannianBallOf (G.flow.base.metric t) (γ 0).val R,
      Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x)) ≤ K) :
    ∀ t ∈ Ico c b,
      metricPathELength (G.flow.base.metric t) ((Subtype.val : G.terminalRegularOpen → P.Carrier) ∘ γ) 0 1 ≤
        ENNReal.ofReal (Real.exp (9 * K * (b - t))) * metricPathELength L.metric γ 0 1 ∧
      ∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (G.flow.base.metric t) (γ z).val 4 (G.flow.base.rm04 t (γ z).val)) ≤ K := by
  let S := terminalPathSolution_CX2 L
  have hS := terminalPathSolution_isSolution_CX2 L
  have hcarrier : Icc c b ⊆ (RealTimeInterval.closed a b G.lt.le).carrier :=
    fun _ ht => ⟨hac.trans ht.1, ht.2⟩
  have hregular : Ioo c b ⊆ (RealTimeInterval.closed a b G.lt.le).regular :=
    fun _ ht => ⟨hac.trans_lt ht.1, ht.2⟩
  have htop : S.base.metric b = L.metric := L.extendedMetric_terminal
  have hconditional : ∀ t ∈ Icc c b,
      metricPathELength (S.base.metric t) γ 0 1 < ENNReal.ofReal R →
      ∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (S.base.metric t) (γ z) 4 (S.base.rm04 t (γ z))) ≤ K := by
    intro t ht hshort z hz
    rcases lt_or_eq_of_le ht.2 with htb | heqb
    · have heq : S.base.metric t = (G.flow.base.metric t).restrictOpen G.terminalRegularOpen :=
        L.extendedMetric_before htb
      have hlenEq : metricPathELength (S.base.metric t) γ 0 1 =
          metricPathELength (G.flow.base.metric t) (Subtype.val ∘ γ) 0 1 := by
        rw [heq]
        exact pathLength_restrictOpen_CX2 _ _ _ hγ
      have hγval : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (Subtype.val ∘ γ) :=
        (contMDiff_subtype_val (n := 1)).comp hγ
      have hd := edistOf_le_metricPathELength (G.flow.base.metric t) hz.1
        (hγval.contMDiffOn.mono (Icc_subset_Icc le_rfl hz.2))
      have hball : (γ z).val ∈ riemannianBallOf (G.flow.base.metric t) (γ 0).val R :=
        (hd.trans (metricPathELength_mono _ _ le_rfl hz.2)).trans_lt (hlenEq ▸ hshort)
      have hrm := hRm t ⟨ht.1, htb⟩ (γ z).val hball
      change Real.sqrt (normSq0S (S.base.metric t) (γ z) 4
        (metricRm04At (S.base.metric t) (γ z))) ≤ K
      rw [heq, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
      exact hrm
    · subst t
      change Real.sqrt (normSq0S (S.base.metric b) (γ z) 4
        (metricRm04At (S.base.metric b) (γ z))) ≤ K
      rw [htop]
      exact hterminal z hz
  have hresult := pathLength_first_exit_CX2 S hS hcb hK hℓ hcarrier hregular γ hγ
    (htop.symm ▸ hlen) hroom hconditional
  intro t ht
  obtain ⟨hL, _, hcurv⟩ := hresult t ⟨ht.1, ht.2.le⟩
  have heq : S.base.metric t = (G.flow.base.metric t).restrictOpen G.terminalRegularOpen :=
    L.extendedMetric_before ht.2
  rw [heq, pathLength_restrictOpen_CX2 _ _ _ hγ, htop] at hL
  refine ⟨hL, ?_⟩
  intro z hz
  have h := hcurv z hz
  change Real.sqrt (normSq0S (S.base.metric t) (γ z) 4
    (metricRm04At (S.base.metric t) (γ z))) ≤ K at h
  rwa [heq, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen] at h

end GC.LongTime.Ch12
