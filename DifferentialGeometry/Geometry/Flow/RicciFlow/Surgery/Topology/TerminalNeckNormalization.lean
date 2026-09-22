import DifferentialGeometry.Geometry.Neck.ScaleComparison
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckSourceBounds
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVaryingChartConvergence

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Scalar

open DifferentialGeometry.Geometry.Curvature

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps δ t : ℝ} {x : M}

theorem StrongNeck.scalar_upper_bound_neckBuffer (nk : StrongNeck S eps x t)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (z : neckBuffer δ) :
    S.scalar t (nk.map z.val) ≤ (1 + 4323 * eps) * S.scalar t x := by
  obtain ⟨V, Φ, hmap, hbound⟩ := nk.exists_neckBuffer_pullback_bound hfit
  let C : Geometry.Neck.cylindricalChart I3 (M := M) :=
    { domain := neckBuffer δ
      target := V
      chart := Φ
      scale := S.scalar t x
      scale_pos := nk.Q_pos }
  have hinv : (2 : ℝ) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ nk.eps_pos).2
    linarith [nk.eps_small]
  have hceil : 2 ≤ Nat.ceil eps⁻¹ := by
    exact_mod_cast hinv.trans (Nat.le_ceil eps⁻¹)
  have hclose : C.metricCloseOn (S.base.metric t) eps Set.univ := by
    intro y _ j hj
    change metricDerivNorm j
      (Diffeomorph.pullbackMetricCross
        (scaleMetric (S.scalar t x) nk.Q_pos ((S.base.metric t).restrictOpen V)) Φ)
      _ _ y ≤ eps
    rw [Diffeomorph.pullbackMetricCross_scaleMetric,
      ← roundCylinderMetric_eq_geometry]
    exact hbound j (hj.trans hceil) y
  have hscalar := C.scalar_comparison_of_metricCloseOn (S.base.metric t) eps
    (by linarith [nk.eps_small]) hclose (Φ z : M)
    ⟨Φ z, ⟨z, Set.mem_univ _, rfl⟩, rfl⟩
  have hu := (abs_le.mp hscalar).2
  change metricScalarAt (S.base.metric t) (Φ z : M) / S.scalar t x - 1 ≤
    4323 * eps at hu
  rw [hmap] at hu
  apply (div_le_iff₀ nk.Q_pos).mp
  change metricScalarAt (S.base.metric t) (nk.map z.val) / S.scalar t x ≤ _
  linarith

end Scalar

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem StrongNeck.exists_terminal_neckBuffer_pullback_bound
    (G : P.IncomingSlab a s) {eps δ t : ℝ} {x : G.terminalRegularOpen}
    (nk : StrongNeck G.flow eps x.val t) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (hregular : ∀ z : neckBuffer δ, nk.map z.val ∈ G.terminalRegularRegion) :
    ∃ (V : TopologicalSpace.Opens G.terminalRegularOpen)
      (Φ : neckBuffer δ ≃ₘ⟮IC, I3⟯ V),
      (∀ z : neckBuffer δ, (Φ z).val.val = nk.map z.val) ∧
      ∀ j ≤ ⌈eps⁻¹⌉₊, ∀ z : neckBuffer δ,
        metricDerivNorm j
          (scaleMetric (G.flow.scalar t x.val) nk.Q_pos
            (Diffeomorph.pullbackMetricCross
              (((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).restrictOpen V) Φ))
          (Surgery.Topology.roundCylinderMetric.restrictOpen (neckBuffer δ))
          (Surgery.Topology.roundCylinderMetric.restrictOpen (neckBuffer δ)) z ≤ eps := by
  obtain ⟨W, Ψ, hmap, hbound⟩ := nk.exists_neckBuffer_pullback_bound hfit
  have hW : W ≤ G.terminalRegularOpen := by
    intro y hy
    obtain ⟨z, hz⟩ := Ψ.surjective ⟨y, hy⟩
    have hzy : (Ψ z : P.Carrier) = y := congrArg Subtype.val hz
    rw [← hzy, hmap]
    exact hregular z
  let V : TopologicalSpace.Opens G.terminalRegularOpen :=
    nestedOpen (U := G.terminalRegularOpen) (V := W)
  let Φ : neckBuffer δ ≃ₘ⟮IC, I3⟯ V := Ψ.trans (flatNestedDiffeo (I := I3) hW)
  have hderiv (z : neckBuffer δ) : mfderiv IC I3 Φ z = mfderiv IC I3 Ψ z := by
    have h₁ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := IC) (J := I3) Φ z
    have h₂ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := IC) (J := I3)
      (fun q => (Φ q).val) z
    have h₃ := DifferentialGeometry.mfderiv_subtypeVal_comp (I := IC) (J := I3) Ψ z
    rw [← h₁, ← h₂]
    exact h₃
  have hmetric : Diffeomorph.pullbackMetricCross
      (((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).restrictOpen V) Φ =
      Diffeomorph.pullbackMetricCross ((G.flow.base.metric t).restrictOpen W) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hderiv]
    rfl
  refine ⟨V, Φ, hmap, ?_⟩
  rw [hmetric]
  exact hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance terminalSigmaCompact : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private local instance terminalOpenSigmaCompact
    (V : TopologicalSpace.Opens G.terminalRegularOpen) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

private local instance pullbackCompleteSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

theorem TerminalLimitMetric.eventually_scalar_normalized_pullback_difference
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop (𝓝[<] s))
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    {Q : ℕ → ℝ} (hQ : ∀ n, 0 < Q n) {Qlim : ℝ}
    (hQlim : 0 < Qlim) (hscale : Tendsto Q atTop (𝓝 Qlim))
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    (V : ℕ → TopologicalSpace.Opens G.terminalRegularOpen)
    (Φ : ∀ n, X ≃ₘ⟮I, ThreeModel⟯ V n)
    (T : Set X) (hT : IsCompact T) (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hTU : ∀ n, T ⊆ U n)
    (himage : ∀ᶠ n in atTop, ∀ x ∈ T,
      (Φ n x).1 ∈ K)
    (gRef : SmoothRiemannianMetric I X) (p : ℕ) :
    let gSource := fun n => Diffeomorph.pullbackMetricCross
      (((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen).restrictOpen (V n))
      (Φ n)
    (∀ᶠ n in atTop, ∀ x ∈ U n, ∀ j ≤ p,
      metricDerivNorm j (scaleMetric (Q n) (hQ n) (gSource n))
        gRef gRef x ≤ 1 / 4) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      metricDerivNormSupOn T p
        (scaleMetric (Q n) (hQ n) (gSource n))
        (scaleMetric (Qlim) hQlim
          (Diffeomorph.pullbackMetricCross (L.metric.restrictOpen (V n)) (Φ n))) gRef < ε := by
  intro gSource hclose ε hε
  have hrange : ∀ᶠ n in atTop, Qlim / 2 ≤ Q n ∧ Q n ≤ Qlim + 1 := by
    filter_upwards [hscale.eventually (Ioo_mem_nhds
      (show Qlim / 2 < Qlim by linarith) (lt_add_one Qlim))] with n hn
    exact ⟨hn.1.le, hn.2.le⟩
  obtain ⟨C, B, hC, hB, hcontrol⟩ :=
    exists_uniform_reference_bounds_of_scaled_metric_jets (I := I) (M := X)
      (qmax := Qlim + 1) p (half_pos hQlim)
  have hequiv : ∀ᶠ n in atTop, ∀ x ∈ U n, ∀ v : TangentSpace I x,
      C⁻¹ * (gSource n).inner x v v ≤ gRef.inner x v v ∧
        gRef.inner x v v ≤ C * (gSource n).inner x v v := by
    filter_upwards [hrange, hclose] with n hn hc
    exact (hcontrol (U n) (hU n) (gSource n) gRef (Q n) (hQ n) hn.1 hn.2 hc).1
  have hjets : ∀ᶠ n in atTop, ∀ x ∈ U n, ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (normSq0S gRef x (2 + j)
        (iterCov (gSource n) 2 (metricTensorField gRef) j x)) ≤ B := by
    filter_upwards [hrange, hclose] with n hn hc
    exact (hcontrol (U n) (hU n) (gSource n) gRef (Q n) (hQ n) hn.1 hn.2 hc).2
  have hterminal := L.eventually_metricDerivNormSupOn_varying_pullbacks hK hτ V Φ T U hU hTU
    himage gRef p hC hB (Q := fun _ => Qlim) (fun _ => hQlim)
    (Qmax := Qlim) (Eventually.of_forall fun _ => le_rfl) hequiv hjets
    (ε / 4) (by positivity)
  let Z := (1 + Real.sqrt (Module.finrank ℝ E : ℝ)) / (Qlim / 2)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hweight : Tendsto (fun n => |Q n - Qlim| * Z) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      (hscale.sub_const Qlim).abs.mul_const Z
  have hsmall : ∀ᶠ n in atTop, |Q n - Qlim| * Z < ε / 4 :=
    hweight.eventually_lt_const (by positivity)
  filter_upwards [hterminal, hclose, hrange, hsmall] with n ht hc hr hs
  let gTerm := Diffeomorph.pullbackMetricCross (L.metric.restrictOpen (V n)) (Φ n)
  have hcov : ∀ j ≤ p, ∀ x ∈ T, metricCovDerivNorm j (gSource n) gRef x ≤ Z := by
    intro j hj x hx
    have hb := covNorm_le_add j (scaleMetric (Q n) (hQ n) (gSource n)) gRef gRef x
    rw [metricCovDerivNorm_scaleMetric_left] at hb
    have hself : metricCovDerivNorm j gRef gRef x ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := by
      cases j with
      | zero => rw [metricCovDerivNorm_self_zero]
      | succ j => rw [covNorm_self_succ]; positivity
    have hscaled : Q n * metricCovDerivNorm j (gSource n) gRef x ≤
        1 + Real.sqrt (Module.finrank ℝ E : ℝ) := by
      have hpoint := hc x (hTU n hx) j hj
      linarith
    have hn : 0 ≤ metricCovDerivNorm j (gSource n) gRef x := Real.sqrt_nonneg _
    apply (le_div_iff₀ (half_pos hQlim)).mpr
    have hlow := mul_le_mul_of_nonneg_right hr.1 hn
    nlinarith
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall T p _ _ gRef (ε / 2)
    (half_pos hε).le ?_) (by linarith)
  intro j hj x hx
  have hchange : metricDerivNorm j (scaleMetric (Q n) (hQ n) (gSource n))
      (scaleMetric Qlim hQlim (gSource n)) gRef x < ε / 4 := by
    rw [metricDerivNorm_scaleMetric_same_metric]
    exact (mul_le_mul_of_nonneg_left (hcov j hj x hx) (abs_nonneg _)).trans_lt hs
  have hlim : metricDerivNorm j (scaleMetric Qlim hQlim (gSource n))
      (scaleMetric Qlim hQlim gTerm) gRef x < ε / 4 :=
    (derivNorm_le_sup hT hj _ _ _ hx).trans_lt ht
  have htri := metricDerivNorm_triangle j
    (scaleMetric (Q n) (hQ n) (gSource n)) (scaleMetric Qlim hQlim (gSource n))
    (scaleMetric Qlim hQlim gTerm) gRef x
  linarith

private local instance neckSigmaCompact (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)

theorem TerminalLimitMetric.eventually_normalizedNeck_of_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (neck : ∀ n, Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck G.flow eps x.1 (τ n))
    (hregular : ∀ n, ∀ z : neckBuffer δ,
      (neck n).map z.1 ∈ G.terminalRegularRegion)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, ∀ z ∈ neckClosedTest δ,
      (neck n).map z.1 ∈ Subtype.val '' K) :
    ∀ᶠ n in atTop, ∃ N : NormalizedNeck L.metric δ k,
      N.center = x ∧ N.sphereMark = (neck n).center ∧
        ∀ z, (N.chart z).1 = (neck n).map z.1 := by
  classical
  have hcharts := fun n => (neck n).exists_terminal_neckBuffer_pullback_bound
    G hfit (hregular n)
  choose V Φ hmap hsource using hcharts
  let gC := Surgery.Topology.roundCylinderMetric.restrictOpen (neckBuffer δ)
  let gSource := fun n => Diffeomorph.pullbackMetricCross
    (((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen).restrictOpen (V n))
    (Φ n)
  let Q := fun n => G.flow.scalar (τ n) x.1
  have hQ : ∀ n, 0 < Q n := fun n => (neck n).Q_pos
  let Qlim := metricScalarAt L.metric x
  have hscale : Tendsto Q atTop (𝓝 Qlim) := (L.tendsto_metricScalarAt x).comp hτ
  have himage : ∀ᶠ n in atTop, ∀ z ∈ neckClosedTest δ, (Φ n z).1 ∈ K := by
    filter_upwards [hcapture] with n hn
    intro z hz
    obtain ⟨y, hy, heq⟩ := hn z hz
    have hyΦ : (Φ n z).1 = y := Subtype.ext ((hmap n z).trans heq.symm)
    exact hyΦ.symm ▸ hy
  have heps : eps ≤ 1 / 4 := (neck 0).eps_small.le.trans (by norm_num)
  have hclose : ∀ᶠ n in atTop, ∀ z ∈ (univ : Set (neckBuffer δ)), ∀ j ≤ k,
      metricDerivNorm j (scaleMetric (Q n) (hQ n) (gSource n)) gC gC z ≤ 1 / 4 :=
    Eventually.of_forall fun n z _ j hj => (hsource n j (hj.trans hk) z).trans heps
  have hnorm := L.eventually_scalar_normalized_pullback_difference hτ hK hQ hx hscale
    V Φ (neckClosedTest δ) (isCompact_neckClosedTest δ) (fun _ => univ)
    (fun _ => isOpen_univ) (fun _ => subset_univ _) himage gC k hclose
    ((δ - eps) / 2) (by linarith)
  filter_upwards [hnorm] with n hn
  let gN := scaleMetric Qlim hx
    (Diffeomorph.pullbackMetricCross (L.metric.restrictOpen (V n)) (Φ n))
  have hterminal : metricDerivNormSupOn (neckClosedTest δ) k gN gC gC < δ := by
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall (neckClosedTest δ) k
      gN gC gC (eps + (δ - eps) / 2) (by have := (neck n).eps_pos; linarith) ?_)
      (by linarith)
    intro j hj z hz
    have ha := (derivNorm_le_sup (isCompact_neckClosedTest δ) hj
      (scaleMetric (Q n) (hQ n) (gSource n)) gN gC hz).trans hn.le
    have hb := hsource n j (hj.trans hk) z
    have ht := metricDerivNorm_triangle j gN
      (scaleMetric (Q n) (hQ n) (gSource n)) gC gC z
    rw [metricDerivNorm_symm j gN (scaleMetric (Q n) (hQ n) (gSource n)) gC z] at ht
    linarith
  let chart : C(neckBuffer δ, G.terminalRegularOpen) :=
    ⟨fun z => (Φ n z).1, continuous_subtype_val.comp (Φ n).continuous⟩
  have hchart : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ chart := by
    apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (contMDiff_subtype_val.comp (Φ n).contMDiff)
      (Subtype.val_injective.comp (Φ n).injective)
    · intro z
      change Function.Injective (mfderiv NeckCylinderModel ThreeModel
        (fun q => (Φ n q).1) z)
      rw [DifferentialGeometry.mfderiv_subtypeVal_comp]
      exact ((Φ n).isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) z).injective
    · simp [ThreeSpace]
  have hmarked : chart ⟨((neck n).center, 0), by
      have := inv_pos.mpr hδ
      constructor <;> linarith⟩ = x := by
    apply Subtype.ext
    exact (hmap n _).trans (neck n).center_eq
  let N : NormalizedNeck L.metric δ k :=
    { delta_pos := hδ
      delta_lt_one := hδ1
      sphereMark := (neck n).center
      center := x
      chart := chart
      chart_smooth := hchart
      marked := hmarked
      scale := Qlim
      scale_pos := hx
      scale_scalar := rfl
      normalizedMetric := gN
      normalized_inner := by
        intro z A B
        rw [scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner,
          SmoothRiemannianMetric.restrictOpen_inner]
        change Qlim * L.metric.inner (Φ n z).1
          (mfderiv NeckCylinderModel ThreeModel (Φ n) z A)
          (mfderiv NeckCylinderModel ThreeModel (Φ n) z B) = _
        change _ = Qlim * L.metric.inner (Φ n z).1
          (mfderiv NeckCylinderModel ThreeModel (fun q => (Φ n q).1) z A)
          (mfderiv NeckCylinderModel ThreeModel (fun q => (Φ n q).1) z B)
        rw [DifferentialGeometry.mfderiv_subtypeVal_comp]
        rfl
      closeness := hterminal }
  exact ⟨N, rfl, rfl, hmap n⟩

theorem TerminalLimitMetric.eventually_normalizedNeck_of_strongNecks_of_scalar_control
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (neck : ∀ n, Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck
      G.flow eps x.1 (τ n)) :
    ∀ᶠ n in atTop, ∃ N : NormalizedNeck L.metric δ k,
      N.center = x ∧ N.sphereMark = (neck n).center ∧
        ∀ z, (N.chart z).1 = (neck n).map z.1 := by
  classical
  let A := (1 + 4323 * eps) * (metricScalarAt L.metric x + 1)
  obtain ⟨Kold, hKold, hKregular, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch A
  let K : Set G.terminalRegularOpen := Subtype.val ⁻¹' Kold
  have himage : Subtype.val '' K = Kold := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKregular hy⟩, hy, rfl⟩
  have hK : IsCompact K := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hKold
  have hcenter : ∀ᶠ n in atTop,
      G.flow.scalar (τ n) x.1 < metricScalarAt L.metric x + 1 :=
    ((L.tendsto_metricScalarAt x).comp hτ).eventually_lt_const (lt_add_one _)
  have hlate : ∀ᶠ n in atTop, ∀ z : neckBuffer δ, (neck n).map z.1 ∈ Kold := by
    filter_upwards [hcenter, hτ.eventually (Ioo_mem_nhdsLT hd.2)] with n hn ht
    intro z
    apply hcapture (τ n) ht
    have hb := (neck n).scalar_upper_bound_neckBuffer hfit z
    exact hb.trans (mul_le_mul_of_nonneg_left hn.le
      (by have := (neck n).eps_pos; positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hlate
  have htail := L.eventually_normalizedNeck_of_strongNecks
    (hτ.comp (tendsto_add_atTop_nat n₀)) x hx hδ hδ1 hepsδ hfit k hk
    (fun n => neck (n + n₀))
    (fun n z => hKregular (hn₀ (n + n₀) (by omega) z)) hK
    (Eventually.of_forall fun n z _ => by
      rw [himage]
      exact hn₀ (n + n₀) (by omega) z)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp htail
  apply eventually_atTop.mpr
  refine ⟨n₀ + n₁, fun n hn => ?_⟩
  have heq : n - n₀ + n₀ = n := Nat.sub_add_cancel (by omega)
  have hresult := hn₁ (n - n₀) (by omega)
  have hresult' : ∃ N : NormalizedNeck L.metric δ k, N.center = x ∧ N.sphereMark = (neck n).center ∧
      ∀ z, (N.chart z).1 = (neck n).map z.1 := by
    obtain ⟨N, hN, hm, hc⟩ := hresult
    refine ⟨N, hN, ?_, ?_⟩
    · exact hm.trans (congrArg (fun i => (neck i).center) heq)
    · intro z
      exact (hc z).trans (congrArg (fun i => (neck i).map z.1) heq)
  exact hresult'

theorem TerminalLimitMetric.eventually_normalizedNeck_of_canonical_neighborhoods
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {q epsCanonical C1 C2 : ℝ} (hq : 0 < q)
    (hcanonical : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      Nonempty (Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness
        G.flow epsCanonical C1 C2 y t))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hepsδ : eps < δ)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (k : ℕ) (hk : k ≤ ⌈eps⁻¹⌉₊)
    (neck : ∀ n, Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck
      G.flow eps x.1 (τ n)) :
    ∀ᶠ n in atTop, ∃ N : NormalizedNeck L.metric δ k,
      N.center = x ∧ N.sphereMark = (neck n).center ∧
        ∀ z, (N.chart z).1 = (neck n).map z.1 := by
  let C : ℝ≥0 := ⟨max C2 0, le_max_right _ _⟩
  have hbound : ∀ y : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2 := by
    intro y t ht hy
    exact ((hcanonical y t ht hy).some.time_derivative).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  exact L.eventually_normalizedNeck_of_strongNecks_of_scalar_control hτ hq hbound
    hPhi hpinch x hx hδ hδ1 hepsδ hfit k hk neck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
