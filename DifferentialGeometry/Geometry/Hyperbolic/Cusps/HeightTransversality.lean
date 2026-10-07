import DifferentialGeometry.Geometry.Hyperbolic.Cusps.TangentGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.Cusps.HeightDistance
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance

noncomputable section
open scoped Manifold ContDiff Bundle ENNReal Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

universe u v
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem deriv_height_ne_zero_of_captured_geodesic_in_cusp
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g) (x₀ : M)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞) (o : M)
    {R A ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hmargin : 2 * A < R)
    (hε : ε ≤ 1 / 100)
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g o R) p ε g gTarget)
    (γ : C(ℝ, N))
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn gTarget γ (Set.Icc (0 : ℝ) 1))
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1)
    (hcaptured : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (riemannianClosedBallOf gTarget (Φ o) A))
    (height : M → ℝ) (hbase : γ 0 = Φ o)
    (hseparation : ENNReal.ofReal 1 ≤ riemannianEDistOf gTarget (γ 0) (γ 1)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
      letI : T3Space M := inferInstance
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
      let ρ := normalizedUniversalCoverDeckRepresentation g hg (-1 / 4) (by norm_num) x₀ hsec i
      let σ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρ
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (Nat.le_add_left 1 2) σ.range r)
        (ξ : D.centers),
      riemannianClosedBallOf g o (2 * A) ⊆
        (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i) ''
          {z : H₃ | Busemann.busemann ξ.val z < D.level ξ} →
      (∀ z : H₃, Busemann.busemann ξ.val z < D.level ξ →
        height (normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i z) =
          2 * Busemann.busemann ξ.val z) →
      Metric.ediam (pH '' Busemann.horosphere ξ.val (height o / 2)) ≤ ENNReal.ofReal (1 / 10) →
      deriv (fun t => height (Φ.symm (γ t))) 0 ≠ 0 := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num)) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  intro r D ξ hcollar hheight hdiam hzero
  let pH := normalizedUniversalCoverProjection g hg (-1 / 4) (by norm_num) x₀ hsec i
  have hsep : ENNReal.ofReal 1 ≤ riemannianEDistOf gTarget (Φ o) (γ 1) := by
    simpa only [hbase] using hseparation
  have hA : 0 ≤ A := by
    have h := hsep.trans (hcaptured (by simp : (1 : ℝ) ∈ Set.Icc 0 1))
    exact (ENNReal.ofReal_pos.mp ((ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1)).trans_le h)).le
  have hAone : 1 ≤ A := by
    have h := hsep.trans (hcaptured (by simp : (1 : ℝ) ∈ Set.Icc 0 1))
    exact (ENNReal.ofReal_le_ofReal_iff hA).mp h
  have hR : 0 < R := by linarith
  have hsmallR : (13 / 30 : ℝ) < R := by linarith
  have hoK : o ∈ riemannianClosedBallOf g o R := by
    change riemannianEDistOf g o o ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact zero_le
  have hbaseinv : Φ.symm (γ 0) = o := by
    rw [hbase]
    exact Φ.left_inv (hΦ.1 hoK)
  have hb := abs_sub_height_le_of_captured_tangent_geodesic_in_cusp
    g hg x₀ hsec gTarget Φ o hp hA hmargin hε hΦ γ hγ hgeo hunit hcaptured height hzero
      i D ξ hcollar hheight
  rw [hbaseinv] at hb
  have hend := PartialDiffeomorph.inverse_mem_closedBall_of_metric_approximation
    g gTarget Φ o hA hmargin (hε.trans (by norm_num : (1 / 100 : ℝ) ≤ 3 / 4))
      (hg.closedEBall_isCompact o R) hΦ (γ 1) (hcaptured (by simp))
  have hoC : o ∈ pH '' {z : H₃ | Busemann.busemann ξ.val z < D.level ξ} := by
    apply hcollar
    change riemannianEDistOf g o o ≤ ENNReal.ofReal (2 * A)
    rw [riemannianEDistOf_self]
    exact zero_le
  obtain ⟨x, hx, hxo⟩ := hoC
  obtain ⟨y, hy, hya⟩ := hcollar hend.2.2
  have hBx : height (pH x) = 2 * Busemann.busemann ξ.val x := hheight x hx
  have hBy : height (pH y) = 2 * Busemann.busemann ξ.val y := hheight y hy
  have hlevel : Busemann.busemann ξ.val x = height o / 2 := by
    rw [hxo] at hBx
    linarith
  have hdiam' : Metric.ediam (pH '' Busemann.horosphere ξ.val (Busemann.busemann ξ.val x)) ≤
      ENNReal.ofReal (1 / 10) := by rwa [hlevel]
  have hh : (Real.sqrt (-(-1 / 4 : ℝ)))⁻¹ *
      |Busemann.busemann ξ.val y - Busemann.busemann ξ.val x| ≤ (1 / 3 : ℝ) := by
    have hb' : |height (pH y) - height (pH x)| ≤ 1 / 3 := by rwa [hxo, hya]
    rw [hBy, hBx, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hb'
    norm_num [Real.sqrt_div]
    exact hb'
  have hdist : riemannianEDistOf g o (Φ.symm (γ 1)) ≤ ENNReal.ofReal (13 / 30) := by
    have h := edist_normalizedUniversalCoverProjection_le_of_ediam_horosphere_le
      g hg (-1 / 4) (by norm_num) x₀ hsec i ξ.val x y (by norm_num : (0 : ℝ) ≤ 1 / 10)
        hdiam' hh
    change riemannianEDistOf g (pH x) (pH y) ≤ ENNReal.ofReal ((1 / 10 : ℝ) + 1 / 3) at h
    rw [hxo, hya] at h
    norm_num only [show (1 / 10 : ℝ) + 1 / 3 = 13 / 30 by norm_num] at h
    exact h
  have hεpos : 0 < ε := hΦ.epsilon_pos
  have hLpos : 0 < Real.sqrt (1 + ε) := Real.sqrt_pos.mpr (by linarith)
  have hupper (z : M) (hz : z ∈ riemannianClosedBallOf g o R) (v : TangentSpace I z) :
      gTarget.inner (Φ z) (mfderiv I I Φ z v) (mfderiv I I Φ z v) ≤
        (Real.sqrt (1 + ε)) ^ 2 * g.inner z v v := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 + ε)]
    exact (hΦ.quadratic_bounds hz v).2
  have hdistR : riemannianEDistOf g o (Φ.symm (γ 1)) < ENNReal.ofReal R :=
    hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hsmallR)
  have hforward := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    g gTarget Φ o (Φ.symm (γ 1)) hR hLpos hΦ.1 hupper hdistR
  have hright : (Φ : M → N) (Φ.symm (γ 1)) = γ 1 := Φ.right_inv hend.1
  have hforward' : riemannianEDistOf gTarget (Φ o) (γ 1) ≤
      ENNReal.ofReal (Real.sqrt (1 + ε)) * riemannianEDistOf g o (Φ.symm (γ 1)) :=
    (congrArg (riemannianEDistOf gTarget (Φ o)) hright).symm.trans_le hforward
  have hLle : Real.sqrt (1 + ε) ≤ (11 / 10 : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith
  have hnum : Real.sqrt (1 + ε) * (13 / 30 : ℝ) < 1 := by nlinarith
  have hlt : riemannianEDistOf gTarget (Φ o) (γ 1) < ENNReal.ofReal 1 := by
    apply (hforward'.trans (mul_le_mul' le_rfl hdist)).trans_lt
    rw [← ENNReal.ofReal_mul hLpos.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hnum
  exact (not_lt_of_ge hsep) hlt

end DifferentialGeometry.Geometry.Hyperbolic
