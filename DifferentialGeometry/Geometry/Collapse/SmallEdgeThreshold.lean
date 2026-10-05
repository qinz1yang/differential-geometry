import DifferentialGeometry.Geometry.Collapse.SmallEdgeRows
import DifferentialGeometry.Geometry.Collapse.SmallZeroRows
import DifferentialGeometry.Geometry.Collapse.EdgeRowThreshold
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

/-!
The outer edge threshold uses the actual canonical pullback bundle on the same small model.
All later edge data are pulled from the original source with their native quantifier order.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set Bundle Metric Function WithLp
open DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open GC.MetricGeometry
open scoped Manifold ContDiff NNReal ENNReal Topology

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3

section CanonicalBundles

variable {M : Type u} [mM : MetricSpace M] [cM : ChartedSpace E3 M]
  [sM : IsManifold I3 ∞ M] (S : SmallManifoldModel (I := I3) M)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

@[instance_reducible] def smallModel_edgeBundle (g : SmoothRiemannianMetric I3 M) :
    RiemannianBundle (fun x : S.Carrier => TangentSpace I3 x) :=
  ⟨(S.metric g).toRiemannianMetric⟩

theorem smallModel_edgeContinuous (g : SmoothRiemannianMetric I3 M) :
    letI _smallBundle := smallModel_edgeBundle S g
    IsContinuousRiemannianBundle E3 (fun x : S.Carrier => TangentSpace I3 x) := by
  let smallBundle := smallModel_edgeBundle S g
  exact ⟨⟨(S.metric g).inner, (S.metric g).contMDiff.continuous,
    fun x v w => rfl⟩⟩

theorem smallModel_edgeManifold (g : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    letI _smallMetric := S.metricSpace
    letI _smallBundle := smallModel_edgeBundle S g
    IsRiemannianManifold I3 S.Carrier := by
  let smallMetric := S.metricSpace
  let smallBundle := smallModel_edgeBundle S g
  let smallContinuous := smallModel_edgeContinuous S g
  have hnorm : IsMetricNorm (S.metric g) := isMetricNorm_of_riemannianBundle (S.metric g)
  refine ⟨fun x y => ?_⟩
  rw [← riemannianEDistOf_eq_riemannianEDist (S.metric g) hnorm,
    S.metric_aligned g hmetric, edist_dist]

theorem smallModel_gradient_all (g : SmoothRiemannianMetric I3 M)
    (F : M → ℝ) (x : S.Carrier) :
    gradFun (S.metric g) (F ∘ S.diffeo) x =
      (S.diffeo.mfderivToContinuousLinearEquiv (by simp) x).symm
        (gradFun g F (S.diffeo x)) := by
  by_cases hF : MDifferentiableAt I3 𝓘(ℝ, ℝ) F (S.diffeo x)
  · exact gradientFun_pullbackCross g S.diffeo F x hF
  · have hFS : ¬ MDifferentiableAt I3 𝓘(ℝ, ℝ) (F ∘ S.diffeo) x := by
      intro hFS
      have hback : MDifferentiableAt I3 𝓘(ℝ, ℝ) (F ∘ S.diffeo)
          (S.diffeo.symm (S.diffeo x)) := by
        simpa only [Diffeomorph.symm_apply_apply] using hFS
      have hcomp := hback.comp (S.diffeo x)
        (S.diffeo.symm.contMDiff.mdifferentiableAt (by simp))
      apply hF
      simpa only [Function.comp_def, Diffeomorph.apply_symm_apply] using hcomp
    have hzeroS : gradFun (S.metric g) (F ∘ S.diffeo) x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero (S.metric g) (F ∘ S.diffeo)
        (mfderiv_zero_of_not_mdifferentiableAt hFS)
    have hzeroM : gradFun g F (S.diffeo x) = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero g F
        (mfderiv_zero_of_not_mdifferentiableAt hF)
    rw [hzeroS, hzeroM, map_zero]

theorem smallModel_gradient_difference_inner (g : SmoothRiemannianMetric I3 M)
    (F G : M → ℝ) (x : S.Carrier) :
    (S.metric g).inner x
      (gradFun (S.metric g) (F ∘ S.diffeo) x - gradFun (S.metric g) (G ∘ S.diffeo) x)
      (gradFun (S.metric g) (F ∘ S.diffeo) x - gradFun (S.metric g) (G ∘ S.diffeo) x) =
      g.inner (S.diffeo x)
        (gradFun g F (S.diffeo x) - gradFun g G (S.diffeo x))
        (gradFun g F (S.diffeo x) - gradFun g G (S.diffeo x)) := by
  let d := S.diffeo.mfderivToContinuousLinearEquiv (by simp) x
  have hF : d (gradFun (S.metric g) (F ∘ S.diffeo) x) =
      gradFun g F (S.diffeo x) := by
    rw [smallModel_gradient_all]
    exact d.apply_symm_apply _
  have hG : d (gradFun (S.metric g) (G ∘ S.diffeo) x) =
      gradFun g G (S.diffeo x) := by
    rw [smallModel_gradient_all]
    exact d.apply_symm_apply _
  rw [S.metric_inner]
  rw [← S.diffeo.mfderivToContinuousLinearEquiv_coe (by simp)]
  change g.inner (S.diffeo x) (d (_ - _)) (d (_ - _)) = _
  rw [map_sub, hF, hG]

omit sM in
def smallModel_edgeFibreHomeomorph (O : TopologicalSpace.Opens S.Carrier)
    (Δ : ℝ) (F f ρ : M → ℝ) :
    {y : O // (f ∘ S.diffeo) y = 0 ∧
      0 ≤ 4 * Δ - edgeRowHeight Δ (F ∘ S.diffeo) (ρ ∘ S.diffeo) y} ≃ₜ
    {y : S.diffeo '' (O : Set S.Carrier) // f y = 0 ∧
      0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} :=
  (S.diffeo.toHomeomorph.image (O : Set S.Carrier)).subtype (fun _y => Iff.rfl)

end CanonicalBundles

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem edgeSourceSlab_disk_bundle_threshold_smallSources {Δ σ ε μ τ : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30)
    (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ (M : Type u) [_iEdge0 : MetricSpace M] [_iEdge1 : ChartedSpace E3 M]
        [_iEdge2 : IsManifold 𝓘(ℝ, E3) ∞ M]
        [_iEdge3 : SigmaCompactSpace M] [_iEdge4 : T2Space (TangentBundle 𝓘(ℝ, E3) M)]
        [_iEdge5 : CompleteSpace M]
        [_iEdge6 : ConnectedSpace M]
        [_iEdge7 : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [_iEdge8 : IsRiemannianManifold 𝓘(ℝ, E3) M]
        [_iEdge9 : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p b⁻¹, SectionalBoundedBelowAt g y (-b ^ 2)) →
        ∀ (Y : Type) [_iEdge10 : MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b)
          (Q : M → WithLp 2 (ℝ × ℝ)) (E : Set M) (F f ρ : M → ℝ) (OF Of : Set M),
        (∀ z, (Q z).fst = (α.toFun z).fst) → Q p = 0 →
        (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
          |dist (Q x) (Q y) - dist x y| ≤ τ * Δ) →
        (∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd) →
        (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
          ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ) →
        IsClosed E → p ∈ E →
        (∀ a ∈ E ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
        (∀ t : ℝ, |t| ≤ 100 * Δ →
          ∃ a ∈ E ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
        (∀ x, |F x - infDist x E| < μ * Δ) →
        IsOpen OF →
        closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ} ⊆ OF →
        ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F OF →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g E y,
            Real.sqrt (g.inner y (gradFun g F y + u) (gradFun g F y + u)) < ε) →
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ},
          Real.sqrt (g.inner y (gradFun g (fun z => F z / ρ z) y - gradFun g F y)
            (gradFun g (fun z => F z / ρ z) y - gradFun g F y)) ≤ 100 * Δ * Λ) →
        (∀ x ∈ ball p (20 * Δ), infDist x E < 41 / 4 * Δ →
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ F ρ) x) →
        LipschitzWith Λ ρ → ρ p = 1 → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ)) →
        IsOpen Of → closedBall p (100 * Δ) ⊆ Of → ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f Of →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| < μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x x') = x' →
          |mvfderiv 𝓘(ℝ, E3) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∃ S : SmallManifoldModel (I := I3) M,
        letI _smallMetric := S.metricSpace
        letI _smallBundle := smallModel_edgeBundle S g
        letI _smallContinuous := smallModel_edgeContinuous S g
        letI _smallRiemannian := smallModel_edgeManifold S g
          (fun a b => riemannianEDistOf_eq_ofReal_dist g hEnorm a b)
        let pS := S.diffeo.symm p
        let FS := F ∘ S.diffeo
        let fS := f ∘ S.diffeo
        let ρS := ρ ∘ S.diffeo
        ∃ O₀ : TopologicalSpace.Opens M,
        ∃ O : TopologicalSpace.Opens S.Carrier,
        (O₀ : Set M) = S.diffeo '' (O : Set S.Carrier) ∧
        (O₀ : Set M) ⊆ ball p (20 * Δ) ∧
        (∀ y ∈ ball p (100 * Δ), |f y| ≤ 4 * Δ →
          edgeRowHeight Δ F ρ y ≤ 4 * Δ → y ∈ O₀) ∧
        (O : Set S.Carrier) ⊆ ball pS (20 * Δ) ∧
        (∀ y ∈ ball pS (100 * Δ), |fS y| ≤ 4 * Δ → edgeRowHeight Δ FS ρS y ≤ 4 * Δ → y ∈ O) ∧
        ∀ (a₀ b₀ : ℝ), -(4 * Δ) < a₀ → ∀ (h0 : (0 : ℝ) ∈ Ioo a₀ b₀), b₀ < 4 * Δ →
        letI _productCharts := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
        letI _productSmooth : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
        ∃ (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => fS y))
          (hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
            (fun y : O => 4 * Δ - edgeRowHeight Δ FS ρS y))
          (hreg : ∀ y : O, fS y = 0 → 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y →
            Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => fS y) y))
          (hregb : ∀ y : O, fS y = 0 → 4 * Δ - edgeRowHeight Δ FS ρS y = 0 →
            Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
              (fun y : O => ((fS y, 4 * Δ - edgeRowHeight Δ FS ρS y) : ℝ × ℝ)) y)),
          letI _sublevelCharts := regularSublevelChartedSpace
            finrank_real_prod_euclideanTwo hΨ hB hreg hregb
          let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
          Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
            {y : O // fS y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y}) ∧
          CompactSpace {y : O // fS y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y} ∧
          ConnectedSpace {y : O // fS y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y} ∧
          (∃ Θ' : {y : O // fS y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y} × Q₀ → O,
            ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
            (∀ p, fS (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS (Θ' p)) ∧
            (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
            ∃ O' : Set O, IsOpen O' ∧
              (∀ y : O, fS y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y → y ∈ O') ∧
              ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
                ∀ (y : O) (hy : fS y ∈ Ioo a₀ b₀),
                  0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y →
                  ∃ hR : fS (R y) = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS (R y),
                    Θ' (⟨R y, hR⟩, ⟨fS y, hy⟩) = y) ∧
          ∀ y : {y : O // fS y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ FS ρS y},
            (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ edgeRowHeight Δ FS ρS y = 4 * Δ := by
  obtain ⟨b₀, hb₀, hthreshold⟩ := edgeSourceSlab_disk_bundle_threshold
    hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ K hK hr hv A
  refine ⟨b₀, hb₀, ?_⟩
  intro b hb hbb₀ M mM cM sM sigM t2TM completeM connectedM bundleM riemM
    continuousM g hEnorm oM p hvol hder hsec Y mY y₀ α Q E F f ρ OF Of
    hQfirst hQp hQdist hheight hQcover hEc hpE hborder hbordercover hFerror
    hOF hCO hFs hFgrad hquot hHs hρ hρp hρs hOf hOfb hfs hfLip hfval hftest
  let S := smallThreeModel M
  let smallMetric := S.metricSpace
  let gS := S.metric g
  let smallBundle := smallModel_edgeBundle S g
  let smallContinuous := smallModel_edgeContinuous S g
  have hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b) :=
    fun a b => riemannianEDistOf_eq_ofReal_dist g hEnorm a b
  let smallRiemannian := smallModel_edgeManifold S g hmetric
  let smallComplete : CompleteSpace S.Carrier := S.isometryEquiv.completeSpace
  let smallConnected : ConnectedSpace S.Carrier :=
    S.diffeo.toHomeomorph.connectedSpace_iff.mpr connectedM
  let smallSigma : SigmaCompactSpace S.Carrier := smallModelSigmaCompact S
  let smallTangentHausdorff : T2Space (TangentBundle I3 S.Carrier) := inferInstance
  have hnormS : IsMetricNorm gS := isMetricNorm_of_riemannianBundle gS
  let oS := Classical.choose (S.exists_orientation oM)
  let pS := S.diffeo.symm p
  let QS := Q ∘ S.diffeo
  let ES := S.diffeo ⁻¹' E
  let FS := F ∘ S.diffeo
  let fS := f ∘ S.diffeo
  let ρS := ρ ∘ S.diffeo
  let OFS := S.diffeo ⁻¹' OF
  let OfS := S.diffeo ⁻¹' Of
  let αS := α.comapSourceIsometryAt S.isometryEquiv pS (S.diffeo.apply_symm_apply p)
  have hd (x : S.Carrier) : dist x pS = dist (S.diffeo x) p := by
    have ht := S.isometryEquiv.dist_eq x pS
    change dist (S.diffeo x) (S.diffeo (S.diffeo.symm p)) = dist x pS at ht
    rw [S.diffeo.apply_symm_apply] at ht
    exact ht.symm
  have hdd (x y : S.Carrier) : dist x y = dist (S.diffeo x) (S.diffeo y) :=
    (S.isometryEquiv.dist_eq x y).symm
  have hi (x : S.Carrier) : infDist x ES = infDist (S.diffeo x) E :=
    smallModel_infDist_preimage S E x
  have hball (x : S.Carrier) (R : ℝ) : x ∈ ball pS R ↔ S.diffeo x ∈ ball p R := by
    simp only [mem_ball, hd]
  have hclosed (x : S.Carrier) (R : ℝ) :
      x ∈ closedBall pS R ↔ S.diffeo x ∈ closedBall p R := by
    simp only [mem_closedBall, hd]
  have hregion (x : S.Carrier)
      (hx : x ∈ closedBall pS (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y ES ∧ infDist y ES ≤ 21 / 2 * Δ}) :
      S.diffeo x ∈ closedBall p (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y E ∧ infDist y E ≤ 21 / 2 * Δ} := by
    simpa only [mem_inter_iff, mem_ofPred_eq, hclosed, hi] using hx
  have hvolS : ENNReal.ofReal v ≤
      riemannianVolumeMeasure I3 S.Carrier gS (ball pS r) := by
    rw [← DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm
      gS hnormS]
    change ENNReal.ofReal v ≤ ballVolume gS pS r
    rw [smallModel_ballVolume, S.diffeo.apply_symm_apply]
    rw [ballVolume,
      DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm g hEnorm]
    exact hvol
  have hderS : ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K,
      ∀ y ∈ ball pS R, curvDerivNorm k gS y ≤ A R := by
    intro R hR hRb k hk y hy
    rw [smallModel_curvDerivNorm]
    exact hder R hR hRb k hk (S.diffeo y) ((hball y R).mp hy)
  have hsecS : ∀ y ∈ ball pS b⁻¹, SectionalBoundedBelowAt gS y (-b ^ 2) := by
    intro y hy
    exact sectionalBoundedBelowAt_pullbackMetricCross g S.diffeo y
      (hsec (S.diffeo y) ((hball y b⁻¹).mp hy))
  have hQS : ∀ z, (QS z).fst = (αS.toFun z).fst := fun z => hQfirst (S.diffeo z)
  have hQpS : QS pS = 0 := by
    simpa only [QS, Function.comp_apply, pS, Diffeomorph.apply_symm_apply] using hQp
  have hdistS : ∀ x ∈ ball pS (200 * Δ), ∀ y ∈ ball pS (200 * Δ),
      |dist (QS x) (QS y) - dist x y| ≤ τ * Δ := by
    intro x hx y hy
    simpa only [QS, Function.comp_apply, hdd] using
      hQdist (S.diffeo x) ((hball x _).mp hx) (S.diffeo y) ((hball y _).mp hy)
  have hheightS : ∀ x ∈ ball pS (200 * Δ), 0 ≤ (QS x).snd :=
    fun x hx => hheight (S.diffeo x) ((hball x _).mp hx)
  have hcoverS : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ →
      z.snd ∈ Icc 0 (100 * Δ) → ∃ x ∈ ball pS (200 * Δ), dist (QS x) z ≤ τ * Δ := by
    intro z hz hz'
    obtain ⟨x, hx, hQx⟩ := hQcover z hz hz'
    refine ⟨S.diffeo.symm x, ?_, ?_⟩
    · apply (hball _ _).mpr
      simpa only [Diffeomorph.apply_symm_apply] using hx
    · simpa only [QS, Function.comp_apply, Diffeomorph.apply_symm_apply] using hQx
  have hES : IsClosed ES := hEc.preimage S.diffeo.continuous
  have hpES : pS ∈ ES := by
    simpa only [ES, pS, mem_preimage, Diffeomorph.apply_symm_apply] using hpE
  have hborderS : ∀ a ∈ ES ∩ ball pS (190 * Δ), (QS a).snd ≤ τ * Δ :=
    fun a ha => hborder (S.diffeo a) ⟨ha.1, (hball a _).mp ha.2⟩
  have hbordercoverS : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ ES ∩ ball pS (190 * Δ),
        dist (QS a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ := by
    intro t ht
    obtain ⟨a, ha, hQa⟩ := hbordercover t ht
    refine ⟨S.diffeo.symm a, ⟨?_, ?_⟩, ?_⟩
    · simpa only [ES, mem_preimage, Diffeomorph.apply_symm_apply] using ha.1
    · apply (hball _ _).mpr
      simpa only [Diffeomorph.apply_symm_apply] using ha.2
    · simpa only [QS, Function.comp_apply, Diffeomorph.apply_symm_apply] using hQa
  have hFerrorS : ∀ x, |FS x - infDist x ES| < μ * Δ := by
    intro x
    simpa only [FS, Function.comp_apply, hi] using hFerror (S.diffeo x)
  have hOFS : IsOpen OFS := hOF.preimage S.diffeo.continuous
  have hCOS : closedBall pS (20 * Δ) ∩
      {y | 3 / 4 * Δ ≤ infDist y ES ∧ infDist y ES ≤ 21 / 2 * Δ} ⊆ OFS :=
    fun x hx => hCO (hregion x hx)
  have hFsS : ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ FS OFS :=
    hFs.comp S.diffeo.contMDiff.contMDiffOn (fun x hx => hx)
  have hFgradS : ∀ y ∈ closedBall pS (20 * Δ) ∩
      {z | 3 / 4 * Δ ≤ infDist z ES ∧ infDist z ES ≤ 21 / 2 * Δ},
      ∀ u ∈ gS.finiteMinimizingDirectionsTo ES y,
        Real.sqrt (gS.inner y (gradFun gS FS y + u) (gradFun gS FS y + u)) < ε := by
    intro y hy u hu
    have hyOF := hCO (hregion y hy)
    have hmdF := ((hFs _ hyOF).contMDiffAt (hOF.mem_nhds hyOF)).mdifferentiableAt
      (by simp)
    rw [smallModel_gradient_add_inner S g F y u hmdF]
    exact hFgrad (S.diffeo y) (hregion y hy) _
      (smallModel_minimizingDirection S g hEnorm hnormS E y u hu)
  have hquotS : ∀ y ∈ closedBall pS (20 * Δ) ∩
      {z | 3 / 4 * Δ ≤ infDist z ES ∧ infDist z ES ≤ 21 / 2 * Δ},
      Real.sqrt (gS.inner y (gradFun gS (fun z => FS z / ρS z) y - gradFun gS FS y)
        (gradFun gS (fun z => FS z / ρS z) y - gradFun gS FS y)) ≤ 100 * Δ * Λ := by
    intro y hy
    have hidentity := smallModel_gradient_difference_inner S g (fun z => F z / ρ z) F y
    change gS.inner y
        (gradFun gS (fun z => FS z / ρS z) y - gradFun gS FS y)
        (gradFun gS (fun z => FS z / ρS z) y - gradFun gS FS y) = _ at hidentity
    rw [hidentity]
    exact hquot (S.diffeo y) (hregion y hy)
  have hHsS : ∀ x ∈ ball pS (20 * Δ), infDist x ES < 41 / 4 * Δ →
      ContMDiffAt I3 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ FS ρS) x := by
    intro x hx hxi
    exact (hHs (S.diffeo x) ((hball x _).mp hx) (by rwa [hi] at hxi)).comp x
      S.diffeo.contMDiff.contMDiffAt
  have hρS : LipschitzWith Λ ρS := by
    have ht := hρ.comp S.isometryEquiv.isometry.lipschitzWith
    change LipschitzWith (Λ * 1) ρS at ht
    simpa only [mul_one] using ht
  have hρpS : ρS pS = 1 := by
    simpa only [ρS, Function.comp_apply, pS, Diffeomorph.apply_symm_apply] using hρp
  have hρsS : ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ρS (ball pS (100 * Δ)) :=
    hρs.comp S.diffeo.contMDiff.contMDiffOn (fun x hx => (hball x _).mp hx)
  have hOfS : IsOpen OfS := hOf.preimage S.diffeo.continuous
  have hOfbS : closedBall pS (100 * Δ) ⊆ OfS :=
    fun x hx => hOfb ((hclosed x _).mp hx)
  have hfsS : ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ fS OfS :=
    hfs.comp S.diffeo.contMDiff.contMDiffOn (fun x hx => hx)
  have hfLipS : LipschitzWith (Real.toNNReal (1 + σ)) fS := by
    have ht := hfLip.comp S.isometryEquiv.isometry.lipschitzWith
    change LipschitzWith (Real.toNNReal (1 + σ) * 1) fS at ht
    simpa only [mul_one] using ht
  have hfvalS : ∀ x ∈ ball pS (100 * Δ), |fS x - (αS.toFun x).fst| < μ * Δ :=
    fun x hx => hfval (S.diffeo x) ((hball x _).mp hx)
  have hftestS : ∀ x ∈ ball pS (100 * Δ), ∀ x' ∈ ball pS (1000 * Δ),
      100 * Δ < dist x x' → ∀ w : TangentSpace I3 x, gS.inner x w w = 1 →
      intrinsicGeodesic gS hnormS x w (dist x x') = x' →
      |mvfderiv I3 fS x w - ((αS.toFun x').fst - (αS.toFun x).fst) / dist x x'| < σ := by
    intro x hx x' hx' hdist w hunit hgeo
    have hxOf := hOfb (ball_subset_closedBall ((hball x _).mp hx))
    have hmdf := ((hfs _ hxOf).contMDiffAt (hOf.mem_nhds hxOf)).mdifferentiableAt
      (by simp)
    rw [smallModel_scalar_derivative S f x w hmdf, hdd]
    apply hftest (S.diffeo x) ((hball x _).mp hx) (S.diffeo x') ((hball x' _).mp hx')
      (by rwa [hdd] at hdist)
    · rw [← S.metric_inner g]
      exact hunit
    · have ht := congrArg S.diffeo hgeo
      rw [smallModel_intrinsicGeodesic S g hEnorm hnormS x w] at ht
      rwa [hdd] at ht
  obtain ⟨O, hO, hslab, hpacket⟩ := hthreshold b hb hbb₀ S.Carrier gS hnormS oS pS
    hvolS hderS hsecS Y y₀ αS QS ES FS fS ρS OFS OfS hQS hQpS hdistS hheightS
    hcoverS hES hpES hborderS hbordercoverS hFerrorS hOFS hCOS hFsS hFgradS hquotS
    hHsS hρS hρpS hρsS hOfS hOfbS hfsS hfLipS hfvalS hftestS
  let O₀ : TopologicalSpace.Opens M :=
    ⟨S.diffeo '' (O : Set S.Carrier), S.diffeo.toHomeomorph.isOpenMap _ O.isOpen⟩
  refine ⟨S, O₀, O, rfl, ?_, ?_, hO, hslab, hpacket⟩
  · rintro x ⟨y, hy, rfl⟩
    exact (hball y _).mp (hO hy)
  · intro y hy hfy hHy
    have hyS : S.diffeo.symm y ∈ ball pS (100 * Δ) := by
      apply (hball _ _).mpr
      simpa only [Diffeomorph.apply_symm_apply] using hy
    have hfS : |fS (S.diffeo.symm y)| ≤ 4 * Δ := by
      simpa only [fS, Function.comp_apply, Diffeomorph.apply_symm_apply] using hfy
    have hHS : edgeRowHeight Δ FS ρS (S.diffeo.symm y) ≤ 4 * Δ := by
      simpa only [edgeRowHeight, FS, ρS, Function.comp_apply,
        Diffeomorph.apply_symm_apply] using hHy
    exact ⟨S.diffeo.symm y, hslab _ hyS hfS hHS, S.diffeo.apply_symm_apply y⟩

end DifferentialGeometry.Geometry.Collapse
