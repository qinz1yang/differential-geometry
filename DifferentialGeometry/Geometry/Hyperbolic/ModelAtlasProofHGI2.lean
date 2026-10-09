import DifferentialGeometry.Geometry.Hyperbolic.Rigidity
import DifferentialGeometry.Geometry.Hyperbolic.ModelAtlas
import DifferentialGeometry.Geometry.Exponential.HyperbolicComparisonFirstJet
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.ModelAtlas
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalIdentity
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalRestriction
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

/-!
# `ModelAtlas` proved: twin of the W8 skeleton `Hyperbolic/ModelAtlas.lean` (S-HG-INTAKE-2, `_HGI2`)

The former `Hyperbolic/ModelAtlas.lean` declaration `has_hyperbolic_atlas_of_curvature_neg_one`
has been removed. This file is the donor file
`Geometry/Hyperbolic/ModelAtlas.lean` of the branch `codex/della-mostow-smooth-adapter-20261004`
(467465bc6c), byte for byte, with two kinds of edits:

* one extra `import` of the canonical model-atlas module;
* the three declarations the tracked file also declares carry the suffix `_HGI2`:
  `has_hyperbolic_atlas_of_curvature_neg_one_HGI2`, `hyperbolicGeometricStructure_HGI2`,
  `hyperbolicGeometricStructure_HGI2_model`.

The other donor declarations (`has_hyperbolic_atlas_scaleMetric`, …) keep their names.  The explicit original contract below checks the proved local atlas without referring to the
removed declaration.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem riemannOp_eq_of_metric_eqOn_of_sectionalCurvature_eq
    (g g' : SmoothRiemannianMetric I M) {W : Set M} (hW : IsOpen W)
    (heq : ∀ q ∈ W, g'.inner q = g.inner q) (κ : ℝ)
    (hsec : ∀ q ∈ W, ∀ v w : TangentSpace I q,
      LinearIndependent ℝ ![v, w] → Riemannian.sectionalCurvature g q v w = κ)
    {q : M} (hq : q ∈ W) (X Y Z : TangentSpace I q) :
    Curvature.riemannOp (Connection.LeviCivita g') q X Y Z =
      κ • (g'.inner q Y Z • X - g'.inner q X Z • Y) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I 3 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  apply Curvature.riemannOp_of_rm g' q κ _ X Y Z
  apply Curvature.metricRm_of_sec g' q κ
  intro v w
  rw [DifferentialGeometry.metricRm04StandardAt_congr_metric g g' hW heq hq,
    heq q hq]
  exact Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq g κ q (hsec q hq) v w

end DifferentialGeometry.Geometry.Hyperbolic
end

noncomputable section

open scoped Manifold ContDiff Bundle Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold I₃ ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem model_chart_of_complete_curvature_neg_one_on
    (g : SmoothRiemannianMetric I₃ M) (hg : RiemannianMetricComplete g)
    {W : Set M} (hW : IsOpen W) (p : M) (hp : p ∈ W)
    (hR : ∀ q ∈ W, ∀ X Y Z : TangentSpace I₃ q,
      Curvature.riemannOp (Connection.LeviCivita g) q X Y Z =
        (-1 : ℝ) • (g.inner q Y Z • X - g.inner q X Z • Y)) :
    ∃ Φ : PartialDiffeomorph I₃ I₃ (Hyperboloid E₃) M ∞,
      p ∈ Φ.target ∧ (∀ y ∈ Φ.source, Φ y ∈ W) ∧
      ∀ y ∈ Φ.source, ∀ v w : TangentSpace I₃ y,
        g.inner (Φ y) (mfderiv I₃ I₃ Φ y v) (mfderiv I₃ I₃ Φ y w) =
          Hyperboloid.riemannianMetric.inner y v w := by
  let _ : IsManifold I₃ 1 M := IsManifold.of_le (I := I₃) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I₃ M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I₃ : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I₃ : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I₃ M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I₃ M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let _ : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩
  let hEnorm : Riemannian.IsMetricNorm g :=
    fun x v => Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hdim : Module.finrank ℝ (TangentSpace I₃ p) = 3 := by
    change Module.finrank ℝ E₃ = 3
    simp
  let b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I₃ p) :=
    (stdOrthonormalBasis ℝ (TangentSpace I₃ p)).reindex (finCongr hdim)
  let i := b.repr.symm
  let F := Riemannian.Exponential.hyperbolicComparison g hg p i
  let L := Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E₃)
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp (hW.mem_nhds hp)
  let U : Set (Hyperboloid E₃) := L.symm ⁻¹' Metric.eball (0 : E₃) ε
  have hU : IsOpen U := Metric.isOpen_eball.preimage L.symm.continuous
  have hU0 : Hyperboloid.origin ∈ U := by
    change L.symm Hyperboloid.origin ∈ Metric.eball (0 : E₃) ε
    rw [Riemannian.Exponential.hyperboloid_expMapIntrinsicOriginDiffeomorph_symm_origin]
    simpa only [Metric.mem_eball, edist_self] using hε
  have hstay (y : Hyperboloid E₃) (hy : y ∈ U) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      Riemannian.Exponential.intrinsicGeodesic g hEnorm p (i (L.symm y)) t ∈ W := by
    let u : E₃ := L.symm y
    have hu : ENNReal.ofReal ‖u‖ < ε := by
      simpa only [U, Set.mem_preimage, Metric.mem_eball, edist_zero_right,
        ← ofReal_norm] using hy
    have hspeed : Real.sqrt (g.inner p (i u) (i u)) = ‖u‖ := by
      rw [← hEnorm.inner_eq, i.inner_map_map, real_inner_self_eq_norm_sq,
        Real.sqrt_sq (norm_nonneg u)]
    have hd := Riemannian.Exponential.intrinsicGeodesic_riemannianEDist_le
      g hEnorm p (i u) (s := 0) (t := t) ht.1
    rw [Riemannian.Exponential.intrinsicGeodesic_zero, hspeed, sub_zero] at hd
    have hmul : ‖u‖ * t ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (norm_nonneg u)
    apply hball
    apply Metric.mem_eball'.mpr
    rw [IsRiemannianManifold.out (I := I₃)]
    exact hd.trans_lt ((ENNReal.ofReal_le_ofReal hmul).trans_lt hu)
  have hmetric (y : Hyperboloid E₃) (hy : y ∈ U) (v w : TangentSpace I₃ y) :
      g.inner (F y) (mfderiv I₃ I₃ F y v) (mfderiv I₃ I₃ F y w) =
        Hyperboloid.riemannianMetric.inner y v w := by
    exact Riemannian.Exponential.hyperbolicComparison_inner_of_radial_curvature
      g hg p i y (fun t ht => hR _ (hstay y hy t ht)) v w
  have hloc : IsLocalDiffeomorphOn I₃ I₃ ∞ F U := by
    have hs := Riemannian.Exponential.contMDiff_hyperbolicComparison g hg p i
    apply hs.contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv hU (by simp)
    intro y hy
    have hinj : Function.Injective (mfderiv I₃ I₃ F y) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h := hmetric y hy v v
      rw [hv] at h
      have hz : Hyperboloid.riemannianMetric.inner y v v = 0 := by
        simpa only [map_zero, zero_apply] using h.symm
      by_contra hne
      exact (ne_of_gt (Hyperboloid.riemannianMetric.pos y v hne)) hz
    have hsurj := LinearMap.surjective_of_injective hinj
    let D : E₃ ≃L[ℝ] E₃ := ContinuousLinearEquiv.ofBijective (mfderiv I₃ I₃ F y)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
    exact ⟨D, rfl⟩
  obtain ⟨Φ, h₀, hΦ⟩ := hloc ⟨Hyperboloid.origin, hU0⟩
  let Ψ := Topology.PartialDiffeomorph.restrict Φ U hU
  have hΨ0 : Hyperboloid.origin ∈ Ψ.source := ⟨h₀, hU0⟩
  have hbase : Ψ Hyperboloid.origin = p :=
    (hΦ h₀).symm.trans (Riemannian.Exponential.hyperbolicComparison_origin g hg p i)
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · rw [← hbase]
    exact Ψ.map_source hΨ0
  · intro y hy
    have hfy : F y = Ψ y := hΦ hy.1
    rw [← hfy]
    change Riemannian.Exponential.hyperbolicComparison g hg p i y ∈ W
    rw [Riemannian.Exponential.hyperbolicComparison_apply]
    exact hstay y hy.2 1 (by norm_num)
  · intro y hy v w
    have he : F =ᶠ[nhds y] Ψ := by
      filter_upwards [Ψ.open_source.mem_nhds hy] with z hz
      exact hΦ hz.1
    have hd : (mfderiv I₃ I₃ F y : E₃ →L[ℝ] E₃) = mfderiv I₃ I₃ Ψ y := by
      ext u
      exact congrArg (fun L : E₃ →L[ℝ] E₃ => L u) he.mfderiv_eq
    have hm := hmetric y hy.2 v w
    rw [hd] at hm
    exact (congrArg (fun q : M => g.inner q (mfderiv I₃ I₃ Ψ y v)
      (mfderiv I₃ I₃ Ψ y w)) (hΦ hy.1)).symm.trans hm

end DifferentialGeometry.Geometry.Hyperbolic
end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold I₃ ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem modelAtlas_of_curvature_neg_one_sigmaCompact
    (g : SmoothRiemannianMetric I₃ M)
    (hsec : ∀ q (v w : TangentSpace I₃ q), LinearIndependent ℝ ![v, w] →
      Riemannian.sectionalCurvature g q v w = -1) :
    GC.Geometry.ModelAtlas g (Hyperboloid.riemannianMetric (E := E₃)) := by
  intro p
  obtain ⟨g', W, hg', hW, hpW, heq, _⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g (isCompact_singleton (x := p))
  have hR (q : M) (hq : q ∈ W) (X Y Z : TangentSpace I₃ q) :
      Curvature.riemannOp (Connection.LeviCivita g') q X Y Z =
        (-1 : ℝ) • (g'.inner q Y Z • X - g'.inner q X Z • Y) :=
    riemannOp_eq_of_metric_eqOn_of_sectionalCurvature_eq g g' hW heq (-1)
      (fun z _ => hsec z) hq X Y Z
  obtain ⟨Φ, hpΦ, hΦW, hΦ⟩ := model_chart_of_complete_curvature_neg_one_on
    g' hg' hW p (hpW (Set.mem_singleton p)) hR
  refine ⟨Φ, hpΦ, ?_⟩
  intro y hy v w
  have h := hΦ y hy v w
  rw [heq _ (hΦW y hy)] at h
  exact h

private theorem has_hyperbolic_atlas_of_curvature_neg_one_sigmaCompact
    (g : SmoothRiemannianMetric I₃ M)
    (hsec : ∀ q (v w : TangentSpace I₃ q), LinearIndependent ℝ ![v, w] →
      Riemannian.sectionalCurvature g q v w = -1) :
    GC.Geometry.HasThurstonAtlas g .hyperbolic := by
  intro x
  obtain ⟨φ, hx, hφ⟩ := modelAtlas_of_curvature_neg_one_sigmaCompact g hsec x
  obtain ⟨e, he, hmetric⟩ := Hyperboloid.hasThurstonAtlas_riemannianMetric (φ.symm x)
  refine ⟨e.trans φ, ⟨hx, he⟩, ?_⟩
  intro p hp v w
  have hed := e.mdifferentiableAt (by decide) hp.1
  have hep : e p ∈ φ.source := hp.2
  have hφd : MDifferentiableAt I₃ I₃ φ (e p) := φ.mdifferentiableAt (by decide) hep
  change g.inner (φ (e p))
    (mfderiv I₃ I₃ (φ ∘ e) p v) (mfderiv I₃ I₃ (φ ∘ e) p w) =
    GC.Geometry.coordinateInner .hyperbolic p
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) p v) (NormedSpace.fromTangentSpace (𝕜 := ℝ) p w)
  rw [mfderiv_comp_apply p hφd hed, mfderiv_comp_apply p hφd hed,
    hφ (e p) hep]
  exact hmetric p hp.1 v w

end DifferentialGeometry.Geometry.Hyperbolic
end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold I₃ ∞ M]

theorem has_hyperbolic_atlas_of_curvature_neg_one_HGI2
    (g : SmoothRiemannianMetric I₃ M)
    (hcurvature : hasConstantSectionalCurvature g (-1)) :
    GC.Geometry.HasThurstonAtlas g .hyperbolic := by
  intro x
  let U : TopologicalSpace.Opens M := ⟨(chartAt E₃ x).source, (chartAt E₃ x).open_source⟩
  let xU : U := ⟨x, mem_chart_source E₃ x⟩
  let A : U ≃ₜ (chartAt E₃ x).target := (chartAt E₃ x).toHomeomorphSourceTarget
  let _ : T2Space U := A.symm.t2Space
  let _ : SecondCountableTopology U := A.secondCountableTopology
  let _ : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace E₃ U
  let _ : SigmaCompactSpace U := inferInstance
  let gU := g.restrictOpen U
  have hsecU : ∀ q (v w : TangentSpace I₃ q), LinearIndependent ℝ ![v, w] →
      Riemannian.sectionalCurvature gU q v w = -1 := by
    intro q v w hvw
    change Riemannian.sectionalCurvature (g.restrictOpen U) q v w = -1
    rw [Riemannian.sectionalCurvature_restrictOpen]
    exact hcurvature (q : M) v w hvw
  obtain ⟨e, hx, he⟩ := has_hyperbolic_atlas_of_curvature_neg_one_sigmaCompact gU hsecU xU
  let j := Topology.PartialDiffeomorph.subtypeVal (I := I₃) U ⟨xU⟩
  have hj : j.source = Set.univ := U.openPartialHomeomorphSubtypeCoe_source _
  have hsource : e.symm xU ∈ (e.trans j).source := by
    refine ⟨e.map_target hx, ?_⟩
    change e (e.symm xU) ∈ j.source
    rw [hj]
    exact Set.mem_univ _
  have hbase : (e.trans j) (e.symm xU) = x := congrArg Subtype.val (e.right_inv hx)
  refine ⟨e.trans j, ?_, ?_⟩
  · rw [← hbase]
    exact (e.trans j).map_source hsource
  · intro p hp v w
    have heD := e.mdifferentiableAt (by decide) hp.1
    have hjD : MDifferentiableAt I₃ I₃ (Subtype.val : U → M) (e p) :=
      (contMDiff_subtype_val (I := I₃) (U := U) (n := ∞)).mdifferentiableAt (by decide)
    change g.inner (e p : M)
      (mfderiv I₃ I₃ ((Subtype.val : U → M) ∘ e) p v)
      (mfderiv I₃ I₃ ((Subtype.val : U → M) ∘ e) p w) =
      GC.Geometry.coordinateInner .hyperbolic p
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) p v) (NormedSpace.fromTangentSpace (𝕜 := ℝ) p w)
    rw [mfderiv_comp_apply p hjD heD, mfderiv_comp_apply p hjD heD,
      mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    exact he p hp.1 v w

end DifferentialGeometry.Geometry.Hyperbolic
end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold I₃ ∞ M]

theorem has_hyperbolic_atlas_scaleMetric
    (g : SmoothRiemannianMetric I₃ M) (κ : ℝ) (hκ : κ < 0)
    (hcurvature : hasConstantSectionalCurvature g κ) :
    GC.Geometry.HasThurstonAtlas (scaleMetric (-κ) (neg_pos.mpr hκ) g) .hyperbolic := by
  apply has_hyperbolic_atlas_of_curvature_neg_one_HGI2
  intro p v w hvw
  let U : TopologicalSpace.Opens M := ⟨(chartAt E₃ p).source, (chartAt E₃ p).open_source⟩
  let pU : U := ⟨p, mem_chart_source E₃ p⟩
  let A : U ≃ₜ (chartAt E₃ p).target := (chartAt E₃ p).toHomeomorphSourceTarget
  let _ : T2Space U := A.symm.t2Space
  let vU : TangentSpace I₃ pU := v
  let wU : TangentSpace I₃ pU := w
  have hmetric : (scaleMetric (-κ) (neg_pos.mpr hκ) g).restrictOpen U =
      scaleMetric (-κ) (neg_pos.mpr hκ) (g.restrictOpen U) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x a b
    rfl
  calc
    Riemannian.sectionalCurvature (scaleMetric (-κ) (neg_pos.mpr hκ) g) p v w =
        Riemannian.sectionalCurvature
          ((scaleMetric (-κ) (neg_pos.mpr hκ) g).restrictOpen U) pU vU wU :=
      (Riemannian.sectionalCurvature_restrictOpen
        (scaleMetric (-κ) (neg_pos.mpr hκ) g) U pU vU wU).symm
    _ = Riemannian.sectionalCurvature
        (scaleMetric (-κ) (neg_pos.mpr hκ) (g.restrictOpen U)) pU vU wU :=
      congrArg (fun metric : SmoothRiemannianMetric I₃ U =>
        Riemannian.sectionalCurvature metric pU vU wU) hmetric
    _ = (-κ)⁻¹ * Riemannian.sectionalCurvature (g.restrictOpen U) pU vU wU :=
      Riemannian.sectionalCurvature_scaleMetric (-κ) (neg_pos.mpr hκ)
        (g.restrictOpen U) pU vU wU
    _ = (-κ)⁻¹ * Riemannian.sectionalCurvature g p v w :=
      congrArg (fun a : ℝ => (-κ)⁻¹ * a)
        (Riemannian.sectionalCurvature_restrictOpen g U pU vU wU)
    _ = -1 := by
      rw [hcurvature p v w hvw]
      field_simp [ne_of_lt hκ]

end DifferentialGeometry.Geometry.Hyperbolic
end

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]

def hyperbolicGeometricStructure_HGI2
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-(1 / 4 : ℝ)))
    (hcomplete : RiemannianMetricComplete g)
    (hvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤) :
    GC.Geometry.GeometricStructure (𝓡 3) M where
  model := .hyperbolic
  metric := scaleMetric (1 / 4 : ℝ) (by norm_num) g
  complete := hcomplete.scaleMetric _ (by norm_num)
  atlas := by
    apply has_hyperbolic_atlas_of_curvature_neg_one_HGI2
    intro p v w hvw
    rw [Geometry.Riemannian.sectionalCurvature_scaleMetric, hcurvature p v w hvw]
    norm_num
  hyperbolic_finite_volume := by
    intro _
    rw [Integral.Measure.volume_scale_apply]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hvolume

@[simp] theorem hyperbolicGeometricStructure_HGI2_model
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-(1 / 4 : ℝ)))
    (hcomplete : RiemannianMetricComplete g)
    (hvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤) :
    (hyperbolicGeometricStructure_HGI2 g hcurvature hcomplete hvolume).model = .hyperbolic := rfl

end DifferentialGeometry.Geometry.Hyperbolic

end

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

open scoped _root_.Manifold _root_.ContDiff

/-- The proved local atlas satisfies the original contract without completeness or separation
assumptions on the ambient manifold. -/
example {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-1)) :
    GC.Geometry.HasThurstonAtlas g .hyperbolic :=
  has_hyperbolic_atlas_of_curvature_neg_one_HGI2 g hcurvature

end DifferentialGeometry.Geometry.Hyperbolic
