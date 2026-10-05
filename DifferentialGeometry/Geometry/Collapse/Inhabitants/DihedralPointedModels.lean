import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralEndLimit
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Sequences

/-! Actual fixed-epsilon cylinder/end indexed models and all-moving limits on the same
long dihedral metric family, with genuine native interior charts, cones and curvature buffers. -/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Geometry.SphericalProduct
open DifferentialGeometry.Geometry.Riemannian Bundle
open Filter Set
open scoped Topology Manifold ContDiff
attribute [local instance] sphereDimension cylinderDimension
namespace DifferentialGeometry.Geometry.Collapse

theorem dihedralSphereAlignment
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      sphereDiffeo (n := 2) A x = y := by
  let A := Submodule.reflection (ℝ ∙ ((x : EuclideanSpace ℝ (Fin 3)) -
    (y : EuclideanSpace ℝ (Fin 3))))ᗮ
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply Submodule.reflection_sub
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  exact hx.trans hy.symm
theorem dihedralNonnegativeSubsequence (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (Tendsto (fun i => f (k i)) atTop atTop ∨
        ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun i => f (k i)) atTop (nhds c)) := by
  obtain ⟨y, k, hk, ht⟩ := CompactSpace.tendsto_subseq (fun i : ℕ => (f i : EReal))
  have hy : (0 : EReal) ≤ y := isClosed_Ici.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun i => by
      change (0 : EReal) ≤ (f (k i) : EReal)
      exact_mod_cast hf (k i)))
  refine ⟨k, hk, ?_⟩
  by_cases htop : y = ⊤
  · left
    subst y
    exact EReal.tendsto_coe_nhds_top_iff.mp ht
  · right
    have hbot : y ≠ ⊥ := by intro h; rw [h] at hy; norm_num at hy
    refine ⟨y.toReal, EReal.toReal_nonneg hy, ?_⟩
    simpa only [Function.comp_def, EReal.toReal_coe] using
      (EReal.tendsto_toReal htop hbot).comp ht
universe u
def dihedralInteriorPartial (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (s : ℝ) (hs : 0 < s) (hsL : s < L)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) sphereCylinderRechart
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞ :=
  Classical.choose (exists_dihedralCylinderPointedMetricChart.{u} ε L hε hL s hs hsL A)
theorem dihedralInteriorPartial_data (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (s : ℝ) (hs : 0 < s) (hsL : s < L)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃ hjm : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (dihedralInteriorPartial.{u} ε L hε hL s hs hsL A : sphereCylinderRechart → _),
      (dihedralInteriorPartial.{u} ε L hε hL s hs hsL A : sphereCylinderRechart → _) =
        dihedralCylinderMap.{u} L hL s A ∧
      localPullMetric (dihedralMetric.{u} ε L hε hL)
        (dihedralInteriorPartial.{u} ε L hε hL s hs hsL A) hjm =
        dihedralRechartedMetric ε (1 / 2) hε (by norm_num) ∧
      ∀ R : ℝ, 0 < R → R ≤ s → R ≤ L - s →
        riemannianBallOf (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
          (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) R ⊆
            (dihedralInteriorPartial.{u} ε L hε hL s hs hsL A).source := by
  obtain ⟨hjm, _hsrc, _htgt, hfun, _hn, hmetric, hballs⟩ :=
    Classical.choose_spec (exists_dihedralCylinderPointedMetricChart.{u} ε L hε hL s hs hsL A)
  exact ⟨hjm, hfun, hmetric, hballs⟩
theorem dihedralInteriorPartial_pullback_on (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (s : ℝ) (hs : 0 < s) (hsL : s < L)
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (U : TopologicalSpace.Opens sphereCylinderRechart)
    (hU : (U : Set sphereCylinderRechart) ⊆
      (dihedralInteriorPartial.{u} ε L hε hL s hs hsL A).source) :
    PartialDiffeomorph.pullbackMetricOn (dihedralInteriorPartial.{u} ε L hε hL s hs hsL A) U hU
      (dihedralMetric.{u} ε L hε hL) =
      (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)).restrictOpen U := by
  obtain ⟨hjm, _hfun, hmetric, _hballs⟩ := dihedralInteriorPartial_data.{u} ε L hε hL s hs hsL A
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [PartialDiffeomorph.pullbackMetricOn_inner, SmoothRiemannianMetric.restrictOpen_inner]
  have h := congrArg (fun g : SmoothRiemannianMetric (𝓡 3) sphereCylinderRechart =>
    g.inner (z : sphereCylinderRechart) v w) hmetric
  rw [localPullMetric_inner (I := 𝓡 3) (J := 𝓡 3) _ _ hjm (z : sphereCylinderRechart) v w] at h
  exact h

theorem dihedralInterior_nativeCharts : (∀ (ε : ℝ) (hε : 0 < ε) (L s : ℕ → ℝ) (hL : ∀ i, 0 < L i),
  (∀ i, 0 < s i) → (∀ i, s i < L i) →
  Filter.Tendsto s Filter.atTop Filter.atTop →
  Filter.Tendsto (fun i => L i - s i) Filter.atTop Filter.atTop →
  ∀ A : ℕ → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
  let _modelMetric : MetricSpace sphereCylinderRechart :=
    inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
  ∃ jm : ∀ _i, PartialDiffeomorph (𝓡 3) (𝓡 3) sphereCylinderRechart
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
    (∀ i, jm i (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) =
      dihedralCylinderMap (L i) (hL i) (s i) (A i)
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))) ∧
    ∀ r : ℝ, 0 < r → ∃ i0 : ℕ,
    ∃ hsub : ∀ l, ((⟨Metric.ball
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) r,
        Metric.isOpen_ball⟩ : TopologicalSpace.Opens sphereCylinderRechart) :
          Set sphereCylinderRechart)
          ⊆ (jm (l + i0)).source,
    ∀ K : Set (⟨Metric.ball
      (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) r,
        Metric.isOpen_ball⟩ : TopologicalSpace.Opens sphereCylinderRechart),
    IsCompact K → CheegerGromovCompactness.MetricCPConvergenceOn K 1
      (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i0)) _ (hsub l)
        (dihedralMetric ε (L (l + i0)) hε (hL (l + i0))))
      ((dihedralRechartedMetric ε (1 / 2) hε (by norm_num)).restrictOpen _)
      ((dihedralRechartedMetric ε (1 / 2) hε (by norm_num)).restrictOpen _)) := by
  intro ε hε L s hL hs hsL hst hLst A
  let _modelMetric : MetricSpace sphereCylinderRechart :=
    inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
  let jm (i : ℕ) := dihedralInteriorPartial.{u} ε (L i) hε (hL i) (s i) (hs i) (hsL i) (A i)
  let n := sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)
  have hanchor (i : ℕ) : jm i n = dihedralCylinderMap (L i) (hL i) (s i) (A i) n := by
    obtain ⟨_hjm, hfun, _hmetric, _hballs⟩ :=
      dihedralInteriorPartial_data.{u} ε (L i) hε (hL i) (s i) (hs i) (hsL i) (A i)
    exact congrFun hfun n
  refine ⟨jm, hanchor, ?_⟩
  intro r hr
  obtain ⟨i0, hi0⟩ := Filter.eventually_atTop.mp
    ((Filter.Tendsto.eventually_ge_atTop hst r).and
      (Filter.Tendsto.eventually_ge_atTop hLst r))
  let U : TopologicalSpace.Opens sphereCylinderRechart := ⟨Metric.ball n r, Metric.isOpen_ball⟩
  have hsub : ∀ l, (U : Set sphereCylinderRechart) ⊆ (jm (l + i0)).source := by
    intro l x hx
    have hb := hi0 (l + i0) (by omega)
    obtain ⟨_hjm, _hfun, _hmetric, hballs⟩ :=
      dihedralInteriorPartial_data.{u} ε (L (l + i0)) hε (hL (l + i0)) (s (l + i0))
        (hs (l + i0)) (hsL (l + i0)) (A (l + i0))
    apply hballs r hr hb.1 hb.2
    change x ∈ Metric.ball n r at hx
    rwa [inducedMetricSpace_ball (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)) n] at hx
  refine ⟨i0, hsub, ?_⟩
  intro K _hK δ hδ
  refine ⟨0, ?_⟩
  intro l _hl
  have heq := dihedralInteriorPartial_pullback_on.{u} ε (L (l + i0)) hε (hL (l + i0))
    (s (l + i0)) (hs (l + i0)) (hsL (l + i0)) (A (l + i0)) U (hsub l)
  change CheegerGromovCompactness.metricDerivNormSupOn K 1
    (PartialDiffeomorph.pullbackMetricOn (jm (l + i0)) U (hsub l)
      (dihedralMetric ε (L (l + i0)) hε (hL (l + i0))))
    ((dihedralRechartedMetric ε (1 / 2) hε (by norm_num)).restrictOpen U)
    ((dihedralRechartedMetric ε (1 / 2) hε (by norm_num)).restrictOpen U) < δ
  rw [heq, CheegerGromovCompactness.metricDerivNormSupOn_self]
  exact hδ

theorem dihedralAxisRange (L : ℝ) (hL : 0 < L)
    (x : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) :
    0 ≤ dihedralAxis L x ∧ dihedralAxis L x ≤ L := by
  obtain ⟨p, _hp, ht, ha⟩ := exists_dihedralCanonicalLift x
  rw [ha L]
  constructor <;> nlinarith [ht.1, ht.2]
theorem dihedralMarginSubsequence (L : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (Tendsto (fun i => dihedralAxis (L (k i)) (z (k i))) atTop atTop ∧
        Tendsto (fun i => L (k i) - dihedralAxis (L (k i)) (z (k i))) atTop atTop ∨
      ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun i =>
        min (dihedralAxis (L (k i)) (z (k i)))
          (L (k i) - dihedralAxis (L (k i)) (z (k i)))) atTop (nhds c)) := by
  let m (i : ℕ) := min (dihedralAxis (L i) (z i)) (L i - dihedralAxis (L i) (z i))
  have hm : ∀ i, 0 ≤ m i := by
    intro i
    obtain ⟨h0, h1⟩ := dihedralAxisRange (L i) (hL i) (z i)
    exact le_min h0 (sub_nonneg.mpr h1)
  obtain ⟨k, hk, hd | hf⟩ := dihedralNonnegativeSubsequence m hm
  · refine ⟨k, hk, Or.inl ⟨?_, ?_⟩⟩
    · exact tendsto_atTop_mono (fun i => min_le_left _ _) hd
    · exact tendsto_atTop_mono (fun i => min_le_right _ _) hd
  · exact ⟨k, hk, Or.inr hf⟩

theorem dihedralCanonicalFrames (L : ℝ) (hL : 0 < L)
    (x : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier)
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      dihedralCylinderMap L hL (dihedralAxis L x) A
        (sphereCylinderRechartDiffeomorph (σ, 0)) = x ∧
      ∀ b : Bool, dihedralEndMap L hL b A
        (dihedralEndProjection (sphereCylinderRechartDiffeomorph
          (σ, if b then L - dihedralAxis L x else dihedralAxis L x))) = x := by
  obtain ⟨p, hp, _ht, ha⟩ := exists_dihedralCanonicalLift x
  obtain ⟨A, hA⟩ := dihedralSphereAlignment σ p.1
  have hdiv : dihedralAxis L x / (2 * L) = p.2 := by
    rw [ha L]
    field_simp
  have hpres : dihedralStandardPresentation.proj p = x := hp
  refine ⟨A, ?_, ?_⟩
  · have hphys := dihedralCylinderPhysical_formula L hL (dihedralAxis L x) A
      (sphereCylinderRechartDiffeomorph (σ, 0))
    have hz : dihedralCylinderPhysicalDiffeo L hL (dihedralAxis L x) A
        (sphereCylinderRechartDiffeomorph (σ, 0)) = sphereCylinderRechartDiffeomorph p := by
      apply sphereCylinderRechartDiffeomorph.symm.injective
      change sphereCylinderRechartDiffeomorph.symm
        (dihedralCylinderPhysicalDiffeo L hL (dihedralAxis L x) A
          (sphereCylinderRechartDiffeomorph (σ, 0))) =
        sphereCylinderRechartDiffeomorph.symm (sphereCylinderRechartDiffeomorph p)
      rw [hphys, sphereCylinderRechartDiffeomorph.symm_apply_apply]
      change ((sphereDiffeo (n := 2) A) σ, (dihedralAxis L x + 0) / (2 * L)) = p
      rw [hA, add_zero, hdiv]
    change dihedralProjection _ = x
    rw [hz]
    exact hp
  · intro b
    rw [dihedralEndMap_projection_formula, hA]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [hdiv]
      exact hpres
    · rw [sub_sub_cancel, hdiv]
      exact hpres

theorem dihedralFiniteBranch (f g : ℕ → ℝ) (c : ℝ)
    (ht : Tendsto (fun i => min (f i) (g i)) atTop (nhds c)) :
    ∃ b : Bool, ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ i, (if b then g (k i) else f (k i)) = min (f (k i)) (g (k i))) ∧
      Tendsto (fun i => if b then g (k i) else f (k i)) atTop (nhds c) := by
  by_cases hf : ∃ᶠ i in atTop, f i ≤ g i
  · obtain ⟨k, hk, hkg⟩ := extraction_of_frequently_atTop hf
    refine ⟨false, k, hk, ?_, ?_⟩
    · intro i
      exact (min_eq_left (hkg i)).symm
    · have heq : (fun i => f (k i)) = (fun i => min (f (k i)) (g (k i))) := by
        funext i
        exact (min_eq_left (hkg i)).symm
      change Tendsto (fun i => f (k i)) atTop (nhds c)
      rw [heq]
      exact ht.comp hk.tendsto_atTop
  · have hg : ∀ᶠ i in atTop, g i ≤ f i := by
      filter_upwards [not_frequently.mp hf] with i hi
      exact le_of_lt (lt_of_not_ge hi)
    obtain ⟨k, hk, hkg⟩ := extraction_of_frequently_atTop hg.frequently
    refine ⟨true, k, hk, ?_, ?_⟩
    · intro i
      exact (min_eq_right (hkg i)).symm
    · have heq : (fun i => g (k i)) = (fun i => min (f (k i)) (g (k i))) := by
        funext i
        exact (min_eq_right (hkg i)).symm
      change Tendsto (fun i => g (k i)) atTop (nhds c)
      rw [heq]
      exact ht.comp hk.tendsto_atTop

theorem dihedralMovingPointClassification (L : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (Tendsto (fun i => dihedralAxis (L (k i)) (z (k i))) atTop atTop ∧
        Tendsto (fun i => L (k i) - dihedralAxis (L (k i)) (z (k i))) atTop atTop ∨
      ∃ b : Bool, ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun i =>
        if b then L (k i) - dihedralAxis (L (k i)) (z (k i))
        else dihedralAxis (L (k i)) (z (k i))) atTop (nhds c)) := by
  obtain ⟨k, hk, hd | hf⟩ := dihedralMarginSubsequence L hL z
  · exact ⟨k, hk, Or.inl hd⟩
  · obtain ⟨c, hc, ht⟩ := hf
    obtain ⟨b, q, hq, _heq, hb⟩ := dihedralFiniteBranch
      (fun i => dihedralAxis (L (k i)) (z (k i)))
      (fun i => L (k i) - dihedralAxis (L (k i)) (z (k i))) c ht
    exact ⟨k ∘ q, hk.comp hq, Or.inr ⟨b, c, hc, hb⟩⟩
theorem dihedralMovingFrames (L : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier)
    (σ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ A : ℕ → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      (∀ i, dihedralCylinderMap (L i) (hL i) (dihedralAxis (L i) (z i)) (A i)
        (sphereCylinderRechartDiffeomorph (σ, 0)) = z i) ∧
      ∀ (i : ℕ) (b : Bool), dihedralEndMap (L i) (hL i) b (A i)
        (dihedralEndProjection (sphereCylinderRechartDiffeomorph
          (σ, if b then L i - dihedralAxis (L i) (z i) else dihedralAxis (L i) (z i)))) = z i := by
  choose A hA using fun i => dihedralCanonicalFrames (L i) (hL i) (z i) σ
  exact ⟨A, fun i => (hA i).1, fun i => (hA i).2⟩

attribute [local instance] dihedralEndSigma dihedralEndMetrizable dihedralEndRawConnected

theorem dihedralMovingGH :
  ∀ (ε : ℝ) (hε : 0 < ε) (L : ℕ → ℝ) (hL : ∀ i, 0 < L i),
    Tendsto L atTop atTop →
    ∀ z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier,
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (@GC.MetricGeometry.PointedGHConverges
        (fun _i : ℕ => (connectedSum projectiveThreeSpaceLift.{u}
          projectiveThreeSpaceLift.{u}).Carrier)
        (fun i => inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i))))
        sphereCylinderRechart
        (inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)))
        (fun i => z (k i))
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) ∨
      ∃ c : ℝ, 0 ≤ c ∧ @GC.MetricGeometry.PointedGHConverges
        (fun _i : ℕ => (connectedSum projectiveThreeSpaceLift.{u}
          projectiveThreeSpaceLift.{u}).Carrier)
        (fun i => inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i))))
        dihedralEndCarrier (inducedMetricSpace (dihedralEndMetric ε hε))
        (fun i => z (k i))
        (dihedralEndProjection
          (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, c)))) := by
  intro ε hε L hL hLt z
  obtain ⟨k, hk, hd | hf⟩ := dihedralMovingPointClassification L hL z
  · obtain ⟨A, hA, _hEnd⟩ := dihedralMovingFrames (fun i => L (k i))
      (fun i => hL (k i)) (fun i => z (k i)) GC.GraphManifold.Assembly.northPole
    have hg := dihedralCylinder_pointedGH.{u} ε hε (fun i => L (k i))
      (fun i => dihedralAxis (L (k i)) (z (k i))) (fun i => hL (k i)) hd.1 hd.2 A
    have heq : (fun i => dihedralCylinderMap (L (k i)) (hL (k i))
        (dihedralAxis (L (k i)) (z (k i))) (A i)
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))) =
        (fun i => z (k i)) := funext hA
    dsimp only at hg
    rw [heq] at hg
    exact ⟨k, hk, Or.inl hg⟩
  · obtain ⟨b, c, hc, ht⟩ := hf
    obtain ⟨A, _hCylinder, hA⟩ := dihedralMovingFrames (fun i => L (k i))
      (fun i => hL (k i)) (fun i => z (k i)) GC.GraphManifold.Assembly.northPole
    have hg := dihedralEnd_pointedGH.{u} ε hε (fun i => L (k i))
      (fun i => if b then L (k i) - dihedralAxis (L (k i)) (z (k i))
        else dihedralAxis (L (k i)) (z (k i))) (fun i => hL (k i)) b
      GC.GraphManifold.Assembly.northPole c (hLt.comp hk.tendsto_atTop) ht A
    have heq : (fun i => dihedralEndMap (L (k i)) (hL (k i)) b (A i)
        (dihedralEndProjection (sphereCylinderRechartDiffeomorph
          (GC.GraphManifold.Assembly.northPole,
            if b then L (k i) - dihedralAxis (L (k i)) (z (k i))
            else dihedralAxis (L (k i)) (z (k i)))))) = (fun i => z (k i)) :=
      funext (fun i => hA i b)
    dsimp only at hg
    rw [heq] at hg
    exact ⟨k, hk, Or.inr ⟨c, hc, hg⟩⟩

theorem dihedralMovingPointClassification_positive (L : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ((∀ i, 0 < dihedralAxis (L (k i)) (z (k i))) ∧
        (∀ i, dihedralAxis (L (k i)) (z (k i)) < L (k i)) ∧
        Tendsto (fun i => dihedralAxis (L (k i)) (z (k i))) atTop atTop ∧
        Tendsto (fun i => L (k i) - dihedralAxis (L (k i)) (z (k i))) atTop atTop ∨
      ∃ b : Bool, ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun i =>
        if b then L (k i) - dihedralAxis (L (k i)) (z (k i))
        else dihedralAxis (L (k i)) (z (k i))) atTop (nhds c)) := by
  obtain ⟨k, hk, hd | hf⟩ := dihedralMovingPointClassification L hL z
  · obtain ⟨i0, hi0⟩ := eventually_atTop.mp
      ((hd.1.eventually_ge_atTop 1).and (hd.2.eventually_ge_atTop 1))
    let q (i : ℕ) := i + i0
    have hq : StrictMono q := fun _i _j hij => Nat.add_lt_add_right hij i0
    refine ⟨k ∘ q, hk.comp hq, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · intro i
      have h := (hi0 (q i) (by dsimp [q]; omega)).1
      change 0 < dihedralAxis (L (k (q i))) (z (k (q i)))
      linarith
    · intro i
      have h := (hi0 (q i) (by dsimp [q]; omega)).2
      change dihedralAxis (L (k (q i))) (z (k (q i))) < L (k (q i))
      linarith
    · exact hd.1.comp hq.tendsto_atTop
    · exact hd.2.comp hq.tendsto_atTop
  · exact ⟨k, hk, Or.inr hf⟩

universe v
def dihedralNativeCharts {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T3Space N] [ConnectedSpace N] (gN : SmoothRiemannianMetric (𝓡 3) N) (n : N)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ → ℝ) (hL : ∀ i, 0 < L i)
    (z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier) : Prop :=
  let _modelMetric : MetricSpace N := inducedMetricSpace gN
  ∃ jm : ∀ _i, PartialDiffeomorph (𝓡 3) (𝓡 3) N
    (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier ∞,
    (∀ i, jm i n = z i) ∧ ∀ r : ℝ, 0 < r → ∃ i0 : ℕ,
    ∃ hsub : ∀ l, ((⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N)
      ⊆ (jm (l + i0)).source,
    ∀ K : Set (⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
      IsCompact K → CheegerGromovCompactness.MetricCPConvergenceOn K 1
        (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i0)) _ (hsub l)
          (dihedralMetric ε (L (l + i0)) hε (hL (l + i0))))
        (gN.restrictOpen _) (gN.restrictOpen _)


theorem dihedralMovingSmooth :
  ∀ (ε : ℝ) (hε : 0 < ε) (L : ℕ → ℝ) (hL : ∀ i, 0 < L i),
    Tendsto L atTop atTop →
    ∀ z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier,
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (dihedralNativeCharts
        (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))
        ε hε (fun i => L (k i)) (fun i => hL (k i)) (fun i => z (k i)) ∧
      @GC.MetricGeometry.PointedGHConverges
        (fun _i : ℕ => (connectedSum projectiveThreeSpaceLift.{u}
          projectiveThreeSpaceLift.{u}).Carrier)
        (fun i => inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i))))
        sphereCylinderRechart
        (inducedMetricSpace (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)))
        (fun i => z (k i))
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)) ∨
      ∃ c : ℝ, 0 ≤ c ∧ dihedralNativeCharts (dihedralEndMetric ε hε)
        (dihedralEndProjection
          (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, c)))
        ε hε (fun i => L (k i)) (fun i => hL (k i)) (fun i => z (k i)) ∧
      @GC.MetricGeometry.PointedGHConverges
        (fun _i : ℕ => (connectedSum projectiveThreeSpaceLift.{u}
          projectiveThreeSpaceLift.{u}).Carrier)
        (fun i => inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i))))
        dihedralEndCarrier (inducedMetricSpace (dihedralEndMetric ε hε))
        (fun i => z (k i))
        (dihedralEndProjection
          (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, c)))) := by
  intro ε hε L hL hLt z
  obtain ⟨k, hk, hd | hf⟩ := dihedralMovingPointClassification_positive L hL z
  · obtain ⟨A, hA, _hEnd⟩ := dihedralMovingFrames (fun i => L (k i))
      (fun i => hL (k i)) (fun i => z (k i)) GC.GraphManifold.Assembly.northPole
    have hg := dihedralCylinder_pointedGH.{u} ε hε (fun i => L (k i))
      (fun i => dihedralAxis (L (k i)) (z (k i))) (fun i => hL (k i)) hd.2.2.1 hd.2.2.2 A
    dsimp only at hg
    have heq : (fun i => dihedralCylinderMap (L (k i)) (hL (k i))
        (dihedralAxis (L (k i)) (z (k i))) (A i)
        (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0))) =
        (fun i => z (k i)) := funext hA
    rw [heq] at hg
    have hj := dihedralInterior_nativeCharts.{u} ε hε (fun i => L (k i))
      (fun i => dihedralAxis (L (k i)) (z (k i))) (fun i => hL (k i))
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 A
    dsimp only at hj
    obtain ⟨jm, ha, hb⟩ := hj
    exact ⟨k, hk, Or.inl ⟨⟨jm, fun i => (ha i).trans (hA i), hb⟩, hg⟩⟩
  · obtain ⟨b, c, hc, ht⟩ := hf
    obtain ⟨A, _hCylinder, hA⟩ := dihedralMovingFrames (fun i => L (k i))
      (fun i => hL (k i)) (fun i => z (k i)) GC.GraphManifold.Assembly.northPole
    let cs (i : ℕ) := if b then L (k i) - dihedralAxis (L (k i)) (z (k i))
      else dihedralAxis (L (k i)) (z (k i))
    have hg := dihedralEnd_pointedGH.{u} ε hε (fun i => L (k i)) cs
      (fun i => hL (k i)) b GC.GraphManifold.Assembly.northPole c
      (hLt.comp hk.tendsto_atTop) ht A
    dsimp only at hg
    have heq : (fun i => dihedralEndMap (L (k i)) (hL (k i)) b (A i)
        (dihedralEndProjection (sphereCylinderRechartDiffeomorph
          (GC.GraphManifold.Assembly.northPole, cs i)))) = (fun i => z (k i)) :=
      funext (fun i => hA i b)
    rw [heq] at hg
    have hj := exists_dihedralEnd_nativeCharts.{u} ε hε (fun i => L (k i)) cs
      (fun i => hL (k i)) b GC.GraphManifold.Assembly.northPole c
      (hLt.comp hk.tendsto_atTop) ht A
    dsimp only at hj
    obtain ⟨jm, ha, hb⟩ := hj
    exact ⟨k, hk, Or.inr ⟨c, hc, ⟨jm, fun i => (ha i).trans (hA i b), hb⟩, hg⟩⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
abbrev dihedralModelCarrier : Unit ⊕ ℝ → Type
  | .inl _ => sphereCylinderRechart
  | .inr _ => dihedralEndCarrier
instance dihedralModelTopology (b : Unit ⊕ ℝ) : TopologicalSpace (dihedralModelCarrier b) := by
  cases b <;> exact inferInstance
instance dihedralModelCharts (b : Unit ⊕ ℝ) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (dihedralModelCarrier b) := by
  cases b <;> exact inferInstance
instance dihedralModelManifold (b : Unit ⊕ ℝ) : IsManifold (𝓡 3) ∞ (dihedralModelCarrier b) := by
  cases b <;> exact inferInstance
instance dihedralModelT3 (b : Unit ⊕ ℝ) : T3Space (dihedralModelCarrier b) := by
  cases b <;> exact inferInstance
instance dihedralModelConnected (b : Unit ⊕ ℝ) : ConnectedSpace (dihedralModelCarrier b) := by
  cases b <;> exact inferInstance
instance dihedralModelTangentT2 (b : Unit ⊕ ℝ) :
    T2Space (TangentBundle (𝓡 3) (dihedralModelCarrier b)) := inferInstance
instance dihedralModelSigma (b : Unit ⊕ ℝ) : SigmaCompactSpace (dihedralModelCarrier b) := by
  cases b with
  | inl _ =>
    exact sphereCylinderRechartDiffeomorph.symm.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  | inr _ => exact dihedralEndSigma
def dihedralModelMetric (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    SmoothRiemannianMetric (𝓡 3) (dihedralModelCarrier b) :=
  match b with
  | .inl _ => dihedralRechartedMetric ε (1 / 2) hε (by norm_num)
  | .inr _ => dihedralEndMetric ε hε
def dihedralModelBase (b : Unit ⊕ ℝ) : dihedralModelCarrier b :=
  match b with
  | .inl _ => sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0)
  | .inr c => dihedralEndProjection
    (sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, c))

@[instance_reducible] def dihedralModelMetricSpace (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    MetricSpace (dihedralModelCarrier b) := inducedMetricSpace (dihedralModelMetric ε hε b)
@[instance_reducible] def dihedralModelBundle (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    RiemannianBundle (fun x : dihedralModelCarrier b => TangentSpace (𝓡 3) x) :=
  ⟨(dihedralModelMetric ε hε b).toRiemannianMetric⟩
theorem dihedralModelRiemannian (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    letI := dihedralModelMetricSpace ε hε b
    letI := dihedralModelBundle ε hε b
    IsRiemannianManifold (𝓡 3) (dihedralModelCarrier b) :=
  inducedMetricSpace_isRiemannianManifold (dihedralModelMetric ε hε b)
theorem dihedralModelContinuousBundle (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    letI := dihedralModelBundle ε hε b
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (fun x : dihedralModelCarrier b => TangentSpace (𝓡 3) x) :=
  isContinuousRiemannianBundle_of_smoothRiemannianMetric (dihedralModelMetric ε hε b)
theorem dihedralModelNorm (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    letI := dihedralModelBundle ε hε b
    IsMetricNorm (I := 𝓡 3) (dihedralModelMetric ε hε b) :=
  isMetricNorm_of_smoothRiemannianMetric (dihedralModelMetric ε hε b)
theorem dihedralModelComplete (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    DifferentialGeometry.RiemannianMetricComplete (dihedralModelMetric ε hε b) := by
  cases b with
  | inl _ => exact dihedralRechartedMetric_complete ε (1 / 2) hε (by norm_num)
  | inr _ => exact dihedralEndMetric_complete ε hε
theorem dihedralModelCompleteSpace (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    letI := dihedralModelMetricSpace ε hε b
    CompleteSpace (dihedralModelCarrier b) :=
  riemannianMetricComplete_iff_inducedMetricSpace.mp (dihedralModelComplete ε hε b)

theorem dihedralCylinderModelSectional (ε : ℝ) (hε : 0 < ε) (x : sphereCylinderRechart) :
    SectionalBoundedBelowAt (dihedralRechartedMetric ε (1 / 2) hε (by norm_num)) x 0 := by
  rw [← dihedralEndMetric_pullback ε hε]
  intro v w
  simp only [zero_mul]
  rw [Curvature.metricRm04StandardAt_localPullMetric]
  have h := dihedralEndMetric_sectional_nonneg ε hε (dihedralEndProjection x)
    (mfderiv (𝓡 3) (𝓡 3) dihedralEndProjection x v)
    (mfderiv (𝓡 3) (𝓡 3) dihedralEndProjection x w)
  simpa only [zero_mul] using h
theorem dihedralModelSectional (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ)
    (x : dihedralModelCarrier b) : SectionalBoundedBelowAt (dihedralModelMetric ε hε b) x 0 := by
  cases b with
  | inl _ => exact dihedralCylinderModelSectional ε hε x
  | inr _ => exact dihedralEndMetric_sectional_nonneg ε hε x
open GC.MetricGeometry

theorem dihedralModelCone :
  ∀ (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ),
  let modelMetric : MetricSpace (dihedralModelCarrier b) := dihedralModelMetricSpace ε hε b
  ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
    ProperSpace C ∧ ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R0 : ℝ,
    ∀ R : ℝ, ∀ hR : 0 < R, R0 ≤ R →
      Nonempty (@KleinerLottApprox (dihedralModelCarrier b) C
        (modelMetric.rescale R⁻¹ (inv_pos.mpr hR)) mC (dihedralModelBase b) o τ) := by
  intro ε hε b
  let modelMetric : MetricSpace (dihedralModelCarrier b) := dihedralModelMetricSpace ε hε b
  let _modelComplete : CompleteSpace (dihedralModelCarrier b) := dihedralModelCompleteSpace ε hε b
  obtain ⟨C, mC, o, hcone, hproper, _hcomplete, _hsegment, _hfour, _hdim, hKL⟩ :=
    exists_cone_at_infinity_package_of_sectional_nonneg (dihedralModelMetric ε hε b)
      (inducedMetricSpace_hmetric _) (dihedralModelSectional ε hε b) (dihedralModelBase b)
  exact ⟨C, mC, o, hcone, hproper, hKL⟩


theorem dihedralIndexedMoving :
  ∀ (ε : ℝ) (hε : 0 < ε) (L : ℕ → ℝ) (hL : ∀ i, 0 < L i),
    Tendsto L atTop atTop →
    ∀ z : ℕ → (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier,
    ∃ b : Unit ⊕ ℝ, ∃ k : ℕ → ℕ, StrictMono k ∧
      @GC.MetricGeometry.PointedGHConverges
        (fun _i : ℕ => (connectedSum projectiveThreeSpaceLift.{u}
          projectiveThreeSpaceLift.{u}).Carrier)
        (fun i => inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i))))
        (dihedralModelCarrier b) (dihedralModelMetricSpace ε hε b)
        (fun i => z (k i)) (dihedralModelBase b) ∧
      dihedralNativeCharts (dihedralModelMetric ε hε b) (dihedralModelBase b)
        ε hε (fun i => L (k i)) (fun i => hL (k i)) (fun i => z (k i)) ∧
      ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ (j : ℕ)
        (y : (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier),
        SectionalBoundedBelowAt (dihedralMetric ε (L (k j)) hε (hL (k j))) y
          (-((Hb j)⁻¹ ^ 2)) := by
  intro ε hε L hL hLt z
  have hcurv (k : ℕ → ℕ) : ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧
      ∀ (j : ℕ) (y : (connectedSum projectiveThreeSpaceLift.{u}
        projectiveThreeSpaceLift.{u}).Carrier),
      SectionalBoundedBelowAt (dihedralMetric ε (L (k j)) hε (hL (k j))) y
        (-((Hb j)⁻¹ ^ 2)) := by
    let Hb (j : ℕ) : ℝ := (j : ℝ) + 1
    refine ⟨Hb, tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop, ?_⟩
    intro j y
    exact SectionalBoundedBelowAt.mono
      (dihedralMetric_sectional_nonneg ε (L (k j)) hε (hL (k j)) y)
      (neg_nonpos.mpr (sq_nonneg ((Hb j)⁻¹)))
  obtain ⟨k, hk, hi | he⟩ := dihedralMovingSmooth.{u} ε hε L hL hLt z
  · exact ⟨Sum.inl (), k, hk, hi.2, hi.1, hcurv k⟩
  · obtain ⟨c, _hc, hm, hg⟩ := he
    exact ⟨Sum.inr c, k, hk, hg, hm, hcurv k⟩

end DifferentialGeometry.Geometry.Collapse
