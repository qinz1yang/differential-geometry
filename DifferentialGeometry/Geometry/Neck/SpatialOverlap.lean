import DifferentialGeometry.Geometry.Neck.SpatialTolerance
import DifferentialGeometry.Topology.GraphBand
import DifferentialGeometry.Topology.Order.DisjointGraphs
import DifferentialGeometry.Geometry.Neck.SpatialOscillation
import DifferentialGeometry.Geometry.Neck.OverlapBand
import DifferentialGeometry.Geometry.Neck.SpatialChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import DifferentialGeometry.Geometry.Metric.Distance.Ball

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem SpatialNeck.ball_subset_closed_slab
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I3 M} {p : M} {eps r : ℝ}
    (nk : SpatialNeck g eps p) (hr : 0 < r) (hreps : r < eps⁻¹) :
    riemannianBallOf (DifferentialGeometry.scaleMetric (metricScalarAt g p) nk.Q_pos g) p (r / 2) ⊆
      nk.map '' (univ ×ˢ Icc (-r) r) := by
  have hslab : (univ ×ˢ Icc (-r) r : Set Cylinder) ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, (neg_lt_neg hreps).trans_le hz.2.1, hz.2.2.trans_lt hreps⟩
  have h := collar_ball_subset_image nk.cylinder _ nk.map nk.comparison rfl
    (by linarith [nk.eps_small]) (by simp) hr nk.domain hslab nk.center
  simpa only [nk.center_eq] using h

private theorem exists_uniform_closed_slab_radius :
    ∃ R : ℝ, 0 < R ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        (g : SmoothRiemannianMetric I3 M) (p : M) (eps : ℝ),
        eps ≤ 1 / 32 → ∀ nk : SpatialNeck g eps p,
          ∀ z ∈ univ ×ˢ Icc (-1 : ℝ) 1,
            riemannianEDistOf (scaleMetric (metricScalarAt g p) nk.Q_pos g)
              p (nk.map z) ≤ ENNReal.ofReal R := by
  obtain ⟨R, hR, hbound⟩ := exists_uniform_spatial_neck_image_radius.{u}
    (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1 / 2)
  refine ⟨R, hR, ?_⟩
  intro M _ _ _ g p eps heps nk z hz
  let nk' := nk.mono heps (by norm_num : (1 / 32 : ℝ) < 1 / 11)
  apply hbound M g p nk' z
  norm_num only [one_div, inv_inv, mem_prod, mem_univ, true_and, mem_Ioo]
  constructor <;> linarith [hz.2.1, hz.2.2]

private theorem scaled_edist_le_twice
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 4 * b) (x y : M) :
    riemannianEDistOf (scaleMetric a ha g) x y ≤
      2 * riemannianEDistOf (scaleMetric b hb g) x y := by
  have hs : Real.sqrt a ≤ 2 * Real.sqrt b := by
    nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [edistOf_scale, edistOf_scale, ← mul_assoc]
  apply mul_le_mul' _ le_rfl
  have h := ENNReal.ofReal_le_ofReal hs
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  norm_num only [ENNReal.ofReal_ofNat] at h
  exact h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem intrinsic_edist_triangle
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) (x y z : M) :
    riemannianEDistOf g x z ≤ riemannianEDistOf g x y + riemannianEDistOf g y z := by
  let : RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle (I := I3) (x := x) (y := y) (z := z)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem intrinsic_edist_comm
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) (x y : M) :
    riemannianEDistOf g x y = riemannianEDistOf g y x := by
  let : RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm (I := I3) (x := x) (y := y)

theorem exists_spatial_neck_intersection_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 / 200000 ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
          IsCompact S ∧ IsConnected S ∧
          S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
          S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S,
            Real.sqrt (g.inner x
              (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)
              (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)) ≤ 369424 * eps := by
  obtain ⟨R, hR, hbound⟩ := exists_uniform_closed_slab_radius.{u}
  let B : ℝ := 12 * (R + 1)
  have hB : 1 < B := by dsimp only [B]; linarith
  let eta : ℝ := min (1 / 400000) (min (1 / 32) (1 / (2 * B)))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have heta_small : eta < 1 / 200000 := by
    have := min_le_left (1 / 400000 : ℝ) (min (1 / 32) (1 / (2 * B)))
    dsimp only [eta]
    linarith
  refine ⟨eta, heta, heta_small, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hmeet
  have hsmall : eps < 1 / 200000 := heps.trans_lt heta_small
  have heps32 : eps ≤ 1 / 32 := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsB : eps ≤ 1 / (2 * B) := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hBinv : B + 1 < eps⁻¹ := by
    have hbpos : 0 < 2 * B := by linarith
    have hm := (le_div_iff₀ hbpos).mp hepsB
    apply (lt_inv_comm₀ (by linarith : 0 < B + 1) nk₀.eps_pos).mpr
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ (by linarith : 0 < B + 1)).mpr
    nlinarith [nk₀.eps_pos]
  have hunit : (1 : ℝ) < eps⁻¹ := by linarith
  have hunitCore : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  obtain ⟨x, hx₀, hx₁⟩ := hmeet
  have hratio₁ := nk₁.scalar_ratio_of_common_point nk₀ hsmall
    ((image_mono hunitCore) hx₁) ((image_mono hunitCore) hx₀)
  have hratio₀ := nk₀.scalar_ratio_of_common_point nk₁ hsmall
    ((image_mono hunitCore) hx₀) ((image_mono hunitCore) hx₁)
  have hscalar₁ : metricScalarAt g p₁ ≤ 4 * metricScalarAt g p₀ := by
    have h := (abs_le.mp hratio₁).2
    have hdiv : metricScalarAt g p₁ / metricScalarAt g p₀ ≤ 4 := by linarith
    exact (div_le_iff₀ nk₀.Q_pos).mp hdiv
  have hscalar₀ : metricScalarAt g p₀ ≤ 4 * metricScalarAt g p₁ := by
    have h := (abs_le.mp hratio₀).2
    have hdiv : metricScalarAt g p₀ / metricScalarAt g p₁ ≤ 4 := by linarith
    exact (div_le_iff₀ nk₁.Q_pos).mp hdiv
  have himage (p : M) (np : SpatialNeck g eps p) (y : M)
      (hy : y ∈ np.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :
      riemannianEDistOf (scaleMetric (metricScalarAt g p) np.Q_pos g) p y ≤
        ENNReal.ofReal R := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact hbound M g p eps heps32 np z hz
  have hcross (p q : M) (np : SpatialNeck g eps p) (nq : SpatialNeck g eps q)
      (hscalar : metricScalarAt g q ≤ 4 * metricScalarAt g p)
      (hxnp : x ∈ np.map '' (univ ×ˢ Icc (-1 : ℝ) 1))
      (hxnq : x ∈ nq.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :
      np.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ nq.map '' (univ ×ˢ Icc (-B) B) := by
    intro y hy
    apply nq.ball_subset_closed_slab (by linarith) (by linarith)
    let gq := scaleMetric (metricScalarAt g q) nq.Q_pos g
    have hqx := himage q nq x hxnq
    have hpx := (scaled_edist_le_twice g nq.Q_pos np.Q_pos hscalar p x).trans
      (mul_le_mul' le_rfl (himage p np x hxnp))
    have hpy := (scaled_edist_le_twice g nq.Q_pos np.Q_pos hscalar p y).trans
      (mul_le_mul' le_rfl (himage p np y hy))
    have hqp : riemannianEDistOf gq q p ≤ ENNReal.ofReal R + 2 * ENNReal.ofReal R := by
      apply (intrinsic_edist_triangle gq q x p).trans
      rw [intrinsic_edist_comm gq x p]
      exact add_le_add hqx hpx
    have hqy : riemannianEDistOf gq q y ≤
        (ENNReal.ofReal R + 2 * ENNReal.ofReal R) + 2 * ENNReal.ofReal R :=
      (intrinsic_edist_triangle gq q p y).trans (add_le_add hqp hpy)
    have hreal : (ENNReal.ofReal R + 2 * ENNReal.ofReal R) + 2 * ENNReal.ofReal R =
        ENNReal.ofReal (5 * R) := by
      have heq : (ENNReal.ofReal R + 2 * ENNReal.ofReal R) + 2 * ENNReal.ofReal R =
          5 * ENNReal.ofReal R := by ring
      rw [heq, ← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by norm_num)]
    rw [hreal] at hqy
    exact hqy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < B / 2)).mpr
      (by dsimp only [B]; linarith))
  have hBcore : (univ ×ˢ Icc (-B) B : Set Cylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hunitB : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆ univ ×ˢ Icc (-B) B := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hsub₀ : S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) :=
    union_subset ((image_mono hunitB).trans (image_mono hBcore))
      ((hcross p₁ p₀ nk₁ nk₀ hscalar₀ hx₁ hx₀).trans (image_mono hBcore))
  have hsub₁ : S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) :=
    union_subset ((hcross p₀ p₁ nk₀ nk₁ hscalar₁ hx₀ hx₁).trans (image_mono hBcore))
      ((image_mono hunitB).trans (image_mono hBcore))
  have hcompact (p : M) (nk : SpatialNeck g eps p) :
      IsCompact (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (nk.map.contMDiffOn_toFun.continuousOn.mono (hunitCore.trans nk.domain))
  have hpre (p : M) (nk : SpatialNeck g eps p) :
      IsPreconnected (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
    let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
        (0 : ThreeSpace) 1)
    exact (isPreconnected_univ.prod isPreconnected_Icc).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono (hunitCore.trans nk.domain))
  have hSpre : IsPreconnected S := IsPreconnected.union x hx₀ hx₁ (hpre p₀ nk₀) (hpre p₁ nk₁)
  have hSin (p : M) (nk : SpatialNeck g eps p)
      (hs : S ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1))) :
      S ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    apply hs.trans (image_mono _)
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  obtain ⟨σ, hσ, hgrad⟩ := nk₀.exists_sign_axial_gradient_bound_on_preconnected nk₁
    hsmall hsmall hSpre (hSin p₀ nk₀ hsub₀) (hSin p₁ nk₁ hsub₁)
  refine ⟨(hcompact p₀ nk₀).union (hcompact p₁ nk₁),
    ⟨⟨x, Or.inl hx₀⟩, hSpre⟩, hsub₀, hsub₁, σ, hσ, ?_⟩
  intro y hy
  convert hgrad y hy using 1
  ring

theorem exists_spatial_neck_overlap_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 / 200000 ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          riemannianEDistOf (scaleMetric (metricScalarAt g p₀) nk₀.Q_pos g) p₀ p₁ <
            ENNReal.ofReal (1 / 8 : ℝ) →
          let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
          IsCompact S ∧ IsConnected S ∧
          p₀ ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
          p₁ ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∧
          S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
          S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S,
            Real.sqrt (g.inner x
              (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)
              (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)) ≤ 369424 * eps := by
  obtain ⟨eta, heta, heta_small, hintersection⟩ := exists_spatial_neck_intersection_tolerance.{u}
  refine ⟨eta, heta, heta_small, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hnear
  have hunit : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hunitCore : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, (neg_lt_neg hunit).trans_le hz.2.1, hz.2.2.trans_lt hunit⟩
  have h₁₀ : p₁ ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
    apply nk₀.ball_subset_closed_slab (by norm_num : (0 : ℝ) < 1) hunit
    exact hnear.trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by norm_num))
  have h₁₁ : p₁ ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(nk₁.center, 0), ⟨mem_univ _, by norm_num⟩, nk₁.center_eq⟩
  have hratio := nk₁.scalar_ratio_of_common_point nk₀ (heps.trans_lt heta_small)
    ((image_mono hunitCore) h₁₁) ((image_mono hunitCore) h₁₀)
  have hscalar : metricScalarAt g p₁ ≤ 4 * metricScalarAt g p₀ := by
    have h := (abs_le.mp hratio).2
    apply (div_le_iff₀ nk₀.Q_pos).mp
    linarith [heps.trans_lt heta_small]
  have h₀₁ : p₀ ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
    apply nk₁.ball_subset_closed_slab (by norm_num : (0 : ℝ) < 1) hunit
    change riemannianEDistOf (scaleMetric (metricScalarAt g p₁) nk₁.Q_pos g) p₁ p₀ < _
    rw [intrinsic_edist_comm _ p₁ p₀]
    have hle := scaled_edist_le_twice g nk₁.Q_pos nk₀.Q_pos hscalar p₀ p₁
    have hmul : 2 * riemannianEDistOf (scaleMetric (metricScalarAt g p₀) nk₀.Q_pos g) p₀ p₁ <
        2 * ENNReal.ofReal (1 / 8 : ℝ) :=
      ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnear
    apply hle.trans_lt (hmul.trans _)
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  obtain ⟨hcompact, hconnected, hsub₀, hsub₁, hgrad⟩ :=
    hintersection eps heps M g p₀ p₁ nk₀ nk₁ ⟨p₁, h₁₀, h₁₁⟩
  exact ⟨hcompact, hconnected, h₀₁, h₁₀, hsub₀, hsub₁, hgrad⟩

private theorem axial_contMDiffAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p x : M}
    (nk : SpatialNeck g eps p) (heps : eps < 1 / 200000)
    (hx : x ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :
    ContMDiffAt I3 𝓘(ℝ) 1 nk.cylindricalChart.axial x := by
  obtain ⟨_, _, hsmooth, _⟩ := nk.cylindricalChart.exists_least_ricci_field_close_to_gradient g
    isOpen_univ eps heps nk.cylindricalChart_metricCloseOn
  have hmem : x ∈ nk.cylindricalChart.target := hx
  exact ((hsmooth x hmem).contMDiffAt
    (nk.cylindricalChart.target.isOpen.mem_nhds hmem)).of_le (by simp)

private theorem signed_axial_mfderiv_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) {u v : M → ℝ} {σ L : ℝ} {x : M}
    (hu : MDifferentiableAt I3 𝓘(ℝ) u x) (hv : MDifferentiableAt I3 𝓘(ℝ) v x)
    (hgrad : Real.sqrt (g.inner x
      (Geometry.Operator.gradFun g u x - σ • Geometry.Operator.gradFun g v x)
      (Geometry.Operator.gradFun g u x - σ • Geometry.Operator.gradFun g v x)) ≤ L) :
    ∀ w : TangentSpace I3 x,
      |(show ℝ from mfderiv I3 𝓘(ℝ) (fun y => u y - σ * v y) x w)| ≤
        L * Real.sqrt (g.inner x w w) := by
  intro w
  have hh := (Geometry.Gradient.abs_mvfderiv_signed_difference_le_gradient_norm g u v σ x w).trans
    (mul_le_mul_of_nonneg_right hgrad (Real.sqrt_nonneg _))
  have heq : mvfderiv I3 (fun y => u y - σ * v y) x w =
      mvfderiv I3 u x w - σ * mvfderiv I3 v x w := by
    have hconst : MDifferentiableAt I3 𝓘(ℝ) (fun y => σ * v y) x :=
      mdifferentiableAt_const.mul hv
    rw [mvfderiv_fun_sub hu hconst]
    rw [DifferentialGeometry.mvfderiv_const_mul I3 σ hv]
    rfl
  exact heq ▸ hh

theorem exists_spatial_neck_anchored_overlap_estimates :
    ∃ eta C : ℝ, 0 < eta ∧ eta < 1 / 200000 ∧ 0 < C ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (z : M), z ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) →
          z ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) →
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            let c := nk₀.cylindricalChart.axial z - σ * nk₁.cylindricalChart.axial z
            ∀ x ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪
                nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
              |nk₀.cylindricalChart.axial x - σ * nk₁.cylindricalChart.axial x - c| ≤
                C * eps / Real.sqrt (metricScalarAt g p₀) ∧
              Real.sqrt (g.inner x
                (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                  σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)
                (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
                  σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)) ≤
                369424 * eps := by
  obtain ⟨eta, heta, heta_small, hcontrol⟩ := exists_spatial_neck_intersection_tolerance.{u}
  obtain ⟨D, hD, hosc⟩ := exists_spatial_neck_slab_oscillation_constant.{u}
  refine ⟨eta, 2 * D * 369424, heta, heta_small, by positivity, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ z hz₀ hz₁
  have hepspos := nk₀.eps_pos
  obtain ⟨_, _, hsub₀, hsub₁, σ, hσ, hgrad⟩ :=
    hcontrol eps heps M g p₀ p₁ nk₀ nk₁ ⟨z, hz₀, hz₁⟩
  let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hfull (x : M) (hx : x ∈ S) :
      x ∈ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
      x ∈ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    have hm : (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) : Set Cylinder) ⊆
        univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
      intro y hy
      exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
    exact ⟨(image_mono hm) (hsub₀ hx), (image_mono hm) (hsub₁ hx)⟩
  let f : M → ℝ := fun x => nk₀.cylindricalChart.axial x - σ * nk₁.cylindricalChart.axial x
  have hf₀ (x : M) (hx : x ∈ S) := axial_contMDiffAt nk₀ (heps.trans_lt heta_small) (hfull x hx).1
  have hf₁ (x : M) (hx : x ∈ S) := axial_contMDiffAt nk₁ (heps.trans_lt heta_small) (hfull x hx).2
  have hf (x : M) (hx : x ∈ S) : ContMDiffAt I3 𝓘(ℝ) 1 f x :=
    (hf₀ x hx).sub (contMDiffAt_const.mul (hf₁ x hx))
  have hb (x : M) (hx : x ∈ S) := signed_axial_mfderiv_bound g
    ((hf₀ x hx).mdifferentiableAt one_ne_zero) ((hf₁ x hx).mdifferentiableAt one_ne_zero)
    (hgrad x hx)
  have hratio := nk₀.scalar_ratio_of_common_point nk₁ (heps.trans_lt heta_small)
    (hfull z (Or.inl hz₀)).1 (hfull z (Or.inl hz₀)).2
  have hQ : metricScalarAt g p₀ ≤ 4 * metricScalarAt g p₁ := by
    apply (div_le_iff₀ nk₁.Q_pos).mp
    have hh := (abs_le.mp hratio).2
    linarith [heps.trans_lt heta_small]
  have hsqrt : Real.sqrt (metricScalarAt g p₀) ≤ 2 * Real.sqrt (metricScalarAt g p₁) := by
    nlinarith [Real.sq_sqrt nk₀.Q_pos.le, Real.sq_sqrt nk₁.Q_pos.le,
      Real.sqrt_nonneg (metricScalarAt g p₀), Real.sqrt_nonneg (metricScalarAt g p₁)]
  refine ⟨σ, hσ, ?_⟩
  dsimp only
  intro x hx
  refine ⟨?_, hgrad x hx⟩
  change |f x - f z| ≤ _
  rcases hx with hx | hx
  · have hh := hosc M g eps p₀ nk₀ f (369424 * eps) (by positivity)
      (fun y hy => hf y (Or.inl hy)) (fun y hy => hb y (Or.inl hy)) x hx z hz₀
    exact hh.trans (by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      nlinarith [nk₀.eps_pos])
  · have hh := hosc M g eps p₁ nk₁ f (369424 * eps) (by positivity)
      (fun y hy => hf y (Or.inr hy)) (fun y hy => hb y (Or.inr hy)) x hx z hz₁
    apply hh.trans
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr nk₁.Q_pos)
      (Real.sqrt_pos.mpr nk₀.Q_pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ D * (369424 * eps) by positivity)]

theorem exists_spatial_neck_ordered_overlap_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (z : M), z ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) →
          z ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) →
          let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
          S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
          S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            let c := nk₀.cylindricalChart.axial z - σ * nk₁.cylindricalChart.axial z
            let ψ := fun x : Sphere 2 × Icc (-1 : ℝ) 1 =>
              nk₁.map.symm (nk₀.map (x.1, (x.2 : ℝ)))
            let e := fun x => ((ψ x).1,
              σ * ((Real.sqrt (metricScalarAt g p₁))⁻¹ * (ψ x).2) + c)
            ∃ h : C(Sphere 2 × Icc (-1 : ℝ) 1, ℝ),
              (∀ x, e x = ((e x).1, h ((e x).1, x.2))) ∧
              (∀ p, StrictMono (fun t => h (p, t))) ∧
              range e = {y | h (y.1, ⟨-1, le_rfl, by norm_num⟩) ≤ y.2 ∧
                y.2 ≤ h (y.1, ⟨1, by norm_num, le_rfl⟩)} ∧
              ∀ s t : Icc (-1 : ℝ) 1,
                e '' ((univ : Set (Sphere 2)) ×ˢ Icc s t) =
                  {y | h (y.1, s) ≤ y.2 ∧ y.2 ≤ h (y.1, t)} := by
  obtain ⟨eta₀, C, heta₀, hsmall₀, hC, hvalue⟩ := exists_spatial_neck_anchored_overlap_estimates.{u}
  obtain ⟨eta₁, heta₁, _, hoverlap⟩ := exists_spatial_neck_intersection_tolerance.{u}
  let eta : ℝ := min eta₀ (min eta₁ (min (1 / (4 * 369424)) (1 / (2 * C))))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ z hz₀ hz₁
  have heps₀ : eps ≤ eta₀ := heps.trans (min_le_left _ _)
  have heps₁ : eps ≤ eta₁ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsG : eps ≤ 1 / (4 * 369424) :=
    heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsC : eps ≤ 1 / (2 * C) :=
    heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨σ, hσ, hest⟩ := hvalue eps heps₀ M g p₀ p₁ nk₀ nk₁ z hz₀ hz₁
  obtain ⟨_, _, hsub₀, hsub₁, _⟩ := hoverlap eps heps₁ M g p₀ p₁ nk₀ nk₁ ⟨z, hz₀, hz₁⟩
  let c := nk₀.cylindricalChart.axial z - σ * nk₁.cylindricalChart.axial z
  have hunit : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hcollar (x : Sphere 2 × Icc (-1 : ℝ) 1) :
      (x.1, (x.2 : ℝ)) ∈ nk₀.cylindricalChart.domain :=
    ⟨mem_univ _, (neg_lt_neg hunit).trans_le x.2.property.1, x.2.property.2.trans_lt hunit⟩
  have htarget (x : Sphere 2 × Icc (-1 : ℝ) 1) :
      (nk₀.cylindricalChart.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M) ∈
        nk₁.cylindricalChart.target := by
    have hh := hsub₁ (Or.inl ⟨(x.1, (x.2 : ℝ)), ⟨mem_univ _, x.2.property⟩, rfl⟩)
    apply (image_mono (show (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) : Set Cylinder) ⊆
        univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ from ?_)) hh
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  have hroot : Real.sqrt (1 + eps) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    linarith [nk₀.eps_small]
  have hgradsmall : (369424 * eps) * Real.sqrt (1 + eps) < 1 := by
    have hn := nk₀.eps_pos
    have hg := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 369424 * eps by positivity)
    nlinarith
  have hsep : 2 * (C * eps / Real.sqrt (metricScalarAt g p₀)) <
      (Real.sqrt nk₀.cylindricalChart.scale)⁻¹ * (1 - (-1)) := by
    change 2 * (C * eps / Real.sqrt (metricScalarAt g p₀)) <
      (Real.sqrt (metricScalarAt g p₀))⁻¹ * (1 - (-1))
    rw [div_eq_mul_inv]
    have hc := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hepsC
    have hp := inv_pos.mpr (Real.sqrt_pos.mpr nk₀.Q_pos)
    nlinarith [mul_le_mul_of_nonneg_right hc hp.le]
  obtain ⟨h, hh, hmono, hrange, hsub⟩ :=
    nk₀.cylindricalChart.exists_ordered_graph_band_of_gradient_close nk₁.cylindricalChart g
      (-1) 1 (by norm_num) hcollar htarget eps (by linarith [nk₀.eps_small])
      nk₁.cylindricalChart_metricCloseOn (fun _ => mem_univ _) σ c (369424 * eps)
      (C * eps / Real.sqrt (metricScalarAt g p₀)) hσ hgradsmall
      (fun x => (hest _ (Or.inl ⟨(x.1, (x.2 : ℝ)), ⟨mem_univ _, x.2.property⟩, rfl⟩)).2)
      (fun x => (hest _ (Or.inl ⟨(x.1, (x.2 : ℝ)), ⟨mem_univ _, x.2.property⟩, rfl⟩)).1) hsep
  exact ⟨hsub₀, hsub₁, σ, hσ, h, hh, hmono, hrange, hsub⟩

theorem exists_spatial_neck_graph_band_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          ∃ a b : Sphere 2 → ℝ, Continuous a ∧ Continuous b ∧ (∀ p, a p < b p) ∧
            let A := {x : Cylinder | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}
            A ⊆ nk₁.map.source ∧
            nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) = nk₁.map '' A := by
  obtain ⟨eta, heta, horder⟩ := exists_spatial_neck_ordered_overlap_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hmeet
  obtain ⟨z, hz₀, hz₁⟩ := hmeet
  obtain ⟨_, hbuffer, σ, hσ, h, _, hmono, hrange, _⟩ :=
    horder eps heps M g p₀ p₁ nk₀ nk₁ z hz₀ hz₁
  let ψ := fun x : Sphere 2 × Icc (-1 : ℝ) 1 => nk₁.map.symm (nk₀.map (x.1, (x.2 : ℝ)))
  let c := nk₀.cylindricalChart.axial z - σ * nk₁.cylindricalChart.axial z
  let s := σ * (Real.sqrt (metricScalarAt g p₁))⁻¹
  have hs : s ≠ 0 := mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num)
    (inv_ne_zero (Real.sqrt_pos.mpr nk₁.Q_pos).ne')
  let lo : Icc (-1 : ℝ) 1 := ⟨-1, le_rfl, by norm_num⟩
  let hi : Icc (-1 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩
  have hcontlo : Continuous (fun p : Sphere 2 => h (p, lo)) :=
    h.continuous.comp (continuous_id.prodMk continuous_const)
  have hconthi : Continuous (fun p : Sphere 2 => h (p, hi)) :=
    h.continuous.comp (continuous_id.prodMk continuous_const)
  have hlt (p : Sphere 2) : h (p, lo) < h (p, hi) := hmono p (by change (-1 : ℝ) < 1; norm_num)
  have hr : range (fun x => ((ψ x).1, s * (ψ x).2 + c)) =
      {y : Cylinder | h (y.1, lo) ≤ y.2 ∧ y.2 ≤ h (y.1, hi)} := by
    simpa only [ψ, s, c, mul_assoc, lo, hi] using hrange
  obtain ⟨a, b, ha, hb, hab, hband⟩ :=
    DifferentialGeometry.Topology.exists_graph_band_of_affine_height ψ hs hcontlo hconthi hlt hr
  have htarget (x : Sphere 2 × Icc (-1 : ℝ) 1) : nk₀.map (x.1, (x.2 : ℝ)) ∈ nk₁.map.target := by
    obtain ⟨y, hy, hyeq⟩ := hbuffer
      (Or.inl ⟨(x.1, (x.2 : ℝ)), ⟨mem_univ _, x.2.property⟩, rfl⟩)
    rw [← hyeq]
    apply nk₁.map.map_source
    exact nk₁.domain ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := hband.symm ▸ hy
    exact nk₁.map.map_target (htarget x)
  · rw [← hband]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let v : Sphere 2 × Icc (-1 : ℝ) 1 := (x.1, ⟨x.2, hx.2⟩)
      exact ⟨ψ v, mem_range_self v, nk₁.map.right_inv (htarget v)⟩
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      have heq := nk₁.map.right_inv (htarget x)
      exact heq ▸ ⟨(x.1, (x.2 : ℝ)), ⟨mem_univ _, x.2.property⟩, rfl⟩

theorem exists_spatial_neck_triple_gap_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ p₂ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (nk₂ : SpatialNeck g eps p₂),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          (nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          Disjoint (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1))
            (nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) →
          ∃ δ σ : ℝ, 0 < δ ∧ (σ = 1 ∨ σ = -1) ∧ ∃ m : C(Sphere 2, ℝ),
            (∀ x ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
              σ * (nk₁.map.symm x).2 + δ ≤ m (nk₁.map.symm x).1) ∧
            (∀ x ∈ nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
              m (nk₁.map.symm x).1 + δ ≤ σ * (nk₁.map.symm x).2) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_graph_band_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ p₂ nk₀ nk₁ nk₂ hmeet₀ hmeet₂ hdisj
  obtain ⟨a, b, ha, hb, hab, hsource₀, heq₀⟩ := hgraph eps heps M g p₀ p₁ nk₀ nk₁ hmeet₀
  obtain ⟨c, d, hc, hd, hcd, hsource₂, heq₂⟩ := hgraph eps heps M g p₂ p₁ nk₂ nk₁ hmeet₂
  let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  have hdisjoint : Disjoint {x : Cylinder | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1}
      {x : Cylinder | c x.1 ≤ x.2 ∧ x.2 ≤ d x.1} := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hdisj
      (heq₀.symm ▸ mem_image_of_mem nk₁.map hx) (heq₂.symm ▸ mem_image_of_mem nk₁.map hy)
  have hleft (x : M) (hx : x ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :
      a (nk₁.map.symm x).1 ≤ (nk₁.map.symm x).2 ∧
      (nk₁.map.symm x).2 ≤ b (nk₁.map.symm x).1 := by
    obtain ⟨y, hy, rfl⟩ := heq₀ ▸ hx
    have hl := nk₁.map.left_inv (hsource₀ hy)
    change nk₁.map.symm (nk₁.map y) = y at hl
    rw [hl]
    exact hy
  have hright (x : M) (hx : x ∈ nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :
      c (nk₁.map.symm x).1 ≤ (nk₁.map.symm x).2 ∧
      (nk₁.map.symm x).2 ≤ d (nk₁.map.symm x).1 := by
    obtain ⟨y, hy, rfl⟩ := heq₂ ▸ hx
    have hl := nk₁.map.left_inv (hsource₂ hy)
    change nk₁.map.symm (nk₁.map y) = y at hl
    rw [hl]
    exact hy
  obtain ⟨δ, hδ, m, hm | hm⟩ :=
    DifferentialGeometry.Topology.exists_uniform_gap_between_disjoint_graph_bands ha hb hc hd
      (fun x => (hab x).le) (fun x => (hcd x).le) hdisjoint
  · refine ⟨δ, 1, hδ, Or.inl rfl, m, ?_, ?_⟩
    · intro x hx
      have hl := (hleft x hx).2
      have hh := (hm (nk₁.map.symm x).1).1
      simp only [one_mul]
      linarith
    · intro x hx
      simpa only [one_mul] using (hm _).2.trans (hright x hx).1
  · refine ⟨δ, -1, hδ, Or.inr rfl, -m, ?_, ?_⟩
    · intro x hx
      have hh := (hm (nk₁.map.symm x).1).2.trans (hleft x hx).1
      change -1 * (nk₁.map.symm x).2 + δ ≤ -m (nk₁.map.symm x).1
      linarith
    · intro x hx
      have hr := (hright x hx).2
      have hh := (hm (nk₁.map.symm x).1).1
      change -m (nk₁.map.symm x).1 + δ ≤ -1 * (nk₁.map.symm x).2
      linarith

theorem exists_spatial_neck_triple_order_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ p₂ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (nk₂ : SpatialNeck g eps p₂),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          (nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          Disjoint (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1))
            (nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) →
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            ∀ x ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
              ∀ y ∈ nk₂.map '' (univ ×ˢ Icc (-1 : ℝ) 1),
                (nk₁.map.symm x).1 = (nk₁.map.symm y).1 →
                σ * (nk₁.map.symm x).2 < σ * (nk₁.map.symm y).2 := by
  obtain ⟨eta, heta, hgap⟩ := exists_spatial_neck_triple_gap_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ p₂ nk₀ nk₁ nk₂ hmeet₀ hmeet₂ hdisj
  obtain ⟨δ, σ, hδ, hσ, m, hleft, hright⟩ :=
    hgap eps heps M g p₀ p₁ p₂ nk₀ nk₁ nk₂ hmeet₀ hmeet₂ hdisj
  refine ⟨σ, hσ, ?_⟩
  intro x hx y hy hxy
  have hl := hleft x hx
  have hr := hright y hy
  rw [hxy] at hl
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
