import DifferentialGeometry.Geometry.Neck.SpatialTolerance
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
    riemannianBallOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) p (r / 2) ⊆
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
  obtain ⟨R, hR, hbound⟩ := exists_uniform_closed_slab_radius.{u}
  let B : ℝ := 8 * (R + 1)
  have hB : 1 < B := by dsimp only [B]; linarith
  let eta : ℝ := min (1 / 400000) (min (1 / 32) (1 / (2 * B)))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have heta_small : eta < 1 / 200000 := by
    have := min_le_left (1 / 400000 : ℝ) (min (1 / 32) (1 / (2 * B)))
    dsimp only [eta]
    linarith
  refine ⟨eta, heta, heta_small, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hnear
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
  have h₁₀ : p₁ ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
    apply nk₀.ball_subset_closed_slab (by norm_num : (0 : ℝ) < 1) hunit
    exact hnear.trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by norm_num))
  have hp₁ : p₁ ∈ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :=
    ⟨(nk₁.center, 0), ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk₁.eps_pos),
      inv_pos.mpr nk₁.eps_pos⟩, nk₁.center_eq⟩
  have hp₁' := (image_mono hunitCore) h₁₀
  have hratio₁ := nk₁.scalar_ratio_of_common_point nk₀ hsmall hp₁ hp₁'
  have hratio₀ := nk₀.scalar_ratio_of_common_point nk₁ hsmall hp₁' hp₁
  have hscalar₁ : metricScalarAt g p₁ ≤ 4 * metricScalarAt g p₀ := by
    have h := (abs_le.mp hratio₁).2
    have hdiv : metricScalarAt g p₁ / metricScalarAt g p₀ ≤ 4 := by linarith
    exact (div_le_iff₀ nk₀.Q_pos).mp hdiv
  have hscalar₀ : metricScalarAt g p₀ ≤ 4 * metricScalarAt g p₁ := by
    have h := (abs_le.mp hratio₀).2
    have hdiv : metricScalarAt g p₀ / metricScalarAt g p₁ ≤ 4 := by linarith
    exact (div_le_iff₀ nk₁.Q_pos).mp hdiv
  let g₀ := scaleMetric (metricScalarAt g p₀) nk₀.Q_pos g
  let g₁ := scaleMetric (metricScalarAt g p₁) nk₁.Q_pos g
  have hnear₁ : riemannianEDistOf g₁ p₁ p₀ < ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [intrinsic_edist_comm g₁ p₁ p₀]
    have hle := scaled_edist_le_twice g nk₁.Q_pos nk₀.Q_pos hscalar₁ p₀ p₁
    have hmul : 2 * riemannianEDistOf g₀ p₀ p₁ <
        2 * ENNReal.ofReal (1 / 8 : ℝ) :=
      ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnear
    apply hle.trans_lt
    have hnum : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) =
        ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      norm_num
    exact hmul.trans_eq hnum
  have h₀₁ : p₀ ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
    apply nk₁.ball_subset_closed_slab (by norm_num : (0 : ℝ) < 1) hunit
    exact hnear₁.trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by norm_num))
  have hBcore : (univ ×ˢ Icc (-B) B : Set Cylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hunitB : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆ univ ×ˢ Icc (-B) B := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hcross (p q : M) (np : SpatialNeck g eps p) (nq : SpatialNeck g eps q)
      (hscalar : metricScalarAt g q ≤ 4 * metricScalarAt g p)
      (hclose : riemannianEDistOf (scaleMetric (metricScalarAt g q) nq.Q_pos g) q p <
        ENNReal.ofReal (1 / 4 : ℝ)) :
      np.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ nq.map '' (univ ×ˢ Icc (-B) B) := by
    rintro x ⟨z, hz, rfl⟩
    apply nq.ball_subset_closed_slab (by linarith) (by linarith)
    have hdist := hbound M g p eps heps32 np z hz
    have hscaled := (scaled_edist_le_twice g nq.Q_pos np.Q_pos hscalar p (np.map z)).trans
      (mul_le_mul' le_rfl hdist)
    have htri := intrinsic_edist_triangle (scaleMetric (metricScalarAt g q) nq.Q_pos g)
      q p (np.map z)
    have hupper : riemannianEDistOf (scaleMetric (metricScalarAt g q) nq.Q_pos g) q (np.map z) ≤
        ENNReal.ofReal (1 / 4 : ℝ) + 2 * ENNReal.ofReal R :=
      htri.trans (add_le_add hclose.le hscaled)
    have hreal : ENNReal.ofReal (1 / 4 : ℝ) + 2 * ENNReal.ofReal R =
        ENNReal.ofReal (1 / 4 + 2 * R) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    rw [hreal] at hupper
    exact hupper.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < B / 2)).mpr
      (by dsimp only [B]; linarith))
  have hcross₀ := hcross p₀ p₁ nk₀ nk₁ hscalar₁ hnear₁
  have hcross₁ := hcross p₁ p₀ nk₁ nk₀ hscalar₀
    (hnear.trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).mpr
      (by norm_num)))
  let S := nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∪ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hsub₀ : S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) :=
    union_subset ((image_mono hunitB).trans (image_mono hBcore)) (hcross₁.trans (image_mono hBcore))
  have hsub₁ : S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) :=
    union_subset (hcross₀.trans (image_mono hBcore)) ((image_mono hunitB).trans (image_mono hBcore))
  have hcompact (p : M) (nk : SpatialNeck g eps p) :
      IsCompact (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (nk.map.contMDiffOn_toFun.continuousOn.mono (hunitCore.trans nk.domain))
  have hcenter (p : M) (nk : SpatialNeck g eps p) :
      p ∈ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
  have hpre (p : M) (nk : SpatialNeck g eps p) :
      IsPreconnected (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
    let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
        (0 : ThreeSpace) 1)
    exact (isPreconnected_univ.prod isPreconnected_Icc).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono (hunitCore.trans nk.domain))
  have hSpre : IsPreconnected S := IsPreconnected.union p₀
    (hcenter p₀ nk₀) h₀₁ (hpre p₀ nk₀) (hpre p₁ nk₁)
  have hSin (p : M) (nk : SpatialNeck g eps p)
      (hs : S ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1))) :
      S ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    apply hs.trans (image_mono _)
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  obtain ⟨σ, hσ, hgrad⟩ := nk₀.exists_sign_axial_gradient_bound_on_preconnected nk₁
    hsmall hsmall hSpre (hSin p₀ nk₀ hsub₀) (hSin p₁ nk₁ hsub₁)
  refine ⟨(hcompact p₀ nk₀).union (hcompact p₁ nk₁),
    ⟨⟨p₀, Or.inl (hcenter p₀ nk₀)⟩, hSpre⟩, h₀₁, h₁₀, hsub₀, hsub₁, σ, hσ, ?_⟩
  intro x hx
  convert hgrad x hx using 1
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
