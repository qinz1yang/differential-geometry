import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarDiameter

set_option autoImplicit false
noncomputable section
open Bundle Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collar_edist_comm (g : SmoothRiemannianMetric I3 M) (x y : M) :
    riemannianEDistOf (I := I3) g x y = riemannianEDistOf (I := I3) g y x := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collar_edist_triangle (g : SmoothRiemannianMetric I3 M) (x y z : M) :
    riemannianEDistOf (I := I3) g x z ≤
      riemannianEDistOf (I := I3) g x y + riemannianEDistOf (I := I3) g y z := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

omit [T2Space M] [SigmaCompactSpace M] in
theorem isEmpty_strongNeck_of_inv_eleven_le {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ}
    (h : 1 / 11 ≤ eps) : IsEmpty (StrongNeck S eps x t) :=
  ⟨fun neck => absurd neck.eps_small (not_lt.mpr h)⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem isEmpty_strongNeck_two_mul_of_inv_twentytwo_le {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ} {x : M} {t : ℝ}
    (h : 1 / 22 ≤ alpha) : IsEmpty (StrongNeck S (2 * alpha) x t) :=
  isEmpty_strongNeck_of_inv_eleven_le (by linarith)

theorem localCap_tube_metricDistance_lt_two_mul_radiusUpper {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) (cap : LocalCap S eps x t W.domain.carrier)
    {v : M} (hv : v ∈ cap.tube) :
    metricDistance (S.base.metric t) x v < 2 * (C1 / Real.sqrt (S.scalar t x)) := by
  have hQ : 0 < S.scalar t x := W.Q_pos
  have hrpos : 0 < W.radius :=
    lt_of_lt_of_le (inv_pos.mpr (Real.sqrt_pos.mpr hQ)) W.radius_lower
  have htube : cap.tube ⊆ W.domain.carrier :=
    fun _ hy => cap.union_eq.symm ▸ (Or.inr hy)
  have hball : riemannianEDistOf (S.base.metric t) x v < ENNReal.ofReal (2 * W.radius) :=
    W.inside_ball (htube hv)
  have hfinite : riemannianEDistOf (S.base.metric t) x v ≠ ⊤ :=
    ne_top_of_lt hball
  have hreal : (riemannianEDistOf (S.base.metric t) x v).toReal < 2 * W.radius := by
    rw [← ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * W.radius)]
    exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hball
  have hupper : 2 * W.radius ≤ 2 * (C1 / Real.sqrt (S.scalar t x)) :=
    mul_le_mul_of_nonneg_left W.radius_upper (by norm_num)
  exact hreal.trans_le hupper

theorem localCap_tube_depth_lt_two_mul_comparisonConstant {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : CanonicalWitness S eps C1 C2 x t) (cap : LocalCap S eps x t W.domain.carrier)
    {H : ℝ} (hdepth : ∀ y ∈ cap.tube,
      H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    {v : M} (hv : v ∈ cap.tube) : H < 2 * C1 := by
  have hsqrt : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr W.Q_pos
  have h1 : H / Real.sqrt (S.scalar t x) < 2 * (C1 / Real.sqrt (S.scalar t x)) :=
    (hdepth v hv).trans_lt (localCap_tube_metricDistance_lt_two_mul_radiusUpper W cap hv)
  rw [← mul_div_assoc] at h1
  rw [div_lt_div_iff_of_pos_right hsqrt] at h1
  linarith

theorem collarSectionDiameter_exists :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
        (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
        (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps z : ℝ),
        MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps →
        eps ≤ 1 → 0 ∈ times → U ⊆ F.source → (∀ y : Sphere 2, (y, z) ∈ U) →
          ∀ x y : Sphere 2,
          riemannianEDistOf (g 0) (F (x, z)) (F (y, z)) ≤ ENNReal.ofReal D := by
  obtain ⟨B, hB, hpaths⟩ := exists_roundSphere_path_length_bound
  refine ⟨2 * B, by positivity, ?_⟩
  intro M _ _ _ _ _ C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel x y
  obtain ⟨gamma, hstart, hend, hgamma, hlen⟩ := hpaths x y
  have hcyl : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s : ℝ => (gamma s, z)) (Set.Icc 0 1) :=
    hgamma.prodMk contMDiffOn_const
  have hinside : ∀ s ∈ Set.Icc (0 : ℝ) 1, (gamma s, z) ∈ U := fun s _ => hlevel (gamma s)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I3 1
      ((F : Cylinder → M) ∘ (fun s : ℝ => (gamma s, z))) (Set.Icc 0 1) :=
    (F.contMDiffOn_toFun.of_le (by simp)).comp hcyl fun s hs => hsource (hinside s hs)
  have hdist := edistOf_le_metricPathELength (g 0) (by norm_num : (0 : ℝ) ≤ 1) hcomp
  simp only [Function.comp_apply, hstart, hend] at hdist
  have hlen' := (collar_pathELength_bounds C g F cmp hmetric heps heps1 hzero hsource
    hcyl hinside).2
  have htrans := C.transverse_length_le z hgamma
  have hsqrt : ENNReal.ofReal (Real.sqrt (1 + eps)) ≤ ENNReal.ofReal (Real.sqrt 2) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith))
  calc riemannianEDistOf (g 0) (F (x, z)) (F (y, z))
      ≤ metricPathELength (g 0) ((F : Cylinder → M) ∘
          (fun s : ℝ => (gamma s, z))) 0 1 := hdist
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) *
          metricPathELength (C.metric 0) (fun s : ℝ => (gamma s, z)) 0 1 := hlen'
    _ ≤ ENNReal.ofReal (Real.sqrt 2) *
          (ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal B) :=
          mul_le_mul' hsqrt (htrans.trans (mul_le_mul' le_rfl hlen.le))
    _ = ENNReal.ofReal (2 * B) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← pow_two,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_mul (by norm_num)]

theorem collarAxialBound_exists :
    ∃ V : ℝ, 0 < V ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (C : CylinderReference) (g : ℝ → SmoothRiemannianMetric I3 M)
        (F : PartialDiffeomorph IC I3 Cylinder M ∞) (U : Set Cylinder) (times : Set ℝ)
        (order : ℕ) (eps : ℝ) (h : ℝ → SmoothRiemannianMetric IC Cylinder),
        MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps →
        eps ≤ 1 → 0 ∈ times → U ⊆ F.source →
        Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆ U →
          ∀ (p : Sphere 2) (k : ℝ), |k| ≤ 10 →
            riemannianEDistOf (g 0) (F (p, k)) (F (p, 0)) ≤ ENNReal.ofReal V := by
  refine ⟨Real.sqrt 2 * 10, by positivity, ?_⟩
  intro M _ _ _ _ _ C g F U times order eps h cmp hmetric heps heps1 hzero hsource hslab p k hk
  refine (collar_axial_edist_le (M := M) C g F cmp hmetric heps hzero hsource hslab p
    (Set.mem_Icc.mpr (abs_le.mp hk))).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (1 + eps) * |k| ≤ Real.sqrt 2 * |k| :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (abs_nonneg k)
    _ ≤ Real.sqrt 2 * 10 := mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg 2)

theorem neckAxialBound_holds : NeckAxialBound.{u} := by
  obtain ⟨V, hV, hax⟩ := collarAxialBound_exists
  refine ⟨V, hV, ?_⟩
  intro M _ _ _ _ _ J S eps x t neck p k hk
  have heps1 : eps ≤ 1 := by linarith [neck.eps_small]
  have h11 : (11 : ℝ) < eps⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ neck.eps_pos]
    linarith [neck.eps_small]
  have hslab : Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆
      (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) := by
    rintro ⟨u, v⟩ ⟨-, hv⟩
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hv
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  exact hax M neck.cylinder (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps
    neck.cylinder.metric neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain
    hslab p k hk

theorem neckCoreDiameterBound_holds : NeckCoreDiameterBound.{u} := by
  obtain ⟨D, hD, hsec⟩ := collarSectionDiameter_exists
  obtain ⟨V, hV, hax⟩ := collarAxialBound_exists
  refine ⟨D + 2 * V, by positivity, ?_⟩
  intro M _ _ _ _ _ J S eps x t neck y hy z hz
  obtain ⟨vx, hvx, rfl⟩ := hy
  obtain ⟨wx, hwx, rfl⟩ := hz
  have heps1 : eps ≤ 1 := by linarith [neck.eps_small]
  have h11 : (11 : ℝ) < eps⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ neck.eps_pos]
    linarith [neck.eps_small]
  have hU : Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆
      (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) := by
    rintro ⟨u, v⟩ ⟨-, hv⟩
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hv
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hzero : (0 : ℝ) ∈ Set.Ioo (-eps⁻¹) eps⁻¹ := by constructor <;> linarith
  have hlevel : ∀ w : Sphere 2,
      (w, (0 : ℝ)) ∈ (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) :=
    fun w => ⟨mem_univ _, hzero⟩
  have hvV := hax M neck.cylinder (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps
    neck.cylinder.metric neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain hU
    vx.1 vx.2
    (abs_le.mpr hvx.2)
  have hwV : riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
      (neck.map (wx.1, 0)) (neck.map wx) ≤ ENNReal.ofReal V :=
    (collar_edist_comm (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) (neck.map (wx.1, 0))
      (neck.map wx)).trans_le
      (hax M neck.cylinder (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
        (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps
        neck.cylinder.metric neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain
        hU wx.1 wx.2 (abs_le.mpr hwx.2))
  have hsection := hsec M neck.cylinder neck.cylinder.metric
    (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps 0
    neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain hlevel vx.1 wx.1
  have htri := collar_edist_triangle (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
    (neck.map vx) (neck.map (vx.1, 0)) (neck.map wx)
  have htri' := collar_edist_triangle (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
    (neck.map (vx.1, 0)) (neck.map (wx.1, 0)) (neck.map wx)
  have hsum : ENNReal.ofReal V + (ENNReal.ofReal D + ENNReal.ofReal V) =
      ENNReal.ofReal (D + 2 * V) := by
    rw [← add_assoc, ← ENNReal.ofReal_add hV.le hD.le,
      ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ V + D) hV.le]
    congr 1
    ring
  refine htri.trans ((add_le_add hvV (htri'.trans (add_le_add hsection hwV))).trans hsum.le)

theorem goodPointNeckArmFrontier_of_structure {kappa alpha theta epsStar Lmin Lmax : ℝ}
    (h : GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax) :
    ∃ C : ℝ, 0 < C ∧ GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax :=
  goodPointNeckArmFrontier_of_structure_and_coreDiameterBound h neckCoreDiameterBound_holds

theorem goodPointNeckArmFrontier_exists_iff_structure {kappa alpha theta epsStar Lmin Lmax : ℝ} :
    (∃ C : ℝ, 0 < C ∧ GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax) ↔
      GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax :=
  ⟨fun ⟨_C, _hC, hf⟩ => goodPointNeckArmStructure_of_frontier hf,
    fun h => goodPointNeckArmFrontier_of_structure h⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
