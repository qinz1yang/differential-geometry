import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Comparison.Toponogov.PuncturedConeApproximation
import DifferentialGeometry.Geometry.Comparison.Toponogov.CompletionRadialNets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckEndDirections
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckEndCurvatureDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocallyFinite
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckCurvatureDistance
import DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction
import DifferentialGeometry.Geometry.Metric.Segment
import DifferentialGeometry.Geometry.Neck.ScalarSeparation
import DifferentialGeometry.Geometry.Neck.SpatialTolerance
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Topology.Compactness.ConvergentFamily
import DifferentialGeometry.Topology.Compactness.Cocompact
import DifferentialGeometry.Topology.DenseEmbedding
import DifferentialGeometry.Topology.Manifold.ProductChartCollar
import DifferentialGeometry.Topology.Homeomorph.CylinderChain
import DifferentialGeometry.Topology.Homeomorph.Interior
import DifferentialGeometry.Topology.LocallyFinite.Frontier
import Mathlib.Topology.Compactness.LocallyFinite
noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u

private theorem exists_homeomorph_annular_end
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [T2Space M]
    (ann : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (eta : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (F : ℕ → Cylinder → M)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (ann n).source)
    (hleft : ∀ n p, ann n (p, 0) = F n (p, 0))
    (hright : ∀ n p, ann n (p, 1) = F (n + 1) (eta n p, 0))
    (hcann : ∀ n, IsCompact (ann n '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hlocalAnn : LocallyFinite (fun n => ann n '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hsep : ∀ i j, i + 1 < j → Disjoint (ann i '' (univ ×ˢ Icc (0 : ℝ) 1))
      (ann j '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hinter : ∀ n, (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
      (ann (n + 1 + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        F (n + 1 + 1) '' (univ ×ˢ ({0} : Set ℝ)))
    (hfrontTail : frontier (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      F 1 '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ E : Sphere 2 × Ici (0 : ℝ) ≃ₜ (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
      ∃ theta : ℕ → Sphere 2 ≃ₜ Sphere 2,
        theta 0 = Homeomorph.refl (Sphere 2) ∧
        (∀ n, theta (n + 1) = (theta n).trans (eta (n + 1)).toHomeomorph) ∧
        (∀ (n : ℕ) (p : Sphere 2) (s : Icc (0 : ℝ) 1),
          (E (p, ⟨n + (s : ℝ), add_nonneg (Nat.cast_nonneg n) s.property.1⟩) : M) =
            ann (n + 1) (theta n p, s)) ∧
        (∀ s : Ici (0 : ℝ), Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
          I2 I3 (fun p : Sphere 2 => (E (p, s) : M)))) ∧
        ∃ D : Sphere 2 × Ioi (0 : ℝ) ≃ₜ
            interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
          ∀ (p : Sphere 2) (s : Ioi (0 : ℝ)), (D (p, s) : M) =
            (E (p, ⟨s, (show 0 ≤ (s : ℝ) from s.property.le)⟩) : M) := by
  have hlocalShift (k : ℕ) := hlocalAnn.comp_injective
    (g := fun n : ℕ => n + k) (fun _ _ hij => Nat.add_right_cancel hij)
  let unit : Sphere 2 × Icc (0 : ℝ) 1 ≃ₜ (univ ×ˢ Icc (0 : ℝ) 1 : Set Cylinder) :=
    (((Homeomorph.Set.univ (Sphere 2)).symm).prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod univ (Icc (0 : ℝ) 1)).symm
  let e (n : ℕ) : Sphere 2 × Icc (0 : ℝ) 1 ≃ₜ
      (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    unit.trans ((ann (n + 1)).toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
      (hsource (n + 1)) rfl)
  have he (n : ℕ) (p : Sphere 2) (s : Icc (0 : ℝ) 1) :
      (e n (p, s) : M) = ann (n + 1) (p, s) := rfl
  have hseam' (n : ℕ) (p : Sphere 2) : (e n (p, ⟨1, by simp⟩) : M) =
      e (n + 1) ((eta (n + 1)).toHomeomorph p, ⟨0, by simp⟩) := by
    rw [he, he, hright, hleft]
    rfl
  have hinter' (n : ℕ) :
      (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
        (ann (n + 1 + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      range (fun p => (e n (p, ⟨1, by simp⟩) : M)) := by
    rw [hinter n]
    ext x
    constructor
    · rintro ⟨⟨p, z⟩, ⟨_, hz⟩, hp⟩
      have hz' : z = 0 := hz
      subst z
      obtain ⟨w, rfl⟩ := (eta (n + 1)).surjective p
      refine ⟨w, ?_⟩
      change (e n (w, ⟨1, by simp⟩) : M) = x
      rw [he, hright]
      exact hp
    · rintro ⟨p, hp⟩
      change (e n (p, ⟨1, by simp⟩) : M) = x at hp
      rw [he, hright] at hp
      exact ⟨(eta (n + 1) p, 0), ⟨mem_univ _, rfl⟩, hp⟩
  obtain ⟨E, theta, htheta0, htheta, hE⟩ :=
    DifferentialGeometry.Topology.exists_homeomorph_iUnion_of_cylinder_chain
      (fun n => ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) e
      (fun n => (eta (n + 1)).toHomeomorph) (fun n => (hcann (n + 1)).isClosed)
      (hlocalShift 1) hseam' hinter' (fun i j hij => hsep (i + 1) (j + 1) (Nat.succ_lt_succ hij))
  have hEzero (p : Sphere 2) : (E (p, ⟨0, by norm_num⟩) : M) = F 1 (p, 0) := by
    have hz := hE 0 p ⟨0, by simp⟩
    rw [htheta0] at hz
    simpa only [Nat.cast_zero, zero_add, Homeomorph.refl_apply, he, hleft, id_eq] using hz
  have hfrontE : frontier (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      range (fun p => (E (p, ⟨0, by norm_num⟩) : M)) := by
    rw [hfrontTail]
    ext x
    constructor
    · rintro ⟨⟨p, z⟩, ⟨_, hz⟩, hp⟩
      have hz' : z = 0 := hz
      subst z
      exact ⟨p, (hEzero p).trans hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, (hEzero p).symm.trans hp⟩
  have hthetaSmooth (n : ℕ) : ContMDiff I2 I2 ∞ (theta n) := by
    induction n with
    | zero => rw [htheta0]; exact contMDiff_id
    | succ n ih =>
      rw [htheta]
      exact (eta (n + 1)).contMDiff.comp ih
  have hthetaInverse (n : ℕ) : ContMDiff I2 I2 ∞ (theta n).symm := by
    induction n with
    | zero => rw [htheta0]; exact contMDiff_id
    | succ n ih =>
      rw [htheta]
      exact ih.comp (eta (n + 1)).symm.contMDiff
  let thetaD (n : ℕ) : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2 :=
    { toEquiv := (theta n).toEquiv
      contMDiff_toFun := hthetaSmooth n
      contMDiff_invFun := hthetaInverse n }
  have hsections (s : Ici (0 : ℝ)) :
      Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
        I2 I3 (fun p : Sphere 2 => (E (p, s) : M))) := by
    let n := Nat.floor (s : ℝ)
    let t : Icc (0 : ℝ) 1 := ⟨(s : ℝ) - n,
      sub_nonneg.mpr (Nat.floor_le s.property),
      by linarith only [Nat.lt_floor_add_one (s : ℝ)]⟩
    have hst : (⟨n + (t : ℝ), add_nonneg (Nat.cast_nonneg n) t.property.1⟩ :
        Ici (0 : ℝ)) = s := by
      apply Subtype.ext
      change (n : ℝ) + ((s : ℝ) - n) = s
      ring
    have heq : (fun p : Sphere 2 => (E (p, s) : M)) =
        fun p => ann (n + 1) (theta n p, (t : ℝ)) := by
      funext p
      rw [← hst]
      exact (hE n p t).trans (he n (theta n p) t)
    let O : TopologicalSpace.Opens Cylinder := ⟨(ann (n + 1)).source, (ann (n + 1)).open_source⟩
    let Φ := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo
      (ann (n + 1)) (U := O) (subset_refl _)
    obtain ⟨c, _, _, _⟩ :=
      DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_reparametrized_product_chart_graph
        O _ Φ (fun _ => (t : ℝ)) contMDiff_const
        (fun p => hsource (n + 1) ⟨mem_univ _, t.property⟩)
        (fun p : Sphere 2 => (E (p, s) : M)) (thetaD n)
        (fun p => congrFun heq p) (r := 1) zero_lt_one
    exact ⟨c⟩
  let D := E.restrictProdIoi hfrontE
  exact ⟨E, theta, htheta0, htheta,
    (fun n p s => (hE n p s).trans (he n (theta n p) s)), hsections,
    D, fun p s => E.restrictProdIoi_apply_coe hfrontE p s⟩

private theorem pathConnectedSpace_of_cylinder_homeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [ConnectedSpace (Sphere 2)] (W : TopologicalSpace.Opens M)
    (D : Sphere 2 × Ioi (0 : ℝ) ≃ₜ W) : PathConnectedSpace W := by
  let _ : ConnectedSpace (Ioi (0 : ℝ)) := isConnected_iff_connectedSpace.mp isConnected_Ioi
  let _ : ConnectedSpace W := D.surjective.connectedSpace D.continuous
  let _ : LocallyPathConnectedSpace W := ChartedSpace.locallyPathConnectedSpace ThreeSpace W
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

private theorem exists_restricted_neck
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (W : TopologicalSpace.Opens M)
    {eps : ℝ} (x : W) (nk : SpatialNeck g eps (x : M))
    (hmap : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ (W : Set M)) :
    ∃ nkW : SpatialNeck (g.restrictOpen W) eps x,
      nkW.map.source = nk.map.source ∩ nk.map ⁻¹' (W : Set M) ∧
      (∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (nkW.map y : M) = nk.map y) ∧
      ∀ y : W, nkW.map.symm y = nk.map.symm (y : M) := by
  refine ⟨nk.restrictOpen (U := W) (x := x) hmap,
    SpatialNeck.restrictOpen_map_source (U := W) (x := x) nk hmap, ?_,
    SpatialNeck.restrictOpen_map_symm (U := W) (x := x) nk hmap⟩
  exact fun y hy => SpatialNeck.restrictOpen_map_coe (U := W) (x := x) nk hmap
    (hmap ⟨y, hy, rfl⟩)

private theorem scalar_distance_lower_bound_of_mem_neck_ball
    {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hM : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {eps : ℝ} {x : M} (nk : SpatialNeck g eps x) (hsmall : eps ≤ 1 / 8646)
    (q : UniformSpace.Completion M)
    (hcenter : eps⁻¹ ^ 2 ≤ metricScalarAt g x * dist q (x : UniformSpace.Completion M) ^ 2)
    {y : M} (hy : y ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hball : y ∈ riemannianClosedBallOf g x
      ((3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g x))) :
    eps⁻¹ ^ 2 / 8 ≤ metricScalarAt g y * dist q (y : UniformSpace.Completion M) ^ 2 := by
  have hip : 0 ≤ eps⁻¹ := (inv_pos.mpr nk.eps_pos).le
  change riemannianEDistOf g x y ≤ ENNReal.ofReal
    ((3 * eps⁻¹ / 100) / Real.sqrt (metricScalarAt g x)) at hball
  rw [← hM, edist_dist] at hball
  have hb := (ENNReal.ofReal_le_ofReal_iff (div_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hip) (by norm_num)) (Real.sqrt_nonneg _))).mp hball
  have hnear : dist x y ≤ eps⁻¹ / (2 * Real.sqrt (metricScalarAt g x)) := by
    apply hb.trans
    simpa only [div_div] using div_le_div_of_nonneg_right
      (show 3 * eps⁻¹ / 100 ≤ eps⁻¹ / 2 by linarith only [hip])
      (Real.sqrt_nonneg (metricScalarAt g x))
  have hlow := nk.scalar_distance_lower_bound
    (by linarith only [hsmall] : eps ≤ 1 / 4323) q hcenter hy hnear
  apply le_trans _ hlow
  have hfactor : (1 : ℝ) / 2 ≤ 1 - 4323 * eps := by linarith only [hsmall]
  nlinarith only [mul_le_mul_of_nonneg_right hfactor (sq_nonneg eps⁻¹)]

private theorem axis_mem_interior_of_frontier_eq_central_sphere
    {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (metric : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf metric x y)
    {r eps : ℝ} (hsmall : eps < 1 / 1000000)
    (gamma : C(Ico 0 r, M)) (hgamma : Isometry gamma)
    (a b : Ico (0 : ℝ) r) (hab : (a : ℝ) < b)
    (nk : SpatialNeck metric eps (gamma a))
    (hstep : (b : ℝ) - a = (eps⁻¹ / 40) / Real.sqrt (metricScalarAt metric (gamma a)))
    {U : Set M} (hfront : frontier U = nk.map '' (univ ×ˢ {(0 : ℝ)}))
    (hstart : gamma b ∈ interior U) :
    ∀ v : Ico (0 : ℝ) r, (b : ℝ) ≤ v → gamma v ∈ interior U := by
  have hI : IsPreconnected (Ici b) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have heq : Subtype.val '' Ici b = Ico (b : ℝ) r := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.property.2⟩
      · intro hv
        exact ⟨⟨v, b.property.1.trans hv.1, hv.2⟩, hv.1, rfl⟩
    rw [heq]
    exact isPreconnected_Ico
  have hP : IsPreconnected (gamma '' Ici b) := hI.image _ gamma.continuous.continuousOn
  have havoid : Disjoint (gamma '' Ici b) (frontier U) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨v, hv, rfl⟩ hz
    rw [hfront] at hz
    have hb := nk.central_sphere_subset_closedBall hz
    change riemannianEDistOf metric (gamma a) (gamma v) ≤
      ENNReal.ofReal (7 / Real.sqrt (metricScalarAt metric (gamma a))) at hb
    rw [← hmetric, hgamma.edist_eq, edist_dist, Subtype.dist_eq, Real.dist_eq] at hb
    rw [abs_of_nonpos (sub_nonpos.mpr (hab.le.trans hv)), neg_sub] at hb
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 7) (Real.sqrt_nonneg _))).mp hb
    have hi : (1000000 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by simpa only [one_div] using hsmall)
    have hnum : (7 : ℝ) < eps⁻¹ / 40 := by linarith only [hi]
    have hd := div_lt_div_of_pos_right hnum (Real.sqrt_pos.mpr nk.Q_pos)
    change (v : ℝ) - a ≤ _ at hreal
    have hv' : (b : ℝ) ≤ v := hv
    linarith only [hv', hreal, hd, hstep]
  have hsub := DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
    hP havoid ⟨gamma b, ⟨b, show b ≤ b from le_rfl, rfl⟩, hstart⟩
  exact fun v hv => hsub ⟨v, hv, rfl⟩

private theorem inv_sq_div_eight_gt_of_small {alpha : ℝ}
    (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000) :
    196 < ((2 * alpha)⁻¹) ^ 2 / 8 := by
  have hlarge : 40 < (2 * alpha)⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    linarith only [hsmall]
  have hsq := (sq_lt_sq₀ (by norm_num : 0 ≤ (40 : ℝ))
    (by positivity : 0 ≤ (2 * alpha)⁻¹)).mpr hlarge
  norm_num only [show (40 : ℝ) ^ 2 = 1600 by norm_num] at hsq
  linarith only [hsq]

private theorem exists_restricted_completion_endpoint
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M)
    (hM : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : ∀ (x : M) (v w : TangentSpace I3 x), 0 ≤ metricRm04StandardAt g x v w w v)
    (W : TopologicalSpace.Opens M) (D : Sphere 2 × Ioi (0 : ℝ) ≃ₜ W)
    [ConnectedSpace (Sphere 2)]
    {a b : ℝ} (hab : a < b) (γ : C(Ico a b, W))
    (hγ : ∀ v w, riemannianEDistOf (g.restrictOpen W) (γ v) (γ w) = edist v w)
    (q : UniformSpace.Completion M)
    (hq : Tendsto (fun t => ((γ t : M) : UniformSpace.Completion M))
      (comap (Subtype.val : Ico a b → ℝ) (𝓝 b)) (𝓝 q))
    (hmissing : q ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {eps : ℝ} (hsmall : eps < 1 / 4323) (t : ℕ → Ico a b) (ht : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 b))
    (hscalarAmbient : Tendsto (fun n => metricScalarAt g (γ (t n) : M)) atTop atTop)
    (regions : ℕ → Set M) (hregions : ∀ n, IsCompact (regions n))
    (hregionsW : ∀ n, regions n ⊆ (W : Set M))
    (nk : ∀ n, SpatialNeck g eps (γ (t n) : M))
    (hregionsNeck : ∀ n, regions n ⊆ (nk n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hwindow : ∀ᶠ n in atTop, (nk n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ (W : Set M))
    (B : Set M) (hB : IsCompact B)
    (hBcover : ∀ x : W, (x : M) ∉ ⋃ n, regions n → (x : M) ∈ B)
    (hfrontRegions : ∀ N, frontier (⋃ n, regions (n + N)) ⊆
      (nk N).map '' (univ ×ˢ {(0 : ℝ)}))
    (hcenters : ∀ n, (γ (t n) : M) ∈ regions n)
    {c : ℝ} (hc : 196 < c) (hquant : ∀ n, ∀ x ∈ regions n,
      c ≤ metricScalarAt g x * dist q (x : UniformSpace.Completion M) ^ 2) :
    ∃ hW : PathConnectedSpace W,
    let _ : PathConnectedSpace W := hW
    let A (n : ℕ) : Set W := (Subtype.val : W → M) ⁻¹' regions n
    let mW : MetricSpace W :=
      let _ : PseudoMetricSpace W := (g.restrictOpen W).toPseudoMetricSpace
      MetricSpace.ofT0PseudoMetricSpace W
    let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
    let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
    let eW : PseudoEMetricSpace W :=
      @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
    let : WeakPseudoEMetricSpace W := @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
    ∃ qW : UniformSpace.Completion W,
      Tendsto (fun t => (γ t : UniformSpace.Completion W))
        (comap (Subtype.val : Ico a b → ℝ) (𝓝 b)) (𝓝 qW) ∧
      (∀ t : Ico a b, dist qW (γ t : UniformSpace.Completion W) = b - t) ∧
      qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
      UniformSpace.Completion.map (Subtype.val : W → M) qW = q ∧
      Topology.IsOpenEmbedding (fun x : W => (x : UniformSpace.Completion W)) ∧
      (∀ U ∈ 𝓝 qW, ∀ᶠ n in atTop, (fun x : W => (x : UniformSpace.Completion W)) '' A n ⊆ U) ∧
      IsCompact (insert qW (⋃ n, (fun x : W => (x : UniformSpace.Completion W)) '' A n)) ∧
      insert qW (⋃ n, (fun x : W => (x : UniformSpace.Completion W)) '' A n) ∈ 𝓝 qW ∧
      Tendsto (fun x : W => metricScalarAt (g.restrictOpen W) x)
        (comap (fun x : W => (x : UniformSpace.Completion W)) (𝓝 qW)) atTop ∧
      (∀ n, ∀ x ∈ A n, c ≤ metricScalarAt (g.restrictOpen W) x *
        dist qW (x : UniformSpace.Completion W) ^ 2) ∧
      (∀ (β : ℝ → UniformSpace.Completion W) (u v w : ℝ), u < v → v < w →
        (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (β s) (β t) = |s - t|) → β v ≠ qW) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
        metricScalarAt g (γ (t n) : M) * (b - (t n : ℝ)) ^ 2 ≤ C) ∧
      ∃ delta : ℝ, 0 < delta ∧ IsCompact (Metric.closedBall qW delta) ∧
        Metric.closedBall qW delta ⊆ insert qW (range (fun x : W => (x : UniformSpace.Completion W))) ∧
        Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
        (∀ eps > 0, ∃ d ∈ Ioo 0 (delta / 3), ∃ A : Finset C(ℝ, UniformSpace.Completion W),
          (∀ ray ∈ A, ray 0 = qW ∧
            ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, dist (ray s) (ray t) = |s - t|) ∧
          ∀ s ∈ Ioc 0 d, ∀ x : W, dist (x : UniformSpace.Completion W) qW = s →
            ∃ ray ∈ A, dist (x : UniformSpace.Completion W) (ray s) < eps * s) ∧
        ∀ {ι : Type u} (len : ι → ℝ) (ray : ι → C(ℝ, UniformSpace.Completion W)),
          (∀ i, 0 < len i) → (∀ i, len i < delta / 3) → (∀ i, ray i 0 = qW) →
          (∀ i, ∀ s ∈ Icc 0 (len i), ∀ t ∈ Icc 0 (len i),
            dist (ray i s) (ray i t) = |s - t|) →
          ∃ K : DifferentialGeometry.Toponogov.AngleKernel ι,
            (∀ i j, K.angle i j = DifferentialGeometry.Toponogov.limitingRadialAngle
              len (fun i => ray i) i j) ∧
            let _ := K.metricSpace
            TotallyBounded (univ : Set (Quotient K.setoid)) ∧
              CompactSpace (UniformSpace.Completion (Quotient K.setoid)) := by
  let hW := pathConnectedSpace_of_cylinder_homeomorph W D
  let _ : PathConnectedSpace W := hW
  refine ⟨hW, ?_⟩
  let A (n : ℕ) : Set W := (Subtype.val : W → M) ⁻¹' regions n
  have hA (n : ℕ) : IsCompact (A n) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : Subtype.val '' A n = regions n := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hregionsW n hx⟩, hx, rfl⟩
    rw [heq]
    exact hregions n
  have hnecks : ∀ᶠ n in atTop, ∃ neck : SpatialNeck (g.restrictOpen W) eps (γ (t n)),
      A n ⊆ neck.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    filter_upwards [hwindow] with n hn
    let neck := (nk n).restrictOpen (U := W) (x := γ (t n)) hn
    refine ⟨neck, ?_⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hregionsNeck n hy
    refine ⟨z, hz, Subtype.ext ?_⟩
    exact (SpatialNeck.restrictOpen_map_coe (U := W) (x := γ (t n)) (nk n) hn
      (hn ⟨z, hz, rfl⟩)).trans hzy
  have hBcover (x : W) (hx : x ∉ ⋃ n, A n) : (x : M) ∈ B := by
    apply hBcover x
    intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact hx (mem_iUnion.mpr ⟨n, hn⟩)
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (g.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let : PseudoEMetricSpace W := eW
  let : WeakPseudoEMetricSpace W := @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  let : EDist W := eW.toEDist
  have hscalar : Tendsto (fun n => metricScalarAt (g.restrictOpen W) (γ (t n))) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hscalarAmbient
  have hmetricW (x y : W) : edist x y = riemannianEDistOf (g.restrictOpen W) x y :=
    (g.restrictOpen W).toPseudoMetricSpace_edist x y
  have hγ' : Isometry (γ : Ico a b → W) := by
    intro v w
    rw [hmetricW]
    exact hγ v w
  obtain ⟨qW, hqW, hdistW⟩ := Geometry.exists_completion_endpoint_of_isometry hab hγ'
  have hi : LipschitzWith 1 (Subtype.val : W → M) := by
    intro x y
    rw [ENNReal.coe_one, one_mul, hM, hmetricW]
    exact riemannianEDistOf_le_restrictOpen g W x y
  have hmap : UniformSpace.Completion.map (Subtype.val : W → M) qW = q := by
    let l : Filter (Ico a b) := comap Subtype.val (𝓝 b)
    have hne : NeBot (map (Subtype.val : Ico a b → ℝ) l) := by
      rw [map_comap_setCoe_val]
      exact right_nhdsWithin_Ico_neBot hab
    let _ : NeBot l := hne.of_map
    have hcomp := (UniformSpace.Completion.continuous_map (f := (Subtype.val : W → M))).continuousAt.tendsto.comp hqW
    have heq : Tendsto (fun t => ((γ t : M) : UniformSpace.Completion M)) l
        (𝓝 (UniformSpace.Completion.map (Subtype.val : W → M) qW)) := by
      apply hcomp.congr'
      exact Eventually.of_forall fun t => UniformSpace.Completion.map_coe hi.uniformContinuous (γ t)
    exact tendsto_nhds_unique heq hq
  have hmissingW : qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) := by
    rintro ⟨x, rfl⟩
    rw [UniformSpace.Completion.map_coe hi.uniformContinuous] at hmap
    exact hmissing ⟨x, hmap⟩
  have hquantW (n : ℕ) (x : W) (hx : x ∈ A n) :
      c ≤ metricScalarAt (g.restrictOpen W) x * dist qW (x : UniformSpace.Completion W) ^ 2 := by
    have hnonneg : 0 ≤ metricScalarAt g (x : M) :=
      (mul_nonneg (show 0 ≤ 1 - 4323 * eps by linarith only [hsmall]) (nk n).Q_pos.le).trans
        ((nk n).scalar_bounds_on_image_window (hregionsNeck n hx)).1
    have hdist := hi.completion_map.dist_le_mul qW (x : UniformSpace.Completion W)
    rw [hmap, UniformSpace.Completion.map_coe hi.uniformContinuous, NNReal.coe_one, one_mul] at hdist
    rw [metricScalarAt_restrictOpen]
    exact (hquant n (x : M) hx).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hdist 2) hnonneg)
  let radius (n : ℕ) := (eps⁻¹ + 6) * Real.sqrt (1 + eps) /
    Real.sqrt (metricScalarAt (g.restrictOpen W) (γ (t n)))
  have hradius : Tendsto radius atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hscalar)
  have hbound : Tendsto (fun n => b - (t n : ℝ) + radius n) atTop (𝓝 0) := by
    simpa only [sub_self, zero_add] using ((tendsto_const_nhds (x := b)).sub ht).add hradius
  have hregion : ∀ U ∈ 𝓝 qW, ∀ᶠ n in atTop,
      (fun x : W => (x : UniformSpace.Completion W)) '' A n ⊆ U := by
    intro U hU
    obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
    filter_upwards [hnecks, hbound.eventually (eventually_lt_nhds hdelta)] with n hn hsmall
    obtain ⟨nk, hnk⟩ := hn
    rintro z ⟨y, hy, rfl⟩
    apply hball
    have hb := nk.image_window_subset_ball (hnk hy)
    change riemannianEDistOf (g.restrictOpen W) (γ (t n)) y < ENNReal.ofReal (radius n) at hb
    rw [← hmetricW, edist_dist] at hb
    have hdist : dist (γ (t n)) y < radius n :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp hb
    have htri := dist_triangle qW (γ (t n) : UniformSpace.Completion W) (y : UniformSpace.Completion W)
    rw [hdistW, UniformSpace.Completion.dist_eq] at htri
    change dist (y : UniformSpace.Completion W) qW < delta
    rw [dist_comm]
    linarith
  have hcompact := isCompact_insert_iUnion_of_eventually_subset
    (fun n => (hA n).image (UniformSpace.Completion.continuous_coe W))
    (fun U hU => by simpa only [Nat.cofinite_eq_atTop] using hregion U hU)
  let K : Set (UniformSpace.Completion W) :=
    insert qW (⋃ n, (fun x : W => (x : UniformSpace.Completion W)) '' A n)
  let V : Set (UniformSpace.Completion W) :=
    UniformSpace.Completion.map (Subtype.val : W → M) ⁻¹'
      ((fun x : M => (x : UniformSpace.Completion M)) '' B)ᶜ
  have hV : IsOpen V :=
    ((hB.image (UniformSpace.Completion.continuous_coe M)).isClosed.isOpen_compl).preimage
      (UniformSpace.Completion.continuous_map (f := (Subtype.val : W → M)))
  have hqV : qW ∈ V := by
    change UniformSpace.Completion.map (Subtype.val : W → M) qW ∉ _
    rw [hmap]
    rintro ⟨x, _, hx⟩
    exact hmissing ⟨x, hx⟩
  have hVK : V ⊆ K := by
    apply (UniformSpace.Completion.denseRange_coe.open_subset_closure_inter hV).trans
    apply closure_minimal _ hcompact.isClosed
    rintro z ⟨hz, x, rfl⟩
    have hx : x ∈ ⋃ n, A n := by
      by_contra hx
      apply hz
      rw [UniformSpace.Completion.map_coe hi.uniformContinuous]
      exact ⟨(x : M), hBcover x hx, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_insert_of_mem _ (mem_iUnion.mpr ⟨n, ⟨x, hn, rfl⟩⟩)
  have hKnhds : K ∈ 𝓝 qW := mem_of_superset (hV.mem_nhds hqV) hVK
  have hcoeOpen : Topology.IsOpenEmbedding (fun x : W => (x : UniformSpace.Completion W)) := by
    let _ : LocallyCompactSpace W := ChartedSpace.locallyCompactSpace ThreeSpace W
    exact (UniformSpace.Completion.isDenseEmbedding_coe).isOpenEmbedding
  have hfrontNecks : ∀ᶠ N in atTop, ∃ neck : SpatialNeck (g.restrictOpen W) eps (γ (t N)),
      frontier (⋃ n, A (n + N)) ⊆ neck.map '' (univ ×ˢ {(0 : ℝ)}) := by
    filter_upwards [hwindow] with N hN
    let neck := (nk N).restrictOpen (U := W) (x := γ (t N)) hN
    have hfrontW (x : W) (hx : x ∈ frontier (⋃ n, A (n + N))) :
        x ∈ neck.map '' (univ ×ˢ {(0 : ℝ)}) := by
      have hxM : (x : M) ∈ frontier (⋃ n, regions (n + N)) := by
        change x ∈ (Subtype.val : W → M) ⁻¹' frontier (⋃ n, regions (n + N))
        rw [W.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
          continuous_subtype_val, preimage_iUnion]
        exact hx
      obtain ⟨z, hz, hzx⟩ := hfrontRegions N hxM
      refine ⟨z, hz, Subtype.ext ?_⟩
      exact (SpatialNeck.restrictOpen_map_coe (U := W) (x := γ (t N)) (nk N) hN
        (hzx.symm ▸ x.property)).trans hzx
    exact ⟨neck, hfrontW⟩
  have hshort : ∀ᶠ N in atTop, ∀ x ∈ frontier (⋃ n, A (n + N)),
      ∀ y ∈ frontier (⋃ n, A (n + N)),
        dist (x : UniformSpace.Completion W) (y : UniformSpace.Completion W) <
          dist (x : UniformSpace.Completion W) qW + dist qW (y : UniformSpace.Completion W) := by
    filter_upwards [hfrontNecks] with N hN
    obtain ⟨neck, hfrontW⟩ := hN
    intro x hx y hy
    exact neck.central_sphere_dist_lt_endpoint_sum hmetricW qW
      (hc.trans_le (hquantW N (γ (t N)) (hcenters N))) (hfrontW hx) (hfrontW hy)
  have havoid := Metric.ne_of_minimizing_of_convergent_separators hcoeOpen hmissingW hA
    hregion hKnhds hshort
  have hscalarW : Tendsto (fun x : W => metricScalarAt (g.restrictOpen W) x)
      (comap (fun x : W => (x : UniformSpace.Completion W)) (𝓝 qW)) atTop := by
    have hlower : Tendsto (fun n => (1 - 4323 * eps) *
        metricScalarAt (g.restrictOpen W) (γ (t n))) cofinite atTop := by
      simpa only [Nat.cofinite_eq_atTop] using
        hscalar.const_mul_atTop (show 0 < 1 - 4323 * eps by linarith)
    have hbounds : ∀ᶠ n in cofinite, ∀ x ∈ A n,
        (1 - 4323 * eps) * metricScalarAt (g.restrictOpen W) (γ (t n)) ≤
          metricScalarAt (g.restrictOpen W) x := by
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [hnecks] with n hn
      obtain ⟨nk, hnk⟩ := hn
      exact fun x hx => (nk.scalar_bounds_on_image_window (hnk hx)).1
    have hT := tendsto_atTop_of_compact_cover hA hlower hbounds
    apply hT.mono_left
    apply le_inf ((UniformSpace.Completion.continuous_coe W).comap_nhds_le_cocompact hmissingW)
    apply le_principal_iff.mpr
    filter_upwards [preimage_mem_comap hKnhds] with x hx
    change (x : UniformSpace.Completion W) ∈
      insert qW (⋃ n, (fun y : W => (y : UniformSpace.Completion W)) '' A n) at hx
    rcases hx with hx | hx
    · exact False.elim (hmissingW ⟨x, hx⟩)
    · obtain ⟨n, y, hy, heq⟩ := mem_iUnion.mp hx
      have hxy : y = x := UniformSpace.Completion.coe_injective W heq
      exact mem_iUnion.mpr ⟨n, hxy ▸ hy⟩
  have hball : ∃ delta : ℝ, 0 < delta ∧ IsCompact (Metric.closedBall qW delta) ∧
      Metric.closedBall qW delta ⊆ insert qW
        (range (fun x : W => (x : UniformSpace.Completion W))) := by
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hKnhds
    have hclosedSub : Metric.closedBall qW (r / 2) ⊆ K := by
      intro z hz
      apply hsub
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    refine ⟨r / 2, by positivity, hcompact.of_isClosed_subset Metric.isClosed_closedBall hclosedSub, ?_⟩
    intro z hz
    rcases hclosedSub hz with rfl | hz
    · exact Or.inl rfl
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      obtain ⟨x, _, hx⟩ := hn
      exact mem_insert_of_mem _ ⟨x, hx⟩
  let _ : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  let _ : SigmaCompactSpace W := isSigmaCompact_univ_iff.mp (by
    simpa only [D.surjective.range_eq] using isSigmaCompact_range D.continuous)
  have hsecW : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (g.restrictOpen W) := by
    apply (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff _).mpr
    intro x v w
    rw [metricRm04StandardAt_restrictOpen]
    exact hsec x _ _
  have hcentersT : Tendsto (fun n => (γ (t n) : UniformSpace.Completion W)) atTop (𝓝 qW) :=
    hqW.comp (tendsto_comap_iff.mpr ht)
  have hupper : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      metricScalarAt g (γ (t n) : M) * (b - (t n : ℝ)) ^ 2 ≤ C := by
    obtain ⟨delta, hdelta, hcompactBall, hcoverBall⟩ := hball
    obtain ⟨C, hC, hbound⟩ := exists_scalar_distance_upper_bound_of_convergent_neck_separators
      (g.restrictOpen W) hmetricW hsecW hmissingW hdelta hcompactBall hcoverBall havoid
      hA hregion hKnhds hfrontNecks hcentersT hscalar
    refine ⟨C, hC, ?_⟩
    simpa only [metricScalarAt_restrictOpen, hdistW] using hbound
  obtain ⟨delta, hdelta, hcompactBall, hcoverBall⟩ := hball
  have hdir : ∀ {ι : Type u} (len : ι → ℝ) (ray : ι → C(ℝ, UniformSpace.Completion W)),
    (∀ i, 0 < len i) → (∀ i, len i < delta / 3) → (∀ i, ray i 0 = qW) →
    (∀ i, ∀ s ∈ Icc 0 (len i), ∀ t ∈ Icc 0 (len i),
      dist (ray i s) (ray i t) = |s - t|) →
    ∃ K : DifferentialGeometry.Toponogov.AngleKernel ι,
      (∀ i j, K.angle i j = DifferentialGeometry.Toponogov.limitingRadialAngle
        len (fun i => ray i) i j) ∧
      let _ := K.metricSpace
      TotallyBounded (univ : Set (Quotient K.setoid)) ∧
        CompactSpace (UniformSpace.Completion (Quotient K.setoid)) := by
    intro ι len ray hlen hlenr hzero hmin
    have hrad : DifferentialGeometry.Toponogov.IsRadialFamily qW len (fun i => ray i) := by
      intro i s hs
      simpa only [hzero, sub_zero, abs_of_pos hs.1, dist_comm qW] using
        hmin i s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, (hlen i).le⟩
    have hmono (i j : ι) := DifferentialGeometry.Toponogov.radialComparisonAngle_nonincreasing_of_completion_segments
      (g.restrictOpen W) hmetricW hsecW hmissingW hcompactBall hcoverBall havoid
      hlen hlenr hzero hmin i j
    let K := DifferentialGeometry.Toponogov.limitingRadialAngleKernel qW len (fun i => ray i)
      hlen hrad (fun i s hs t ht => hmin i s ⟨hs.1.le, hs.2⟩ t ⟨ht.1.le, ht.2⟩)
      (fun i j _ => hmono i j)
    have hK (i j : ι) : K.angle i j =
        DifferentialGeometry.Toponogov.limitingRadialAngle len (fun i => ray i) i j := rfl
    refine ⟨K, hK, ?_⟩
    let _ := K.metricSpace
    have htb := totallyBounded_limiting_directions_of_convergent_neck_separators
      (g.restrictOpen W) hmetricW hsecW hmissingW hcompactBall hcoverBall havoid
      hA hregion hKnhds hfrontNecks hcentersT hscalar
      (Eventually.of_forall (fun n => hc.trans_le (hquantW n (γ (t n)) (hcenters n))))
      len ray hlen hlenr hzero hmin K hK
    exact ⟨htb, Metric.compactSpace_completion_of_totallyBounded htb⟩
  refine ⟨qW, hqW, hdistW, hmissingW, hmap, hcoeOpen, hregion, hcompact, hKnhds,
    hscalarW, hquantW, havoid, hupper, delta, hdelta, hcompactBall, hcoverBall, ?_, ?_, hdir⟩
  · apply DifferentialGeometry.Toponogov.exists_punctured_annulus_cone_approximation
      (g.restrictOpen W) hmetricW hsecW hmissingW hdelta hcompactBall hcoverBall havoid
    intro ι len ray hlen hlenr hzero hmin
    obtain ⟨K, hK, htb, _⟩ := hdir len ray hlen hlenr hzero hmin
    exact ⟨K, hK, htb⟩
  · intro eps heps
    apply DifferentialGeometry.Toponogov.exists_radial_sphere_nets_of_totallyBounded_limiting_directions
      (g.restrictOpen W) hmetricW hdelta hcompactBall hcoverBall ?_ heps
    intro ι len ray hlen hlenr hzero hmin
    obtain ⟨K, hK, htb, _⟩ := hdir len ray hlen hlenr hzero hmin
    exact ⟨K, hK, htb⟩


theorem exists_spatialNeck_sequence_with_punctured_completion
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (metric : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf metric x y)
    {b alpha : ℝ} (hb : 0 < b) (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000)
    (hsec : ∀ (x : M) (v w : TangentSpace I3 x),
      0 ≤ metricRm04StandardAt metric x v w w v)
    (g : C(Ico 0 b, M)) (hg : Isometry g)
    (hblow : Tendsto (fun t => metricScalarAt metric (g t))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) atTop)
    (q : UniformSpace.Completion M)
    (hq : Tendsto (fun t => (g t : UniformSpace.Completion M))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) (𝓝 q))
    (hnecks : ∀ᶠ tau : Ico 0 b in comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b),
      Nonempty (SpatialNeck metric alpha (g tau))) :
        ∃ t : ℕ → Ico 0 b,
          ∃ nk : ∀ n, SpatialNeck metric (2 * alpha) (g (t n)),
            StrictMono (fun n => (t n : ℝ)) ∧
            Tendsto (fun n => (t n : ℝ)) atTop (𝓝 b) ∧
            (∀ n, (t (n + 1) : ℝ) - t n =
              ((2 * alpha)⁻¹ / 40) /
                Real.sqrt (metricScalarAt metric (g (t n)))) ∧
            (∀ n, ∃ (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
              (height : Sphere 2 → ℝ), ContMDiff I2 𝓘(ℝ, ℝ) ∞ height ∧
              (∀ p, height p ∈ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ∧
              ∀ p, (nk n).map (p, height p) = (nk (n + 1)).map (eta p, 0)) ∧
            Pairwise (fun i j =>
              Disjoint ((nk i).map '' (univ ×ˢ ({0} : Set ℝ)))
                ((nk j).map '' (univ ×ˢ ({0} : Set ℝ)))) ∧
            LocallyFinite (fun n =>
              (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) ∧
            ∃ eta : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
              ∃ Ψ : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞,
                (∀ n, (univ ×ˢ Icc (0 : ℝ) 1 ⊆ (Ψ n).source) ∧
                  (∀ p, Ψ n (p, 0) = (nk n).map (p, 0)) ∧
                  (∀ p, Ψ n (p, 1) = (nk (n + 1)).map (eta n p, 0)) ∧
                  IsCompact (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                  (frontier (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                    (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) ∪
                      (nk (n + 1)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                  (Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                    (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) ∧
                  Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
                    riemannianClosedBallOf metric (g (t n))
                      ((3 * (2 * alpha)⁻¹ / 100) /
                        Real.sqrt (metricScalarAt metric (g (t n)))) ∩
                    riemannianClosedBallOf metric (g (t (n + 1)))
                      ((3 * (2 * alpha)⁻¹ / 100) /
                        Real.sqrt (metricScalarAt metric (g (t n))))) ∧
                (∀ i j, i + 1 < j →
                  Disjoint (Ψ i '' (univ ×ˢ Icc (0 : ℝ) 1))
                    (Ψ j '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
                Pairwise (fun i j =>
                  Disjoint (interior (Ψ (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)))
                    (interior (Ψ (j + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)))) ∧
                (∀ n, (Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
                  (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                    (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                (∀ n, (nk (n + 2)).map '' (univ ×ˢ ({0} : Set ℝ)) ⊆
                  interior ((Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∪
                    (Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)))) ∧
                LocallyFinite (fun n => Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                IsClosed (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                IsConnected (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                ¬ IsCompact (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                (frontier (⋃ n, Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
                  ⋃ n, (nk n).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                IsClosed (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                IsConnected (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                ¬ IsCompact (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
                (frontier (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
                  (nk 1).map '' (univ ×ˢ ({0} : Set ℝ))) ∧
                (∀ v : Ico 0 b, (t 2 : ℝ) ≤ v →
                  g v ∈ interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
                (∀ n (x : M), x ∈ Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) →
                  dist q (x : UniformSpace.Completion M) ≤
                    (11 / 5) * (b - (t n : ℝ))) ∧
                (∀ n (x : M), x ∈ Ψ n '' (univ ×ˢ Icc (0 : ℝ) 1) →
                  ((2 * alpha)⁻¹) ^ 2 / 8 ≤ metricScalarAt metric x *
                    dist q (x : UniformSpace.Completion M) ^ 2) ∧
                (∀ᶠ n in atTop,
                  (nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ⊆
                    interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
                ∃ E : Sphere 2 × Ici (0 : ℝ) ≃ₜ
                  (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                  ∃ theta : ℕ → Sphere 2 ≃ₜ Sphere 2,
                    theta 0 = Homeomorph.refl (Sphere 2) ∧
                    (∀ n, theta (n + 1) =
                      (theta n).trans (eta (n + 1)).toHomeomorph) ∧
                    (∀ (n : ℕ) (p : Sphere 2) (s : Icc (0 : ℝ) 1),
                      (E (p, ⟨n + (s : ℝ),
                        add_nonneg (Nat.cast_nonneg n) s.property.1⟩) : M) =
                          Ψ (n + 1) (theta n p, s)) ∧
                    (∀ s : Ici (0 : ℝ), Nonempty
                      (DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
                        (fun p : Sphere 2 => (E (p, s) : M)))) ∧
                    ∃ D : Sphere 2 × Ioi (0 : ℝ) ≃ₜ
                      interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                      (∀ (p : Sphere 2) (s : Ioi (0 : ℝ)),
                        (D (p, s) : M) =
                          (E (p, Set.inclusion Ioi_subset_Ici_self s) : M)) ∧
                      let W : TopologicalSpace.Opens M :=
                        ⟨interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)),
                          isOpen_interior⟩
                      ∃ gW : C(Ico (t 2 : ℝ) b, W),
                        (∀ v : Ico (t 2 : ℝ) b, (gW v : M) =
                          g ⟨v, (t 2).property.1.trans v.property.1, v.property.2⟩) ∧
                        (∀ v w : Ico (t 2 : ℝ) b,
                          riemannianEDistOf (metric.restrictOpen W) (gW v) (gW w) =
                            edist v w) ∧
                        (∀ᶠ n in atTop, ∃ hn : (t 2 : ℝ) ≤ t n,
                          ∃ nkW : SpatialNeck (metric.restrictOpen W) (2 * alpha)
                            (gW ⟨t n, hn, (t n).property.2⟩),
                            nkW.map.source = (nk n).map.source ∩
                              (nk n).map ⁻¹' (W : Set M) ∧
                            (∀ y ∈ univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
                              (nkW.map y : M) = (nk n).map y) ∧
                            ∀ y : W, nkW.map.symm y = (nk n).map.symm (y : M)) ∧
                        ∃ hW : PathConnectedSpace W,
                          let _ : PathConnectedSpace W := hW
                          let mW : MetricSpace W :=
                            let _ : PseudoMetricSpace W :=
                              (metric.restrictOpen W).toPseudoMetricSpace
                            MetricSpace.ofT0PseudoMetricSpace W
                          let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
                          let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
                          let eW : PseudoEMetricSpace W :=
                            @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
                          let _ : WeakPseudoEMetricSpace W :=
                            @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
                          ∃ qW : UniformSpace.Completion W,
                            Tendsto (fun v => (gW v : UniformSpace.Completion W))
                              (comap (Subtype.val : Ico (t 2 : ℝ) b → ℝ)
                                (𝓝 b)) (𝓝 qW) ∧
                            (∀ v : Ico (t 2 : ℝ) b,
                              dist qW (gW v : UniformSpace.Completion W) = b - v) ∧
                            qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
                            UniformSpace.Completion.map (Subtype.val : W → M) qW = q ∧
                            Topology.IsOpenEmbedding
                              (fun x : W => (x : UniformSpace.Completion W)) ∧
                            (∀ U ∈ 𝓝 qW, ∀ᶠ n in atTop,
                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                {x : W | (x : M) ∈ Ψ (n + 2) ''
                                  (univ ×ˢ Icc (0 : ℝ) 1)} ⊆ U) ∧
                            IsCompact (insert qW (⋃ n,
                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                {x : W | (x : M) ∈ Ψ (n + 2) ''
                                  (univ ×ˢ Icc (0 : ℝ) 1)})) ∧
                            insert qW (⋃ n,
                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                {x : W | (x : M) ∈ Ψ (n + 2) ''
                                  (univ ×ˢ Icc (0 : ℝ) 1)}) ∈ 𝓝 qW ∧
                            Tendsto (fun x : W => metricScalarAt (metric.restrictOpen W) x)
                              (comap (fun x : W => (x : UniformSpace.Completion W))
                                (𝓝 qW)) atTop ∧
                            (∀ n (x : W), (x : M) ∈ Ψ (n + 2) ''
                              (univ ×ˢ Icc (0 : ℝ) 1) →
                              ((2 * alpha)⁻¹) ^ 2 / 8 ≤
                                metricScalarAt (metric.restrictOpen W) x *
                                  dist qW (x : UniformSpace.Completion W) ^ 2) ∧
                            (∀ (β : ℝ → UniformSpace.Completion W) (u v w : ℝ),
                              u < v → v < w →
                              (∀ s ∈ Icc u w, ∀ t ∈ Icc u w,
                                dist (β s) (β t) = |s - t|) → β v ≠ qW) ∧
                            (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
                              metricScalarAt metric (g (t (n + 2))) *
                                (b - (t (n + 2) : ℝ)) ^ 2 ≤ C) ∧
                            ∃ delta : ℝ, 0 < delta ∧
                              IsCompact (Metric.closedBall qW delta) ∧
                              Metric.closedBall qW delta ⊆ insert qW
                                (range (fun x : W => (x : UniformSpace.Completion W))) ∧
                                Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
                                (∀ eps > 0, ∃ d ∈ Ioo 0 (delta / 3), ∃ A : Finset C(ℝ, UniformSpace.Completion W),
                                  (∀ ray ∈ A, ray 0 = qW ∧
                                    ∀ s ∈ Icc 0 d, ∀ t ∈ Icc 0 d, dist (ray s) (ray t) = |s - t|) ∧
                                  ∀ s ∈ Ioc 0 d, ∀ x : W, dist (x : UniformSpace.Completion W) qW = s →
                                    ∃ ray ∈ A, dist (x : UniformSpace.Completion W) (ray s) < eps * s) ∧
                                ∀ {ι : Type u} (len : ι → ℝ) (ray : ι → C(ℝ, UniformSpace.Completion W)),
                                  (∀ i, 0 < len i) → (∀ i, len i < delta / 3) → (∀ i, ray i 0 = qW) →
                                  (∀ i, ∀ s ∈ Icc 0 (len i), ∀ t ∈ Icc 0 (len i),
                                    dist (ray i s) (ray i t) = |s - t|) →
                                  ∃ K : DifferentialGeometry.Toponogov.AngleKernel ι,
                                    (∀ i j, K.angle i j = DifferentialGeometry.Toponogov.limitingRadialAngle
                                      len (fun i => ray i) i j) ∧
                                    let _ := K.metricSpace
                                    TotallyBounded (univ : Set (Quotient K.setoid)) ∧
                                      CompactSpace (UniformSpace.Completion (Quotient K.setoid)) := by
  have hmap : NeBot (map (Subtype.val : Ico 0 b → ℝ)
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b))) := by
    rw [map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot hb
  let _ := hmap.of_map
  obtain ⟨q', hq', hdist⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hb hg
  have hqq : q' = q := tendsto_nhds_unique hq' hq
  subst q'
  have hmissing : q ∉ range (fun x : M => (x : UniformSpace.Completion M)) := by
    rintro ⟨x, hx⟩
    exact (UniformSpace.Completion.ne_coe_of_tendsto_atTop (f := fun x => metricScalarAt metric x)
      hq hblow x
      (metricScalar_smooth metric).continuous.continuousAt) hx.symm
  obtain ⟨delta, hdelta, hprop⟩ := Metric.eventually_nhds_iff.mp
    (Filter.eventually_comap.mp hnecks)
  let a := max 0 (b - delta / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have har : a < b := max_lt hb (by linarith only [hdelta])
  have hgood (tau : Ico 0 b) (htau : a ≤ (tau : ℝ)) :
      Nonempty (SpatialNeck metric alpha (g tau)) := by
    have hd : dist (tau : ℝ) b < delta := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr tau.property.2), neg_sub]
      have hh : b - delta / 2 ≤ (tau : ℝ) := (le_max_right _ _).trans htau
      linarith only [hh, hdelta]
    exact hprop hd tau rfl
  let incl : C(Ico a b, Ico 0 b) :=
    ⟨fun tau => ⟨tau, ha0.trans tau.property.1, tau.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let curve := g.comp incl
  have hcurve (v w : Ico a b) :
      riemannianEDistOf metric (curve v) (curve w) = edist v w := by
    rw [← hmetric]
    change edist (g (incl v)) (g (incl w)) = edist v w
    rw [hg.edist_eq]
    rfl
  have hquant' (tau : Ico a b) :
      ((2 * alpha)⁻¹) ^ 2 ≤ metricScalarAt metric (curve tau) * (b - tau) ^ 2 := by
    obtain ⟨nk⟩ := hgood (incl tau) tau.property.1
    have hh := nk.scalar_mul_completion_dist_sq_lower_bound_of_scalar_tendsto_atTop
      hmetric hq hblow
    rw [dist_comm, hdist] at hh
    have hquarter : (1 : ℝ) / 4 ≤ 1 - alpha := by linarith only [hsmall]
    have hfactor : ((2 * alpha)⁻¹) ^ 2 = (alpha⁻¹) ^ 2 / 4 := by
      rw [mul_inv_rev, mul_pow]
      norm_num
      ring
    rw [hfactor]
    apply le_trans _ hh
    nlinarith only [mul_le_mul_of_nonneg_left hquarter (sq_nonneg alpha⁻¹)]
  obtain ⟨t, nk, _ht0, hmono, hlim, hstep, _hcover, hgraph, hdisjoint, eta, ann, hannuli, hsep, hinterior, hinter, hseam⟩ :=
    exists_spatialNeck_sequence_along_isometric_curve metric har (by linarith only [hsmall]) curve hcurve
      (fun tau => (hgood (incl tau) tau.property.1).map
        (fun nk => nk.mono (by linarith only [ha]) (by linarith only [hsmall]))) hquant'
  have htend : Tendsto (incl ∘ t) atTop
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) :=
    tendsto_comap_iff.mpr hlim
  have hscalar : Tendsto (fun n => metricScalarAt metric (g (incl (t n)))) cofinite atTop := by
    rw [Nat.cofinite_eq_atTop]
    exact hblow.comp htend
  have hlocal := SpatialNeck.locallyFinite_of_scalar_tendsto_atTop nk
    (eta := 2 * alpha) (by linarith only [hsmall] : 2 * alpha < 1 / 4323) (fun _ => le_rfl) hscalar
  have hsource := fun n => (hannuli n).1
  have hleft := fun n => (hannuli n).2.1
  have hright := fun n => (hannuli n).2.2.1
  have hcann := fun n => (hannuli n).2.2.2.1
  have hfrann := fun n => (hannuli n).2.2.2.2.1
  have hsubann := fun n => (hannuli n).2.2.2.2.2.1
  have hlocalAnn := hlocal.subset hsubann
  have hclosedAnn := hlocalAnn.isClosed_iUnion (fun n => (hcann n).isClosed)
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  have hconnAnn (n : ℕ) : IsConnected (ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    (isConnected_univ.prod (isConnected_Icc zero_le_one)).image _
      ((ann n).contMDiffOn_toFun.continuousOn.mono (hsource n))
  have hmeetAnn (n : ℕ) : ((ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
      (ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))).Nonempty := by
    let p : Sphere 2 := Classical.choice inferInstance
    refine ⟨ann n (p, 1), ⟨(p, 1), ⟨mem_univ _, by simp⟩, rfl⟩,
      ⟨(eta n p, 0), ⟨mem_univ _, by simp⟩, ?_⟩⟩
    rw [hleft, hright]
  have hconnUnion := IsConnected.iUnion_of_chain hconnAnn hmeetAnn
  have hlocalShift (k : ℕ) := hlocalAnn.comp_injective
    (g := fun n : ℕ => n + k) (fun _ _ hij => Nat.add_right_cancel hij)
  have hnotCompact (k : ℕ) : ¬ IsCompact (⋃ n, ann (n + k) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    intro hc
    apply (Set.infinite_univ : (univ : Set ℕ).Infinite)
    apply ((hlocalShift k).finite_nonempty_inter_compact hc).subset
    intro n _
    obtain ⟨y, hy⟩ := (hconnAnn (n + k)).nonempty
    exact ⟨y, hy, mem_iUnion.mpr ⟨n, hy⟩⟩
  have hfrontAnn : frontier (⋃ n, ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
      ⋃ n, (nk n).map '' (univ ×ˢ ({0} : Set ℝ)) := by
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hlocalAnn.frontier_iUnion_subset hy)
    rw [hfrann n] at hn
    rcases hn with hn | hn
    · exact mem_iUnion.mpr ⟨n, hn⟩
    · exact mem_iUnion.mpr ⟨n + 1, hn⟩
  have hclosedTail := (hlocalShift 1).isClosed_iUnion (fun n => (hcann (n + 1)).isClosed)
  have hconnTail := IsConnected.iUnion_of_chain (fun n => hconnAnn (n + 1))
    (fun n => hmeetAnn (n + 1))
  have hfrontTail := hlocalAnn.frontier_iUnion_succ_eq_of_chain _
    (fun n => (hcann n).isClosed) hfrann hseam (fun n => hsep 0 (n + 2) (Nat.succ_lt_succ (Nat.zero_lt_succ n)))
  have hstart : g (incl (t 2)) ∈ interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    apply interior_mono (union_subset (subset_iUnion (fun n => ann (n + 1) ''
      (univ ×ˢ Icc (0 : ℝ) 1)) 0) (subset_iUnion (fun n => ann (n + 1) ''
        (univ ×ˢ Icc (0 : ℝ) 1)) 1))
    apply hseam 0
    exact ⟨((nk 2).center, 0), ⟨mem_univ _, rfl⟩, (nk 2).center_eq⟩
  have haxisTail := axis_mem_interior_of_frontier_eq_central_sphere metric hmetric
    (by linarith only [hsmall] : 2 * alpha < 1 / 1000000) g hg (incl (t 1)) (incl (t 2))
    (hmono (by decide : (1 : ℕ) < 2)) (nk 1) (hstep 1) hfrontTail hstart
  have hcollapse (n : ℕ) (x : M) (hx : x ∈ ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) :
      dist q (x : UniformSpace.Completion M) ≤ (11 / 5) * (b - (t n : ℝ)) := by
    have hb := ((hannuli n).2.2.2.2.2.2 hx).1
    change riemannianEDistOf metric (g (incl (t n))) x ≤ ENNReal.ofReal
      ((3 * (2 * alpha)⁻¹ / 100) / Real.sqrt (metricScalarAt metric (g (incl (t n))))) at hb
    rw [← hmetric, edist_dist] at hb
    have hD : (3 * (2 * alpha)⁻¹ / 100) /
        Real.sqrt (metricScalarAt metric (g (incl (t n)))) =
          (6 / 5) * ((t (n + 1) : ℝ) - t n) := by
      rw [hstep n]
      change _ = (6 / 5) * (((2 * alpha)⁻¹ / 40) /
        Real.sqrt (metricScalarAt metric (g (incl (t n)))))
      ring
    rw [hD] at hb
    have hstepNonneg : 0 ≤ (t (n + 1) : ℝ) - t n :=
      sub_nonneg.mpr (hmono.monotone (Nat.le_succ n))
    have hb' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hstepNonneg)).mp hb
    have htriangle := dist_triangle q
      (g (incl (t n)) : UniformSpace.Completion M) (x : UniformSpace.Completion M)
    rw [hdist, UniformSpace.Completion.dist_eq] at htriangle
    have hremain := (t (n + 1)).property.2
    change _ ≤ b - (t n : ℝ) + dist (g (incl (t n))) x at htriangle
    linarith only [htriangle, hb', hremain]
  have hquantAnn (n : ℕ) (x : M) (hx : x ∈ ann n '' (univ ×ˢ Icc (0 : ℝ) 1)) :
      ((2 * alpha)⁻¹) ^ 2 / 8 ≤ metricScalarAt metric x *
        dist q (x : UniformSpace.Completion M) ^ 2 := by
    apply scalar_distance_lower_bound_of_mem_neck_ball metric hmetric (nk n)
      (by linarith only [hsmall] : 2 * alpha ≤ 1 / 8646) q _ (hsubann n hx)
      (((hannuli n).2.2.2.2.2.2 hx).1)
    have hd : dist q (curve (t n) : UniformSpace.Completion M) = b - (t n : ℝ) :=
      hdist (incl (t n))
    rw [hd]
    exact hquant' (t n)
  have hip : 0 < (2 * alpha)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) ha)
  have hfrontCompact : IsCompact
      (frontier (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))) := by
    rw [hfrontTail]
    apply ((isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod
      (isCompact_singleton : IsCompact ({0} : Set ℝ))).image_of_continuousOn
    apply (nk 1).map.contMDiffOn_toFun.continuousOn.mono
    intro z hz
    apply (nk 1).domain
    refine ⟨mem_univ _, ?_⟩
    have hz' : z.2 = 0 := hz.2
    rw [hz']
    exact ⟨neg_lt_zero.mpr hip, hip⟩
  have hwindowConn : ∀ᶠ n in cofinite, IsPreconnected
      ((nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) := by
    apply Filter.Eventually.of_forall
    intro n
    exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
      ((nk n).map.contMDiffOn_toFun.continuousOn.mono (nk n).domain)
  have hwindowMeet : ∀ᶠ n in cofinite,
      ((nk n).map '' (univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ∩
        interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1))).Nonempty := by
    rw [Nat.cofinite_eq_atTop]
    apply (eventually_ge_atTop 2).mono
    intro n hn
    exact ⟨g (incl (t n)),
      ⟨((nk n).center, 0), ⟨mem_univ _, neg_lt_zero.mpr hip, hip⟩, (nk n).center_eq⟩,
      haxisTail (incl (t n)) (hmono.monotone hn)⟩
  have hwindowCapture := hlocal.eventually_subset_interior_of_isCompact_frontier
    hfrontCompact hwindowConn hwindowMeet
  rw [Nat.cofinite_eq_atTop] at hwindowCapture
  obtain ⟨E, theta, htheta0, htheta, hE, hsections, D, hD⟩ :=
    exists_homeomorph_annular_end ann eta (fun n => (nk n).map)
      hsource hleft hright hcann hlocalAnn hsep hinter hfrontTail
  let W : TopologicalSpace.Opens M :=
    ⟨interior (⋃ n, ann (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)), isOpen_interior⟩
  let tailIncl : Ico (t 2 : ℝ) b → Ico 0 b :=
    fun v => ⟨v, (incl (t 2)).property.1.trans v.property.1, v.property.2⟩
  let gW : C(Ico (t 2 : ℝ) b, W) :=
    ⟨fun v => ⟨g (tailIncl v), haxisTail (tailIncl v) v.property.1⟩,
      (g.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  have hgW (v w : Ico (t 2 : ℝ) b) :
      riemannianEDistOf (metric.restrictOpen W) (gW v) (gW w) = edist v w := by
    apply le_antisymm
    · have hbound (v w : Ico (t 2 : ℝ) b) :
          riemannianEDistOf metric (gW v) (gW w) ≤ (1 : ℝ≥0∞) * edist v w := by
        rw [← hmetric]
        change edist (g (tailIncl v)) (g (tailIncl w)) ≤ 1 * edist v w
        rw [hg.edist_eq, one_mul]
        rfl
      have h := DifferentialGeometry.Geometry.riemannianEDistOf_restrictOpen_le_of_lipschitz
        metric W ordConnected_Ico (C := 1) hbound v w
      simpa only [ENNReal.coe_one, one_mul] using h
    · have h := riemannianEDistOf_le_restrictOpen metric W (gW v) (gW w)
      rw [← hmetric] at h
      change edist (g (tailIncl v)) (g (tailIncl w)) ≤ _ at h
      rw [hg.edist_eq] at h
      exact h
  have hnkW : ∀ᶠ n in atTop, ∃ hn : (t 2 : ℝ) ≤ t n,
      ∃ nkW : SpatialNeck (metric.restrictOpen W) (2 * alpha)
        (gW ⟨t n, hn, (t n).property.2⟩),
        nkW.map.source = (nk n).map.source ∩ (nk n).map ⁻¹' (W : Set M) ∧
        (∀ y ∈ univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
          (nkW.map y : M) = (nk n).map y) ∧
        ∀ y : W, nkW.map.symm y = (nk n).map.symm (y : M) := by
    apply (hwindowCapture.and (eventually_ge_atTop 2)).mono
    rintro n ⟨hn, h2n⟩
    refine ⟨hmono.monotone h2n, ?_⟩
    exact exists_restricted_neck metric W
      (gW ⟨t n, hmono.monotone h2n, (t n).property.2⟩) (nk n) hn
  have htailT : Tendsto tailIncl
      (comap (Subtype.val : Ico (t 2 : ℝ) b → ℝ) (𝓝 b))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) :=
    tendsto_comap_iff.mpr tendsto_comap
  have hannW (n : ℕ) : ann (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ (W : Set M) := by
    intro x hx
    have hu : x ∈ ⋃ k, ann (k + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) :=
      mem_iUnion.mpr ⟨n + 1, hx⟩
    by_contra hnotW
    have hf : x ∈ frontier (⋃ k, ann (k + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
      ⟨subset_closure hu, hnotW⟩
    rw [hfrontTail] at hf
    have hx0 : x ∈ ann 0 '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      apply (hcann 0).isClosed.frontier_subset
      rw [hfrann 0]
      exact Or.inr hf
    exact Set.disjoint_left.mp (hsep 0 (n + 2) (Nat.succ_lt_succ (Nat.zero_lt_succ n))) hx0 hx
  let u : ℕ → Ico (t 2 : ℝ) b := fun n =>
    ⟨t (n + 2), hmono.monotone (Nat.le_add_left 2 n), (t (n + 2)).property.2⟩
  have huT : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 b) :=
    hlim.comp (tendsto_add_atTop_nat 2)
  have hscalarU : Tendsto (fun n => metricScalarAt metric (gW (u n) : M))
      atTop atTop := by
    have hs : Tendsto (fun n => metricScalarAt metric (g (incl (t n)))) atTop atTop := by
      simpa only [Nat.cofinite_eq_atTop] using hscalar
    exact hs.comp (tendsto_add_atTop_nat 2)
  have hBcover (x : W) (hx : (x : M) ∉ ⋃ n, ann (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)) :
      (x : M) ∈ ann 1 '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp (interior_subset x.property)
    cases k with
    | zero => exact hk
    | succ n => exact False.elim (hx (mem_iUnion.mpr ⟨n, hk⟩))
  have hfrontRegions := (hlocalShift 2).frontier_iUnion_nat_add_subset
    (fun n => (hfrann (n + 2)).le) (fun n => hseam (n + 1))
  have hcenters (n : ℕ) : (gW (u n) : M) ∈ ann (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    refine ⟨((nk (n + 2)).center, 0), ⟨mem_univ _, le_rfl, zero_le_one⟩, ?_⟩
    exact (hleft (n + 2) _).trans (nk (n + 2)).center_eq
  have hcompletion := exists_restricted_completion_endpoint metric hmetric hsec
    W D (t 2).property.2 gW hgW q (hq.comp htailT) hmissing
    (by linarith only [hsmall] : 2 * alpha < 1 / 4323) u huT hscalarU
    (fun n => ann (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1)) (fun n => hcann (n + 2)) hannW
    (fun n => nk (n + 2)) (fun n => hsubann (n + 2))
    ((tendsto_add_atTop_nat 2).eventually hwindowCapture)
    (ann 1 '' (univ ×ˢ Icc (0 : ℝ) 1)) (hcann 1) hBcover
    hfrontRegions hcenters (inv_sq_div_eight_gt_of_small ha hsmall)
    (fun n x hx => hquantAnn (n + 2) x hx)
  refine ⟨incl ∘ t, nk, hmono, hlim, hstep, hgraph, hdisjoint,
    hlocal, eta, ann, hannuli, hsep, hinterior, hinter, hseam, hlocalAnn, hclosedAnn,
    hconnUnion, hnotCompact 0, hfrontAnn, hclosedTail, hconnTail, hnotCompact 1, hfrontTail,
    haxisTail, hcollapse, hquantAnn, hwindowCapture, ?_⟩
  refine ⟨E, theta, htheta0, htheta, hE, hsections, D, hD, gW, fun _ => rfl, hgW, hnkW, ?_⟩
  exact hcompletion

theorem exists_punctured_cone_end_of_spatial_necks
    {M : Type u} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (metric : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf metric x y)
    {b alpha : ℝ} (hb : 0 < b) (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000)
    (hsec : ∀ (x : M) (v w : TangentSpace I3 x),
      0 ≤ metricRm04StandardAt metric x v w w v)
    (g : C(Ico 0 b, M)) (hg : Isometry g)
    (hblow : Tendsto (fun t => metricScalarAt metric (g t))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) atTop)
    (q : UniformSpace.Completion M)
    (hq : Tendsto (fun t => (g t : UniformSpace.Completion M))
      (comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b)) (𝓝 q))
    (hnecks : ∀ᶠ tau : Ico 0 b in comap (Subtype.val : Ico 0 b → ℝ) (𝓝 b),
      Nonempty (SpatialNeck metric alpha (g tau))) :
    ∃ W : TopologicalSpace.Opens M, ∃ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let mW : MetricSpace W :=
        let _ : PseudoMetricSpace W := (metric.restrictOpen W).toPseudoMetricSpace
        MetricSpace.ofT0PseudoMetricSpace W
      let _ : MetricSpace W := mW
      let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
      let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
      let eW : PseudoEMetricSpace W :=
        @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
      let _ : WeakPseudoEMetricSpace W :=
        @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
      ∃ qW : UniformSpace.Completion W, ∃ delta : ℝ, 0 < delta ∧
        qW ∉ range (fun x : W => (x : UniformSpace.Completion W)) ∧
        UniformSpace.Completion.map (Subtype.val : W → M) qW = q ∧
        IsCompact (Metric.closedBall qW delta) ∧
        Metric.closedBall qW delta ⊆ insert qW
          (range (fun x : W => (x : UniformSpace.Completion W))) ∧
        ∃ x : ℕ → W, ∃ times : ℕ → Ico 0 b,
          (∀ n, (x n : M) = g (times n)) ∧
          Tendsto (fun n => (times n : ℝ)) atTop (𝓝 b) ∧
          Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
          (∀ n, dist (x n : UniformSpace.Completion W) qW = b - times n) ∧
          Tendsto (fun n => metricScalarAt (metric.restrictOpen W) (x n)) atTop atTop ∧
          (∀ n, ((2 * alpha)⁻¹) ^ 2 / 8 ≤
            metricScalarAt (metric.restrictOpen W) (x n) *
              dist (x n : UniformSpace.Completion W) qW ^ 2) ∧
          (∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
            metricScalarAt (metric.restrictOpen W) (x n) *
              dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B) ∧
          Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) := by
  obtain ⟨t, nk, htstrict, htend, _, _, _, _, eta, Ψ, hann, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, E, theta, _, _, _, _, D, _, hrest⟩ :=
    exists_spatialNeck_sequence_with_punctured_completion metric hmetric hb ha hsmall
      hsec g hg hblow q hq hnecks
  let W : TopologicalSpace.Opens M :=
    ⟨interior (⋃ n, Ψ (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)), isOpen_interior⟩
  obtain ⟨gW, hgW, _, _, hW, hrest⟩ := hrest
  let _ : PathConnectedSpace W := hW
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, hqW, hdistW, hmissing, hmap, _, _, _, _, _, hquantW, _, hupper,
    delta, hdelta, hcompact, hcover, happrox, _, _⟩ := hrest
  let u : ℕ → Ico (t 2 : ℝ) b := fun n =>
    ⟨t (n + 2), htstrict.monotone (by omega), (t (n + 2)).property.2⟩
  let x : ℕ → W := fun n => gW (u n)
  let times : ℕ → Ico 0 b := fun n => t (n + 2)
  have hux : ∀ n, (x n : M) = g (times n) := fun n => hgW (u n)
  have htimes : Tendsto (fun n => (times n : ℝ)) atTop (𝓝 b) :=
    htend.comp (tendsto_add_atTop_nat 2)
  have hu : Tendsto u atTop
      (comap (Subtype.val : Ico (t 2 : ℝ) b → ℝ) (𝓝 b)) :=
    tendsto_comap_iff.mpr htimes
  have hx : Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 qW) :=
    hqW.comp hu
  have hxdist (n : ℕ) : dist (x n : UniformSpace.Completion W) qW = b - times n := by
    rw [dist_comm]
    exact hdistW (u n)
  have hQ : Tendsto (fun n => metricScalarAt (metric.restrictOpen W) (x n))
      atTop atTop := by
    simp only [metricScalarAt_restrictOpen, hux]
    exact hblow.comp (tendsto_comap_iff.mpr htimes)
  have hlower (n : ℕ) : ((2 * alpha)⁻¹) ^ 2 / 8 ≤
      metricScalarAt (metric.restrictOpen W) (x n) *
        dist (x n : UniformSpace.Completion W) qW ^ 2 := by
    have hmem : (x n : M) ∈ Ψ (n + 2) '' (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [hux]
      refine ⟨((nk (n + 2)).center, 0), ⟨mem_univ _, le_rfl, zero_le_one⟩, ?_⟩
      exact ((hann (n + 2)).2.1 _).trans (nk (n + 2)).center_eq
    simpa only [dist_comm qW] using hquantW n (x n) hmem
  have hupper' : ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      metricScalarAt (metric.restrictOpen W) (x n) *
        dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, hBpos, hB⟩ := hupper
    refine ⟨B, hBpos, ?_⟩
    simpa only [metricScalarAt_restrictOpen, hux, hxdist, times] using hB
  exact ⟨W, hW, qW, delta, hdelta, hmissing, hmap, hcompact, hcover, x, times,
    hux, htimes, hx, hxdist, hQ, hlower, hupper', happrox⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
