import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderAxialDistance
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalTranslatedNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalModelChain

section
noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

private theorem ofReal_abs_snd_sub_le
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    ENNReal.ofReal |p.2 - q.2| ≤
      riemannianEDistOf (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) roundThreeCylinderShrinkerMetric p q := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have heq : roundThreeCylinderShrinkerMetric =
      roundTwoSphereShrinkerMetric.prod (standardEuclideanMetric ℝ) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  rw [heq]
  have h := riemannianEDistOf_snd_le_prod roundTwoSphereShrinkerMetric
    (standardEuclideanMetric ℝ) p q
  simpa only [riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq] using h

end DifferentialGeometry.Geometry

end

end

section
noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

private local instance : PreconnectedSpace Cylinder := by
  change PreconnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
  infer_instance

private theorem cylinder_reference_zero_eq_shrinker :
    cylinderReference.metric 0 = roundThreeCylinderShrinkerMetric := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, s⟩ ⟨v, a⟩ ⟨w, b⟩
  change (cylinderMetric (scaleMetric (max (2 * (1 - 0)) 1) _
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))).inner
      (y, s) (v, a) (w, b) = _
  erw [cylinderMetric_inner, roundThreeCylinderShrinkerMetric, SmoothRiemannianMetric.prod_inner,
    roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
    scaleMetric_inner, roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2), euclideanMetric_inner]
  norm_num
  change a * b = b * a
  exact mul_comm a b

theorem cylinderDiagonalQuotientMap_edist_le
    (z w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    riemannianEDistOf cylinderDiagonalQuotientMetric
      (cylinderDiagonalQuotientMap z) (cylinderDiagonalQuotientMap w) ≤
        riemannianEDistOf roundThreeCylinderShrinkerMetric z w := by
  have hquad : ∀ x v,
      cylinderDiagonalQuotientMetric.inner (cylinderDiagonalQuotientMap x)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          cylinderDiagonalQuotientMap x v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          cylinderDiagonalQuotientMap x v) ≤
        (1 : ℝ) * roundThreeCylinderShrinkerMetric.inner x v v := by
    intro x v
    rw [one_mul]
    have h := congrArg
      (fun g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) => g.inner x v v)
        localPullMetric_cylinderDiagonalQuotientMetric
    rw [localPullMetric_inner] at h
    exact h.le
  have h := edistOf_le_of_quad_of_localDiffeomorph
    roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph
    zero_lt_one hquad z w
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h

theorem exists_cylinderDiagonalQuotient_distance_upper_constant :
    ∃ B : ℝ, 0 < B ∧ ∀ z w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
      (riemannianEDistOf cylinderDiagonalQuotientMetric
        (cylinderDiagonalQuotientMap z) (cylinderDiagonalQuotientMap w)).toReal ≤
          abs (|z.2| - |w.2|) + B := by
  obtain ⟨B, hB, herror⟩ := exists_cylinderReference_axial_distance_error
  refine ⟨B, hB, ?_⟩
  intro z w
  have hup (a b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
      (riemannianEDistOf cylinderDiagonalQuotientMetric
        (cylinderDiagonalQuotientMap a) (cylinderDiagonalQuotientMap b)).toReal ≤
          |a.2 - b.2| + B := by
    have hfin := riemannianEDistOf_ne_top (cylinderReference.metric 0) a b
    have hproj := cylinderDiagonalQuotientMap_edist_le a b
    rw [← cylinder_reference_zero_eq_shrinker] at hproj
    have h := ENNReal.toReal_mono hfin hproj
    have he := (abs_le.mp (herror cylinderReference a b)).2
    linarith
  have hflip (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
      cylinderDiagonalQuotientMap (cylinderDiagonalDiffeomorph p) = cylinderDiagonalQuotientMap p :=
    cylinderDiagonalQuotientMap_eq_iff.mpr (Or.inr rfl)
  rcases le_total 0 z.2 with hz | hz <;> rcases le_total 0 w.2 with hw | hw
  · simpa only [abs_of_nonneg hz, abs_of_nonneg hw] using hup z w
  · have h := hup z (cylinderDiagonalDiffeomorph w)
    rw [hflip] at h
    rw [cylinderDiagonalDiffeomorph_apply] at h
    change _ ≤ |z.2 - -w.2| + B at h
    simpa only [abs_of_nonneg hz, abs_of_nonpos hw] using h
  · have h := hup (cylinderDiagonalDiffeomorph z) w
    rw [hflip] at h
    rw [cylinderDiagonalDiffeomorph_apply] at h
    change _ ≤ |-z.2 - w.2| + B at h
    simpa only [abs_of_nonpos hz, abs_of_nonneg hw] using h
  · simpa only [abs_of_nonpos hz, abs_of_nonpos hw, neg_sub_neg, abs_sub_comm] using hup z w

theorem exists_cylinderDiagonalQuotient_slab_ball_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) (R r : ℝ),
        max |z.2| (R - |z.2|) + B < 2 * r →
        cylinderDiagonalQuotientMap '' (Set.univ ×ˢ Set.Icc (-R) R) ⊆
          riemannianBallOf cylinderDiagonalQuotientMetric
            (cylinderDiagonalQuotientMap z) (2 * r) := by
  obtain ⟨B, hB, hup⟩ := exists_cylinderDiagonalQuotient_distance_upper_constant
  refine ⟨B, hB, ?_⟩
  intro z R r hr
  rintro q ⟨w, hw, rfl⟩
  have hwR : |w.2| ≤ R := abs_le.mpr hw.2
  have hheight : abs (|z.2| - |w.2|) ≤ max |z.2| (R - |z.2|) := by
    rw [abs_le]
    constructor
    · linarith [le_max_right |z.2| (R - |z.2|)]
    · linarith [le_max_left |z.2| (R - |z.2|), abs_nonneg w.2]
  have hdist := (hup z w).trans (add_le_add_left hheight B)
  have hfiniteSource : riemannianEDistOf roundThreeCylinderShrinkerMetric z w ≠ ⊤ := by
    rw [← cylinder_reference_zero_eq_shrinker]
    exact riemannianEDistOf_ne_top (cylinderReference.metric 0) z w
  have hfinite : riemannianEDistOf cylinderDiagonalQuotientMetric
      (cylinderDiagonalQuotientMap z) (cylinderDiagonalQuotientMap w) ≠ ⊤ :=
    ne_top_of_le_ne_top hfiniteSource (cylinderDiagonalQuotientMap_edist_le z w)
  exact (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr (hdist.trans_lt hr)

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Metric

private local instance :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

theorem ofReal_abs_abs_snd_sub_le_diagonalQuotient_edist
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    ENNReal.ofReal (abs (|p.2| - |q.2|)) ≤
      riemannianEDistOf cylinderDiagonalQuotientMetric
        (cylinderDiagonalQuotientMap p) (cylinderDiagonalQuotientMap q) := by
  apply le_edistOf_of_coveringMap_localPullMetric roundThreeCylinderShrinkerMetric
    cylinderDiagonalQuotientMetric cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_isCoveringMap localPullMetric_cylinderDiagonalQuotientMetric
    p (cylinderDiagonalQuotientMap q)
  intro w hw
  have habs : |w.2| = |q.2| := by
    rcases cylinderDiagonalQuotientMap_eq_iff.mp hw with h | h
    · rw [h]
    · rw [h, cylinderDiagonalDiffeomorph_apply]
      exact abs_neg q.2
  calc
    ENNReal.ofReal (abs (|p.2| - |q.2|)) = ENNReal.ofReal (abs (|p.2| - |w.2|)) := by rw [habs]
    _ ≤ ENNReal.ofReal |p.2 - w.2| := ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le _ _)
    _ ≤ riemannianEDistOf roundThreeCylinderShrinkerMetric p w := ofReal_abs_snd_sub_le p w

theorem abs_abs_snd_sub_le_diagonalQuotient_distance
    (p q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    abs (|p.2| - |q.2|) ≤
      (riemannianEDistOf cylinderDiagonalQuotientMetric
        (cylinderDiagonalQuotientMap p) (cylinderDiagonalQuotientMap q)).toReal := by
  have hsource : riemannianEDistOf roundThreeCylinderShrinkerMetric p q ≠ ⊤ :=
    riemannianEDistOf_ne_top roundThreeCylinderShrinkerMetric p q
  have hfin := ne_top_of_le_ne_top hsource (cylinderDiagonalQuotientMap_edist_le p q)
  have h := ENNReal.toReal_mono hfin (ofReal_abs_abs_snd_sub_le_diagonalQuotient_edist p q)
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h

end DifferentialGeometry.Geometry

end

end

section
noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

private theorem diagonal_metric_edist_eq
    (g : SmoothRiemannianMetric I3 M)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = cylinderDiagonalQuotientMetric)
    (p q : Cylinder) :
    riemannianEDistOf g (d (cylinderDiagonalQuotientMap p)) (d (cylinderDiagonalQuotientMap q)) =
      riemannianEDistOf cylinderDiagonalQuotientMetric
        (cylinderDiagonalQuotientMap p) (cylinderDiagonalQuotientMap q) := by
  have h := edistOf_pullbackMetricCross g d
    (cylinderDiagonalQuotientMap p) (cylinderDiagonalQuotientMap q)
  rw [hmetric] at h
  exact h.symm

private theorem diagonal_tube_distance_lower
    (g : SmoothRiemannianMetric I3 M)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = cylinderDiagonalQuotientMetric)
    (p : Cylinder) {L R : ℝ} {y : M}
    (hy : y ∈ d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R))) :
    L - |p.2| ≤ metricDistance g (d (cylinderDiagonalQuotientMap p)) y := by
  obtain ⟨q,⟨w,hw,rfl⟩,rfl⟩ := hy
  have hlower := abs_abs_snd_sub_le_diagonalQuotient_distance p w
  unfold metricDistance
  rw [diagonal_metric_edist_eq g d hmetric]
  have hwL : L ≤ w.2 := hw.2.1
  linarith [le_abs_self w.2, neg_le_abs (|p.2| - |w.2|)]

private theorem diagonal_ball_subset_slab
    (g : SmoothRiemannianMetric I3 M)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = cylinderDiagonalQuotientMetric)
    (p : Cylinder) {R r : ℝ} (hr : r ≤ R - |p.2|) :
    riemannianBallOf g (d (cylinderDiagonalQuotientMap p)) r ⊆
      d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-R) R)) := by
  intro y hy
  obtain ⟨q,rfl⟩ := d.surjective y
  obtain ⟨w,rfl⟩ := cylinderDiagonalQuotientMap_surjective q
  have hdist := ENNReal.toReal_lt_of_lt_ofReal hy
  change (riemannianEDistOf g (d (cylinderDiagonalQuotientMap p))
    (d (cylinderDiagonalQuotientMap w))).toReal < r at hdist
  rw [diagonal_metric_edist_eq g d hmetric] at hdist
  have hlower := abs_abs_snd_sub_le_diagonalQuotient_distance p w
  have hheight : |w.2| ≤ R := by
    linarith [neg_le_abs (|p.2| - |w.2|)]
  exact ⟨cylinderDiagonalQuotientMap w,⟨w,⟨mem_univ _,abs_le.mp hheight⟩,rfl⟩,rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_diagonal_slab_ball_sandwich_and_depth_with_margin
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = cylinderDiagonalQuotientMetric)
    (p : Cylinder) (H : ℝ) :
    ∃ L : ℝ, |p.2| < L ∧ max 10000 H < L - |p.2| ∧
      ∀ w : ℝ, 0 < w →
      ∃ R r : ℝ, R = L + w ∧ L < R ∧ 1 ≤ r ∧
      riemannianBallOf g (d (cylinderDiagonalQuotientMap p)) r ⊆
        d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-R) R)) ∧
      d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-R) R)) ⊆
        riemannianBallOf g (d (cylinderDiagonalQuotientMap p)) (2 * r) ∧
      ∀ y ∈ d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R)),
        max 10000 H < metricDistance g (d (cylinderDiagonalQuotientMap p)) y := by
  obtain ⟨B,hB,hupper⟩ := exists_cylinderDiagonalQuotient_slab_ball_bound
  let a := |p.2|
  let m := max (10000 : ℝ) H
  let L := 3 * a + B + m + 1
  have ha : 0 ≤ a := abs_nonneg _
  have hm : 10000 ≤ m := le_max_left _ _
  have hL : a < L := by dsimp only [L]; linarith
  have hml : m < L - |p.2| := by change m < L - a; dsimp only [L]; linarith
  refine ⟨L,hL,hml,?_⟩
  intro w hw
  let R := L + w
  let r := R - a
  have hLR : L < R := by dsimp only [R]; linarith
  have hr : 1 ≤ r := by dsimp only [r,R,L]; linarith
  have hra : a ≤ r := by dsimp only [r,R,L]; linarith
  have hBr : B < r := by dsimp only [r,R,L]; linarith
  have hmargin : max |p.2| (R - |p.2|) + B < 2 * r := by
    change max a r + B < 2 * r
    rw [max_eq_right hra]
    linarith
  refine ⟨R,r,rfl,hLR,hr,?_,?_,?_⟩
  · exact diagonal_ball_subset_slab g d hmetric p le_rfl
  · rintro _ ⟨q,hq,rfl⟩
    obtain ⟨v,hv,rfl⟩ := hq
    have hup := hupper p R r hmargin ⟨v,hv,rfl⟩
    change riemannianEDistOf g (d (cylinderDiagonalQuotientMap p))
      (d (cylinderDiagonalQuotientMap v)) < ENNReal.ofReal (2 * r)
    rw [diagonal_metric_edist_eq g d hmetric]
    exact hup
  · intro y hy
    have hlow := diagonal_tube_distance_lower g d hmetric p hy
    change m < _
    exact hml.trans_le hlow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem scalarOneShrinkingCylinderMetric_zero_eq_roundThreeCylinderShrinkerMetric :
    scalarOneShrinkingCylinderMetric 0 (by norm_num) = roundThreeCylinderShrinkerMetric := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, s⟩ ⟨v, a⟩ ⟨w, b⟩
  erw [scalarOneShrinkingCylinderMetric_inner, roundThreeCylinderShrinkerMetric,
    SmoothRiemannianMetric.prod_inner]
  simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
    roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2), sub_zero, mul_one]
  norm_num
  erw [scaleMetric_inner]
  change 2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b =
    2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + inner ℝ a b
  rw [Real.inner_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

omit [T2Space M] in
theorem pullbackMetric_diagonal_at_zero
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) :
    Diffeomorph.pullbackMetricCross (S.base.metric 0) d = cylinderDiagonalQuotientMetric := by
  apply localPullMetric_injective_of_surjective cylinderDiagonalQuotientMap
    cylinderDiagonalQuotientMap_isLocalDiffeomorph cylinderDiagonalQuotientMap_surjective
  rw [hmetric 0 le_rfl, scalarOneShrinkingCylinderMetric_zero_eq_roundThreeCylinderShrinkerMetric,
    localPullMetric_cylinderDiagonalQuotientMetric]

theorem scalar_eq_one_of_diagonal_shrinking_model
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) (x : M) :
    S.scalar 0 x = 1 := by
  obtain ⟨z, rfl⟩ := d.surjective x
  obtain ⟨p, rfl⟩ := cylinderDiagonalQuotientMap_surjective z
  let j : Cylinder → M := (d ∘ cylinderDiagonalQuotientMap) ∘ cylinderLineTranslation 0
  let hj := isLocalDiffeomorph_comp
    (isLocalDiffeomorph_comp d.isLocalDiffeomorph cylinderDiagonalQuotientMap_isLocalDiffeomorph)
    (cylinderLineTranslation 0).isLocalDiffeomorph
  have hlocal : localPullMetric (S.base.metric 0) j hj = scalarOneShrinkingCylinderMetric 0 (by norm_num) :=
    localPullMetric_diagonal_projection_translate (S.base.metric 0) d 0 0 _ (hmetric 0 le_rfl)
  have hh := metricScalarAt_localPull (S.base.metric 0) j hj p
  rw [hlocal, scalarOneShrinkingCylinderMetric_zero, doubleSphereCylinderMetric_scalar_native] at hh
  change metricScalarAt (S.base.metric 0) (d (cylinderDiagonalQuotientMap p)) = 1
  simpa only [j, Function.comp_apply, cylinderLineTranslation_apply, add_zero, Prod.mk.eta] using hh.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
