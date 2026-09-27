import DifferentialGeometry.Geometry.Neck.BallComplement
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FarSpatialNeck
import DifferentialGeometry.Geometry.Neck.SeparatingSphere
import DifferentialGeometry.Geometry.Neck.SpatialDiameter

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem TerminalLimit.exists_uniform_pathConnected_ball_complement
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit X) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : L.space.M,
      IsPathConnected (riemannianBallOf L.space.metric p r)ᶜ := by
  obtain ⟨Q₀, hQ₀⟩ := L.scalar_bound
  let Q := max Q₀ 0
  have hbound : ∀ x : L.space.M,
      Tensor0SBundle.normSq0S L.space.metric x 4 (metricRm04At L.space.metric x) ≤
        100 ^ 2 * Q ^ 2 := by
    intro x
    have hop : metricAlgebraicCurvatureTensorAt L.space.metric x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        L.space.metric x (by simp [ThreeSpace])).mpr
      intro v w
      have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
        funext i
        fin_cases i <;> simp [vec4]
      simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using
        L.nonnegative x (mem_univ x) v w
    have hnorm := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
      L.space.metric x (by simp [ThreeSpace]) hop
    have hR0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative L.space.metric x hop
    have hRQ : metricScalarAt L.space.metric x ≤ Q := (hQ₀ x).trans (le_max_left _ _)
    exact hnorm.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hR0 hRQ 2) (by positivity))
  obtain ⟨kappa', hkappa', hnc⟩ := L.noncollapse
  exact exists_uniform_pathConnected_ball_complement_of_metricNoncollapsed hkappa' (by positivity)
    L.space L.complete L.connected hnc hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem sectional_nonnegative_of_secLower_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] (g : SmoothRiemannianMetric I3 M)
    (h : SecLower g 0 univ) : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g := by
  apply (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff g).mpr
  intro x v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using h x (mem_univ x) v w

theorem exists_uniform_scalar_bound_outside_terminal_ball (kappa : ℝ) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ {eps sigma : ℝ} {Phi : ℝ → ℝ}, eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
          ¬ CompactSpace L.space.M → ∀ (A : ℝ), 0 ≤ A → ∀ p : L.space.M,
          ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
            ∀ (J : RealTimeInterval) (B : BackwardExtension L J) s, s ∈ J.carrier →
              (∀ x y : L.space.M,
                metricDistance L.space.metric x y ≤ metricDistance (B.solution.base.metric s) x y ∧
                metricDistance (B.solution.base.metric s) x y ≤ metricDistance L.space.metric x y + A) →
              ∀ y : L.space.M, R < metricDistance L.space.metric p y →
                B.solution.scalar s y ≤ C := by
  obtain ⟨eta0, heta0, hsep⟩ := exists_far_spatialNeck_unbounded_separated_component_of_nonnegative.{u}
  let alpha := min (eta0 / 4) (1 / 64)
  have halpha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have hsmall : alpha < 1 / 32 := (min_le_right _ _).trans_lt (by norm_num)
  have htol : 2 * alpha ≤ eta0 := by
    have h := min_le_left (eta0 / 4) (1 / 64 : ℝ)
    change alpha ≤ eta0 / 4 at h
    linarith
  obtain ⟨epsStar, hepsStar, hneck⟩ := exists_far_spatialNeck_of_backwardExtension.{u}
    kappa halpha hsmall
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps sigma Phi heps X L hnoncompact A hA p
  let _ : ConnectedSpace L.space.M := L.connected
  let _ : NoncompactSpace L.space.M := ⟨fun h => hnoncompact (isCompact_univ_iff.mp h)⟩
  let _ : EMetricSpace L.space.M := L.space.emetricSpace
  have hfinite (x y : L.space.M) : edist x y ≠ ⊤ := riemannianEDistOf_ne_top L.space.metric x y
  let _ : MetricSpace L.space.M := EMetricSpace.toMetricSpace hfinite
  have hdist (x y : L.space.M) : dist x y = metricDistance L.space.metric x y := rfl
  obtain ⟨r, hr, hball⟩ := L.exists_uniform_pathConnected_ball_complement
  have hcomplete0 : RiemannianMetricComplete L.space.metric := ⟨L.complete.complete⟩
  have hsec0 := sectional_nonnegative_of_secLower_zero L.space.metric L.nonnegative
  obtain ⟨Rn, hRn, hcenter⟩ := hneck heps X L hnoncompact A hA p
  obtain ⟨Rs, Cs, hRs, hCs, hseparate⟩ := hsep L.space.M L.space.metric hcomplete0 hsec0 p A hA
  obtain ⟨Cd, hCd, hdiam⟩ := exists_uniform_spatial_neck_core_diameter (M := L.space.M)
  let R := max Rn (max Rs r) + 1
  let C := max 4 (max Cs ((Cd / r) ^ 2)) + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_left Rn (max Rs r)]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨R, C, hR, hC, ?_⟩
  intro J B s hs herror y hy
  by_contra hnot
  have hqbig : max 4 (max Cs ((Cd / r) ^ 2)) < B.solution.scalar s y := by
    dsimp [C] at hnot
    linarith
  have hq4 : 4 < B.solution.scalar s y := (le_max_left _ _).trans_lt hqbig
  have hqCs : Cs < B.solution.scalar s y :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hqbig
  have hqscale : (Cd / r) ^ 2 < B.solution.scalar s y :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hqbig
  have hyrn : Rn < metricDistance L.space.metric p y := by
    dsimp [R] at hy
    linarith [le_max_left Rn (max Rs r)]
  have hyrs : Rs < metricDistance L.space.metric p y := by
    dsimp [R] at hy
    linarith [(le_max_left Rs r).trans (le_max_right Rn (max Rs r))]
  have hyr : r < metricDistance L.space.metric p y := by
    dsimp [R] at hy
    linarith [(le_max_right Rs r).trans (le_max_right Rn (max Rs r))]
  have habs : ∀ x z : L.space.M,
      |metricDistance (B.solution.base.metric s) x z - metricDistance L.space.metric x z| ≤ A := by
    intro x z
    rw [abs_of_nonneg (sub_nonneg.mpr (herror x z).1)]
    linarith [(herror x z).2]
  obtain ⟨nk⟩ := hcenter J B s hs habs y hyrn hq4
  have hdiamr : Cd / Real.sqrt (B.solution.scalar s y) < r := by
    have hq : 0 < B.solution.scalar s y := by linarith
    have hroot := Real.sq_sqrt hq.le
    have hdiv : 0 ≤ Cd / r := div_nonneg hCd.le hr.le
    have hlt : Cd / r < Real.sqrt (B.solution.scalar s y) := by
      nlinarith [Real.sqrt_nonneg (B.solution.scalar s y)]
    have hcross := (div_lt_iff₀ hr).mp hlt
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hq)).mpr
    nlinarith
  let S := nk.map '' (univ ×ˢ ({0} : Set ℝ))
  have hcentral : S ⊆ riemannianBallOf L.space.metric y r := by
    intro w hw
    have hycore : y ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) :=
      ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
    have hwcore : w ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) := by
      obtain ⟨u, hu, rfl⟩ := hw
      exact ⟨u, ⟨hu.1, by rw [show u.2 = 0 from hu.2]; norm_num⟩, rfl⟩
    have hd := (herror y w).1.trans_lt
      ((hdiam (B.solution.base.metric s) (2 * alpha) y nk y hycore w hwcore).trans_lt hdiamr)
    change riemannianEDistOf L.space.metric y w < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)]
    exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr hd
  have hp : p ∈ (riemannianBallOf L.space.metric y r)ᶜ := by
    intro hmem
    have hsmall := ENNReal.toReal_lt_of_lt_ofReal hmem
    change metricDistance L.space.metric y p < r at hsmall
    rw [show metricDistance L.space.metric y p = metricDistance L.space.metric p y from
      by simp only [metricDistance, riemannianEDistOf_comm]] at hsmall
    linarith
  have hcomplete : RiemannianMetricComplete (B.solution.base.metric s) := ⟨(B.complete s hs).complete⟩
  have hsec := sectional_nonnegative_of_secLower_zero (B.solution.base.metric s) (B.nonnegative s hs)
  obtain ⟨z, hzfar, hzcomp⟩ := hseparate (B.solution.base.metric s) hcomplete hsec
    (2 * alpha) y nk htol habs hyrs hqCs (metricDistance L.space.metric p y + r)
  have hz : z ∈ (riemannianBallOf L.space.metric y r)ᶜ := by
    intro hmem
    have hsmall := ENNReal.toReal_lt_of_lt_ofReal hmem
    change metricDistance L.space.metric y z < r at hsmall
    have htri := dist_triangle p y z
    rw [hdist, hdist, hdist] at htri
    linarith
  have hcomponent : (riemannianBallOf L.space.metric y r)ᶜ ⊆ connectedComponentIn Sᶜ p :=
    (hball y).isConnected.isPreconnected.subset_connectedComponentIn hp
      (compl_subset_compl.mpr hcentral)
  exact hzcomp (hcomponent hz)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
