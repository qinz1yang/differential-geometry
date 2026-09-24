import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannProper
import DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannDiameter
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveSoulDiffeomorph
import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology.SphereSeparation (AxialInterval axialZero sliceImage)
open KappaSolutions (SpatialNeckSphere SpatialNeckWitness SpatialNeckSideData)

private local instance neckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps eta t : ℝ} {v p : M}
  {h : SmoothRiemannianMetric I3 M} {yStar : SpatialNeckSphere}
  {W : SpatialNeckWitness h yStar p eta}

namespace StrongNeck

theorem bicollar_zero_sides_eq_of_centralSphere_eq (nk : StrongNeck S eps v t)
    (ψ : Diffeomorph I3 I3 M ThreeSpace ∞) (sides : SpatialNeckSideData W)
    (hsphere : nk.map '' (univ ×ˢ ({0} : Set ℝ)) = W.centralSphere) :
    (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).compactSide = sides.lower 0 ∧
      (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).endSide = sides.upper 0 := by
  have heta : 0 < eta := W.epsilon_pos
  have hzero : |(0 : ℝ)| < eta⁻¹ + 1 := by
    rw [abs_zero]
    positivity
  have hslice : sliceImage nk.bicollar (axialZero (inv_pos.mpr nk.eps_pos)) =
      W.centralSphere :=
    (nk.bicollar_slice (axialZero (inv_pos.mpr nk.eps_pos))).trans hsphere
  obtain ⟨hlower, hupper, hlowerOpen, hupperOpen, hdisjoint, hunion,
    hcompact, hnoncompact, _⟩ := sides.slice_spec 0 hzero
  change sides.lower 0 ∪ sides.upper 0 = W.centralSphereᶜ at hunion
  have heq :=
    (nk.bicollarSides ψ (axialZero (inv_pos.mpr nk.eps_pos))).side_sets_unique_of_core_properties
      (sides.lower 0) (sides.upper 0) hlowerOpen hupperOpen hlower hupper hdisjoint
      (hunion.trans (congrArg compl hslice.symm)) hcompact hnoncompact
  exact ⟨heq.1.symm, heq.2.symm⟩

end StrongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology NNReal

open private side_data_of_oriented
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature (RealTimeInterval)
open Surgery.Topology (ThreeSpace)
open DifferentialGeometry.Topology.SphereSeparation (axialZero IsAxiallyOriented)
open KappaSolutions (SpatialNeckWitness SpatialNeckSideData spatialNeckControlEpsilon
  spatialNeckControlEpsilon_pos spatialNeckScale spatialNeckScale_pos spatialNeckBuffer
  spatialNeckCentralPoint cylinderAxialScale cylinderAxialScale_central spatialNeckReflection_val)
open Geometry.Topology (busemann)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_localCapOfCompactSide_outer_radius :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [CompleteSpace M] (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
        (eps time : ℝ) (v : M) (nk : StrongNeck S eps v time)
        (psi : Diffeomorph I3 I3 M ThreeSpace ∞)
        (ho : IsAxiallyOriented nk.bicollar (nk.bicollarSides psi))
        (core : CapCore (closure
          (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide))
        (p : M) (hp : p ∈ (nk.bicollarSides psi
          (axialZero (inv_pos.mpr nk.eps_pos))).compactSide),
        eps ≤ eta →
        (∀ x y : M, dist x y = metricDistance (S.base.metric time) x y) →
        Geometry.HasNonnegativeSectionalCurvature (S.base.metric time) →
        ∀ c : ℝ≥0 → M, Isometry c → c 0 = p →
          IsCompact {x : M | busemann c x ≤ 0} ∧
          let cap := nk.localCapOfCompactSide psi ho core p hp
          ∀ x ∈ cap.core.carrier ∪ cap.tube,
            dist p x ≤ dist p v + C / Real.sqrt (S.scalar time v) +
              Metric.diam {x : M | busemann c x ≤ 0} := by
  obtain ⟨eta, heta, hconvert⟩ := exists_spatialNeckWitness_of_spatialNeck
    spatialNeckControlEpsilon_pos
  obtain ⟨Cd, hCd, hdiam⟩ := metricDistance_core_le_of_neckCoreDiameterBound.{u}
    neckCoreDiameterBound_holds
  refine ⟨eta, Cd + 11 * Real.pi * Real.sqrt 2, heta, by positivity, ?_⟩
  intro M _ _ _ _ J S eps time v nk psi ho core p hp heps hintrinsic hsec c hc hc0
  let _ : SigmaCompactSpace M := psi.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let _ : ConnectedSpace M := psi.toHomeomorph.connectedSpace_iff.mpr inferInstance
  let _ : NoncompactSpace M := psi.symm.toHomeomorph.isClosedEmbedding.noncompactSpace
  let _ : LocallyPathConnectedSpace M := psi.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let g := S.base.metric time
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hnorm : Geometry.Riemannian.IsMetricNorm (I := I3) g :=
    Geometry.Riemannian.isMetricNorm_of_riemannianBundle g
  let : IsRiemannianManifold I3 M := by
    refine ⟨fun y z => ?_⟩
    rw [edist_dist, hintrinsic]
    rw [metricDistance, riemannianEDistOf_eq_riemannianEDist g hnorm]
    exact ENNReal.ofReal_toReal (Geometry.Riemannian.Exponential.riemannianEDist_ne_top y z)
  have hcomplete : RiemannianMetricComplete g :=
    Geometry.Topology.riemannianMetricComplete_of_isMetricNorm g hnorm
  obtain ⟨W, hW⟩ := hconvert M g hcomplete v eps heps nk.toSpatialNeck
  have hsphere : nk.map '' (univ ×ˢ ({0} : Set ℝ)) = W.centralSphere := by
    rw [W.centralSphere_eq_range]
    ext x
    constructor
    · rintro ⟨⟨y, z⟩, ⟨_, hz⟩, rfl⟩
      have hz0 : z = 0 := hz
      subst z
      refine ⟨y, ?_⟩
      change W.embedding (spatialNeckCentralPoint _ W.epsilon_pos y) = nk.map (y, 0)
      rw [hW]
      change nk.map (cylinderAxialScale (Real.sqrt 2) _ (y, 0)) = nk.map (y, 0)
      rw [cylinderAxialScale_central]
    · rintro ⟨y, rfl⟩
      refine ⟨(y, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      change nk.map (y, 0) = W.embedding (spatialNeckCentralPoint _ W.epsilon_pos y)
      rw [hW]
      change nk.map (y, 0) = nk.map (cylinderAxialScale (Real.sqrt 2) _ (y, 0))
      rw [cylinderAxialScale_central]
  obtain ⟨B, U, hB, hU, hBop, _hUop, _hBU, hcover, hBc, _hUnc,
    _hcl, hint, hfr, _hUfr, horient⟩ := W.compact_end_sides_of_homeomorph psi.toHomeomorph
  obtain ⟨q, hq⟩ := hU.nonempty
  let rho : C(M, M) := ContinuousMap.const M q
  have hrho : ContinuousMap.Homotopic rho (ContinuousMap.id M) := by
    refine ⟨{
      toFun := fun z => psi.symm ((1 - (z.1 : ℝ)) • psi q + (z.1 : ℝ) • psi z.2)
      continuous_toFun := psi.symm.continuous.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          continuous_const).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (psi.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      simp [rho]
    · intro x
      simp
  have hrange : Disjoint (range rho) W.centralSphere := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ hx
    have hqc : q ∈ B ∪ U := Or.inr hq
    rw [hcover] at hqc
    exact hqc hx
  have hfront : frontier B = W.centralSphere := by
    have heq : frontier B = frontier (closure B) := by
      rw [frontier, frontier, closure_closure, hBop.interior_eq, hint]
    exact heq.trans hfr
  have horiented : ∃ W' : SpatialNeckWitness g nk.toSpatialNeck.center v spatialNeckControlEpsilon,
      W'.centralSphere = W.centralSphere ∧ Nonempty (SpatialNeckSideData W') := by
    rcases horient with ⟨hn, _hp⟩ | ⟨_hn, hpOrient⟩
    · exact ⟨W, rfl, side_data_of_oriented W rho hrho hrange B hB hBop hBc hfront hn⟩
    · refine ⟨W.reflect, W.reflect_centralSphere, ?_⟩
      apply side_data_of_oriented W.reflect rho hrho
        (by rwa [W.reflect_centralSphere]) B hB hBop hBc
        (hfront.trans W.reflect_centralSphere.symm)
      intro z hz
      rw [W.reflect_embedding]
      apply hpOrient
      rw [spatialNeckReflection_val]
      exact neg_pos.mpr hz
  obtain ⟨W', hsphere', ⟨D⟩⟩ := horiented
  have hsides := (nk.bicollar_zero_sides_eq_of_centralSphere_eq psi D
    (hsphere.trans hsphere'.symm)).1
  have hsublevel := D.busemann_sublevel_isCompact hnorm le_rfl hsec hc
  have hzero : IsCompact {x : M | busemann c x ≤ 0} := hsublevel 0
  refine ⟨hzero, ?_⟩
  dsimp only
  intro x hx
  have hscale : 0 < Real.sqrt (S.scalar time v) := Real.sqrt_pos.mpr nk.Q_pos
  have hconstant : 0 ≤ (Cd + 11 * Real.pi * Real.sqrt 2) / Real.sqrt (S.scalar time v) :=
    div_nonneg (by positivity) hscale.le
  have hsum : 11 * Real.pi * spatialNeckScale g v ≤
      (Cd + 11 * Real.pi * Real.sqrt 2) / Real.sqrt (S.scalar time v) := by
    change 11 * Real.pi * (Real.sqrt 2 / Real.sqrt (S.scalar time v)) ≤ _
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hscale.le
  have hbv : busemann c v ≤ dist p v := by
    have hb := Geometry.Topology.abs_busemann_le hc v
    rw [hc0, dist_comm] at hb
    exact (le_abs_self _).trans hb
  have hpzero : p ∈ {x : M | busemann c x ≤ 0} := by
    rw [← hc0]
    exact (Geometry.Topology.busemann_ray hc 0).le
  rcases hx with hx | hx
  · by_cases hxzero : busemann c x ≤ 0
    · have hd := Metric.dist_le_diam_of_mem hzero.isBounded hpzero hxzero
      linarith [dist_nonneg (x := p) (y := v)]
    by_cases hxlow : busemann c x < busemann c v
    · have hxpos : 0 ≤ busemann c x := (lt_of_not_ge hxzero).le
      let a : ℝ≥0 := ⟨busemann c x, hxpos⟩
      obtain ⟨hCa, _hCv, hlevel⟩ :=
        Geometry.Topology.busemann_level_diameter_le_of_compact_sublevel
          g hnorm hsec hc hxlow ⟨x, rfl⟩ (hsublevel (busemann c v))
      have hd := Metric.dist_le_diam_of_mem hCa.isBounded
        (by rfl : x ∈ {z : M | busemann c z = busemann c x})
        (show c a ∈ {z : M | busemann c z = busemann c x} from
          Geometry.Topology.busemann_ray hc a)
      have hdiameter := (D.busemann_level_diam_bounds hnorm le_rfl hsec hc).2
      have hpdist : dist p (c a) = busemann c x := by
        rw [← hc0, hc.dist_eq]
        change |(0 : ℝ) - busemann c x| = busemann c x
        rw [zero_sub, abs_neg, abs_of_nonneg hxpos]
      have htri := dist_triangle p (c a) x
      rw [hpdist, dist_comm (c a) x] at htri
      linarith [Metric.diam_nonneg (s := {z : M | busemann c z ≤ 0})]
    · have hgap := KappaSolutions.spatialNeckControlEpsilon_inverse_gap
        W'.epsilon_pos (le_refl spatialNeckControlEpsilon)
      have h0 : |(0 : ℝ)| < spatialNeckControlEpsilon⁻¹ + 1 := by
        rw [abs_zero]
        linarith [inv_pos.mpr spatialNeckControlEpsilon_pos]
      have hn : |-(5 * Real.pi)| < spatialNeckControlEpsilon⁻¹ + 1 := by
        rw [abs_neg, abs_of_pos (by positivity : 0 < 5 * Real.pi)]
        linarith [Real.pi_pos]
      have hxl : x ∈ closure (D.lower 0) := by
        change x ∈ closure (nk.bicollarSides psi (axialZero (inv_pos.mpr nk.eps_pos))).compactSide at hx
        rwa [hsides] at hx
      have hxnot : x ∉ D.upper 0 := by
        rwa [D.closure_lower_eq_compl_upper 0 h0] at hxl
      have hxband : x ∈ W'.embedding ''
          {z : spatialNeckBuffer spatialNeckControlEpsilon | -(5 * Real.pi) ≤ z.val.2 ∧ z.val.2 ≤ 0} := by
        by_contra hnot
        have hm : x ∈ (W'.embedding ''
            {z : spatialNeckBuffer spatialNeckControlEpsilon | -(5 * Real.pi) ≤ z.val.2 ∧ z.val.2 ≤ 0})ᶜ := hnot
        rw [(D.ordered_band (-(5 * Real.pi)) 0 hn h0 (neg_neg_of_pos (by positivity))).2.2] at hm
        rcases hm with hm | hm
        · exact hxlow (D.busemann_inward_lt hnorm le_rfl hc hm)
        · exact hxnot hm
      obtain ⟨z, hz, rfl⟩ := hxband
      have hedist := W'.band_edist_lt le_rfl
        (spatialNeckCentralPoint _ W'.epsilon_pos nk.toSpatialNeck.center) z
        (by change |(0 : ℝ)| ≤ 5 * Real.pi; rw [abs_zero]; positivity)
        (abs_le.mpr ⟨hz.1, hz.2.trans (by positivity)⟩)
      rw [W'.marked, riemannianEDistOf_eq_riemannianEDist g hnorm,
        ← IsRiemannianManifold.out (I := I3)] at hedist
      have hd : dist v (W'.embedding z) ≤ 11 * Real.pi * spatialNeckScale g v := by
        have hs := spatialNeckScale_pos g v nk.Q_pos
        exact (edist_le_ofReal (by positivity)).mp hedist.le
      have htri := dist_triangle p v (W'.embedding z)
      linarith [Metric.diam_nonneg (s := {z : M | busemann c z ≤ 0})]
  · have hcore : x ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) := by
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩
    have hv : v ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) :=
      ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
    have hd := hdiam M J S eps v time nk v hv x hcore
    rw [← hintrinsic] at hd
    have hCdle : Cd / Real.sqrt (S.scalar time v) ≤
        (Cd + 11 * Real.pi * Real.sqrt 2) / Real.sqrt (S.scalar time v) :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hscale.le
    have htri := dist_triangle p v x
    linarith [Metric.diam_nonneg (s := {z : M | busemann c z ≤ 0})]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
