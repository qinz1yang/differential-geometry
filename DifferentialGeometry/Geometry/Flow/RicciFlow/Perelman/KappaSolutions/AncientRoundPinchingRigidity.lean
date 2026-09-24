import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardSpaceForm


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

private instance pinchingRigidity_sphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance pinchingRigidityTopology : TopologicalSpace F.M := F.topology
local instance pinchingRigidityCharted : ChartedSpace H F.M := F.charted
local instance pinchingRigiditySmooth : IsManifold I ∞ F.M := F.smooth
local instance pinchingRigidityC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance pinchingRigidityT2 : T2Space F.M := F.t2
local instance pinchingRigiditySigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem ancient_sphericalSpaceFormFlow_of_backward_pinching
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (hcompact : CompactSpace F.M) {a c : ℕ → ℝ}
    (ha : Tendsto a atTop atBot) (hc : Tendsto c atTop (𝓝 (1 / 3)))
    (hcUpper : ∀ i, c i < 1 / 3)
    (hpositive : ∀ i, ∀ x : F.M, 0 < F.S.scalar (a i) x)
    (hpinch : ∀ i, ∀ x : F.M, ∀ v : TangentSpace I x,
      c i * F.S.scalar (a i) x * (F.S.family.metric (a i)).inner x v v ≤
        F.S.ricciAt (a i) x (vec2 v v)) : IsShrinkingSphericalSpaceFormFlow F := by
  let _ : CompactSpace F.M := hcompact
  let _ : ConnectedSpace F.M := hconn
  have hconstant := ancient_scalar_constant_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hpinch
  have hEin := ancient_ricci_einstein_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hpinch
  have hpos (b : ℝ) (hb : b ≤ 0) (x : F.M) : 0 < F.S.scalar b x := by
    obtain ⟨i, hi⟩ := (ha.eventually (eventually_le_atBot b)).exists
    exact (hpositive i x).trans_le (ancient_scalar_monotone_of_spatially_constant F
      hconstant x (hi.trans hb) hb hi)
  obtain ⟨hT, hprofile, hmetric⟩ := ancient_einstein3_roundScaling F.S F.isSolution hdim
    hpos hconstant hEin F.basepoint
  let T := 3 / (2 * F.S.scalar 0 F.basepoint)
  let k := 1 / (4 * T)
  have hk : 0 < k := one_div_pos.mpr (mul_pos (by norm_num) hT)
  have hsec : ∀ x : F.M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (F.S.family.metric 0) x X Y Y X = k *
        ((F.S.family.metric 0).inner x X X * (F.S.family.metric 0).inner x Y Y -
          (F.S.family.metric 0).inner x X Y * (F.S.family.metric 0).inner x X Y) := by
    intro x X Y
    let g := F.S.family.metric 0
    obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
      ricciEigen3 g (F.S.ricciAt 0 x) hdim (ricci_is_symmetric F.S 0 x)
    have htrace := riemann_from_ricci_trace F.S (t := 0) (x := x) (basis := basis) horth
    have hneg (i j : Fin 3) : ricciCompAt basis (-(F.S.ricciAt 0 x)) i j =
        ((-F.S.scalar 0 x) / 3) * delta3 i j := by
      rw [ricciCompAt_apply]
      change -(F.S.ricciAt 0 x (vec2 (basis i) (basis j))) = _
      rw [hEin 0 le_rfl x (basis i) (basis j)]
      change -((F.S.scalar 0 x / 3) * g.inner x (basis i) (basis j)) = _
      rw [horth i j]
      ring
    have hRm := rm04_einstein3_at htrace hneg X Y
    rw [hprofile 0 le_rfl x] at hRm
    dsimp only [k, T]
    refine hRm.trans ?_
    simp only [SolutionOn.family, sub_zero, div_mul_eq_div_div]
    ring
  obtain ⟨D, e, hQ⟩ := exists_roundSphereQuotient_metric hcompact hconn
    (inferInstance : I.Boundaryless) hdim (F.S.family.metric 0) k hk hsec
  refine ⟨T, hT, D, e, fun t ht => ?_⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [hmetric t ht, scaleMetric_inner, scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner]
  rw [hQ x v w]
  change ((T - t) / T) * (F.S.family.metric 0).inner x v w =
    (4 * (T - t)) * (k * (F.S.family.metric 0).inner x v w)
  dsimp only [k]
  simp only [div_mul_eq_div_div]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
