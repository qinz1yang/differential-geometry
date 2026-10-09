import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundComponentVolume
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Covering
import DifferentialGeometry.Topology.Covering.FiniteFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
universe u
variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
  [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]

theorem round_cover_with_fundamental_degree (h : SmoothRiemannianMetric I3 Z) (z₀ : Z)
    (hcc : ∀ z (v w : TangentSpace I3 z),
      metricRm04At h z (fun i : Fin 4 => ![v,w,w,v] i) =
        (1/6 : ℝ) * (h.inner z v v * h.inner z w w - (h.inner z v w)^2)) :
    Finite (FundamentalGroup Z z₀) ∧
    0 < Nat.card (FundamentalGroup Z z₀) ∧
    ∃ (p : RoundSphereThree → Z) (hp : IsLocalDiffeomorph I3 I3 ∞ p),
      Function.Surjective p ∧ IsCoveringMap p ∧
      localPullMetric h p hp = roundSphereThreeMetric ∧
      ∀ z : Z, {x : RoundSphereThree | p x = z}.encard =
        (Nat.card (FundamentalGroup Z z₀) : ℕ∞) := by
  have hsec : ∀ z (v w : TangentSpace I3 z),
      metricRm04StandardAt (I := I3) (M := Z) h z v w w v =
        (1/6 : ℝ) * (h.inner z v v * h.inner z w w - h.inner z v w * h.inner z v w) := by
    intro z v w
    have hv : vec4 v w w v = (fun i : Fin 4 => ![v,w,w,v] i) := by
      funext i
      fin_cases i <;> simp [vec4]
    rw [metricRm04StandardAt_apply,hv,hcc,sq]
  obtain ⟨p,hp,hs,hcover,hmetric⟩ :=
    exists_round_sphere_cover_of_constant_positive_sectional_curvature
      (I := I3) (M := Z) (n := 3) (by norm_num) inferInstance inferInstance
      inferInstance (by simp [ThreeSpace]) h (1/6) (by norm_num) hsec
  have hsc : SimplyConnectedSpace RoundSphereThree :=
    inferInstanceAs (SimplyConnectedSpace DifferentialGeometry.Topology.SphereThree)
  let : SimplyConnectedSpace RoundSphereThree := hsc
  let : Finite (FundamentalGroup Z z₀) :=
    DifferentialGeometry.Topology.finite_fundamentalGroup_of_compact_simplyConnected_cover
      p hcover hs z₀
  let : LocallyPathConnectedSpace Z := ChartedSpace.locallyPathConnectedSpace ThreeSpace Z
  let : PathConnectedSpace Z := PathConnectedSpace.of_locallyPathConnectedSpace
  refine ⟨inferInstance,Nat.card_pos, p,hp,hs,hcover,?_,?_⟩
  · apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner]
    have hm := hmetric z v w
    simp only [scaleMetric_inner] at hm
    change _ = 6 * (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner z v w
    linarith
  · intro z
    let : Finite (p ⁻¹' {z}) :=
      Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact hcover z
    obtain ⟨x,hx⟩ := hs z
    have hcard : (p ⁻¹' {z}).ncard = Nat.card (FundamentalGroup Z z) :=
      Nat.card_congr (Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
        hcover z (⟨x,hx⟩ : p ⁻¹' {z}))
    have he := Nat.card_congr
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected z z₀).toEquiv
    have hfin : (p ⁻¹' {z}).Finite := Set.toFinite _
    have hf := hfin.cast_ncard_eq.symm
    rw [hcard, he] at hf
    exact hf

theorem round_volume_lower_div_fundamental_degree
    (h : SmoothRiemannianMetric I3 Z) (z₀ : Z)
    (hcc : ∀ z (v w : TangentSpace I3 z),
      metricRm04At h z (fun i : Fin 4 => ![v,w,w,v] i) =
        (1/6 : ℝ) * (h.inner z v v * h.inner z w w - (h.inner z v w)^2)) :
    Finite (FundamentalGroup Z z₀) ∧ 0 < Nat.card (FundamentalGroup Z z₀) ∧
    ENNReal.ofReal ((8 * Real.sqrt 6 * Real.pi) /
      (Nat.card (FundamentalGroup Z z₀) : ℝ)) ≤
      riemannianVolumeMeasure I3 Z h univ := by
  obtain ⟨hfinite,hpos,p,hp,_hs,_hcover,hpull,hcard⟩ :=
    round_cover_with_fundamental_degree h z₀ hcc
  refine ⟨hfinite,hpos,?_⟩
  let k := Nat.card (FundamentalGroup Z z₀)
  have hk : (0 : ℝ) < k := by exact_mod_cast hpos
  let : MeasurableSpace RoundSphereThree := borel RoundSphereThree
  let : BorelSpace RoundSphereThree := ⟨rfl⟩
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  have hm := riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    roundSphereThreeMetric h hp hpull k hcard
  have htotal := congrArg (fun μ : Measure Z => μ univ) hm
  rw [Measure.map_apply hp.contMDiff.continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.smul_apply, smul_eq_mul] at htotal
  have hbound :=
    ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_roundSphereThree_univ
  rw [htotal] at hbound
  rw [ENNReal.ofReal_div_of_pos hk]
  have hcast : ENNReal.ofReal (k : ℝ) = (k : ENNReal) := by simp
  rw [hcast]
  exact (ENNReal.div_le_iff' (by exact_mod_cast Nat.ne_of_gt hpos) (by simp)).mpr hbound

end GC.GeneralFlow
