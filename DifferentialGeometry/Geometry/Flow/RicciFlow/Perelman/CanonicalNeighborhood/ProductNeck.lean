import DifferentialGeometry.Geometry.Neck.ProductCapExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapTruncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckScalarTime

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ} {x y : M}
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem CanonicalWitness.exists_localNeck_of_product_chart
    (W : CanonicalWitness S epsc C1 C2 x t)
    (hchart : W.capTubeHasNeckChart eps) (heps : eps ≤ 1 / 1000)
    (hy : y ∈ connectedComponent x) (hscalar : C2 * S.scalar t y < S.scalar t x)
    (hprod : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : W.domain.carrier ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4) (hsmall : 720 * eta < (C2⁻¹ * S.scalar t x) / 16)
    (hclose : ∀ z : V, ∀ a : ℕ, a ≤ 2 →
      metricDerivNorm a (Diffeomorph.pullbackMetricCross ((S.base.metric t).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    ∃ neck : LocalNeck S epsc x t W.domain.carrier,
      W.alternative = CanonicalAlternative.neck neck := by
  rcases W.alternative_eq_neck_or_cap_of_mul_scalar_lt hy hscalar with hneck |
    ⟨cap,hdepth,htag⟩
  · exact hneck
  obtain ⟨v,nk,hmap⟩ := hchart cap hdepth htag
  obtain ⟨K,hK,hx,hKU,hfront⟩ := cap.exists_truncated_compactDomain
    (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1)
  have hfront' : frontier K.carrier = range (fun q : Sphere 2 => nk.toSpatialNeck.map (q,1/2)) := by
    rw [hfront]
    congr 1
    funext q
    exact hmap _
  have hv : v ∈ W.domain.carrier := by
    have hmem : cap.tubeMap (nk.center,0) ∈ cap.tube := by
      rw [← cap.tube_eq]
      exact ⟨(nk.center,0),⟨mem_univ _,by norm_num⟩,rfl⟩
    rw [hmap,nk.center_eq] at hmem
    exact cap.union_eq.ge (Or.inr hmem)
  have hnksmall : 720 * eta < metricScalarAt (S.base.metric t) v / 16 :=
    hsmall.trans_le (div_le_div_of_nonneg_right (W.scalar_bounds v hv).1 (by norm_num))
  have hinterval : (1/2 : ℝ) ∈ Ioo (-eps⁻¹) eps⁻¹ := by
    have hinv : (1000 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ nk.eps_pos).mpr
      linarith
    constructor <;> linarith
  have hempty := nk.toSpatialNeck.interior_eq_empty_of_frontier_in_product_chart heps hinterval
    hprod hdim O V Φ K.compact (hKU.trans hcapture) hfront' heta hnksmall
      (fun z _ a ha => hclose z a ha)
  exact False.elim (by simp only [hempty,mem_empty_iff_false] at hx)

theorem CanonicalWitness.scalar_derivWithin_pos_of_product_chart
    (hS : IsSolutionOn S) (W : CanonicalWitness S epsc C1 C2 x t)
    (hchart : W.capTubeHasNeckChart eps) (heps : eps ≤ 1 / 1000)
    (hy : y ∈ connectedComponent x) (hscalar : C2 * S.scalar t y < S.scalar t x)
    (hprod : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : W.domain.carrier ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4) (hsmall : 720 * eta < (C2⁻¹ * S.scalar t x) / 16)
    (hclose : ∀ z : V, ∀ a : ℕ, a ≤ 2 →
      metricDerivNorm a (Diffeomorph.pullbackMetricCross ((S.base.metric t).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta)
    (hregular : ∀ v ∈ Ioo (-1 : ℝ) 0, parabolicTime t (S.scalar t x) v ∈ D.regular) :
    0 < derivWithin (fun v => S.scalar v x) (Iic t) t := by
  obtain ⟨neck,_⟩ := W.exists_localNeck_of_product_chart hchart heps hy hscalar
    hprod hdim O V Φ hcapture heta hsmall hclose
  exact neck.strong.scalar_derivWithin_pos hS hregular

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
  {eps epsc C1 C2 t : ℝ} {x y : P.Carrier}
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]

theorem scalar_derivWithin_pos_of_canonical_product_chart
    (W : CanonicalWitness G.flow epsc C1 C2 x t)
    (hchart : W.capTubeHasNeckChart eps) (heps : eps ≤ 1 / 1000)
    (hy : y ∈ connectedComponent x) (hscalar : C2 * G.flow.scalar t y < G.flow.scalar t x)
    (hprod : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens P.Carrier)
    (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), ThreeModel⟯ V)
    (hcapture : W.domain.carrier ⊆ V)
    {eta : ℝ} (heta : eta ≤ 1 / 4) (hsmall : 720 * eta < (C2⁻¹ * G.flow.scalar t x) / 16)
    (hclose : ∀ z : V, ∀ b : ℕ, b ≤ 2 →
      metricDerivNorm b (Diffeomorph.pullbackMetricCross ((G.flow.base.metric t).restrictOpen V) Φ)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    0 < derivWithin (fun v => G.flow.scalar v x) (Iic t) t := by
  obtain ⟨neck,_⟩ := W.exists_localNeck_of_product_chart hchart heps hy hscalar
    hprod hdim O V Φ hcapture heta hsmall hclose
  have htime := neck.strong.time_domain ⟨le_rfl,sub_le_self _ (inv_nonneg.mpr neck.strong.Q_pos.le)⟩
  have ht := W.time_mem
  apply neck.strong.scalar_derivWithin_pos G.equation
  intro v hv
  change a < parabolicTime t (G.flow.scalar t x) v ∧ parabolicTime t (G.flow.scalar t x) v < s
  change a ≤ t - (G.flow.scalar t x)⁻¹ ∧ t - (G.flow.scalar t x)⁻¹ < s at htime
  change a ≤ t ∧ t < s at ht
  have hlow := (div_lt_div_of_pos_right hv.1 neck.strong.Q_pos)
  have hhigh := div_neg_of_neg_of_pos hv.2 neck.strong.Q_pos
  simp only [neg_div,one_div] at hlow
  unfold parabolicTime
  constructor <;> linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
