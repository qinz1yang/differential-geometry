import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringT1_S16
import DifferentialGeometry.Geometry.Collapse.CuspidalCutBallLocalization

/-!
# CH12-S16: G2, the collar negative plane near an interior point at distance `D - 1`

`collarNegativePlane_S16 K : CollarNegativePlane K` (S2's explicit input), proved from the picked
`CuspEmbedding` files: a near-minimizing curve from `p` to the boundary, the intermediate value
theorem for the distance to the endpoint, path-length additivity, ball containment of the collar
and the `-1/8` curvature estimate at positive height.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology.Manifold GC.Endpoint Bundle Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A collar point of positive height carries a plane of sectional curvature below `-1/81`. -/
theorem not_sectionalBoundedBelowAt_collar_S16 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hK : 2 ≤ K) (hδ : δ ≤ 1 / 10000)
    (z : CuspHalfSpace) (hz : z ∈ cuspDomain) (hzpos : 0 < z.2.val 0) :
    ¬ SectionalBoundedBelowAt g (e.toFun z) (-(1 / 81 : ℝ)) := by
  have hdim : Module.finrank ℝ (TangentSpace halfCollarModel z) = 3 := by
    change Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) = 3
    norm_num [Module.finrank_prod, finrank_euclideanSpace_fin]
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis e.cusp.metric z
  let i₀ : Fin (Module.finrank ℝ (TangentSpace halfCollarModel z)) :=
    ⟨0, by rw [hdim]; norm_num⟩
  let i₁ : Fin (Module.finrank ℝ (TangentSpace halfCollarModel z)) :=
    ⟨1, by rw [hdim]; norm_num⟩
  let u := basis i₀
  let v := basis i₁
  have hu : e.cusp.metric.inner z u u = 1 := (hON i₀ i₀).trans (if_pos rfl)
  have hv : e.cusp.metric.inner z v v = 1 := (hON i₁ i₁).trans (if_pos rfl)
  have huv : e.cusp.metric.inner z u v = 0 := by
    have hne : i₀ ≠ i₁ := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [i₀, i₁] at hv
    exact (hON i₀ i₁).trans (if_neg hne)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simpa using hu
  have hvsmul (c : ℝ) : v ≠ c • u := by
    intro h
    have hc : c = 0 := by
      simpa only [h, map_smul, smul_eq_mul, hu, mul_one] using huv
    rw [hc, zero_smul] at h
    rw [h] at hv
    simpa using hv
  let a := mfderiv halfCollarModel W.model e.toFun z u
  let b' := mfderiv halfCollarModel W.model e.toFun z v
  have ha0 : a ≠ 0 := by
    intro h
    apply hu0
    apply e.immersion z hz
    simpa only [map_zero] using h
  have hbsmul (c : ℝ) : b' ≠ c • a := by
    intro h
    apply hvsmul c
    apply e.immersion z hz
    simpa only [map_smul] using h
  have haa : 0 < g.inner (e.toFun z) a a := g.pos _ _ ha0
  let c := g.inner (e.toFun z) a b' / g.inner (e.toFun z) a a
  have hw : b' - c • a ≠ 0 := by
    intro h
    exact hbsmul c (sub_eq_zero.mp h)
  have hgram_eq : g.inner (e.toFun z) a a *
      g.inner (e.toFun z) (b' - c • a) (b' - c • a) =
      g.inner (e.toFun z) a a * g.inner (e.toFun z) b' b' -
        g.inner (e.toFun z) a b' ^ 2 := by
    dsimp only [c]
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm (e.toFun z) b' a]
    field_simp [ne_of_gt haa]
    ring
  have hgram : 0 < g.inner (e.toFun z) a a * g.inner (e.toFun z) b' b' -
      g.inner (e.toFun z) a b' ^ 2 := by
    rw [← hgram_eq]
    exact mul_pos haa (g.pos _ _ hw)
  have hcurv := e.metricRm04_lt_neg_one_eighth_of_positive_height
    hK hδ z hz hzpos u v hu hv huv
  change metricRm04StandardAt g (e.toFun z) a b' b' a <
    -(1 / 8 : ℝ) * (g.inner (e.toFun z) a a * g.inner (e.toFun z) b' b' -
      g.inner (e.toFun z) a b' ^ 2) at hcurv
  intro h
  have hplane := h a b'
  norm_num at hplane
  have hcurv' : metricRm04At g (e.toFun z) (vec4 a b' b' a) <
      -(1 / 8 : ℝ) * (g.inner (e.toFun z) a a * g.inner (e.toFun z) b' b' -
        g.inner (e.toFun z) a b' ^ 2) := hcurv
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metricPathELength_add_S16 {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (γ : ℝ → W.Carrier) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    metricPathELength g γ a b + metricPathELength g γ b c = metricPathELength g γ a c := by
  let _ : RiemannianBundle (TangentSpace W.model : W.Carrier → Type _) := ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength W.model γ a b + Manifold.pathELength W.model γ b c = _
  exact Manifold.pathELength_add (I := W.model) (γ := γ) hab hbc

/-- On a near-minimizing curve from `p` to `b` there is a point `q` at distance exactly `1`
from `b` which has `d(p,q) + 1 < r`. -/
theorem exists_point_dist_one_S16 {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (p b : W.Carrier) {r : ℝ}
    (h1 : ENNReal.ofReal 1 ≤ riemannianEDistOf g b p)
    (hr : riemannianEDistOf g p b < ENNReal.ofReal r) :
    ∃ q, riemannianEDistOf g b q = ENNReal.ofReal 1 ∧
      riemannianEDistOf g p q + ENNReal.ofReal 1 < ENNReal.ofReal r := by
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_edistOf_lt g hr
  have hc : Continuous fun q : W.Carrier => riemannianEDistOf g b q :=
    continuous_riemannianEDist g b
  have hcont : ContinuousOn (fun t => riemannianEDistOf g b (γ t)) (Icc (0 : ℝ) 1) :=
    hc.comp_continuousOn hγ.continuousOn
  have hmem : ENNReal.ofReal 1 ∈
      Icc (riemannianEDistOf g b (γ 1)) (riemannianEDistOf g b (γ 0)) := by
    rw [hγ0, hγ1, riemannianEDistOf_self]
    exact ⟨bot_le, h1⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  refine ⟨γ t, hft, ?_⟩
  have hpre : riemannianEDistOf g p (γ t) ≤ metricPathELength g γ 0 t := by
    have := edistOf_le_metricPathELength g ht.1 (hγ.mono (Icc_subset_Icc le_rfl ht.2))
    rwa [hγ0] at this
  have hpost : ENNReal.ofReal 1 ≤ metricPathELength g γ t 1 := by
    have := edistOf_le_metricPathELength g ht.2 (hγ.mono (Icc_subset_Icc ht.1 le_rfl))
    rw [hγ1, riemannianEDistOf_comm] at this
    exact (le_of_eq_of_le hft.symm this)
  calc riemannianEDistOf g p (γ t) + ENNReal.ofReal 1
      ≤ metricPathELength g γ 0 t + metricPathELength g γ t 1 := add_le_add hpre hpost
    _ = metricPathELength g γ 0 1 := metricPathELength_add_S16 g γ ht.1 ht.2
    _ < _ := hlen

/-- G2, proved: S2's explicit input `CollarNegativePlane K`. -/
theorem collarNegativePlane_S16 (K : ℕ) : CollarNegativePlane.{u} K := by
  intro W g B p h10 hDtop η hη
  have hDne : distanceToBoundary W g p ≠ ⊤ := hDtop.ne
  have hD10 : 10 < (distanceToBoundary W g p).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) hDne).mp h10
  set D := (distanceToBoundary W g p).toReal with hDdef
  have hDeq : distanceToBoundary W g p = ENNReal.ofReal D := (ENNReal.ofReal_toReal hDne).symm
  set η' : ℝ := min η (1 / 2) with hη'
  have hη'pos : 0 < η' := lt_min hη (by norm_num)
  have hη'le : η' ≤ η := min_le_left _ _
  have hη'half : η' ≤ 1 / 2 := min_le_right _ _
  have hlt : distanceToBoundary W g p < ENNReal.ofReal (D + η') := by
    rw [hDeq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨b, hb⟩ := iInf_lt_iff.mp hlt
  have hDle : distanceToBoundary W g p ≤ riemannianEDistOf g p b.val :=
    iInf_le (fun z : W.model.boundary W.Carrier => riemannianEDistOf g p z.val) b
  have h1 : ENNReal.ofReal 1 ≤ riemannianEDistOf g b.val p := by
    rw [riemannianEDistOf_comm]
    exact ((ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 10)).trans h10.le).trans hDle
  obtain ⟨q, hq1, hq2⟩ := exists_point_dist_one_S16 g p b.val h1 hb
  have hsplit : ENNReal.ofReal (D + η') =
      ENNReal.ofReal (D - 1 + η') + ENNReal.ofReal 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by norm_num)]
    congr 1
    ring
  rw [hsplit] at hq2
  have hpq : riemannianEDistOf g p q < ENNReal.ofReal (D - 1 + η') :=
    (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hq2
  have hpqD : riemannianEDistOf g p q < distanceToBoundary W g p := by
    rw [hDeq]
    exact hpq.trans ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  have hqint : q ∈ W.model.interior W.Carrier :=
    mem_interior_of_edist_lt_distanceToBoundary g p q hpqD
  refine ⟨q, hqint, ?_, ?_⟩
  · exact hpq.le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · -- locate `q` in the collar
    have hbcover : b.val ∈ ⋃ i, B.component i := by
      rw [B.covers]
      exact b.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hbcover
    let e := B.collar i
    have hrange : b.val ∈ Set.range (fun y : Torus => e.toFun (y, halfZero)) := by
      rw [e.boundary_image]
      exact hi
    obtain ⟨y, hy⟩ := hrange
    obtain ⟨hδ2, -, -, h32, -⟩ := collarNumerics_S16
      (δ := (1 / 10000 : ℝ)) (by norm_num) le_rfl
    have hδ1 : (1 / 10000 : ℝ) < 1 := by norm_num
    have hqball : q ∈ riemannianBallOf g (e.toFun (y, halfZero)) (3 / 2) := by
      change riemannianEDistOf g (e.toFun (y, halfZero)) q < ENNReal.ofReal (3 / 2)
      have hy' : e.toFun (y, halfZero) = b.val := hy
      rw [hy', hq1]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    have hcapture := e.riemannianBallOf_subset_image_height_lt_of_lt_one hδ1
      (p := (y, halfZero)) (H := 2) (r := 3 / 2)
      (by change (0 : ℝ) < 2; norm_num) (by norm_num [cuspDepth])
      (by change (3 / 2 : ℝ) ≤ (2 - 0) / Real.sqrt ((1 - (1 / 10000 : ℝ))⁻¹)
          simpa only [sub_zero] using h32)
    obtain ⟨z, hz, hzq⟩ := hcapture hqball
    have hz2 : z.2.val 0 < 2 := hz
    have hzdom : z ∈ cuspDomain := by
      change z.2.val 0 < cuspDepth
      exact hz2.trans_le (by norm_num [cuspDepth])
    have hz0 : 0 ≤ z.2.val 0 := z.2.property
    have hzpos : 0 < z.2.val 0 := by
      rcases hz0.eq_or_lt with h | h
      · exfalso
        have hbd : e.toFun z ∈ W.model.boundary W.Carrier :=
          (e.boundary_preimage hzdom).mpr h.symm
        rw [hzq] at hbd
        rw [← W.model.compl_boundary] at hqint
        exact hqint hbd
      · exact h
    have := not_sectionalBoundedBelowAt_collar_S16 e (by omega) le_rfl z hzdom hzpos
    rwa [hzq] at this

end GC.LongTime.Ch12
