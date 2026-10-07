import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingCurvature
import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingBallContainment
import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingPathLength
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology.Manifold GC.Endpoint Bundle Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem exists_collar_localization_of_distanceToBoundary_le
    {K : ℕ} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g (K + 4) δ) (hδ : δ ≤ 1 / 10000)
    (p : W.Carrier) (hp : distanceToBoundary W g p ≤ ENNReal.ofReal 10) :
    ∃ (i : Fin B.count) (y : Torus),
      (B.collar i).toFun (y, halfZero) ∈ W.model.boundary W.Carrier ∧
      (B.collar i).toFun (y, halfZero) ∈ B.component i ∧
      riemannianEDistOf g p ((B.collar i).toFun (y, halfZero)) < ENNReal.ofReal 11 ∧
      curvatureRadius g p ≤ ENNReal.ofReal 13 ∧
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius g p →
        r < 13 ∧ riemannianClosedBallOf g p r ⊆
          (B.collar i).toFun '' {x : CuspHalfSpace | x.2.val 0 < 25} := by
  classical
  have hnear : distanceToBoundary W g p < ENNReal.ofReal 11 :=
    hp.trans_lt (by norm_num)
  obtain ⟨b, hb⟩ := iInf_lt_iff.mp hnear
  have hbcover : b.val ∈ ⋃ i, B.component i := by
    rw [B.covers]
    exact b.property
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hbcover
  have hrange : b.val ∈ Set.range (fun y : Torus => (B.collar i).toFun (y, halfZero)) := by
    rwa [(B.collar i).boundary_image]
  obtain ⟨y, hy⟩ := hrange
  let e := B.collar i
  let z : CuspHalfSpace := (y, halfSpaceOneLift 1)
  have hzheight : z.2.val 0 = 1 := by
    change max (1 : ℝ) 0 = 1
    norm_num
  have hz : z ∈ cuspDomain := by
    change z.2.val 0 < cuspDepth
    rw [hzheight]
    norm_num [cuspDepth]
  have hzpos : 0 < z.2.val 0 := by rw [hzheight]; norm_num
  have hzero : halfSpaceOneLift 0 = halfZero := by
    apply Subtype.ext
    apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).injective
    change max (0 : ℝ) 0 = 0
    norm_num
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans (e.metric_error 0 (by omega) z hz)
  have hvertical : riemannianEDistOf g (e.toFun (y, halfZero)) (e.toFun z) <
      ENNReal.ofReal 2 := by
    have hd := (e.vertical_path_length_and_distance_le y
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num [cuspDepth] : (1 : ℝ) < cuspDepth)).2
    have hsqrt : Real.sqrt (1 + δ) < 2 := by
      have hs := Real.sqrt_lt_sqrt (by linarith : 0 ≤ 1 + δ)
        (by linarith : 1 + δ < 4)
      norm_num at hs
      exact hs
    have hd' : riemannianEDistOf g (e.toFun (y, halfZero)) (e.toFun z) ≤
        ENNReal.ofReal (Real.sqrt (1 + δ)) := by
      simpa only [hzero, sub_zero, mul_one] using hd
    exact hd'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hsqrt)
  have hbase : riemannianEDistOf g p (e.toFun (y, halfZero)) <
      ENNReal.ofReal 11 := by
    simpa only [e, hy] using hb
  have hdist : riemannianEDistOf g p (e.toFun z) < ENNReal.ofReal 13 := by
    calc
      _ ≤ riemannianEDistOf g p (e.toFun (y, halfZero)) +
          riemannianEDistOf g (e.toFun (y, halfZero)) (e.toFun z) :=
        riemannianEDistOf_triangle g _ _ _
      _ < ENNReal.ofReal 11 + ENNReal.ofReal 2 := ENNReal.add_lt_add hbase hvertical
      _ = ENNReal.ofReal 13 := by norm_num
  have hsec : ¬ SectionalBoundedBelowAt g (e.toFun z) (-((13 : ℝ) ^ 2)⁻¹) := by
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
      (by omega) hδ z hz hzpos u v hu hv huv
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
  have hR : curvatureRadius g p ≤ ENNReal.ofReal 13 :=
    curvatureRadius_le_of_not_sectionalBoundedBelowAt g (by norm_num) hdist.le hsec
  have hδ1 : δ < 1 := by linarith
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  have hinv : (1 - δ)⁻¹ ≤ (100 : ℝ) / 99 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hmargin : (24 : ℝ) ≤ 25 / Real.sqrt ((1 - δ)⁻¹) := by
    have hspos : 0 < Real.sqrt ((1 - δ)⁻¹) := Real.sqrt_pos.mpr (inv_pos.mpr hden)
    have hsbound : Real.sqrt ((1 - δ)⁻¹) ≤ (25 : ℝ) / 24 := by
      apply (Real.sqrt_le_left (by norm_num)).mpr
      exact hinv.trans (by norm_num)
    apply (le_div_iff₀ hspos).mpr
    nlinarith
  have hcapture : riemannianBallOf g (e.toFun (y, halfZero)) 24 ⊆
      e.toFun '' {x : CuspHalfSpace | x.2.val 0 < 25} := by
    exact e.riemannianBallOf_subset_image_height_lt_of_lt_one hδ1
      (p := (y, halfZero)) (H := 25) (r := 24)
      (by change (0 : ℝ) < 25; norm_num) (by norm_num [cuspDepth])
      (by change (24 : ℝ) ≤ (25 - 0) / Real.sqrt ((1 - δ)⁻¹)
          simpa only [sub_zero] using hmargin)
  refine ⟨i, y, ?_, ?_, hbase, hR, ?_⟩
  · simpa only [hy] using b.property
  · exact ((B.collar i).boundary_image ▸ Set.mem_range_self y :)
  · intro r hr hrho
    have hr13 : r < 13 :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le).mp (hrho.trans_le hR)
    refine ⟨hr13, ?_⟩
    intro q hq
    apply hcapture
    change riemannianEDistOf g (e.toFun (y, halfZero)) q < ENNReal.ofReal 24
    have hbcomm : riemannianEDistOf g (e.toFun (y, halfZero)) p <
        ENNReal.ofReal 11 := by
      rw [riemannianEDistOf_comm]
      exact hbase
    have hq13 : riemannianEDistOf g p q < ENNReal.ofReal 13 :=
      hq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hr13)
    calc
      _ ≤ riemannianEDistOf g (e.toFun (y, halfZero)) p + riemannianEDistOf g p q :=
        riemannianEDistOf_triangle g _ _ _
      _ < ENNReal.ofReal 11 + ENNReal.ofReal 13 := ENNReal.add_lt_add hbcomm hq13
      _ = ENNReal.ofReal 24 := by norm_num

end DifferentialGeometry.Geometry.Collapse
