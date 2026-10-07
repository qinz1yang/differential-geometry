import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingMetric
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Topology.Manifold.HalfLine
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold GC.Endpoint Bundle Manifold
open MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CuspEmbedding.height_edist_le_metricPathELength
    {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    {γ : ℝ → CuspHalfSpace} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) halfCollarModel 1 γ (Icc a b))
    (hmaps : MapsTo γ (Icc a b) cuspDomain) :
    edist ((γ a).2.val 0) ((γ b).2.val 0) ≤
      ENNReal.ofReal (Real.sqrt ((1 - δ)⁻¹)) *
        metricPathELength g (e.toFun ∘ γ) a b := by
  let z : CuspHalfSpace → ℝ := fun p => p.2.val 0
  have hz : ContMDiff halfCollarModel 𝓘(ℝ) ∞ z :=
    contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd
  have hdz (p : CuspHalfSpace) (v : TangentSpace halfCollarModel p) :
      mfderiv halfCollarModel 𝓘(ℝ) z p v = v.2 0 := by
    change mfderiv halfCollarModel 𝓘(ℝ)
      ((fun t : EuclideanHalfSpace 1 => t.1 0) ∘ Prod.snd) p v = _
    rw [mfderiv_comp_apply p
      (hasMFDerivAt_halfSpaceOneCoordinate p.2).mdifferentiableAt
      mdifferentiableAt_snd,
      (hasMFDerivAt_halfSpaceOneCoordinate p.2).mfderiv, mfderiv_snd]
    rfl
  have hdomain : IsOpen cuspDomain := isOpen_lt hz.continuous continuous_const
  have he : ContMDiffOn halfCollarModel W.model 1 e.toFun cuspDomain :=
    e.contMDiffOn.of_le (by exact_mod_cast (show 1 ≤ K + 1 by omega))
  have hscalar : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) 1 (z ∘ γ) (Icc a b) :=
    (hz.of_le (by simp)).comp_contMDiffOn hγ
  have hdist : edist ((γ a).2.val 0) ((γ b).2.val 0) ≤
      pathELength 𝓘(ℝ) (z ∘ γ) a b := by
    have h := riemannianEDist_le_pathELength hscalar rfl rfl hab
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ))] at h
    exact h
  apply hdist.trans
  rw [pathELength_eq_lintegral_mfderiv_Ioo, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hγt : MDifferentiableAt 𝓘(ℝ) halfCollarModel γ t :=
    (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hp : γ t ∈ cuspDomain := hmaps ⟨ht.1.le, ht.2.le⟩
  have het : MDifferentiableAt halfCollarModel W.model e.toFun (γ t) :=
    (he.contMDiffAt (hdomain.mem_nhds hp)).mdifferentiableAt one_ne_zero
  rw [enorm_tangentSpace_vectorSpace, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [mfderiv_comp_apply t (hz.mdifferentiableAt (by simp)) hγt, hdz]
  rw [mfderiv_comp_apply t het hγt]
  have hsq := e.height_component_sq_le hδ (γ t) hp
    (mfderiv 𝓘(ℝ) halfCollarModel γ t 1)
  calc
    _ = Real.sqrt ((mfderiv 𝓘(ℝ) halfCollarModel γ t 1).2 0 ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((1 - δ)⁻¹ * g.inner (e.toFun (γ t))
        (mfderiv halfCollarModel W.model e.toFun (γ t)
          (mfderiv 𝓘(ℝ) halfCollarModel γ t 1))
        (mfderiv halfCollarModel W.model e.toFun (γ t)
          (mfderiv 𝓘(ℝ) halfCollarModel γ t 1))) :=
      Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_mul (inv_nonneg.mpr (sub_pos.mpr hδ).le) _

private theorem mfderiv_height_lift (t : ℝ) (ht : 0 < t) :
    mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift t 1 =
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm 1 := by
  let E := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hdiff : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift t :=
    halfSpaceOneInteriorDiffeomorph.mdifferentiableAt (by decide) ht
  have hlocal : (fun s => (halfSpaceOneLift s).val 0) =ᶠ[𝓝 t] id := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact max_eq_left hs.le
  have hcoord : mfderiv 𝓘(ℝ) 𝓘(ℝ)
      (fun s => (halfSpaceOneLift s).val 0) t 1 = 1 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun s => (halfSpaceOneLift s).val 0) t 1 = 1
    rw [fderiv_apply_one_eq_deriv, hlocal.deriv_eq, deriv_id]
  have hchain : mfderiv 𝓘(ℝ) 𝓘(ℝ)
      (fun s => (halfSpaceOneLift s).val 0) t 1 =
        E (mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift t 1) := by
    change mfderiv 𝓘(ℝ) 𝓘(ℝ)
      ((fun z : EuclideanHalfSpace 1 => z.val 0) ∘ halfSpaceOneLift) t 1 = _
    rw [mfderiv_comp_apply t
      (hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceOneLift t)).mdifferentiableAt hdiff,
      (hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceOneLift t)).mfderiv]
    rfl
  apply E.injective
  rw [E.apply_symm_apply]
  exact hchain.symm.trans hcoord

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The same finite-regularity collar has its actual vertical path length bound.
Only interior times are differentiated; the initial height may be zero. -/
theorem CuspEmbedding.vertical_path_length_and_distance_le
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} {X : Set W.Carrier} (e : CuspEmbedding W g K δ X)
    (y : Torus) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < cuspDepth) :
    let γ : ℝ → W.Carrier := fun t => e.toFun (y, halfSpaceOneLift t);
    metricPathELength g γ a b ≤ ENNReal.ofReal (Real.sqrt (1 + δ) * (b - a)) ∧
    riemannianEDistOf g (γ a) (γ b) ≤
      ENNReal.ofReal (Real.sqrt (1 + δ) * (b - a)) := by
  let β : ℝ → CuspHalfSpace := fun t => (y, halfSpaceOneLift t)
  let γ : ℝ → W.Carrier := e.toFun ∘ β
  have hβ : ContMDiffOn 𝓘(ℝ) halfCollarModel 1 β (Icc a b) :=
    contMDiffOn_const.prodMk
      ((contMDiffOn_halfSpaceOneLift.of_le (by simp)).mono
        (fun _ ht => ha.trans ht.1))
  have hmaps : MapsTo β (Icc a b) cuspDomain := by
    intro t ht
    change (halfSpaceOneLift t).val 0 < cuspDepth
    change max t 0 < cuspDepth
    rw [max_eq_left (ha.trans ht.1)]
    exact ht.2.trans_lt hb
  have he : ContMDiffOn halfCollarModel W.model 1 e.toFun cuspDomain :=
    e.contMDiffOn.of_le (by exact_mod_cast (show 1 ≤ K + 1 by omega))
  have hγ : ContMDiffOn 𝓘(ℝ) W.model 1 γ (Icc a b) := he.comp hβ hmaps
  have hdomain : IsOpen cuspDomain := isOpen_lt
    (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const
  have hspeed (t : ℝ) (ht : t ∈ Ioo a b) :
      Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ) W.model γ t 1)
        (mfderiv 𝓘(ℝ) W.model γ t 1)) ≤ Real.sqrt (1 + δ) := by
    have htpos : 0 < t := ha.trans_lt ht.1
    have hlift : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift t :=
      halfSpaceOneInteriorDiffeomorph.mdifferentiableAt (by decide) htpos
    have hβt : MDifferentiableAt 𝓘(ℝ) halfCollarModel β t :=
      mdifferentiableAt_const.prodMk hlift
    have hp := hmaps ⟨ht.1.le, ht.2.le⟩
    have het := (he.contMDiffAt (hdomain.mem_nhds hp)).mdifferentiableAt one_ne_zero
    have hunit : e.cusp.metric.inner (β t)
        (mfderiv 𝓘(ℝ) halfCollarModel β t 1)
        (mfderiv 𝓘(ℝ) halfCollarModel β t 1) = 1 := by
      rw [e.cusp.metric_formula]
      change
        (mfderiv 𝓘(ℝ) halfCollarModel (fun s => (y, halfSpaceOneLift s)) t 1).2 0 *
          (mfderiv 𝓘(ℝ) halfCollarModel (fun s => (y, halfSpaceOneLift s)) t 1).2 0 +
        Real.exp (-(halfSpaceOneLift t).val 0) * e.cusp.torusMetric.inner y
          (mfderiv 𝓘(ℝ) halfCollarModel (fun s => (y, halfSpaceOneLift s)) t 1).1
          (mfderiv 𝓘(ℝ) halfCollarModel (fun s => (y, halfSpaceOneLift s)) t 1).1 = 1
      rw [mfderiv_prodMk mdifferentiableAt_const hlift, mfderiv_const]
      change
        (show EuclideanSpace ℝ (Fin 1) from
          mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift t 1) 0 *
          (show EuclideanSpace ℝ (Fin 1) from
            mfderiv 𝓘(ℝ) (𝓡∂ 1) halfSpaceOneLift t 1) 0 +
        Real.exp (-(halfSpaceOneLift t).val 0) * e.cusp.torusMetric.inner y 0 0 = 1
      rw [mfderiv_height_lift t htpos]
      have heval : ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm (1 : ℝ)) 0 = 1 :=
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).apply_symm_apply 1
      simp only [heval, map_zero, mul_zero, add_zero, one_mul]
    apply Real.sqrt_le_sqrt
    change g.inner (e.toFun (β t))
      (mfderiv 𝓘(ℝ) W.model (e.toFun ∘ β) t 1)
      (mfderiv 𝓘(ℝ) W.model (e.toFun ∘ β) t 1) ≤ _
    rw [mfderiv_comp_apply t het hβt]
    have hu := e.inner_mfderiv_self_le (β t) hp (mfderiv 𝓘(ℝ) halfCollarModel β t 1)
    simpa only [hunit, mul_one] using hu
  have hlength : metricPathELength g γ a b ≤
      ENNReal.ofReal (Real.sqrt (1 + δ) * (b - a)) := by
    rw [metricPathELength_eq, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    calc
      _ ≤ ∫⁻ _t in Ioo a b, ENNReal.ofReal (Real.sqrt (1 + δ)) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht =>
          ENNReal.ofReal_le_ofReal (hspeed t ht)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  exact ⟨hlength, (edistOf_le_metricPathELength g hab hγ).trans hlength⟩

end DifferentialGeometry.Geometry.Collapse
