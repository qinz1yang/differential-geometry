import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth

noncomputable section

open Manifold Filter
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem differentiableAt_diskMapMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    DifferentiableAt ℝ
      (fun p => g.inner (U p) (diskMapPartial U p v) (diskMapPartial U p w)) z := by
  have hp (a : ℂ) := contMDiffOn_source_partial hs hU (m := 1) (by norm_num) a
  have h : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 1
      (fun q => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
        (g.inner (U q) (diskMapPartial U q v) (diskMapPartial U q w))) z := by
    apply ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact (g.contMDiff.contMDiffAt.of_le (by simp)).comp z
        (((hU z hz).contMDiffAt (hs.mem_nhds hz)).of_le (by norm_num))
    · exact (hp v z hz).contMDiffAt (hs.mem_nhds hz)
    · exact (hp w z hz).contMDiffAt (hs.mem_nhds hz)
  exact (Bundle.contMDiffAt_totalSpace.mp h).2.contDiffAt.differentiableAt (by norm_num)

private theorem hasDerivAt_diskMapMetricPairing_add_smul
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U s)
    {z : ℂ} (hz : z ∈ s) (q v w : ℂ) :
    HasDerivAt (fun t : ℝ => g.inner (U (z + t • q))
      (diskMapPartial U (z + t • q) (v + t • w))
      (diskMapPartial U (z + t • q) (v + t • w)))
      (fderiv ℝ (fun p => g.inner (U p) (diskMapPartial U p v) (diskMapPartial U p v)) z q +
        2 * g.inner (U z) (diskMapPartial U z w) (diskMapPartial U z v)) 0 := by
  let P (a b p : ℂ) := g.inner (U p) (diskMapPartial U p a) (diskMapPartial U p b)
  have hP (a b : ℂ) : HasDerivAt (fun t : ℝ => P a b (z + t • q))
      (fderiv ℝ (P a b) z q) 0 := by
    have h := differentiableAt_diskMapMetricPairing g hs hU hz a b
    have hline : HasDerivAt (fun t : ℝ => z + t • q) q 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const q).const_add z
    have hc := h.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp : z = z + (0 : ℝ) • q)
    simpa only [Function.comp_apply] using! hc
  have hexpand (t : ℝ) : g.inner (U (z + t • q))
      (diskMapPartial U (z + t • q) (v + t • w))
      (diskMapPartial U (z + t • q) (v + t • w)) =
      P v v (z + t • q) + 2 * t * P w v (z + t • q) + t ^ 2 * P w w (z + t • q) := by
    let A : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U (z + t • q)) :=
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z + t • q)
    change g.inner (U (z + t • q)) (A (v + t • w)) (A (v + t • w)) =
      g.inner (U (z + t • q)) (A v) (A v) +
        2 * t * g.inner (U (z + t • q)) (A w) (A v) +
        t ^ 2 * g.inner (U (z + t • q)) (A w) (A w)
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [g.symm (U (z + t • q)) (A v) (A w)]
    ring
  have h := ((hP v v).add (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul (hP w v))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul (hP w w))
  have heq : (fun t : ℝ => g.inner (U (z + t • q))
      (diskMapPartial U (z + t • q) (v + t • w))
      (diskMapPartial U (z + t • q) (v + t • w))) =
      (fun t : ℝ => P v v (z + t • q) + 2 * t * P w v (z + t • q) +
        t ^ 2 * P w w (z + t • q)) := by
    funext t
    exact hexpand t
  rw [heq]
  simpa [P, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using! h

theorem hasDerivAt_diskMapEnergyDensity_domain_variation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U s)
    {z : ℂ} (hz : z ∈ s) {X : ℂ → ℂ} (hX : DifferentiableAt ℝ X z) :
    HasDerivAt (fun t : ℝ => diskMapEnergyDensity g (fun w => U (w + t • X w)) z)
      (fderiv ℝ (diskMapEnergyDensity g U) z (X z) +
        g.inner (U z) (diskMapPartial U z (fderiv ℝ X z 1)) (diskMapPartial U z 1) +
        g.inner (U z) (diskMapPartial U z (fderiv ℝ X z Complex.I))
          (diskMapPartial U z Complex.I)) 0 := by
  have hc : ContinuousAt (fun t : ℝ => z + t • X z) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, z + t • X z ∈ s := by
    apply hc.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using hs.mem_nhds hz
  have hchain {t : ℝ} (ht : z + t • X z ∈ s) (v : ℂ) :
      (diskMapPartial (fun w => U (w + t • X w)) z v : E) =
        diskMapPartial U (z + t • X z) (v + t • fderiv ℝ X z v) := by
    have hφ : HasFDerivAt (fun w : ℂ => w + t • X w)
        (ContinuousLinearMap.id ℝ ℂ + t • fderiv ℝ X z) z :=
      (hasFDerivAt_id z).add (hX.hasFDerivAt.const_smul t)
    have hUd := ((hU _ ht).contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp z hUd hφ.hasMFDerivAt.mdifferentiableAt
    rw [hφ.hasMFDerivAt.mfderiv] at hcomp
    have he := congrArg (fun L : ℂ →L[ℝ] E => L v) hcomp
    simpa only [diskMapPartial, ContinuousLinearMap.comp_apply, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.id_apply] using! he
  have heq : (fun t : ℝ => diskMapEnergyDensity g (fun w => U (w + t • X w)) z) =ᶠ[𝓝 0]
      (fun t : ℝ => (g.inner (U (z + t • X z))
        (diskMapPartial U (z + t • X z) (1 + t • fderiv ℝ X z 1))
        (diskMapPartial U (z + t • X z) (1 + t • fderiv ℝ X z 1)) +
        g.inner (U (z + t • X z))
          (diskMapPartial U (z + t • X z) (Complex.I + t • fderiv ℝ X z Complex.I))
          (diskMapPartial U (z + t • X z) (Complex.I + t • fderiv ℝ X z Complex.I))) / 2) := by
    filter_upwards [hnear] with t ht
    unfold diskMapEnergyDensity
    rw [hchain ht 1, hchain ht Complex.I]
  have hd := ((hasDerivAt_diskMapMetricPairing_add_smul g hs hU hz (X z) 1
    (fderiv ℝ X z 1)).add (hasDerivAt_diskMapMetricPairing_add_smul g hs hU hz (X z)
      Complex.I (fderiv ℝ X z Complex.I))).div_const 2
  have hp (v : ℂ) : DifferentiableAt ℝ
      (fun p => g.inner (U p) (diskMapPartial U p v) (diskMapPartial U p v)) z :=
    differentiableAt_diskMapMetricPairing g hs hU hz v v
  have henergy : fderiv ℝ (diskMapEnergyDensity g U) z (X z) =
      (fderiv ℝ (fun p => g.inner (U p) (diskMapPartial U p 1) (diskMapPartial U p 1)) z
        (X z) +
      fderiv ℝ (fun p => g.inner (U p) (diskMapPartial U p Complex.I)
        (diskMapPartial U p Complex.I)) z (X z)) / 2 := by
    have hh := ((hp 1).hasFDerivAt.add (hp Complex.I).hasFDerivAt).mul_const (2 : ℝ)⁻¹
    have hf : fderiv ℝ (diskMapEnergyDensity g U) z =
        (2 : ℝ)⁻¹ •
          (fderiv ℝ (fun p => g.inner (U p) (diskMapPartial U p 1) (diskMapPartial U p 1)) z +
            fderiv ℝ (fun p => g.inner (U p) (diskMapPartial U p Complex.I)
              (diskMapPartial U p Complex.I)) z) := by
      simpa only [diskMapEnergyDensity, div_eq_mul_inv, Pi.add_apply] using! hh.fderiv
    rw [hf]
    simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [henergy]
  convert hd.congr_of_eventuallyEq heq using 1 <;> first | rfl | ring

end DifferentialGeometry.Geometry
