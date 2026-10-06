import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem morrey_mfderiv_injective_of_projected_fderiv_invertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {p : M} (P : E →L[ℝ] ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (hsrc : diskExtension q z ∈ (chartAt E p).source)
    (hF : (fderiv ℝ
      (fun x : ℂ => P (extChartAt 𝓘(ℝ, E) p (diskExtension q x))) z).IsInvertible) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
  let U : ℂ → M := diskExtension q
  let X : ℂ → E := fun x => extChartAt 𝓘(ℝ, E) p (U x)
  have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z :=
    hq.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hsrc
  have hX : DifferentiableAt ℝ X z :=
    ((hc.comp z hU).contDiffAt).differentiableAt (by simp)
  let C : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U z)
  let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  have hDX : fderiv ℝ X z = C.comp D :=
    mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp z (hc.mdifferentiableAt (by simp))
        (hU.mdifferentiableAt (by simp)))
  have hDF : fderiv ℝ (fun x : ℂ => P (X x)) z = P.comp (fderiv ℝ X z) :=
    (P.hasFDerivAt.comp z hX.hasFDerivAt).fderiv
  have hF' : (fderiv ℝ (fun x : ℂ => P (X x)) z).IsInvertible := hF
  have hDinj : Function.Injective D := by
    intro v w hvw
    apply hF'.injective
    rw [hDF, hDX]
    exact congrArg (fun y : E => P (C y)) hvw
  exact hDinj

/-- A zero germ for the normal height difference of the same actual branched
coordinate gives coincident regular image germs at every sufficiently small
nonzero coordinate. The original metric, disk, coordinate and splitting remain
fixed. The zero germ is an input from the downstream classifier, and no global
factorization, injectivity or exclusion of critical values is asserted. -/
theorem IsMorreyDisk.coincident_regular_germs_of_branched_height_zero_germ
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) {a : ℂ}
    (m : ℕ) (b : Fin (Module.finrank ℝ E) → ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hae : a ∈ e.source) (hea : e a = 0)
    (heinterior : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (hechart : ∀ z ∈ e.source,
      diskExtension q z ∈ (chartAt E (diskExtension q a)).source) :
    let U : ℂ → M := diskExtension q
    let p := U a
    let GramQ := chartGramBilin g p p
    let P := chartLeadingPlaneProjection g p p b
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := P ∘ X
    (∀ z ∈ e.source, z ≠ a → (fderiv ℝ F z).IsInvertible) →
    (∀ w ∈ e.target,
      F (e.symm w) = F a + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) →
    ∀ (N : E) (lift : ℂ → E),
      (∀ v : E, v = lift (P v) + (GramQ N v) • N) →
      let H : ℂ → ℝ := fun w => GramQ N (X (e.symm w) - X a)
      ∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ζ ≠ 1 →
        (∀ᶠ w in 𝓝 (0 : ℂ), H w - H (ζ * w) = 0) →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ε →
            e.symm w ∈ Metric.ball (0 : ℂ) 1 ∧
            e.symm (ζ * w) ∈ Metric.ball (0 : ℂ) 1 ∧
            e.symm w ≠ e.symm (ζ * w) ∧
            Function.Injective
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm w)) ∧
            Function.Injective
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm (ζ * w))) ∧
            U (e.symm w) = U (e.symm (ζ * w)) ∧
            Filter.map U (𝓝 (e.symm w)) =
              Filter.map U (𝓝 (e.symm (ζ * w))) := by
  intro U p GramQ P X F hreg hpower N lift hsplit H ζ hζpower hζne hzero
  have hζ0 : ζ ≠ 0 := by
    intro hz
    simp [hz] at hζpower
  have h0target : (0 : ℂ) ∈ e.target := by
    rw [← hea]
    exact e.map_source hae
  have hrotCont : Continuous (fun w : ℂ => ζ * w) := continuous_const.mul continuous_id
  have hrotAt : Tendsto (fun w : ℂ => ζ * w)
      (𝓝 (0 : ℂ)) (𝓝 (ζ * 0)) := hrotCont.continuousAt
  have hrot0 : Tendsto (fun w : ℂ => ζ * w) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero] using hrotAt
  have hnear : {w : ℂ | w ∈ e.target ∧ ζ * w ∈ e.target ∧
      H w - H (ζ * w) = 0} ∈ 𝓝 (0 : ℂ) := by
    filter_upwards [e.open_target.mem_nhds h0target,
      hrot0.eventually (e.open_target.mem_nhds h0target), hzero] with w hw hζw hh
    exact ⟨hw, hζw, hh⟩
  obtain ⟨Ω, hΩsub, hΩopen, h0Ω⟩ := mem_nhds_iff.mp hnear
  have hvalues (w : ℂ) (hw : w ∈ Ω) : U (e.symm w) = U (e.symm (ζ * w)) := by
    obtain ⟨hwt, hζwt, hh⟩ := hΩsub hw
    have hP : P (X (e.symm w)) = P (X (e.symm (ζ * w))) := by
      change F (e.symm w) = F (e.symm (ζ * w))
      rw [hpower w hwt, hpower (ζ * w) hζwt, mul_pow, hζpower, one_mul]
    have hN : GramQ N (X (e.symm w)) = GramQ N (X (e.symm (ζ * w))) := by
      have hh' := sub_eq_zero.mp hh
      simpa only [H, map_sub, sub_left_inj] using hh'
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · simpa only [extChartAt_source] using hechart (e.symm w) (e.map_target hwt)
    · simpa only [extChartAt_source] using hechart (e.symm (ζ * w)) (e.map_target hζwt)
    · change X (e.symm w) = X (e.symm (ζ * w))
      calc
        X (e.symm w) = lift (P (X (e.symm w))) + (GramQ N (X (e.symm w))) • N :=
          hsplit _
        _ = lift (P (X (e.symm (ζ * w)))) + (GramQ N (X (e.symm (ζ * w)))) • N := by
          rw [hP, hN]
        _ = X (e.symm (ζ * w)) := (hsplit _).symm
  have hoff {v : ℂ} (hvt : v ∈ e.target) (hv0 : v ≠ 0) : e.symm v ≠ a := by
    intro h
    have hv : v = e a := (e.right_inv hvt).symm.trans (congrArg e h)
    exact hv0 (hv.trans hea)
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (hΩopen.mem_nhds h0Ω)
  refine ⟨ε, hε, ?_⟩
  intro w hwpos hwε
  have hw0 : w ≠ 0 := norm_pos_iff.mp hwpos
  have hwΩ : w ∈ Ω := hεΩ (by simpa only [Metric.mem_ball, dist_zero_right] using hwε)
  obtain ⟨hwt, hζwt, _hh⟩ := hΩsub hwΩ
  have hζw0 : ζ * w ≠ 0 := mul_ne_zero hζ0 hw0
  have hsource₁ := e.map_target hwt
  have hsource₂ := e.map_target hζwt
  have hdistinct : e.symm w ≠ e.symm (ζ * w) := by
    intro h
    have hww : w = ζ * w := (e.right_inv hwt).symm.trans
      ((congrArg e h).trans (e.right_inv hζwt))
    apply hζne
    exact mul_right_cancel₀ hw0 (by simpa only [one_mul] using hww.symm)
  have hrank₁ := morrey_mfderiv_injective_of_projected_fderiv_invertible hq P
    (heinterior hsource₁) (hechart _ hsource₁) (hreg _ hsource₁ (hoff hwt hw0))
  have hrank₂ := morrey_mfderiv_injective_of_projected_fderiv_invertible hq P
    (heinterior hsource₂) (hechart _ hsource₂) (hreg _ hsource₂ (hoff hζwt hζw0))
  refine ⟨heinterior hsource₁, heinterior hsource₂, hdistinct,
    hrank₁, hrank₂, hvalues w hwΩ, ?_⟩
  have hlocal : (U ∘ e.symm) =ᶠ[𝓝 w]
      ((U ∘ e.symm) ∘ (fun v : ℂ => ζ * v)) := by
    filter_upwards [hΩopen.mem_nhds hwΩ] with v hv
    exact hvalues v hv
  calc
    Filter.map U (𝓝 (e.symm w)) = Filter.map (U ∘ e.symm) (𝓝 w) := by
      rw [← Filter.map_map, e.symm.map_nhds_eq hwt]
    _ = Filter.map ((U ∘ e.symm) ∘ (fun v : ℂ => ζ * v)) (𝓝 w) :=
      Filter.map_congr hlocal
    _ = Filter.map U (𝓝 (e.symm (ζ * w))) := by
      rw [← Filter.map_map, map_mul_left_nhds₀ hζ0, ← Filter.map_map,
        e.symm.map_nhds_eq hζwt]

end DifferentialGeometry.Geometry
