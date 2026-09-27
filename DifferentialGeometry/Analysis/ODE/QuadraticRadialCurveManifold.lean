import DifferentialGeometry.Analysis.ODE.QuadraticRadialCurve
import DifferentialGeometry.Analysis.ODE.IntegralCurveNaturality
import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

open Set Manifold Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ F H}

theorem isMIntegralCurveOn_comp_quadraticRadialCurve
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (V : (x : M) → TangentSpace I x)
    (b : ℝ) {x : E} (hx : x ≠ 0) {s : Set ℝ}
    (hdomain : ∀ t ∈ s, 0 < 1 + 2 * b * t / ‖x‖ ^ 2 ∧ quadraticRadialCurve b x t ∈ χ.source)
    (hcoords : ∀ t ∈ s,
      mfderiv I 𝓘(ℝ, E) χ.symm (χ (quadraticRadialCurve b x t))
          (V (χ (quadraticRadialCurve b x t))) =
        (b / ‖quadraticRadialCurve b x t‖ ^ 2) • quadraticRadialCurve b x t) :
    IsMIntegralCurveOn (χ ∘ quadraticRadialCurve b x) V s := by
  have hcurve : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) (quadraticRadialCurve b x)
      (fun y => (b / ‖y‖ ^ 2) • y) s :=
    isMIntegralCurveOn_iff_isIntegralCurveOn.mpr
      (fun t ht => (hasDerivAt_quadraticRadialCurve b hx (hdomain t ht).1).hasDerivWithinAt)
  apply hcurve.map (fun t ht => χ.mdifferentiableAt (by simp) (hdomain t ht).2)
  intro t ht
  let y := quadraticRadialCurve b x t
  have hy : y ∈ χ.source := (hdomain t ht).2
  have hback : mfderiv 𝓘(ℝ, E) I χ y
      (mfderiv I 𝓘(ℝ, E) χ.symm (χ y) (V (χ y))) = V (χ y) := by
    rw [← DifferentialGeometry.VectorField.inverse_mfderiv_partialDiffeomorph χ (by simp) hy]
    exact (DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph χ
      (by simp) hy).self_apply_inverse _
  exact (congrArg (mfderiv 𝓘(ℝ, E) I χ y) (hcoords t ht)).symm.trans hback

theorem curveAt_eqOn_comp_quadraticRadialCurve [I.Boundaryless] [IsManifold I 1 M] [T2Space M]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V)
    (b : ℝ) {x : E} (hx : x ≠ 0) {u v : ℝ} (hzero : 0 ∈ Ioo u v)
    (hdomain : ∀ t ∈ Ioo u v, 0 < 1 + 2 * b * t / ‖x‖ ^ 2 ∧ quadraticRadialCurve b x t ∈ χ.source)
    (hcoords : ∀ t ∈ Ioo u v,
      mfderiv I 𝓘(ℝ, E) χ.symm (χ (quadraticRadialCurve b x t))
          (V (χ (quadraticRadialCurve b x t))) =
        (b / ‖quadraticRadialCurve b x t‖ ^ 2) • quadraticRadialCurve b x t) :
    EqOn (curveAt V hcomplete (χ x)) (χ ∘ quadraticRadialCurve b x) (Ioo u v) := by
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hV
    ((curveAt_integralCurve V hcomplete (χ x)).isMIntegralCurveOn _)
    (isMIntegralCurveOn_comp_quadraticRadialCurve χ V b hx hdomain hcoords)
    (by simp [curveAt_zero])

theorem exists_pos_curveAt_eq_quadraticRadialCurve_on_compact
    [I.Boundaryless] [IsManifold I 1 M] [T2Space M]
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V)
    (b : ℝ) {C : Set E} (hC : IsCompact C) (hCχ : C ⊆ χ.source \ {0})
    (hcoords : ∀ᶠ z in 𝓝ˢ (χ '' C),
      mfderiv I 𝓘(ℝ, E) χ.symm z (V z) = (b / ‖χ.symm z‖ ^ 2) • χ.symm z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ C, ∀ t ∈ Ioo (-ε) ε,
      curveAt V hcomplete (χ x) t = χ (quadraticRadialCurve b x t) := by
  obtain ⟨U, hU, hCU, hUcoords⟩ := eventually_nhdsSet_iff_exists.mp hcoords
  let good : Set (E × ℝ) := {p | 0 < 1 + 2 * b * p.2 / ‖p.1‖ ^ 2 ∧
    quadraticRadialCurve b p.1 p.2 ∈ χ.source ∧ χ (quadraticRadialCurve b p.1 p.2) ∈ U}
  have hgood : good ∈ (𝓝ˢ C) ×ˢ 𝓝 (0 : ℝ) := by
    apply hC.mem_nhdsSet_prod_of_forall
    intro x hx
    rw [← nhds_prod_eq]
    have hx0 : x ≠ 0 := (hCχ hx).2
    have hr : ContinuousAt (fun p : E × ℝ => 1 + 2 * b * p.2 / ‖p.1‖ ^ 2) (x, 0) :=
      continuousAt_const.add ((continuousAt_const.mul continuousAt_snd).div
        (continuousAt_fst.norm.pow 2) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0)))
    have hcurve := continuousAt_quadraticRadialCurve b (p := (x, 0)) hx0
    have hχ : ContinuousAt (fun p : E × ℝ => χ (quadraticRadialCurve b p.1 p.2)) (x, 0) :=
      (χ.toOpenPartialHomeomorph.continuousAt
        (show quadraticRadialCurve b x 0 ∈ χ.source by simpa using (hCχ hx).1)).comp
          (f := fun p : E × ℝ => quadraticRadialCurve b p.1 p.2) hcurve
    have hrpos : ∀ᶠ p : E × ℝ in 𝓝 (x, 0), 0 < 1 + 2 * b * p.2 / ‖p.1‖ ^ 2 :=
      hr.eventually (Ioi_mem_nhds (by simp))
    have hsource : ∀ᶠ p : E × ℝ in 𝓝 (x, 0), quadraticRadialCurve b p.1 p.2 ∈ χ.source :=
      hcurve.preimage_mem_nhds (χ.open_source.mem_nhds (by simpa using (hCχ hx).1))
    have htarget : ∀ᶠ p : E × ℝ in 𝓝 (x, 0), χ (quadraticRadialCurve b p.1 p.2) ∈ U :=
      hχ.preimage_mem_nhds (hU.mem_nhds (by simpa using hCU (mem_image_of_mem χ hx)))
    exact hrpos.and (hsource.and htarget)
  obtain ⟨S, hS, T, hT, hST⟩ := Filter.mem_prod_iff.mp hgood
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hg {x : E} (hx : x ∈ C) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : (x, t) ∈ good := by
    apply hST
    refine ⟨subset_of_mem_nhdsSet hS hx, hεT ?_⟩
    rw [Real.ball_eq_Ioo]
    simpa only [zero_sub, zero_add] using ht
  refine ⟨ε, hε, ?_⟩
  intro x hx t ht
  apply curveAt_eqOn_comp_quadraticRadialCurve χ V hV hcomplete b ((hCχ hx).2)
    (show 0 ∈ Ioo (-ε) ε from ⟨neg_neg_of_pos hε, hε⟩)
    (fun s hs => ⟨(hg hx hs).1, (hg hx hs).2.1⟩) ?_ ht
  intro s hs
  have h := hUcoords _ (hg hx hs).2.2
  have hinv := χ.left_inv (hg hx hs).2.1
  exact h.trans (congrArg (fun y : E => (b / ‖y‖ ^ 2) • y) hinv)

end DifferentialGeometry.Analysis.ODE
