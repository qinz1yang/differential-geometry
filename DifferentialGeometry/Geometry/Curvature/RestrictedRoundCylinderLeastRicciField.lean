import DifferentialGeometry.Geometry.Curvature.SmoothRestrictedRoundCylinderLeastRicci
import DifferentialGeometry.Geometry.Curvature.RicciEigenpairUniqueness
import DifferentialGeometry.Geometry.Gradient.CylinderPerturbation

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem exists_smooth_least_ricci_field_on_restricted_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) O)
    {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε) :
    ∃ (μ : O → ℝ)
      (w : ∀ x : O, TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x),
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ μ U ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)).tangent ∞
        (fun x ↦ (⟨x, w x⟩ : TangentBundle ((𝓡 2).prod 𝓘(ℝ)) O)) U ∧
      ∀ x ∈ U, g.inner x (w x) (w x) = 1 ∧ ricciSharp g x (w x) = μ x • w x ∧
        (∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
          g.inner x z z = 1 → μ x ≤ ricciTensor g x z z) ∧
        |μ x| ≤ 5772 * ε ∧
        Module.End.eigenspace (ricciSharp g x).toLinearMap (μ x) = Submodule.span ℝ {w x} ∧
        0 < mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x (w x) ∧
        Real.sqrt (((roundCylinderMetric (E := E) (n := 2)).restrictOpen O).inner x
          (w x - restrictedCylinderAxis O x) (w x - restrictedCylinderAxis O x)) ≤ 92354 * ε := by
  classical
  let IC := (𝓡 2).prod 𝓘(ℝ)
  choose a v hv he hmin ha hs hp hd using fun x (hx : x ∈ U) ↦
    exists_least_ricci_direction_on_restricted_roundCylinder O g x ε hε (hsmall x hx)
  let μ := fun x ↦ if hx : x ∈ U then a x hx else 0
  let w : ∀ x : O, TangentSpace IC x :=
    fun x ↦ if hx : x ∈ U then v x hx else 0
  have hμeq (x) (hx : x ∈ U) : μ x = a x hx := dif_pos hx
  have hweq (x) (hx : x ∈ U) : w x = v x hx := dif_pos hx
  have hlocal (x) (hx : x ∈ U) :
      ContMDiffAt IC 𝓘(ℝ) ∞ μ x ∧
      ContMDiffAt IC IC.tangent ∞
        (fun y ↦ (⟨y, w y⟩ : TangentBundle IC O)) x := by
    obtain ⟨V, hVo, hxV, hVU, b, z, hb, hz, hprop⟩ :=
      exists_smooth_least_ricci_direction_on_restricted_roundCylinder O g hU ε hε hsmall hx
    have heq (y) (hy : y ∈ V) : μ y = b y ∧ w y = z y := by
      have hyU := hVU hy
      rw [hμeq y hyU, hweq y hyU]
      obtain ⟨hzn, hze, hzm, _, hzs, hzp, _⟩ := hprop y hy
      exact least_ricci_eigenpair_eq_of_positive_functional g y (mvfderiv IC (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) y).toLinearMap
        (a y hyU) (b y) (v y hyU) (z y) (hv y hyU) hzn (he y hyU) hze
        (hmin y hyU) hzm hzs (hp y hyU) hzp
    refine ⟨?_, ?_⟩
    · exact (hb.congr (fun y hy ↦ (heq y hy).1)).contMDiffAt (hVo.mem_nhds hxV)
    · exact (hz.congr (fun y hy ↦ by rw [(heq y hy).2])).contMDiffAt (hVo.mem_nhds hxV)
  refine ⟨μ, w, (fun x hx ↦ (hlocal x hx).1.contMDiffWithinAt),
    (fun x hx ↦ (hlocal x hx).2.contMDiffWithinAt), ?_⟩
  intro x hx
  rw [hμeq x hx, hweq x hx]
  exact ⟨hv x hx, he x hx, hmin x hx, ha x hx, hs x hx, hp x hx, hd x hx⟩

theorem exists_smooth_least_ricci_field_close_to_gradient_on_restricted_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) O)
    {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε) :
    ∃ (μ : O → ℝ)
      (w : ∀ x : O, TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x),
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ μ U ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)).tangent ∞
        (fun x ↦ (⟨x, w x⟩ : TangentBundle ((𝓡 2).prod 𝓘(ℝ)) O)) U ∧
      ∀ x ∈ U, g.inner x (w x) (w x) = 1 ∧ ricciSharp g x (w x) = μ x • w x ∧
        (∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
          g.inner x z z = 1 → μ x ≤ ricciTensor g x z z) ∧
        |μ x| ≤ 5772 * ε ∧
        Module.End.eigenspace (ricciSharp g x).toLinearMap (μ x) = Submodule.span ℝ {w x} ∧
        0 < mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x (w x) ∧
        Real.sqrt (((roundCylinderMetric (E := E) (n := 2)).restrictOpen O).inner x
          (w x - restrictedCylinderAxis O x) (w x - restrictedCylinderAxis O x)) ≤ 92354 * ε ∧
        let d := w x - DifferentialGeometry.Geometry.Operator.gradFun g
          (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x
        Real.sqrt (g.inner x d d) ≤ 184712 * ε := by
  obtain ⟨μ, w, hμ, hw, hprop⟩ :=
    exists_smooth_least_ricci_field_on_restricted_roundCylinder O g hU ε hε hsmall
  refine ⟨μ, w, hμ, hw, ?_⟩
  intro x hx
  obtain ⟨hwn, hwe, hwm, hwa, hws, hwp, hwd⟩ := hprop x hx
  refine ⟨hwn, hwe, hwm, hwa, hws, hwp, hwd, ?_⟩
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  have hsmall₀ := hsmall x hx 0 (by decide)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hsmall₀
  have hb := DifferentialGeometry.Geometry.Gradient.sqrt_inner_sub_gradFun_restricted_height_le
    gS O g x ε (by linarith) hsmall₀ (w x) (92354 * ε) hwd
  have hsqrt : Real.sqrt (1 + ε) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  calc
    _ ≤ Real.sqrt (1 + ε) * (92354 * ε + 2 * ε) := hb
    _ ≤ 2 * (92354 * ε + 2 * ε) := mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = _ := by ring

end DifferentialGeometry.Geometry.Curvature
