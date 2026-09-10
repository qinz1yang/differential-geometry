import DifferentialGeometry.Geometry.Curvature.SmoothRoundCylinderLeastRicci
import DifferentialGeometry.Geometry.Curvature.RicciEigenpairUniqueness

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open Poincare.Geometry.Metric

namespace Poincare.Geometry.Curvature

theorem exists_smooth_least_ricci_field_on_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))
    {U : Set (Metric.sphere (0 : E) 1 × ℝ)} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g (roundCylinderMetric (E := E) (n := 2))
        (roundCylinderMetric (E := E) (n := 2)) x ≤ ε) :
    ∃ (μ : Metric.sphere (0 : E) 1 × ℝ → ℝ)
      (w : ∀ x : Metric.sphere (0 : E) 1 × ℝ, TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x),
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ μ U ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)).tangent ∞
        (fun x ↦ (⟨x, w x⟩ : TangentBundle ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))) U ∧
      ∀ x ∈ U, g.inner x (w x) (w x) = 1 ∧ ricciSharp g x (w x) = μ x • w x ∧
        (∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
          g.inner x z z = 1 → μ x ≤ ricciTensor g x z z) ∧
        |μ x| ≤ 5772 * ε ∧
        Module.End.eigenspace (ricciSharp g x).toLinearMap (μ x) = Submodule.span ℝ {w x} ∧
        0 < mvfderiv ((𝓡 2).prod 𝓘(ℝ)) Prod.snd x (w x) ∧
        Real.sqrt ((roundCylinderMetric (E := E) (n := 2)).inner x
          (w x - cylinderAxis x) (w x - cylinderAxis x)) ≤ 92354 * ε := by
  classical
  let IC := (𝓡 2).prod 𝓘(ℝ)
  choose a v hv he hmin ha hs hp hd using fun x (hx : x ∈ U) ↦
    exists_least_ricci_direction_on_roundCylinder g x ε hε (hsmall x hx)
  let μ := fun x ↦ if hx : x ∈ U then a x hx else 0
  let w : ∀ x : Metric.sphere (0 : E) 1 × ℝ, TangentSpace IC x :=
    fun x ↦ if hx : x ∈ U then v x hx else 0
  have hμeq (x) (hx : x ∈ U) : μ x = a x hx := dif_pos hx
  have hweq (x) (hx : x ∈ U) : w x = v x hx := dif_pos hx
  have hlocal (x) (hx : x ∈ U) :
      ContMDiffAt IC 𝓘(ℝ) ∞ μ x ∧
      ContMDiffAt IC IC.tangent ∞
        (fun y ↦ (⟨y, w y⟩ : TangentBundle IC (Metric.sphere (0 : E) 1 × ℝ))) x := by
    obtain ⟨V, hVo, hxV, hVU, b, z, hb, hz, hprop⟩ :=
      exists_smooth_least_ricci_direction_on_roundCylinder g hU ε hε hsmall hx
    have heq (y) (hy : y ∈ V) : μ y = b y ∧ w y = z y := by
      have hyU := hVU hy
      rw [hμeq y hyU, hweq y hyU]
      obtain ⟨hzn, hze, hzm, _, hzs, hzp, _⟩ := hprop y hy
      exact least_ricci_eigenpair_eq_of_positive_functional g y (mvfderiv IC Prod.snd y).toLinearMap
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

end Poincare.Geometry.Curvature
