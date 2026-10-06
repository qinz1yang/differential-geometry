import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimSmoothJN74

/-!
# Draft 74, the rim base is smooth, general domain (chain level)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G15 part 1 (suffix `_JN74`). `rimBase_contMDiffOn_JN74` with
the edge base replaced by an arbitrary one-dimensional manifold `Y` and a smooth map `j : Y → B₂`
(the proof uses only the smoothness of `j`): `rimBase_contMDiffOn_gen_JN74`. Instance: `Y` the good
open edge base `↥edgeBaseOpen` of the rows, `j` its inclusion into `B₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}


namespace Gaf02ChainEJA

section RimChartGen

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The rim base is smooth, general domain**: `Y` a one-dimensional manifold, `j : Y → B₂`
smooth, `rb : Y → B₁` sending every rim point over `j c`, `c ∈ S₂`, to its circle-base image;
over every point of `S₂` there is a rim point in `X₁`. Then `rb` is smooth on `S₂`. -/
theorem rimBase_contMDiffOn_gen_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Y]
    (j : Y → C.edgeBaseOpens_EFE)
    (hj : let _ := A.edgeChartedSpace1
      ContMDiff (𝓡 1) (𝓡 1) ∞ j)
    (S₂ : Set Y) (rb : Y → C.circleBaseOpens_EFE)
    (hrb : ∀ cc ∈ S₂, ∀ y : C.edgeSource_EFE, C.edgeProj_EFE y = j cc →
      C.edgeHeight_EFE y = 4 * Δ → ∀ hy : (y : X) ∈ C.circleDomain_EFE,
        C.circleProj_EFE ⟨y.1, hy⟩ = rb cc)
    (hX₁ : ∀ cc ∈ S₂, ∃ y : C.edgeSource_EFE, C.edgeProj_EFE y = j cc ∧
      C.edgeHeight_EFE y = 4 * Δ ∧ (y : X) ∈ C.circleDomain_EFE) :
    let _ := A.edgeChartedSpace1
    let _ := A.circleChartedSpace
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ²) ∞ rb S₂ := by
  intro _ _
  refine contMDiffOn_of_locally_contMDiffOn fun cc hcc => ?_
  obtain ⟨x₀, hx₀c, hx₀T, hx₀X⟩ := hX₁ cc hcc
  obtain ⟨ℓ, Φ, U₀, hU₀, hx₀U, hΦx, hlocal⟩ := C.rim_local_chart_JN74 A hβ hd hΔ2 hc hϑ hε0 hε hμ
    hτ hσc hb hγc hγc1 hβc1 x₀ hx₀T hx₀X
  refine ⟨j ⁻¹' U₀, hU₀.preimage hj.continuous, ?_, ?_⟩
  · change j cc ∈ U₀
    rw [← hx₀c]
    exact hx₀U
  have hval := C.contMDiff_edgeValB_EFE A
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun c' : Y => ((0 : ℝ), ℓ (C.edgeValB_EFE (j c')))) :=
    contMDiff_const.prodMk_space (ℓ.contDiff.contMDiff.comp (hval.comp hj))
  have hrbeq : ∀ c' ∈ S₂ ∩ j ⁻¹' U₀, rb c' = Φ.symm (0, ℓ (C.edgeValB_EFE (j c'))) ∧
      (0, ℓ (C.edgeValB_EFE (j c'))) ∈ Φ.target := by
    intro c' hc'
    obtain ⟨y, hyc, hyT, hyX⟩ := hX₁ c' hc'.1
    obtain ⟨hy, hys, hyΦ⟩ := hlocal y (hyc ▸ hc'.2) hyT
    have hrbc : rb c' = C.circleProj_EFE ⟨y.1, hy⟩ := (hrb c' hc'.1 y hyc hyT hy).symm
    have hΦy : Φ (C.circleProj_EFE ⟨y.1, hy⟩) = (0, ℓ (C.edgeValB_EFE (j c'))) := by
      rw [hyΦ, hyc]
    rw [hrbc]
    refine ⟨?_, ?_⟩
    · rw [← hΦy]
      exact (Φ.left_inv hys).symm
    · rw [← hΦy]
      exact Φ.map_source hys
  have hsymm : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ²) ∞ Φ.symm Φ.target := Φ.symm.contMDiffOn
  have hcomp : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ²) ∞
      (fun c' => Φ.symm (0, ℓ (C.edgeValB_EFE (j c')))) (S₂ ∩ j ⁻¹' U₀) :=
    hsymm.comp hg.contMDiffOn (fun c' hc' => (hrbeq c' hc').2)
  exact hcomp.congr fun c' hc' => (hrbeq c' hc').1

end RimChartGen

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
