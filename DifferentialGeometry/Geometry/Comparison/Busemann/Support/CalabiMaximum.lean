import DifferentialGeometry.Geometry.Comparison.Busemann.Support.CalabiChartPhase
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.CalabiMaximumPerturbation
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem exists_centered_euclidean_chart (p : M) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        M (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
      p ∈ Φ.source ∧ Φ p = 0 := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (by simp [F])
  let Ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := extChartAt I p
      open_source := isOpen_extChartAt_source p
      open_target := isOpen_extChartAt_target p
      contMDiffOn_toFun := by
        simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := p))
      contMDiffOn_invFun := contMDiffOn_extChartAt_symm p }
  let T : E ≃ₘ[ℝ] E :=
    { toEquiv :=
        { toFun := fun z => z - extChartAt I p p
          invFun := fun z => z + extChartAt I p p
          left_inv := fun z => sub_add_cancel z _
          right_inv := fun z => add_sub_cancel_right z _ }
      contMDiff_toFun := contMDiff_id.sub contMDiff_const
      contMDiff_invFun := contMDiff_id.add contMDiff_const }
  refine ⟨Ψ.trans (T.trans L.toDiffeomorph).toPartialDiffeomorph,
    ⟨mem_extChartAt_source p, Set.mem_univ _⟩, ?_⟩
  change L (extChartAt I p p - extChartAt I p p) = 0
  rw [sub_self, map_zero]

theorem eq_of_smooth_lower_support_at_global_max
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : Continuous f)
    (hsupport : ∀ x : M, ∀ ε : ℝ, 0 < ε → ∃ φ : M → ℝ,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ φ x ∧ φ x = f x ∧
        (∀ᶠ y in 𝓝 x, φ y ≤ f y) ∧
        -ε < laplacian (I := I) (LeviCivita (I := I) g) g φ x)
    (p : M) (hmax : ∀ x : M, f x ≤ f p) : ∀ x : M, f x = f p := by
  let A : Set M := {x | f x = f p}
  have hclosed : IsClosed A := isClosed_eq hf continuous_const
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    by_contra hnot
    obtain ⟨Φ, hqsource, hcenter⟩ := exists_centered_euclidean_chart (I := I) q
    let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    have hzero : (0 : F) ∈ Φ.target := hcenter ▸ Φ.toPartialEquiv.map_source hqsource
    obtain ⟨d, hd, hdball⟩ := Metric.mem_nhds_iff.mp (Φ.open_target.mem_nhds hzero)
    let U : Set M := Φ.source ∩ Φ ⁻¹' Metric.ball (0 : F) (d / 2)
    have hU : IsOpen U := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage Metric.isOpen_ball
    have hqU : q ∈ U := by
      refine ⟨hqsource, ?_⟩
      change dist (Φ q) 0 < d / 2
      rw [hcenter, dist_self]
      positivity
    have hnotSubset : ¬ U ⊆ A := fun hsub =>
      hnot (Filter.mem_of_superset (hU.mem_nhds hqU) hsub)
    obtain ⟨y, hy, hyA⟩ := Set.not_subset.mp hnotSubset
    have hcoord : Φ y ≠ 0 := by
      intro h0
      have heq : y = q := Φ.toPartialEquiv.injOn hy.1 hqsource (h0.trans hcenter.symm)
      exact hyA (heq ▸ hq)
    let r : ℝ := ‖Φ y‖
    have hr : 0 < r := norm_pos_iff.mpr hcoord
    have hrd : r < d / 2 := by
      have h : dist (Φ y) 0 < d / 2 := hy.2
      simpa only [dist_zero_right] using h
    have hball : Metric.closedBall (0 : F) r ⊆ Φ.target := by
      intro z hz
      apply hdball
      change dist z 0 < d
      have hzle : dist z 0 ≤ r := hz
      linarith
    let v : F := r⁻¹ • Φ y
    have hv : ‖v‖ = 1 := by
      dsimp only [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact inv_mul_cancel₀ hr.ne'
    have hrv : r • v = Φ y := by
      dsimp only [v]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hybelow : f (Φ.symm (r • v)) < f q := by
      rw [hrv]
      have hleft : Φ.symm (Φ y) = y := Φ.toPartialEquiv.left_inv hy.1
      rw [hleft]
      change f q = f p at hq
      rw [hq]
      exact lt_of_le_of_ne (hmax y) hyA
    obtain ⟨K, hK, hqK, h, hh, hzeroH, hboundary, hlap⟩ :=
      exists_calabi_boundary_perturbation_of_chart (I := I) g Φ q hqsource hcenter
        r hr hball v hv f hf hybelow
    exact false_of_positive_laplacian_boundary_perturbation (I := I) g hK hqK
      hf.continuousOn (fun x _ => hh.contMDiffAt) (fun x _ => by
        change f q = f p at hq
        rw [hq]
        exact hmax x) hzeroH hboundary
      (fun x hx => hlap x (interior_subset hx)) (fun x _ => hsupport x)
  have hA : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, rfl⟩
  intro x
  change x ∈ A
  rw [hA]
  exact Set.mem_univ x

end DifferentialGeometry.Geometry.Topology

end
