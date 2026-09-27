import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowDiffeomorph
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.UniformInwardFlow
import DifferentialGeometry.Topology.Compactness.Strip
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Restriction

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_boundary_flow_collar_diffeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] (hK : IsCompact ((𝓡∂ (n + 1)).boundary M))
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    {U : Opens M} (hKU : (𝓡∂ (n + 1)).boundary M ⊆ U)
    {ε : ℝ} [Fact ((0 : ℝ) < ε)] {F : M × ℝ → M}
    (hF : ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ F
      ((U : Set M) ×ˢ Icc (0 : ℝ) ε))
    (hzero : ∀ q ∈ U, F (q, 0) = q)
    (hcurve : ∀ q ∈ U, IsMIntegralCurveOn (fun t => F (q, t)) V (Icc (0 : ℝ) ε))
    (hi : ∀ q ∈ U, ∀ t ∈ Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (q, t)))
    (N : Opens M) (hKN : (𝓡∂ (n + 1)).boundary M ⊆ N) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      let S : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε) :=
        ⟨{q | (q.2 : ℝ) < δ},
          isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
      ∃ Y : Opens M, (𝓡∂ (n + 1)).boundary M ⊆ Y ∧ Y ≤ N ∧
        ∃ d : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) S Y ∞,
          ∀ q : S, (d q : M) = F ((q.val.1 : M), (q.val.2 : ℝ)) := by
  have hε : 0 < ε := Fact.out
  obtain ⟨W, _, Ω, hzΩ, e, he⟩ :=
    exists_boundary_flow_diffeomorph hK hV hpos hKU hF hzero hcurve hi
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let c : B × Icc (0 : ℝ) ε → M := fun q => F ((q.1 : M), (q.2 : ℝ))
  have hc : ContMDiff ((HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)) I ∞ c :=
    hF.comp_contMDiff ((boundaryInclusion_contMDiff (I := I) (M := M)).prodMap
      (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)))
      (fun q => ⟨hKU q.1.2, q.2.2⟩)
  let : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hzeroN (p : B) : (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) ∈ (Ω : Set _) ∩ c ⁻¹' N := by
    refine ⟨hzΩ p, ?_⟩
    change F (p.val, 0) ∈ N
    rw [hzero p.val (hKU p.2)]
    exact hKN p.2
  obtain ⟨δ, hδ, hδε, hsmall⟩ := DifferentialGeometry.Topology.exists_shorter_strip_image_subset hε
    (continuous_id : Continuous (id : B × Icc (0 : ℝ) ε → B × Icc (0 : ℝ) ε))
    (Ω.isOpen.inter (N.isOpen.preimage hc.continuous)) hzeroN
  let S : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | (q.2 : ℝ) < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  have hSΩ : S ≤ Ω := fun q hq => (hsmall ⟨q, hq, rfl⟩).1
  obtain ⟨Y, _, _, d, hd, _⟩ := DifferentialGeometry.Manifold.Diffeomorph.exists_restrict_opens e S hSΩ
  have hdF (q : S) : (d q : M) = c q.val := (hd q).trans (he _)
  have hd0 (p : B) : (d ⟨(p, ⟨0, ⟨le_rfl, hε.le⟩⟩), hδ⟩ : M) = p.val := by
    rw [hdF]
    exact hzero p.val (hKU p.2)
  refine ⟨δ, hδ, hδε, Y, ?_, ?_, d, hdF⟩
  · intro p hp
    have hh : (d ⟨(⟨p, hp⟩, ⟨0, ⟨le_rfl, hε.le⟩⟩), hδ⟩ : M) = p := hd0 ⟨p, hp⟩
    rw [← hh]
    exact (d ⟨(⟨p, hp⟩, ⟨0, ⟨le_rfl, hε.le⟩⟩), hδ⟩).property
  · intro y hy
    let q := d.symm ⟨y, hy⟩
    have hq : (d q : M) = y := congrArg Subtype.val (d.apply_symm_apply ⟨y, hy⟩)
    rw [← hq, hdF]
    exact (hsmall ⟨q.val, q.property, rfl⟩).2

theorem exists_boundary_collar_diffeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ (δ : ℝ) (hδ : 0 < δ), δ < ε ∧
        let S : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε) :=
          ⟨{q | (q.2 : ℝ) < δ},
            isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
        ∃ W : Opens M, (𝓡∂ (n + 1)).boundary M ⊆ W ∧
          ∃ e : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
            (𝓡∂ (n + 1)) S W ∞,
            (∀ p, (e ⟨(p, ⟨0, ⟨le_rfl, hε.le⟩⟩), hδ⟩ : M) =
              boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
            ∀ q : S, 0 < (q.val.2 : ℝ) → (𝓡∂ (n + 1)).IsInteriorPoint (e q : M) := by
  obtain ⟨V, hV, _, hpos, U, hKU, ε, hε, F, hF, hzero, hcurve, hi, _⟩ :=
    exists_uniform_positive_boundary_flow hK
  refine ⟨ε, hε, ?_⟩
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨δ, hδ, hδε, Y, hKY, _, d, hd⟩ :=
    exists_boundary_flow_collar_diffeomorph hK hV hpos hKU hF hzero hcurve hi ⊤
      (fun _ _ => trivial)
  refine ⟨δ, hδ, hδε, Y, hKY, d, ?_, ?_⟩
  · intro p
    rw [hd]
    exact hzero p.val (hKU p.2)
  · intro q hq
    rw [hd]
    exact hi q.val.1.val (hKU q.val.1.2) q.val.2.val ⟨hq, q.val.2.property.2⟩

end DifferentialGeometry.Manifold.BoundaryCollar
