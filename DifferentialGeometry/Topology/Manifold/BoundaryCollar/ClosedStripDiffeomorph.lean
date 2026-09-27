import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Diffeomorph

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_closed_boundary_collar_diffeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ c : C(BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε, M),
        IsClosedEmbedding c ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        (∀ q, 0 < q.2.val → (𝓡∂ (n + 1)).IsInteriorPoint (c q)) ∧
        ∃ (δ : ℝ) (_ : 0 < δ), δ < ε ∧
          let S : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε) :=
            ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
          ∃ Y : Opens M, (𝓡∂ (n + 1)).boundary M ⊆ Y ∧
            (Y : Set M) = c '' {q | q.2.val < δ} ∧
            ∃ e : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
                (𝓡∂ (n + 1)) S Y ∞,
              ∀ q : S, (e q : M) = c q.val := by
  obtain ⟨V, hV, _, hpos, U, hKU, ε, hε, F, hF, hzero, hcurve, hi, _⟩ :=
    exists_uniform_positive_boundary_flow hK
  refine ⟨ε, hε, ?_⟩
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let J := (HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)
  let cfun : B × Icc (0 : ℝ) ε → M := fun q => F ((q.1 : M), (q.2 : ℝ))
  have hcs : ContMDiff J I ∞ cfun := hF.comp_contMDiff
    ((boundaryInclusion_contMDiff (I := I) (M := M)).prodMap
      (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)))
    (fun q => ⟨hKU q.1.2, q.2.2⟩)
  let c : C(B × Icc (0 : ℝ) ε, M) := ⟨cfun, hcs.continuous⟩
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hc : IsClosedEmbedding c := hcs.continuous.isClosedEmbedding
    (boundary_flow_injective hV hKU hzero hcurve hi)
  obtain ⟨δ, hδ, hδε, Y, hKY, _, e, he⟩ :=
    exists_boundary_flow_collar_diffeomorph hK hV hpos hKU hF hzero hcurve hi ⊤
      (fun _ _ => trivial)
  refine ⟨c, hc, hcs, (fun p => hzero p.val (hKU p.2)),
    (fun q hq => hi q.1.val (hKU q.1.2) q.2.val ⟨hq, q.2.property.2⟩),
    δ, hδ, hδε, Y, hKY, ?_, e, he⟩
  ext y
  constructor
  · intro hy
    let q := e.symm ⟨y, hy⟩
    exact ⟨q.val, q.property, (he q).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
  · rintro ⟨q, hq, rfl⟩
    change F (q.1.val, q.2.val) ∈ Y
    rw [← he ⟨q, hq⟩]
    exact (e ⟨q, hq⟩).property

end DifferentialGeometry.Manifold.BoundaryCollar
