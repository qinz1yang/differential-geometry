import DifferentialGeometry.Topology.VectorField.CollarPullback
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ClosedStripDiffeomorph
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Restriction

set_option autoImplicit false
open Set Function Bundle Manifold TopologicalSpace Topology
open scoped ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
noncomputable section
namespace Poincare.VectorField

theorem exists_nonvanishing_boundary_collar_pullback
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M))
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x)
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hzero : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, V p.val ≠ 0) :
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
              (∀ q : S, (e q : M) = c q.val) ∧
              let W := _root_.VectorField.mpullback
                ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
                (𝓡∂ (n + 1)) e (fun y : Y => V y.val)
              ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
                ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1)).tangent ∞
                (fun q => (⟨q, W q⟩ : TangentBundle
                  ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1)) S)) ∧
              ∀ q : S, W q ≠ 0 := by
  obtain ⟨ε, hε, c, hc, hcs, hc0, hci, δ₀, hδ₀, hδ₀ε, Y₀, hKY₀, hY₀, e₀, he₀⟩ :=
    Poincare.Manifold.BoundaryCollar.exists_closed_boundary_collar_diffeomorph hK
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let J := HasSmoothBoundary.boundaryModel I
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  obtain ⟨_, hz, _, δ, hδ, hδε, hS, hn⟩ := exists_nonvanishing_collar_pullback_strip
    (J := J) (I := I) c _ Y₀ e₀ he₀ (fun _ => hδ₀) V hV.contMDiffOn
    (fun p => by change (V (c _) : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0; rw [hc0 p]; exact hzero p)
  let S : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  obtain ⟨Y, hYY₀, _, e, he, _⟩ := Poincare.Manifold.Diffeomorph.exists_restrict_opens e₀ S hS
  have hec (q : S) : (e q : M) = c q.val := (he q).trans (he₀ _)
  have hY : (Y : Set M) = c '' {q | q.2.val < δ} := by
    ext y
    constructor
    · intro hy
      let q := e.symm ⟨y, hy⟩
      exact ⟨q.val, q.property, (hec q).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
    · rintro ⟨q, hq, rfl⟩
      rw [← hec ⟨q, hq⟩]
      exact (e ⟨q, hq⟩).property
  have hKY : I.boundary M ⊆ Y := by
    intro x hx
    rw [hY]
    exact ⟨(⟨x, hx⟩, ⟨0, ⟨le_rfl, hε.le⟩⟩), hδ, hc0 ⟨x, hx⟩⟩
  refine ⟨ε, hε, c, hc, hcs, hc0, hci, δ, hδ, hδε, Y, hKY, hY, e, hec, ?_, ?_⟩
  · have hVr := contMDiff_tangentSection_restrict_opens Y hV.contMDiffOn
    intro q
    exact contMDiffAt_mpullback_partialDiffeomorph e.toPartialDiffeomorph (by simp)
      (by trivial) (hVr (e q))
  · intro q hh
    have hVz := (mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) q).mp hh
    have hVcz : V (c q.val) = 0 := by
      change (V ((e q).val) : EuclideanSpace ℝ (Fin (n + 1))) = 0 at hVz
      rw [hec q] at hVz
      exact hVz
    exact hn ⟨q.val, hS q.property⟩ q.property ((hz _).mpr hVcz)

end Poincare.VectorField
