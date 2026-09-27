import DifferentialGeometry.Topology.Ehresmann.ProductEnds
import DifferentialGeometry.Topology.Manifold.ProductHalfSpaceBoundary
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev CI := (𝓡 2).prod (𝓡∂ 1)

private local instance : DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
    (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) CI :=
  productHalfSpaceBoundaryModel

private theorem injective_mfderiv_of_smooth_partial_equiv
    (e : PartialEquiv (S2 × unitInterval) E3) (hes : e.source = univ)
    (he : ContMDiff CI (𝓡 3) ∞ e) (hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target)
    (q : S2 × unitInterval) : Injective (mfderiv CI (𝓡 3) e q) := by
  have hcomp : e.symm ∘ e = id := funext (fun p => e.left_inv (hes ▸ mem_univ p))
  have hd := mfderivWithin_comp q
    (hei.mdifferentiableOn (by decide) (e q) (e.map_source (hes ▸ mem_univ q)))
    ((he.mdifferentiable (by decide) q).mdifferentiableWithinAt (s := univ))
    (fun p _ => e.map_source (hes ▸ mem_univ p)) (uniqueMDiffWithinAt_univ CI)
  rw [hcomp,mfderivWithin_univ,mfderiv_id,mfderivWithin_univ] at hd
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 3) CI e.symm e.target (e q)) hvw
  rw [← ContinuousLinearMap.comp_apply,← hd,← ContinuousLinearMap.comp_apply,← hd] at h
  exact h

theorem exists_parametrized_sphere_annulus_of_smooth_partial_equiv
    (e : PartialEquiv (S2 × unitInterval) E3) (hes : e.source = univ)
    (he : ContMDiff CI (𝓡 3) ∞ e) (hei : ContMDiffOn (𝓡 3) CI ∞ e.symm e.target)
    (e₀ e₁ : S2 → E3)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier e.target = range e₀ ∪ range e₁) :
    ∃ Ψ : Diffeomorph CI CI (S2 × unitInterval) (S2 × unitInterval) ∞,
      ∃ η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
        (∀ p : S2, e (Ψ (p,0)) = e₀ p) ∧
        ∀ p : S2, e (Ψ (η p,1)) = e₁ p := by
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  have hinj := e.injective_of_source_eq_univ hes
  have hclosed := he.continuous.isClosedEmbedding hinj
  have hder := injective_mfderiv_of_smooth_partial_equiv e hes he hei
  have hrange : range e = e.target := by
    rw [← image_univ,← hes,e.image_source_eq_target]
  have hbdy : e '' CI.boundary (S2 × unitInterval) = range e₀ ∪ range e₁ := by
    rw [DifferentialGeometry.Geometry.Boundary.image_boundary_eq_frontier_of_fullRank_closedEmbedding
      e he hclosed hder (by simp),hrange,hfront]
  obtain ⟨D,h₀,h₁⟩ := Ehresmann.exists_intervalProduct_with_labeled_ends
    (Diffeomorph.refl CI (S2 × unitInterval) ∞) e he.continuous hinj
    (range e₀) (range e₁) (isPreconnected_range he₀.contMDiff.continuous)
    (isPreconnected_range he₁.contMDiff.continuous) hbdy
  have hsmooth (t : unitInterval) :
      ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : S2 => e (D (p,t))) :=
    he.comp (D.contMDiff.comp (contMDiff_id.prodMk contMDiff_const))
  have hslice (t : unitInterval) :
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p : S2 => e (D (p,t))) := by
    refine ⟨isImmersion_of_injective_mfderiv (by decide) (hsmooth t) ?_,
      (hsmooth t).continuous.isClosedEmbedding (fun p q h => congrArg Prod.fst (D.injective (hinj h)))
        |>.isEmbedding⟩
    intro p
    have hD : Injective (mfderiv CI CI D (p,t)) :=
      (D.isLocalDiffeomorph (p,t)).mfderivToContinuousLinearEquiv (by decide) |>.injective
    have hι : Injective (mfderiv (𝓡 2) CI (fun q : S2 => (q,t)) p) := by
      rw [mfderiv_prod_left]
      exact fun _ _ h => congrArg Prod.fst h
    have hinc : ContMDiff (𝓡 2) CI ∞ (fun q : S2 => (q,t)) :=
      contMDiff_id.prodMk contMDiff_const
    have hdiff : MDifferentiableAt (𝓡 2) CI (D ∘ fun q : S2 => (q,t)) p :=
      (D.contMDiff.comp hinc).mdifferentiableAt (by decide)
    have hde := mfderiv_comp p (he.mdifferentiableAt (by decide)) hdiff
    have hdD := mfderiv_comp p (D.contMDiff.mdifferentiableAt (by decide))
      (hinc.mdifferentiableAt (by decide))
    change Injective (mfderiv (𝓡 2) (𝓡 3) (e ∘ D ∘ fun q : S2 => (q,t)) p)
    rw [hde,hdD]
    exact (hder _).comp (hD.comp hι)
  let η₀ := he₀.diffeomorphOfRangeEq (hslice 0) h₀.symm
  let η₁ := he₁.diffeomorphOfRangeEq (hslice 1) h₁.symm
  let Ψ := (η₀.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)).trans D
  let η := η₁.trans η₀.symm
  refine ⟨Ψ,η,?_,?_⟩
  · intro p
    exact he₀.comp_diffeomorphOfRangeEq (hslice 0) h₀.symm p
  · intro p
    change e (D (η₀ (η₀.symm (η₁ p)),1)) = e₁ p
    rw [η₀.apply_symm_apply]
    exact he₁.comp_diffeomorphOfRangeEq (hslice 1) h₁.symm p

end DifferentialGeometry.Topology.Manifold
