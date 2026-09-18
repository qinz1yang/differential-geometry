import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordFourArcs

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_image
    {Q : Type*} [TopologicalSpace Q] {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {p' q' u' v' : Q} (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {f : Q → X} (hf : Continuous f) {x : X}
    (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (hL : ¬loopClassMeets γ x N)
    (hpair : (f u' = f p' ∧ f v' = f q') ∨ (f u' = f q' ∧ f v' = f p')) :
    (∃ (a b : X) (σ υ : Path a b) (τ φ : Path b a),
        (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧ (∀ t, υ t = f (υ₀ t)) ∧
        (∀ t, φ t = f (φ₀ t)) ∧
        (¬loopClassMeets (pathToCircle (σ.trans υ.symm)) x N ∨
          ¬loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) x N)) ∨
      (∃ (a b : X) (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a),
        (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧ (∀ t, υ t = f (υ₀ t)) ∧
        (∀ t, φ t = f (φ₀ t)) ∧
        (¬loopClassMeets (pathToCircle (σ.trans υ)) x N ∨
          ¬loopClassMeets (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) x N)) := by
  rcases hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · refine Or.inl ⟨f p', f q', σ₀.map hf, (υ₀.map hf).cast hu.symm hv.symm,
      (τ₀.map hf).cast rfl hu.symm, (φ₀.map hf).cast hv.symm rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing
      σ₀ τ₀ υ₀ φ₀ ev hev (PathConnectedSpace.somePath x (f p'))
      (PathConnectedSpace.somePath (f p') (f q'))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) γ hγ N hL
  · refine Or.inr ⟨f p', f q', σ₀.map hf, (τ₀.map hf).cast rfl hu.symm,
      (υ₀.map hf).cast hu.symm hv.symm, (φ₀.map hf).cast hv.symm rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving
      σ₀ τ₀ υ₀ φ₀ ev hev (PathConnectedSpace.somePath x (f p'))
      (PathConnectedSpace.somePath (f p') (f q'))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) γ hγ N hL

namespace NormalSystem

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem singularMap_mem_boundaryNeighborhood (S : NormalSystem E)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ frontier S.sourceComplex.space) :
    S.singularMap z ∈ (normalSystemBoundaryNeighborhood S.ambientComplex S.imageComplex
      S.loopComplex S.image_faces_subset_ambient).space := by
  obtain ⟨θ, hθ⟩ := S.boundaryParam.surjective ⟨z, hz⟩
  have hmem := (S.boundaryLoop θ).2
  rw [S.boundaryLoop_eq θ, hθ] at hmem
  exact hmem

omit [FiniteDimensional ℝ E] in
theorem not_loopClassMeets_boundaryLoop (S : NormalSystem E)
    [PathConnectedSpace S.boundaryNeighborhoodSpace] :
    ¬loopClassMeets S.boundaryLoop S.basepoint S.normalSubgroup := by
  have hclass : FreeLoop.conjugacyClass S.boundaryLoop S.basepoint =
      normalSystemLoopConjugacyClass S.basepoint S.boundaryLoop S.connector :=
    FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong S.connector S.boundaryBasedLoop
  intro hmeet
  exact S.loopClass_avoids_normal (hclass ▸ hmeet)

end NormalSystem

theorem NormalSystem.exists_boundary_word_loop_dichotomy_of_four_arcs
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) [PathConnectedSpace S.boundaryNeighborhoodSpace]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} (hdom : D.domain = S.sourceComplex.space)
    {p q u v : EuclideanSpace ℝ (Fin 2)} {p' q' u' v' : frontier D.domain}
    (hp' : (p' : EuclideanSpace ℝ (Fin 2)) = p) (hq' : (q' : EuclideanSpace ℝ (Fin 2)) = q)
    (hu' : (u' : EuclideanSpace ℝ (Fin 2)) = u) (hv' : (v' : EuclideanSpace ℝ (Fin 2)) = v)
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle ≃ₜ frontier D.domain)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    (hpair : (D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p))
    (hfactor : ∀ z ∈ frontier D.domain, ∀ w ∈ frontier D.domain,
      D z = D w → S.singularMap z = S.singularMap w)
    (hparam : ∀ θ, ((S.boundaryParam θ : EuclideanSpace ℝ (Fin 2))) =
      ((ev θ : EuclideanSpace ℝ (Fin 2)))) :
    (∃ (a b : S.boundaryNeighborhoodSpace) (σ υ : Path a b) (τ φ : Path b a),
        (∀ t, (σ t : E) = S.singularMap (σ₀ t)) ∧ (∀ t, (τ t : E) = S.singularMap (τ₀ t)) ∧
        (∀ t, (υ t : E) = S.singularMap (υ₀ t)) ∧ (∀ t, (φ t : E) = S.singularMap (φ₀ t)) ∧
        (¬loopClassMeets (pathToCircle (σ.trans υ.symm)) S.basepoint S.normalSubgroup ∨
          ¬loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) S.basepoint
            S.normalSubgroup)) ∨
      (∃ (a b : S.boundaryNeighborhoodSpace) (σ : Path a b) (τ : Path b b) (υ : Path b a)
          (φ : Path a a),
        (∀ t, (σ t : E) = S.singularMap (σ₀ t)) ∧ (∀ t, (τ t : E) = S.singularMap (τ₀ t)) ∧
        (∀ t, (υ t : E) = S.singularMap (υ₀ t)) ∧ (∀ t, (φ t : E) = S.singularMap (φ₀ t)) ∧
        (¬loopClassMeets (pathToCircle (σ.trans υ)) S.basepoint S.normalSubgroup ∨
          ¬loopClassMeets (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) S.basepoint
            S.normalSubgroup)) := by
  have : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  have := S.normal
  have hfr : frontier D.domain ⊆ S.sourceComplex.space := by
    rw [← hdom]
    exact D.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
  have hmem : ∀ z : frontier D.domain, S.singularMap z ∈
      (normalSystemBoundaryNeighborhood S.ambientComplex S.imageComplex S.loopComplex
        S.image_faces_subset_ambient).space := by
    intro z
    refine S.singularMap_mem_boundaryNeighborhood ?_
    rw [← hdom]
    exact z.2
  set f : frontier D.domain → S.boundaryNeighborhoodSpace :=
    fun z => ⟨S.singularMap z, hmem z⟩ with hfdef
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact (((isPiecewiseAffineOn_simplicialMap S.sourceComplex S.vertexMap).continuousOn).mono
      hfr).domRestrict
  have hfeq : ∀ z w : frontier D.domain, D z = D w → f z = f w := by
    intro z w hzw
    exact Subtype.ext (hfactor z z.2 w w.2 hzw)
  have hγ : ∀ θ, S.boundaryLoop θ = f (ev θ) := by
    intro θ
    refine Subtype.ext ?_
    rw [S.boundaryLoop_eq θ]
    exact congrArg S.singularMap (hparam θ)
  have hpair' : (f u' = f p' ∧ f v' = f q') ∨ (f u' = f q' ∧ f v' = f p') := by
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hfeq u' p' (by rw [hu', hp']; exact h1),
        hfeq v' q' (by rw [hv', hq']; exact h2)⟩
    · exact Or.inr ⟨hfeq u' q' (by rw [hu', hq']; exact h1),
        hfeq v' p' (by rw [hv', hp']; exact h2)⟩
  rcases not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_image σ₀ τ₀ υ₀ φ₀
    (fun θ => ev θ) hev hf S.boundaryLoop hγ S.normalSubgroup S.not_loopClassMeets_boundaryLoop
    hpair' with ⟨a, b, σ, υ, τ, φ, hσ, hτ, hυ, hφ, hdich⟩ |
      ⟨a, b, σ, τ, υ, φ, hσ, hτ, hυ, hφ, hdich⟩
  · exact Or.inl ⟨a, b, σ, υ, τ, φ, fun t => congrArg Subtype.val (hσ t),
      fun t => congrArg Subtype.val (hτ t), fun t => congrArg Subtype.val (hυ t),
      fun t => congrArg Subtype.val (hφ t), hdich⟩
  · exact Or.inr ⟨a, b, σ, τ, υ, φ, fun t => congrArg Subtype.val (hσ t),
      fun t => congrArg Subtype.val (hτ t), fun t => congrArg Subtype.val (hυ t),
      fun t => congrArg Subtype.val (hφ t), hdich⟩

end DifferentialGeometry.Topology.PiecewiseLinear
