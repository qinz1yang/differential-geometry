import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem IsPLOn.comp_isPiecewiseAffineOn
    {n m p : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    {f : EuclideanSpace ℝ (Fin n) → M}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n)}
    {P : Set (EuclideanSpace ℝ (Fin n))} {Q : Set (EuclideanSpace ℝ (Fin p))}
    (hf : IsPLOn n m f P) (hg : IsPiecewiseAffineOn g Q) (hmap : MapsTo g Q P) :
    IsPLOn p m (f ∘ g) Q := by
  intro x hx
  have hfx :=
    (StructureGroupoid.liftPropWithinAt_self_source).mp
      (hf (g x) (hmap hx))
  apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
  refine ⟨hfx.1.comp (hg x hx).continuousWithinAt hmap, ?_⟩
  have hcomp := hfx.2.comp (hg x hx)
  have hQP : Q ∩ g ⁻¹' P = Q := inter_eq_left.mpr hmap
  rw [hQP] at hcomp
  exact IsPiecewiseAffineWithinAt.congr hcomp fun _ _ => rfl

open Classical in
private theorem isPLOn_piecewise_of_isClosed
    {n m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    {f g : EuclideanSpace ℝ (Fin n) → M}
    {P Q : Set (EuclideanSpace ℝ (Fin n))}
    (hf : IsPLOn n m f P) (hg : IsPLOn n m g Q)
    (hP : IsClosed P) (hQ : IsClosed Q) (hfg : EqOn f g (P ∩ Q)) :
    IsPLOn n m (P.piecewise f g) (P ∪ Q) := by
  let h := P.piecewise f g
  have hPf : EqOn h f P := P.piecewise_eqOn f g
  have hQg : EqOn h g Q := by
    intro x hx
    by_cases hxP : x ∈ P
    · change P.piecewise f g x = g x
      rw [P.piecewise_eq_of_mem f g hxP, hfg ⟨hxP, hx⟩]
    · change P.piecewise f g x = g x
      exact P.piecewise_eq_of_notMem f g hxP
  intro x hx
  by_cases hxP : x ∈ P
  · have hhP : IsPLWithinAt n m h P x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
        (hf x hxP) hPf hxP
    by_cases hxQ : x ∈ Q
    · have hhQ : IsPLWithinAt n m h Q x :=
        piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
          (hg x hxQ) hQg hxQ
      have hhP' :=
        (StructureGroupoid.liftPropWithinAt_self_source).mp hhP
      have hhQ' :=
        (StructureGroupoid.liftPropWithinAt_self_source).mp hhQ
      apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
      exact ⟨hhP'.1.union hhQ'.1, hhP'.2.union hhQ'.2⟩
    · have hset : (fun y => y ∈ P) =ᶠ[𝓝 x] (fun y => y ∈ P ∪ Q) := by
        filter_upwards [hQ.isOpen_compl.mem_nhds hxQ] with y hy
        apply propext
        exact ⟨Or.inl, fun h => h.resolve_right hy⟩
      exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hhP
  · have hxQ : x ∈ Q := hx.resolve_left hxP
    have hhQ : IsPLWithinAt n m h Q x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
        (hg x hxQ) hQg hxQ
    have hset : (fun y => y ∈ Q) =ᶠ[𝓝 x] (fun y => y ∈ P ∪ Q) := by
      filter_upwards [hP.isOpen_compl.mem_nhds hxP] with y hy
      apply propext
      exact ⟨Or.inr, fun h => h.resolve_left hy⟩
    exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hhQ

namespace SingularTwoCell

open Classical in
theorem exists_glue_of_isPLHomeomorphOn_boundary_arc
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D₁ D₂ : SingularTwoCell M)
    {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hAfront : A ⊆ frontier D₁.domain)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A B) (hBfront : B ⊆ frontier D₂.domain)
    (hcompat : EqOn D₁ (D₂ ∘ g) A) :
    ∃ (D : SingularTwoCell M) (P Q : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ IsPLBall 2 (P ∪ Q) ∧
      D.domain = P ∪ Q ∧ IsPLBall 1 (P ∩ Q) ∧
      P ∩ Q ⊆ frontier P ∧ P ∩ Q ⊆ frontier Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧
      IsPLHomeomorphOn f₂ Q D₂.domain ∧
      EqOn f₂ (g ∘ f₁) (P ∩ Q) ∧
      EqOn D (D₁ ∘ f₁) P ∧ EqOn D (D₂ ∘ f₂) Q := by
  obtain ⟨K, L, hKfin, hLfin, hK, hL, hKL, p, q, hpq, hinter, hSK, hSL⟩ :=
    exists_isPLBall_pair_with_segment_inter
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let S := segment ℝ p q
  have hS : IsPLBall 1 S := isPLBall_segment hpq
  have hSarc : Schoenflies.IsArcBetween S p q := Schoenflies.isArcBetween_segment hpq
  obtain ⟨r, s, hArs⟩ := hA.isArc.exists_isArcBetween
  obtain ⟨a, ha, -, -⟩ :=
    exists_isPLHomeomorphOn_of_isArcBetween hS hA hSarc hArs
  have hSfrontK : S ⊆ frontier K.space := by
    rw [← boundaryComplex_space_eq_of_isPLBall_of_frontier K hK hK.isPLSphere_frontier rfl]
    exact hSK
  have hSfrontL : S ⊆ frontier L.space := by
    rw [← boundaryComplex_space_eq_of_isPLBall_of_frontier L hL hL.isPLSphere_frontier rfl]
    exact hSL
  obtain ⟨b₁, hb₁, hb₁a⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    hK.isPLSphere_frontier D₁.isPLSphere_frontier hSarc hSfrontK ha hAfront
  obtain ⟨f₁, hf₁, hf₁b⟩ := exists_isPLHomeomorphOn_of_frontier hK D₁.isPLBall_domain hb₁
  have hf₁a : EqOn f₁ a S := (hf₁b.mono hSfrontK).trans hb₁a
  have hga : IsPLHomeomorphOn (g ∘ a) S B := ha.trans hg
  obtain ⟨b₂, hb₂, hb₂ga⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    hL.isPLSphere_frontier D₂.isPLSphere_frontier hSarc hSfrontL hga hBfront
  obtain ⟨f₂, hf₂, hf₂b⟩ := exists_isPLHomeomorphOn_of_frontier hL D₂.isPLBall_domain hb₂
  have hf₂ga : EqOn f₂ (g ∘ a) S := (hf₂b.mono hSfrontL).trans hb₂ga
  have hf₂f₁ : EqOn f₂ (g ∘ f₁) S := by
    intro x hx
    exact (hf₂ga hx).trans (congrArg g (hf₁a hx).symm)
  let F₁ := D₁.toFun ∘ f₁
  let F₂ := D₂.toFun ∘ f₂
  have hF₁ : IsPLOn 2 3 F₁ K.space :=
    D₁.isPLOn.comp_isPiecewiseAffineOn hf₁.isPiecewiseAffineOn hf₁.bijOn.mapsTo
  have hF₂ : IsPLOn 2 3 F₂ L.space :=
    D₂.isPLOn.comp_isPiecewiseAffineOn hf₂.isPiecewiseAffineOn hf₂.bijOn.mapsTo
  have hFcompat : EqOn F₁ F₂ (K.space ∩ L.space) := by
    rw [hinter]
    intro x hx
    change D₁ (f₁ x) = D₂ (f₂ x)
    rw [hf₂f₁ hx]
    exact hcompat (hf₁a hx ▸ ha.bijOn.mapsTo hx)
  let F := K.space.piecewise F₁ F₂
  have hF : IsPLOn 2 3 F (K.space ∪ L.space) :=
    isPLOn_piecewise_of_isClosed hF₁ hF₂ hK.isPolyhedron.isClosed
      hL.isPolyhedron.isClosed hFcompat
  let D : SingularTwoCell M :=
    { domain := K.space ∪ L.space
      isPLBall_domain := hKL
      toFun := F
      isPLOn := hF }
  refine ⟨D, K.space, L.space, f₁, f₂, hK, hL, hKL, rfl, hinter.symm ▸ hS,
    ?_, ?_, hf₁, hf₂, hinter.symm ▸ hf₂f₁, ?_, ?_⟩
  · rw [hinter]
    exact hSfrontK
  · rw [hinter]
    exact hSfrontL
  · exact K.space.piecewise_eqOn F₁ F₂
  · intro x hx
    by_cases hxK : x ∈ K.space
    · rw [show D x = F₁ x from K.space.piecewise_eq_of_mem F₁ F₂ hxK]
      exact hFcompat ⟨hxK, hx⟩
    · exact K.space.piecewise_eq_of_notMem F₁ F₂ hxK

end SingularTwoCell

end DifferentialGeometry.Topology.PiecewiseLinear
