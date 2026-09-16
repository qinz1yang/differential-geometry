import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion
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

open Classical in
theorem exists_complementary_frontier_arcs_of_isPLBall_union
    {C D : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) (hD : IsPLBall 2 D) (hI : IsPLBall 1 (C ∩ D))
    (hIC : C ∩ D ⊆ frontier C) (hID : C ∩ D ⊆ frontier D) :
    ∃ p q : EuclideanSpace ℝ (Fin 2), ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      Schoenflies.IsCutPair (frontier C) p q (C ∩ D) A ∧
      Schoenflies.IsCutPair (frontier D) p q (C ∩ D) B ∧
      IsPLBall 1 A ∧ IsPLBall 1 B ∧ frontier (C ∪ D) = A ∪ B := by
  obtain ⟨p, q, hIpq⟩ := hI.isArc.exists_isArcBetween
  obtain ⟨A, hcutC, -, hA⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hC.isPLSphere_frontier hIpq hIC
  obtain ⟨B, hcutD, -, hB⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hD.isPLSphere_frontier hIpq hID
  have hCclosed : IsClosed C := hC.isPolyhedron.isClosed
  have hDclosed : IsClosed D := hD.isPolyhedron.isClosed
  have hAfront : A ⊆ frontier (C ∪ D) := by
    have hAdiff : A \ {p, q} ⊆ frontier (C ∪ D) := by
      intro x hx
      have hxfrontC : x ∈ frontier C := hcutC.snd_subset hx.1
      have hxC : x ∈ C := hCclosed.frontier_subset hxfrontC
      have hxnotI : x ∉ C ∩ D := by
        intro hxI
        have hxpair : x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [← hcutC.inter_eq]
          exact ⟨hxI, hx.1⟩
        exact hx.2 hxpair
      have hxnotD : x ∉ D := fun hxD => hxnotI ⟨hxC, hxD⟩
      apply (mem_frontier_iff_notMem_interior
        (show x ∈ C ∪ D from Or.inl hxC)).mpr
      intro hxint
      have hxside : x ∈ D ∪ interior C := by
        apply hDclosed.interior_union_left
        rwa [union_comm]
      rcases hxside with hxD | hxintC
      · exact hxnotD hxD
      · exact (mem_frontier_iff_notMem_interior hxC).mp hxfrontC hxintC
    calc
      A ⊆ closure (A \ {p, q}) := hA.subset_closure_sdiff_finite (Set.toFinite {p, q})
      _ ⊆ closure (frontier (C ∪ D)) := closure_mono hAdiff
      _ = frontier (C ∪ D) := isClosed_frontier.closure_eq
  have hBfront : B ⊆ frontier (C ∪ D) := by
    have hBdiff : B \ {p, q} ⊆ frontier (C ∪ D) := by
      intro x hx
      have hxfrontD : x ∈ frontier D := hcutD.snd_subset hx.1
      have hxD : x ∈ D := hDclosed.frontier_subset hxfrontD
      have hxnotI : x ∉ C ∩ D := by
        intro hxI
        have hxpair : x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [← hcutD.inter_eq]
          exact ⟨hxI, hx.1⟩
        exact hx.2 hxpair
      have hxnotC : x ∉ C := fun hxC => hxnotI ⟨hxC, hxD⟩
      apply (mem_frontier_iff_notMem_interior
        (show x ∈ C ∪ D from Or.inr hxD)).mpr
      intro hxint
      have hxside : x ∈ C ∪ interior D := hCclosed.interior_union_left hxint
      rcases hxside with hxC | hxintD
      · exact hxnotC hxC
      · exact (mem_frontier_iff_notMem_interior hxD).mp hxfrontD hxintD
    calc
      B ⊆ closure (B \ {p, q}) := hB.subset_closure_sdiff_finite (Set.toFinite {p, q})
      _ ⊆ closure (frontier (C ∪ D)) := closure_mono hBdiff
      _ = frontier (C ∪ D) := isClosed_frontier.closure_eq
  have hinterAB : A ∩ B = ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Subset.antisymm
    · intro x hx
      have hxC : x ∈ C := hCclosed.frontier_subset (hcutC.snd_subset hx.1)
      have hxD : x ∈ D := hDclosed.frontier_subset (hcutD.snd_subset hx.2)
      rw [← hcutC.inter_eq]
      exact ⟨⟨hxC, hxD⟩, hx.1⟩
    · intro x hx
      have hxA : x ∈ (C ∩ D) ∩ A := hcutC.inter_eq.symm.subset hx
      have hxB : x ∈ (C ∩ D) ∩ B := hcutD.inter_eq.symm.subset hx
      exact ⟨hxA.2, hxB.2⟩
  have hcutAB : Schoenflies.IsCutPair (A ∪ B) p q A B :=
    ⟨hcutC.snd, hcutD.snd, rfl, hinterAB⟩
  have hABsphere : IsPLSphere 1 (A ∪ B) :=
    isPLSphere_one_of_isCutPair hcutAB hA hB
  have hCDball : IsPLBall 2 (C ∪ D) :=
    (isPLBall_union_and_finite_frontier_inter hC hD hI hIC hID).1
  have hfrontierEq : A ∪ B = frontier (C ∪ D) :=
    DifferentialGeometry.Topology.PlanarJordan.eq_of_isJordanCurve_of_subset
      (isJordanCurve_of_isPLSphere_one hABsphere)
      (isJordanCurve_of_isPLSphere_one hCDball.isPLSphere_frontier)
      (union_subset hAfront hBfront)
  exact ⟨p, q, A, B, hcutC, hcutD, hA, hB, hfrontierEq.symm⟩

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
      EqOn D (D₁ ∘ f₁) P ∧ EqOn D (D₂ ∘ f₂) Q ∧
      ∃ p q : EuclideanSpace ℝ (Fin 2), ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
        Schoenflies.IsCutPair (frontier P) p q (P ∩ Q) R ∧
        Schoenflies.IsCutPair (frontier Q) p q (P ∩ Q) T ∧
        IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier D.domain = R ∪ T := by
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
    ?_, ?_, hf₁, hf₂, hinter.symm ▸ hf₂f₁, ?_, ?_, ?_⟩
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
  · obtain ⟨p', q', R, T, hcutK, hcutL, hR, hT, hfront⟩ :=
      exists_complementary_frontier_arcs_of_isPLBall_union hK hL
        (hinter.symm ▸ hS) (hinter.symm ▸ hSfrontK) (hinter.symm ▸ hSfrontL)
    exact ⟨p', q', R, T, hcutK, hcutL, hR, hT, hfront⟩

end SingularTwoCell

end DifferentialGeometry.Topology.PiecewiseLinear
