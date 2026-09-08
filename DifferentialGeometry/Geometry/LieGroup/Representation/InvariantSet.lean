import DifferentialGeometry.Geometry.LieGroup.Representation
import DifferentialGeometry.Analysis.ODE.Nagumo

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace ContRepresentation

section TangentCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem mvfderiv_one_mem_posTangentConeAt (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hC : ∀ g, MapsTo (ρ g) C C) {w : W} (hw : w ∈ C)
    (U : GroupLieAlgebra I G) :
    mvfderiv I (fun g => ρ g) 1 U w ∈ posTangentConeAt C w := by
  let f : G → W := fun g => ρ g w
  have hf : MDifferentiableAt I 𝓘(ℝ, W) f 1 := hρ.clm_apply mdifferentiableAt_const
  let c := extChartAt I (1 : G) (1 : G)
  let F : E → W := fun u => f ((extChartAt I (1 : G)).symm u)
  have hF : HasFDerivAt F (show E →L[ℝ] W from mvfderiv I f 1) c := by
    have h := hf.hasMFDerivAt.2
    have h' : HasFDerivWithinAt F (mfderiv I 𝓘(ℝ, W) f 1) (Set.range I) c := by
      convert! h using 1
    rw [I.range_eq_univ] at h'
    convert! h'.hasFDerivAt_of_univ using 1
  let v : E := U
  let γ : ℝ → W := fun t => F (c + t • v)
  have hγ : HasDerivAt γ (mvfderiv I f 1 U) 0 := by
    have hline : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
    have hF' : HasFDerivAt F (show E →L[ℝ] W from mvfderiv I f 1)
        (c + (0 : ℝ) • v) := by
      rw [zero_smul, add_zero]
      exact hF
    exact hF'.comp_hasDerivAt 0 hline
  have hzero : γ 0 = w := by
    change ρ ((extChartAt I (1 : G)).symm (c + (0 : ℝ) • v)) w = w
    rw [zero_smul, add_zero]
    change ρ ((extChartAt I (1 : G)).symm (extChartAt I (1 : G) (1 : G))) w = w
    rw [(extChartAt I (1 : G)).left_inv (mem_extChartAt_source (1 : G)), map_one]
    rfl
  have hmem := DifferentialGeometry.Analysis.ODE.HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right
    hγ (Filter.Eventually.of_forall (fun t => hC _ hw))
  rw [hzero] at hmem
  have heval := congrArg (fun L => L U)
    (hρ.mvfderiv_clm_apply (mdifferentiableAt_const (c := w)))
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at heval
  exact heval ▸ hmem

end TangentCone

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

private theorem mapsTo_of_isIntegralCurveOn_mvfderiv_left (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) {a b : ℝ}
    (U : ℝ → GroupLieAlgebra I G) (hU : ContinuousOn U (Icc a b))
    {z : ℝ → W}
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z
      (mvfderiv I (fun g => ρ g) 1 (U t) (z t)) (Icc a b) t)
    (ha : z a ∈ C) : MapsTo z (Icc a b) C := by
  let A : ℝ → W →L[ℝ] W := fun t => mvfderiv I (fun g => ρ g) 1 (U t)
  have hA : ContinuousOn A (Icc a b) :=
    (mvfderiv I (fun g => ρ g) 1).continuous.comp_continuousOn hU
  obtain ⟨L, hLpos, hL⟩ := (isCompact_Icc.image_of_continuousOn hA).isBounded.exists_pos_norm_le
  apply DifferentialGeometry.Analysis.ODE.nagumo_mapsTo_of_lipschitz
    ⟨z a, ha⟩ hclosed hconvex
    (fun t w hw => ρ.mvfderiv_one_mem_posTangentConeAt hρ hC hw (U t))
    ⟨L, hLpos.le⟩ ?_ hz ha
  intro t ht
  exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (hL _ ⟨t, mem_Icc_of_Ico ht, rfl⟩)

private theorem mapsTo_of_isIntegralCurveOn_mvfderiv_right (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) {a b : ℝ}
    (U : ℝ → GroupLieAlgebra I G) (hU : ContinuousOn U (Icc a b))
    {z : ℝ → W}
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z
      (mvfderiv I (fun g => ρ g) 1 (U t) (z t)) (Icc a b) t)
    (hb : z b ∈ C) : MapsTo z (Icc a b) C := by
  have hneg : MapsTo (fun t : ℝ => -t) (Icc (-b) (-a)) (Icc a b) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hU' : ContinuousOn (fun t => -U (-t)) (Icc (-b) (-a)) :=
    (hU.comp continuous_neg.continuousOn hneg).neg
  have hz' : ∀ t ∈ Icc (-b) (-a), HasDerivWithinAt (fun s => z (-s))
      (mvfderiv I (fun g => ρ g) 1 (-U (-t)) (z (-t))) (Icc (-b) (-a)) t := by
    intro t ht
    have hd := (hz (-t) (hneg ht)).scomp t (hasDerivWithinAt_neg t (Icc (-b) (-a))) hneg
    simpa only [Function.comp_def, map_neg, neg_apply, neg_one_smul] using hd
  have hm := ρ.mapsTo_of_isIntegralCurveOn_mvfderiv_left hρ hclosed hconvex hC
    (fun t => -U (-t)) hU' hz' (by simpa only [neg_neg] using hb)
  intro t ht
  have hmt := hm (show -t ∈ Icc (-b) (-a) from ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩)
  simpa only [neg_neg] using hmt

theorem mapsTo_of_isIntegralCurveOn_mvfderiv (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (U : ℝ → GroupLieAlgebra I G) (hU : ContinuousOn U (Icc a b))
    {z : ℝ → W}
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z
      (mvfderiv I (fun g => ρ g) 1 (U t) (z t)) (Icc a b) t)
    (hinit : z t₀ ∈ C) : MapsTo z (Icc a b) C := by
  have hleft : Icc a t₀ ⊆ Icc a b := fun _ ht => ⟨ht.1, ht.2.trans ht₀.2⟩
  have hright : Icc t₀ b ⊆ Icc a b := fun _ ht => ⟨ht₀.1.trans ht.1, ht.2⟩
  have hl := ρ.mapsTo_of_isIntegralCurveOn_mvfderiv_right hρ hclosed hconvex hC U
    (hU.mono hleft) (fun t ht => (hz t (hleft ht)).mono hleft) hinit
  have hr := ρ.mapsTo_of_isIntegralCurveOn_mvfderiv_left hρ hclosed hconvex hC U
    (hU.mono hright) (fun t ht => (hz t (hright ht)).mono hright) hinit
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hl ⟨ht.1, h⟩
  · exact hr ⟨h, ht.2⟩

theorem mem_iff_of_isIntegralCurveOn_mvfderiv (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) {a b t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (U : ℝ → GroupLieAlgebra I G) (hU : ContinuousOn U (Icc a b))
    {z : ℝ → W}
    (hz : ∀ s ∈ Icc a b, HasDerivWithinAt z
      (mvfderiv I (fun g => ρ g) 1 (U s) (z s)) (Icc a b) s) :
    z t ∈ C ↔ z t₀ ∈ C := by
  constructor
  · intro h
    exact ρ.mapsTo_of_isIntegralCurveOn_mvfderiv hρ hclosed hconvex hC ht U hU hz h ht₀
  · intro h
    exact ρ.mapsTo_of_isIntegralCurveOn_mvfderiv hρ hclosed hconvex hC ht₀ U hU hz h ht

end Hilbert

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem mapsTo_of_isIntegralCurveOn_mvfderiv_of_finiteDimensional
    (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (U : ℝ → GroupLieAlgebra I G) (hU : ContinuousOn U (Icc a b))
    {z : ℝ → W}
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z
      (mvfderiv I (fun g => ρ g) 1 (U t) (z t)) (Icc a b) t)
    (hinit : z t₀ ∈ C) : MapsTo z (Icc a b) C := by
  let e := toEuclidean (E := W)
  let L := e.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let ρ' : ContRepresentation ℝ G (EuclideanSpace ℝ (Fin (Module.finrank ℝ W))) :=
    .ofMonoidHom (e.conjContinuousAlgEquiv.toAlgEquiv.toMonoidHom.comp ρ.toMonoidHom)
  have hρ' : MDifferentiableAt I 𝓘(ℝ, _ →L[ℝ] _) (fun g => ρ' g) 1 :=
    L.mdifferentiableAt.comp 1 hρ
  have hd (v : GroupLieAlgebra I G) :
      mvfderiv I (fun g => ρ' g) 1 v = L (mvfderiv I (fun g => ρ g) 1 v) := by
    change mvfderiv I (fun g => L (ρ g)) 1 v = _
    have h := congrArg (fun D => D v)
      ((mdifferentiableAt_const (c := L)).mvfderiv_clm_apply hρ)
    simpa only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
      ContinuousLinearMap.comp_apply] using h
  have hclosed' : IsClosed (e '' C) := e.toHomeomorph.isClosedMap _ hclosed
  have hconvex' : Convex ℝ (e '' C) := hconvex.linear_image e.toLinearEquiv.toLinearMap
  have hC' : ∀ g, MapsTo (ρ' g) (e '' C) (e '' C) := by
    intro g y hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨ρ g x, hC g hx, ?_⟩
    change e (ρ g x) = e (ρ g (e.symm (e x)))
    rw [e.symm_apply_apply]
  have hz' : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => e (z s))
      (mvfderiv I (fun g => ρ' g) 1 (U t) (e (z t))) (Icc a b) t := by
    intro t ht
    rw [hd]
    have h := (e.toContinuousLinearMap.hasFDerivAt (x := z t)).comp_hasDerivWithinAt t (hz t ht)
    change HasDerivWithinAt (fun s => e (z s))
      (e ((mvfderiv I (fun g => ρ g) 1 (U t)) (e.symm (e (z t))))) (Icc a b) t
    rw [e.symm_apply_apply]
    exact h
  have hm := ρ'.mapsTo_of_isIntegralCurveOn_mvfderiv hρ' hclosed' hconvex' hC'
    ht₀ U hU hz' ⟨z t₀, hinit, rfl⟩
  intro t ht
  obtain ⟨x, hx, heq⟩ := hm ht
  rwa [e.injective heq] at hx

theorem mem_iff_of_isIntegralCurveOn_mvfderiv_of_finiteDimensional
    (ρ : ContRepresentation ℝ G W)
    (hρ : MDifferentiableAt I 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) {a b t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (U : ℝ → GroupLieAlgebra I G) (hU : ContinuousOn U (Icc a b))
    {z : ℝ → W}
    (hz : ∀ s ∈ Icc a b, HasDerivWithinAt z
      (mvfderiv I (fun g => ρ g) 1 (U s) (z s)) (Icc a b) s) :
    z t ∈ C ↔ z t₀ ∈ C := by
  constructor
  · intro h
    exact ρ.mapsTo_of_isIntegralCurveOn_mvfderiv_of_finiteDimensional
      hρ hclosed hconvex hC ht U hU hz h ht₀
  · intro h
    exact ρ.mapsTo_of_isIntegralCurveOn_mvfderiv_of_finiteDimensional
      hρ hclosed hconvex hC ht₀ U hU hz h ht

end FiniteDimensional

end ContRepresentation
