import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.InverseBranch
import DifferentialGeometry.Geometry.Exponential.Trivialization

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem exists_ball_trivialization_source
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (hc : c ∈ e.baseSet) {W : Set (M × E)} (hW : IsOpen W) (hcW : (c, (0 : E)) ∈ W) :
    ∃ S : Set M, IsOpen S ∧ c ∈ S ∧ ∃ r : ℝ, 0 < r ∧
      S ×ˢ Metric.ball (0 : E) r ⊆ W ∩ e.target ∧
      MapsTo e.toOpenPartialHomeomorph.symm (S ×ˢ Metric.ball (0 : E) r) B.hom.source := by
  let Q := e.target ∩ e.toOpenPartialHomeomorph.symm ⁻¹' B.hom.source ∩ W
  have hQ : IsOpen Q := (e.toOpenPartialHomeomorph.symm.continuousOn.isOpen_inter_preimage
    e.open_target B.hom.open_source).inter hW
  have hcQ : (c, (0 : E)) ∈ Q := by
    refine ⟨⟨e.mk_mem_target.mpr hc, ?_⟩, hcW⟩
    change e.toOpenPartialHomeomorph.symm (c, (0 : E)) ∈ B.hom.source
    rw [← e.mk_symm hc, ← e.symmL_apply (R := ℝ) hc, map_zero]
    exact B.zero_mem
  have hnhds := hQ.mem_nhds hcQ
  rw [nhds_prod_eq] at hnhds
  obtain ⟨A, hA, T, hT, hAT⟩ := Filter.mem_prod_iff.mp hnhds
  obtain ⟨S, hSA, hS, hcS⟩ := mem_nhds_iff.mp hA
  obtain ⟨r, hr, hTr⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨S, hS, hcS, r, hr, ?_, ?_⟩
  · intro z hz
    have hzQ := hAT ⟨hSA hz.1, hTr hz.2⟩
    exact ⟨hzQ.2, hzQ.1.1⟩
  · intro z hz
    exact (hAT ⟨hSA hz.1, hTr hz.2⟩).1.2

private theorem isOpen_image_expMapIntrinsic_trivialization
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    {W : Set (M × E)} (hW : IsOpen W) (hWt : W ⊆ e.target)
    (hWB : MapsTo e.toOpenPartialHomeomorph.symm W B.hom.source) :
    IsOpen ((fun z : M × E => (z.1, expMapIntrinsic g hEnorm z.1
      (e.symmL ℝ z.1 z.2))) '' W) := by
  let A := e.toOpenPartialHomeomorph.symm.trans B.hom
  have hWA : W ⊆ A.source := fun z hz => ⟨hWt hz, hWB hz⟩
  have hEq : EqOn A (fun z : M × E => (z.1, expMapIntrinsic g hEnorm z.1
      (e.symmL ℝ z.1 z.2))) W := by
    intro z hz
    change B.hom (e.toOpenPartialHomeomorph.symm z) = _
    have hzbase : z.1 ∈ e.baseSet := e.mem_target.mp (hWt hz)
    have he : e.toOpenPartialHomeomorph.symm z =
        (⟨z.1, e.symmL ℝ z.1 z.2⟩ : TangentBundle I M) := by
      rw [← e.mk_symm hzbase, ← e.symmL_apply (R := ℝ) hzbase]
    calc
      B.hom (e.toOpenPartialHomeomorph.symm z) =
          diagExp (I := I) g hEnorm (e.toOpenPartialHomeomorph.symm z) :=
        B.hom_eq (hWB hz)
      _ = (z.1, expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 z.2)) := by
        rw [he]
        rfl
  rw [← image_congr hEq]
  exact A.isOpen_image_of_subset_source hW hWA

theorem exists_ball_trivialization_domain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (hc : c ∈ e.baseSet) {W : Set (M × E)} (hW : IsOpen W) (hcW : (c, (0 : E)) ∈ W) :
    ∃ S : Set M, IsOpen S ∧ c ∈ S ∧ ∃ r : ℝ, 0 < r ∧
      ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
        S ×ˢ Metric.ball (0 : E) r ⊆ W ∩ e.target ∧
        MapsTo e.toOpenPartialHomeomorph.symm (S ×ˢ Metric.ball (0 : E) r) B.hom.source ∧
        MapsTo B.inv V e.source ∧
        let F : M × E → M × M := fun z => (z.1, expMapIntrinsic g hEnorm z.1
          (e.symmL ℝ z.1 z.2))
        let R : M × M → M × E := fun z => (z.1, (e (B.inv z)).2)
        ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod I) ∞ F (S ×ˢ Metric.ball (0 : E) r) ∧
        ContMDiffOn (I.prod I) (I.prod 𝓘(ℝ, E)) ∞ R V ∧
        MapsTo F (S ×ˢ Metric.ball (0 : E) r) V ∧
        MapsTo R V (S ×ˢ Metric.ball (0 : E) r) ∧
        LeftInvOn R F (S ×ˢ Metric.ball (0 : E) r) ∧ RightInvOn R F V := by
  obtain ⟨S, hS, hcS, r, hr, hT, hTB⟩ := B.exists_ball_trivialization_source e hc hW hcW
  let T := S ×ˢ Metric.ball (0 : E) r
  let F : M × E → M × M := fun z => (z.1, expMapIntrinsic g hEnorm z.1
    (e.symmL ℝ z.1 z.2))
  let R : M × M → M × E := fun z => (z.1, (e (B.inv z)).2)
  let V := F '' T
  have hTe : T ⊆ e.target := fun z hz => (hT hz).2
  have hTopen : IsOpen T := hS.prod Metric.isOpen_ball
  have hVopen : IsOpen V := B.isOpen_image_expMapIntrinsic_trivialization e hTopen hTe hTB
  have hEF : ∀ z ∈ T, diagExp (I := I) g hEnorm (e.toOpenPartialHomeomorph.symm z) = F z := by
    intro z hz
    have hzbase : z.1 ∈ e.baseSet := e.mem_target.mp (hTe hz)
    have he : e.toOpenPartialHomeomorph.symm z =
        (⟨z.1, e.symmL ℝ z.1 z.2⟩ : TangentBundle I M) := by
      rw [← e.mk_symm hzbase, ← e.symmL_apply (R := ℝ) hzbase]
    rw [he]
    rfl
  have hBF : ∀ z ∈ T, B.inv (F z) = e.toOpenPartialHomeomorph.symm z := by
    intro z hz
    rw [← hEF z hz]
    exact B.left_inv (hTB hz)
  have hleft : LeftInvOn R F T := by
    intro z hz
    have he : e (B.inv (F z)) = z := by
      rw [hBF z hz]
      exact e.right_inv (hTe hz)
    change (z.1, (e (B.inv (F z))).2) = z
    rw [he]
  have hVB : V ⊆ B.dom := by
    rintro z ⟨x, hx, rfl⟩
    have hmap := B.hom.map_source (hTB hx)
    have heq : B.hom (e.toOpenPartialHomeomorph.symm x) = F x :=
      (B.hom_eq (hTB hx)).trans (hEF x hx)
    exact heq ▸ hmap
  have hVR : MapsTo R V T := by
    rintro z ⟨x, hx, rfl⟩
    rw [hleft hx]
    exact hx
  have hright : RightInvOn R F V := by
    rintro z ⟨x, hx, rfl⟩
    rw [hleft hx]
  have hRe : MapsTo B.inv V e.source := by
    rintro z ⟨x, hx, rfl⟩
    rw [hBF x hx]
    exact e.map_target (hTe hx)
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod I) ∞ F T :=
    contMDiffOn_fst.prodMk ((contMDiffOn_expMapIntrinsic_trivialization g hEnorm e).mono hTe)
  have hR : ContMDiffOn (I.prod I) (I.prod 𝓘(ℝ, E)) ∞ R V := by
    have he := e.contMDiffOn.comp (B.inv_contMDiffOn.mono hVB) hRe
    exact contMDiffOn_fst.prodMk (contMDiff_snd.comp_contMDiffOn he)
  have hcV : (c, c) ∈ V := by
    refine ⟨(c, 0), ⟨hcS, Metric.mem_ball_self hr⟩, ?_⟩
    simp only [F, map_zero, expMapIntrinsic_zero]
  exact ⟨S, hS, hcS, r, hr, V, hVopen, hcV, hVB, hT, hTB, hRe, hF, hR,
    fun z hz => mem_image_of_mem F hz, hVR, hleft, hright⟩

theorem exists_starConvex_fixed_source_domain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) :
    ∃ V : Set (M × M), IsOpen V ∧ (c, c) ∈ V ∧ V ⊆ B.dom ∧
      ∀ z ∈ V, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
        U ⊆ (B.fixed z.1).hom.source ∧ (B.fixed z.1).inv z.2 ∈ U := by
  let e := trivializationAt E (TangentSpace I) c
  have hc : c ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) c
  obtain ⟨S, _, _, r, hr, V, hV, hcV, hVB, hT, hTB, _, _, _, _, hRT, _, _⟩ :=
    B.exists_ball_trivialization_domain e hc isOpen_univ (mem_univ _)
  refine ⟨V, hV, hcV, hVB, ?_⟩
  intro z hz
  have hpS : z.1 ∈ S := (hRT hz).1
  have hp : z.1 ∈ e.baseSet := e.mem_target.mp
    (hT (show (z.1, (0 : E)) ∈ S ×ˢ Metric.ball (0 : E) r from
      ⟨hpS, Metric.mem_ball_self hr⟩)).2
  let L : E ≃L[ℝ] E := (e.continuousLinearEquivAt ℝ z.1 hp).symm
  let U := L '' Metric.ball (0 : E) r
  have hU : IsOpen U := L.toHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hstar : StarConvex ℝ 0 U := by
    have h := ((convex_ball (0 : E) r).starConvex (Metric.mem_ball_self hr)).linear_image
      L.toLinearMap
    change StarConvex ℝ (L (0 : E)) (L '' Metric.ball (0 : E) r) at h
    simpa only [map_zero] using h
  have hsub : U ⊆ (B.fixed z.1).hom.source := by
    rintro v ⟨w, hw, rfl⟩
    have he : e.toOpenPartialHomeomorph.symm (z.1, w) =
        (⟨z.1, show TangentSpace I z.1 from L w⟩ : TangentBundle I M) := by
      rw [← e.mk_symm hp, ← e.symmL_apply (R := ℝ) hp]
      congr 1
      exact (congrFun (e.symm_continuousLinearEquivAt_eq (R := ℝ) hp) w).symm
    have h := hTB (show (z.1, w) ∈ S ×ˢ Metric.ball (0 : E) r from ⟨hpS, hw⟩)
    rw [he] at h
    exact h
  refine ⟨U, hU, hstar, hsub, ?_⟩
  refine ⟨(e (B.inv z)).2, (hRT hz).2, ?_⟩
  have htotal : B.inv z =
      (⟨z.1, show TangentSpace I z.1 from (B.inv z).snd⟩ : TangentBundle I M) := by
    apply TotalSpace.ext (B.proj_eq (hVB hz))
    exact heq_of_eq rfl
  change L (e (B.inv z)).2 = (B.fixed z.1).inv z.2
  rw [htotal, e.apply_eq_prod_continuousLinearEquivAt ℝ z.1 hp]
  exact L.apply_symm_apply _

end DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch
