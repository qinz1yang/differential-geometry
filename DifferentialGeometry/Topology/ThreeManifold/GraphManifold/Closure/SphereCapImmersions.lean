import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapSmoothFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapBoundary
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.ModelImmersion
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion

/-!
Actual smooth embeddings of the core and closed balls into the spherical capping quotient.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private abbrev CapE1 := EuclideanSpace ℝ (Fin 1)
private abbrev CapE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CapE3 := EuclideanSpace ℝ (Fin 3)

private def capAngularTranslation (v : CapE2) : CapE2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ CapE2 where
  toFun z := z + v
  invFun z := z - v
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private def capOneReal : CapE1 ≃L[ℝ] ℝ where
  toFun v := v 0
  invFun r := WithLp.toLp 2 (Function.const (Fin 1) r)
  left_inv v := by
    ext i
    exact congrArg v (Subsingleton.elim 0 i)
  right_inv r := rfl
  map_add' v w := rfl
  map_smul' r v := rfl
  continuous_toFun := (EuclideanSpace.proj 0).continuous
  continuous_invFun := by
    fun_prop

private def capSignedLinear : (CapE2 × ℝ) ≃L[ℝ] CapE3 :=
  ((ContinuousLinearEquiv.refl ℝ CapE2).prodCongr
    capOneReal.symm).trans
      EuclideanSpace.finAddEquivProd.symm

private theorem capSignedLinear_zero (v : CapE2) (s : ℝ) :
    capSignedLinear (v, s) 0 = v 0 := rfl

private theorem capInteriorZero_val (v : CapE3) (hv : 0 < v 0) :
    (halfSpaceThreeInteriorPartialDiffeomorph 0 v).val = v := by
  apply halfSpaceThreeSplit.injective
  apply Prod.ext
  · change max ((halfSpaceThreeSplit v).1 - 0) 0 = (halfSpaceThreeSplit v).1
    have h : 0 ≤ (halfSpaceThreeSplit v).1 := hv.le
    rw [sub_zero, max_eq_left h]
  · change (halfSpaceThreeSplit (halfSpaceThreeSplit.symm
      (max ((halfSpaceThreeSplit v).1 - 0) 0, (halfSpaceThreeSplit v).2))).2 = _
    rw [ContinuousLinearEquiv.apply_symm_apply]

private def capNormalSign (σ : ℝ) :
    CapE1 ≃L[ℝ] CapE1 := by
  exact if σ = 1 then ContinuousLinearEquiv.refl ℝ CapE1
    else ContinuousLinearEquiv.neg ℝ

private theorem capNormalSign_apply (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (v : CapE1) :
    capNormalSign σ v = σ • v := by
  rcases hσ with h | h
  · subst σ
    simp [capNormalSign]
  · subst σ
    simp [capNormalSign, show (-1 : ℝ) ≠ 1 by norm_num]

private theorem capHalfSelfCharts :
    prodChartedSpace CapE2 CapE2 (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) =
      chartedSpaceSelf (ModelProd CapE2 (EuclideanHalfSpace 1)) := by
  change prodChartedSpace CapE2 CapE2 (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) =
    chartedSpaceSelf (CapE2 × EuclideanHalfSpace 1)
  exact chartedSpaceSelf_prod

private theorem capHalfSigned_immersion
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N]
    (e : PartialDiffeomorph sphereSignedCollarModel (𝓡∂ 3)
      (ClosureSphere.{u} × ℝ) N ∞) (he : e.source = sphereSignedCollarSource)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    IsImmersionAtOfComplement PUnit.{1} sphereHalfCollarModel (𝓡∂ 3) ∞
      (e ∘ sphereCapHalfSignedCoordinate σ) p := by
  let a₀ := PartialDiffeomorph.extendedChart (I := 𝓡 2) p.1
  let v : CapE2 := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 1 - a₀ p.1 0 else 0)
  let a := a₀.trans (capAngularTranslation v).toPartialDiffeomorph
  have hpa : p.1 ∈ a.source := ⟨mem_extChartAt_source p.1, mem_univ _⟩
  have ha0 : 0 < a p.1 0 := by
    change 0 < a₀ p.1 0 + (1 - a₀ p.1 0)
    linarith
  let d := DifferentialGeometry.Topology.PartialDiffeomorph.prod a
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞).toPartialDiffeomorph
  let b := DifferentialGeometry.Topology.PartialDiffeomorph.prod a
    (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph
  let ld : (CapE2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), 𝓡 3⟯ CapE3 :=
    { toEquiv := capSignedLinear.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact capSignedLinear.contDiff.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact capSignedLinear.symm.contDiff.contMDiff }
  let l := ld.toPartialDiffeomorph
  let c := ((e.symm.trans b).trans l).trans (halfSpaceThreeInteriorPartialDiffeomorph 0)
  let s : Set (ClosureSphere.{u} × EuclideanHalfSpace 1) :=
    sphereHalfCollarSource ∩ (d.source ∩ d ⁻¹' {q | 0 < q.1 0})
  have hs : IsOpen s := by
    apply IsOpen.inter ?_
      (d.contMDiffOn.continuousOn.isOpen_inter_preimage d.open_source
        (isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp continuous_fst)))
    exact isOpen_lt (by fun_prop) continuous_const
  have hps : p ∈ s := ⟨hp, ⟨hpa, mem_univ _⟩, ha0⟩
  let α := d.toOpenPartialHomeomorph.restr s
  have hαsource : α.source = s := by
    rw [OpenPartialHomeomorph.restr_source' d.toOpenPartialHomeomorph s hs,
      inter_eq_right]
    exact fun q hq => hq.2.1
  have hαmax : α ∈ IsManifold.maximalAtlas sphereHalfCollarModel ∞
      (ClosureSphere.{u} × EuclideanHalfSpace 1) :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ sphereHalfCollarModel)
      (IsManifold.mem_maximalAtlas_prod
        (a.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
          a.contMDiffOn_toFun a.contMDiffOn_invFun)
        (by
          let r := Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞
          have hr : r.toPartialDiffeomorph.toOpenPartialHomeomorph =
                OpenPartialHomeomorph.refl (EuclideanHalfSpace 1) := by
            ext q : 1 <;> rfl
          rw [hr]
          simpa only [chartAt_self_eq] using
            (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ 1) (n := ∞) p.2))) hs
  have hcmax : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ N :=
    c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun
  let L : (CapE2 × CapE1) ≃L[ℝ] CapE3 :=
    ((ContinuousLinearEquiv.refl ℝ CapE2).prodCongr
      (capNormalSign σ)).trans EuclideanSpace.finAddEquivProd.symm
  have hsource (q : ClosureSphere.{u} × EuclideanHalfSpace 1) (hq : q ∈ s) :
      e (sphereCapHalfSignedCoordinate σ q) ∈ c.source := by
    have hqe : sphereCapHalfSignedCoordinate σ q ∈ e.source := by
      rw [he]
      exact sphereCapHalfSignedCoordinate_mem hσ hq.1
    have hleft : e.symm.toPartialEquiv (e.toPartialEquiv
        (sphereCapHalfSignedCoordinate σ q)) = sphereCapHalfSignedCoordinate σ q :=
      e.left_inv hqe
    change ((e (sphereCapHalfSignedCoordinate σ q) ∈ e.target ∧
      e.symm (e (sphereCapHalfSignedCoordinate σ q)) ∈ b.source) ∧
      b (e.symm (e (sphereCapHalfSignedCoordinate σ q))) ∈ l.source) ∧
      l (b (e.symm (e (sphereCapHalfSignedCoordinate σ q)))) ∈
        (halfSpaceThreeInteriorPartialDiffeomorph 0).source
    rw [hleft]
    refine ⟨⟨⟨e.map_source hqe, ⟨hq.2.1.1, mem_univ _⟩⟩, mem_univ _⟩, ?_⟩
    change capSignedLinear (a q.1, σ * q.2.val 0) ∈
      (halfSpaceThreeInteriorChart 0).source
    rw [halfSpaceThreeInteriorChart_mem_source]
    change 0 < capSignedLinear (a q.1, σ * q.2.val 0) 0
    rw [capSignedLinear_zero]
    exact hq.2.2
  have hformula (q : ClosureSphere.{u} × EuclideanHalfSpace 1) (hq : q ∈ s) :
      c.toOpenPartialHomeomorph.extend (𝓡∂ 3)
        (e (sphereCapHalfSignedCoordinate σ q)) = L ((α.extend sphereHalfCollarModel) q) := by
    have hqe : sphereCapHalfSignedCoordinate σ q ∈ e.source := by
      rw [he]
      exact sphereCapHalfSignedCoordinate_mem hσ hq.1
    have hleft : e.symm.toPartialEquiv (e.toPartialEquiv
        (sphereCapHalfSignedCoordinate σ q)) = sphereCapHalfSignedCoordinate σ q :=
      e.left_inv hqe
    change (halfSpaceThreeInteriorPartialDiffeomorph 0
      (capSignedLinear (a (e.symm (e (sphereCapHalfSignedCoordinate σ q))).1,
        (e.symm (e (sphereCapHalfSignedCoordinate σ q))).2))).val =
      L (a q.1, q.2.val)
    rw [hleft, capInteriorZero_val _ (by rw [capSignedLinear_zero]; exact hq.2.2)]
    change EuclideanSpace.finAddEquivProd.symm
      (a q.1, capOneReal.symm (σ * q.2.val 0)) =
        EuclideanSpace.finAddEquivProd.symm (a q.1, capNormalSign σ q.2.val)
    apply congrArg EuclideanSpace.finAddEquivProd.symm
    change (a q.1, capOneReal.symm
      (σ * q.2.val 0)) = (a q.1, capNormalSign σ q.2.val)
    rw [capNormalSign_apply σ hσ]
    refine Prod.ext rfl ?_
    apply capOneReal.injective
    change σ * q.2.val 0 = (σ • q.2.val) 0
    rfl
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ (CapE2 × CapE1) PUnit.{1}).trans L)
    α c.toOpenPartialHomeomorph (hαsource.symm ▸ hps) (hsource p hps)
    hαmax hcmax (fun q hq => hsource q (hαsource ▸ hq)) ?_
  intro v hv
  let q := (α.extend sphereHalfCollarModel).symm v
  have hq : q ∈ s := by
    have h := (α.extend sphereHalfCollarModel).map_target hv
    rwa [OpenPartialHomeomorph.extend_source, hαsource] at h
  change c.toOpenPartialHomeomorph.extend (𝓡∂ 3)
    (e (sphereCapHalfSignedCoordinate σ q)) = L v
  rw [hformula q hq]
  exact congrArg L ((α.extend sphereHalfCollarModel).right_inv hv)

private def capEuclideanTranslation (v : CapE3) : CapE3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ CapE3 where
  toFun z := z + v
  invFun z := z - v
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private theorem capEuclideanPDImmersion
    {M N : Type u} [TopologicalSpace M] [ChartedSpace CapE3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N]
    (e : PartialDiffeomorph (𝓡 3) (𝓡∂ 3) M N ∞) {x : M} (hx : x ∈ e.source) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡 3) (𝓡∂ 3) ∞ e x := by
  let a₀ := PartialDiffeomorph.extendedChart (I := 𝓡 3) x
  let v : CapE3 := WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then 1 - a₀ x 0 else 0)
  let a := a₀.trans (capEuclideanTranslation v).toPartialDiffeomorph
  have hxa : x ∈ a.source := ⟨mem_extChartAt_source x, mem_univ _⟩
  have ha0 : 0 < a x 0 := by
    change 0 < a₀ x 0 + (1 - a₀ x 0)
    linarith
  let s : Set M := e.source ∩ (a.source ∩ a ⁻¹' {v | 0 < v 0})
  have hs : IsOpen s := e.open_source.inter
    (a.contMDiffOn.continuousOn.isOpen_inter_preimage a.open_source
      (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous))
  let α := a.toOpenPartialHomeomorph.restr s
  let c := (e.symm.trans a).trans (halfSpaceThreeInteriorPartialDiffeomorph 0)
  have hαsource : α.source = s := by
    rw [OpenPartialHomeomorph.restr_source' a.toOpenPartialHomeomorph s hs,
      inter_eq_right]
    exact fun y hy => hy.2.1
  have hxs : x ∈ s := ⟨hx, hxa, ha0⟩
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡 3) ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡 3))
      (a.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
        a.contMDiffOn_toFun a.contMDiffOn_invFun) hs
  have hcmax : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ N :=
    c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun
  have hsource (y : M) (hy : y ∈ s) : e y ∈ c.source := by
    have hleft : e.symm.toPartialEquiv (e.toPartialEquiv y) = y := e.left_inv hy.1
    change (e y ∈ e.target ∧ e.symm (e y) ∈ a.source) ∧
      a (e.symm (e y)) ∈ (halfSpaceThreeInteriorPartialDiffeomorph 0).source
    rw [hleft]
    refine ⟨⟨e.map_source hy.1, hy.2.1⟩, ?_⟩
    change a y ∈ (halfSpaceThreeInteriorChart 0).source
    exact (halfSpaceThreeInteriorChart_mem_source 0 (a y)).mpr hy.2.2
  have hformula (y : M) (hy : y ∈ s) :
      c.toOpenPartialHomeomorph.extend (𝓡∂ 3) (e y) = (α.extend (𝓡 3)) y := by
    have hleft : e.symm.toPartialEquiv (e.toPartialEquiv y) = y := e.left_inv hy.1
    change (halfSpaceThreeInteriorPartialDiffeomorph 0 (a (e.symm (e y)))).val = a y
    rw [hleft]
    exact capInteriorZero_val _ hy.2.2
  refine IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ CapE3 PUnit.{1})
    α c.toOpenPartialHomeomorph (hαsource.symm ▸ hxs) (hsource x hxs)
    hαmax hcmax (fun y hy => hsource y (hαsource ▸ hy)) ?_
  intro v hv
  let y := (α.extend (𝓡 3)).symm v
  have hy : y ∈ s := by
    have h := (α.extend (𝓡 3)).map_target hv
    rwa [OpenPartialHomeomorph.extend_source, hαsource] at h
  change c.toOpenPartialHomeomorph.extend (𝓡∂ 3) (e y) = v
  rw [hformula y hy]
  exact (α.extend (𝓡 3)).right_inv hv

section Parameter

variable {E F G H H' H'' M P N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace H' P]
  [TopologicalSpace N] [ChartedSpace H'' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {Z : ModelWithCorners ℝ G H''} [IsManifold J ∞ P]

private theorem capParameterImmersion
    (e : PartialDiffeomorph I J M P ∞) (f : P → N)
    (hf : ContMDiff J Z ∞ f) (θ : H ≃ₘ⟮I, J⟯ H') (L : E ≃L[ℝ] F)
    (hθ : ∀ y, J (θ y) = L (I y)) {p : M} (hp : p ∈ e.source)
    (h : IsImmersionAtOfComplement PUnit.{1} I Z ∞ (f ∘ e) p) :
    IsImmersionAtOfComplement PUnit.{1} J Z ∞ f (e p) := by
  let α := (e.symm.toOpenPartialHomeomorph.trans h.domChart).trans
    θ.toHomeomorph.toOpenPartialHomeomorph
  have hαsource : α.source = e.target ∩ e.symm ⁻¹' h.domChart.source := by
    simp [α]
  have hαmax : α ∈ IsManifold.maximalAtlas J ∞ P := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn J J ∞ (θ ∘ h.domChart ∘ e.symm) α.source
      rw [hαsource]
      exact θ.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
          (e.symm.contMDiffOn.mono inter_subset_left) inter_subset_right)
    · change ContMDiffOn J J ∞ (e ∘ h.domChart.symm ∘ θ.symm) α.target
      have ht : α.target = θ.symm ⁻¹'
          (h.domChart.target ∩ h.domChart.symm ⁻¹' e.source) := by simp [α]
      rw [ht]
      exact (e.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          inter_subset_left) inter_subset_right).comp θ.symm.contMDiff.contMDiffOn
            (fun y hy => hy)
  have hleft : e.symm.toPartialEquiv (e.toPartialEquiv p) = p := e.left_inv hp
  have hxα : e p ∈ α.source := by
    rw [hαsource]
    refine ⟨e.map_source hp, ?_⟩
    change e.symm (e p) ∈ h.domChart.source
    rw [hleft]
    exact h.mem_domChart_source
  refine IsImmersionAtOfComplement.mk_of_continuousAt (hf (e p)).continuousAt
    (((L.symm).prodCongr (ContinuousLinearEquiv.refl ℝ PUnit.{1})).trans h.equiv)
    α h.codChart hxα h.mem_codChart_source hαmax h.codChart_mem_maximalAtlas ?_
  intro v hv
  have hy := (α.extend J).map_target hv
  rw [OpenPartialHomeomorph.extend_source, hαsource] at hy
  let y := (α.extend J).symm v
  have hye : y ∈ e.target := hy.1
  have hym : e.symm y ∈ h.domChart.source := hy.2
  have hvα : (α.extend J) y = v := (α.extend J).right_inv hv
  have hvL : (h.domChart.extend I) (e.symm y) = L.symm v := by
    apply L.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (hθ (h.domChart (e.symm y))).symm.trans hvα
  have hvt : L.symm v ∈ (h.domChart.extend I).target := by
    rw [← hvL]
    exact (h.domChart.extend I).map_source
      (by rwa [OpenPartialHomeomorph.extend_source])
  have hinv : (h.domChart.extend I).symm (L.symm v) = e.symm y := by
    rw [← hvL]
    exact (h.domChart.extend I).left_inv
      (by rwa [OpenPartialHomeomorph.extend_source])
  have hright : e.toPartialEquiv (e.symm.toPartialEquiv y) = y := e.right_inv hye
  have hw := h.writtenInCharts hvt
  change (h.codChart.extend Z) (f (e ((h.domChart.extend I).symm (L.symm v)))) =
    h.equiv (L.symm v, 0) at hw
  rw [hinv, hright] at hw
  exact hw

end Parameter

private def capHalfProductDiffeomorph :
    ModelProd CapE2 (EuclideanHalfSpace 1) ≃ₘ⟮sphereHalfCollarModel, 𝓡∂ 3⟯
      EuclideanHalfSpace 3 :=
  DifferentialGeometry.Manifold.modelLinearHomeomorphDiffeomorph
    sphereHalfCollarModel (𝓡∂ 3)
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model

namespace MixedBoundaryCertificate

local instance capBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance capBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

local instance capLiftedBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} sphereCapBallOpen) :=
  uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)
  [ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient]
  [IsManifold (𝓡∂ 3) ∞ B.SphereCapQuotient]
  (hA : ∀ a : B.SphereCapPatchIndex,
    ContMDiffOn (B.sphereCapPatchModel a) (𝓡∂ 3) ∞
      (B.sphereCapPatch a) (B.sphereCapPatch a).source ∧
    ContMDiffOn (𝓡∂ 3) (B.sphereCapPatchModel a) ∞
      (B.sphereCapPatch a).symm (B.sphereCapPatch a).target)

include hA

private theorem capBallHalfImmersion (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    IsImmersionAtOfComplement PUnit.{1} sphereHalfCollarModel (𝓡∂ 3) ∞
      (B.sphereCapBall i ∘ sphereCapBallCollar.{u}) p := by
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have he : e.source = sphereSignedCollarSource := B.sphereCapSignedSeam_source i
  apply (capHalfSigned_immersion e he (-1) (Or.inr rfl) hp).congr_of_eventuallyEq
  have hopen : IsOpen (sphereHalfCollarSource :
      Set (ClosureSphere.{u} × EuclideanHalfSpace 1)) :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hp] with q hq
  change B.sphereCapSignedSeam i (q.1, -1 * q.2.val 0) =
    B.sphereCapBall i (sphereCapBallCollar.{u} q)
  rw [neg_one_mul, B.sphereCapSignedSeam_negative i q.1 (-q.2.val 0)
    (neg_nonpos.mpr q.2.property) (by linarith [show q.2.val 0 < 1 from hq])]
  congr 1
  exact congrArg (fun y => sphereCapBallCollar.{u} (q.1, y))
    (halfPoint_eq_self q.2 (by simpa using q.2.property) (by simp))

private theorem capCoreHalfImmersion (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    IsImmersionAtOfComplement PUnit.{1} sphereHalfCollarModel (𝓡∂ 3) ∞
      (B.sphereCapCore ∘ B.sphere i) p := by
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have he : e.source = sphereSignedCollarSource := B.sphereCapSignedSeam_source i
  apply (capHalfSigned_immersion e he 1 (Or.inl rfl) hp).congr_of_eventuallyEq
  have hopen : IsOpen (sphereHalfCollarSource :
      Set (ClosureSphere.{u} × EuclideanHalfSpace 1)) :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hp] with q hq
  change B.sphereCapSignedSeam i (q.1, 1 * q.2.val 0) = B.sphereCapCore (B.sphere i q)
  rw [one_mul, B.sphereCapSignedSeam_positive i q.1 (q.2.val 0) q.2.property hq]
  rw [halfPoint_eq_self q.2 q.2.property rfl]

omit hA in
private theorem capBallBoundaryTarget (x : ClosedCell 3) (hx : x ∉ sphereCapBallOpen) :
    x ∈ sphereCapBallCollar.{u}.target := by
  have hn : ‖x.val‖ = 1 := by
    have hb : ‖x.val‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using x.property
    exact le_antisymm hb (le_of_not_gt hx)
  let z : ClosureSphere.{u} := ULift.up ⟨x.val, by
    simpa [Metric.mem_sphere, dist_zero_right] using hn⟩
  have hs : (z, halfZero) ∈ sphereCapBallCollar.source := by
    rw [sphereCapBallCollar_source]
    change (0 : ℝ) < 1
    exact zero_lt_one
  have ht := sphereCapBallCollar.map_source hs
  change sphereCapBallCollar.{u} (z, halfZero) ∈ sphereCapBallCollar.target at ht
  rwa [sphereCapBallCollar_zero z] at ht

private theorem capBallOpenImmersion (i : Fin B.sphereCount) (x : ClosedCell 3)
    (hx : x ∈ sphereCapBallOpen) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) (𝓡∂ 3) ∞ (B.sphereCapBall i) x := by
  let d := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
    sphereCapBallOpen ⟨⟨x, hx⟩⟩
  let lift : sphereCapBallOpen ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ULift.{u} sphereCapBallOpen :=
    uliftDiffeomorph (𝓡∂ 3) sphereCapBallOpen
  let e := d.symm.trans
    (lift.toPartialDiffeomorph.trans
      (B.sphereCapPatchDiffeomorph hA (.inr (.inl i))))
  have hpatch : (B.sphereCapPatchDiffeomorph hA (.inr (.inl i))).source = univ := by
    simp only [sphereCapPatchDiffeomorph, sphereCapPatch, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ]
  have hxe : x ∈ e.source := by
    change x ∈ d.target ∧ d.symm x ∈
      (lift.toPartialDiffeomorph.trans
        (B.sphereCapPatchDiffeomorph hA (.inr (.inl i)))).source
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    refine ⟨hx, ?_⟩
    change d.symm x ∈ (univ : Set sphereCapBallOpen) ∧
      lift (d.symm x) ∈ (B.sphereCapPatchDiffeomorph hA (.inr (.inl i))).source
    rw [hpatch]
    exact ⟨mem_univ _, mem_univ _⟩
  have hi := (IsImmersionOfComplement.id (I := 𝓡∂ 3) (n := ∞)
    (M := ClosedCell 3) x).isLocalDiffeomorphAt_comp
      (e.isLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ hxe)
  apply hi.congr_of_eventuallyEq
  filter_upwards [sphereCapBallOpen.isOpen.mem_nhds hx] with y hy
  change B.sphereCapBall i (d.symm y).val = B.sphereCapBall i y
  exact congrArg (B.sphereCapBall i) (d.right_inv (by
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    exact hy))

theorem sphereCapBall_isSmoothEmbedding (i : Fin B.sphereCount) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞ (B.sphereCapBall i) := by
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
    (B.sphereCapBall_embedding i).isEmbedding⟩
  intro x
  by_cases hx : x ∈ sphereCapBallOpen
  · exact B.capBallOpenImmersion hA i x hx
  · have ht := capBallBoundaryTarget.{u} x hx
    let p := sphereCapBallCollar.{u}.symm x
    have hp : p ∈ sphereCapBallCollar.{u}.source := sphereCapBallCollar.map_target ht
    have he : sphereCapBallCollar.{u} p = x := sphereCapBallCollar.right_inv ht
    rw [← he]
    apply capParameterImmersion sphereCapBallCollar.{u} (B.sphereCapBall i)
      (B.sphereCapBall_smooth hA i) capHalfProductDiffeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model hp
    exact B.capBallHalfImmersion hA i ((sphereCapBallCollar_source).subset hp)

theorem sphereCapCore_isSmoothEmbedding :
    IsSmoothEmbedding C.model (𝓡∂ 3) ∞ B.sphereCapCore := by
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
    B.sphereCapCore_embedding.isEmbedding⟩
  rcases C with @⟨k, M, t, a, m, ht, hc, hs, O⟩
  cases k with
  | closed =>
    intro x
    have hx : x ∈ B.sphereCapCoreOpen := by
      by_contra h
      have hxS : x ∈ B.sphereImage := by simpa [sphereCapCoreOpen] using h
      obtain ⟨i, z, hz⟩ := mem_iUnion.mp hxS
      have hb := B.sphere_zero_boundary i z
      change (𝓡 3).IsBoundaryPoint (B.sphere i (z, halfZero)) at hb
      rw [ModelWithCorners.isBoundaryPoint_iff, (𝓡 3).range_eq_univ,
        frontier_univ] at hb
      exact hb
    let e := B.sphereCapCoreOpenDiffeomorph hA ⟨x, hx⟩
    have hxe : x ∈ e.source := by
      rw [B.sphereCapCoreOpenDiffeomorph_source]
      exact hx
    apply (capEuclideanPDImmersion e hxe).congr_of_eventuallyEq
    filter_upwards [B.sphereCapCoreOpen.isOpen.mem_nhds hx] with y hy
    exact B.sphereCapCoreOpenDiffeomorph_apply hA ⟨x, hx⟩ hy
  | withBoundary =>
    intro x
    by_cases hx : x ∈ B.sphereCapCoreOpen
    · let e := B.sphereCapCoreOpenDiffeomorph hA ⟨x, hx⟩
      have hxe : x ∈ e.source := by
        rw [B.sphereCapCoreOpenDiffeomorph_source]
        exact hx
      have hi := (IsImmersionOfComplement.id (I := 𝓡∂ 3) (n := ∞)
        (M := M) x).isLocalDiffeomorphAt_comp
          (e.isLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ hxe)
      apply hi.congr_of_eventuallyEq
      filter_upwards [B.sphereCapCoreOpen.isOpen.mem_nhds hx] with y hy
      exact B.sphereCapCoreOpenDiffeomorph_apply hA ⟨x, hx⟩ hy
    · have hxS : x ∈ B.sphereImage := by simpa [sphereCapCoreOpen] using hx
      obtain ⟨i, z, hz⟩ := mem_iUnion.mp hxS
      have hp : (z, halfZero) ∈ (B.sphere i).source := by
        rw [B.sphere_source]
        change (0 : ℝ) < 1
        exact zero_lt_one
      rw [← hz]
      apply capParameterImmersion (B.sphere i) B.sphereCapCore
        (B.sphereCapCore_smooth hA) capHalfProductDiffeomorph
        DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
        DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model hp
      exact B.capCoreHalfImmersion hA i ((B.sphere_source i).subset hp)

omit [ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient]
  [IsManifold (𝓡∂ 3) ∞ B.SphereCapQuotient] hA in
theorem sphereCapCore_isSmoothEmbedding_canonical :
    letI := B.sphereCapQuotientChartedSpace
    IsSmoothEmbedding C.model (𝓡∂ 3) ∞ B.sphereCapCore := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  exact B.sphereCapCore_isSmoothEmbedding B.exists_sphereCapQuotientAtlas.choose_spec.2

omit [ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient]
  [IsManifold (𝓡∂ 3) ∞ B.SphereCapQuotient] hA in
theorem sphereCapBall_isSmoothEmbedding_canonical (i : Fin B.sphereCount) :
    letI := B.sphereCapQuotientChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) (𝓡∂ 3) ∞ (B.sphereCapBall i) := by
  let := B.sphereCapQuotientChartedSpace
  let := B.sphereCapQuotientIsManifold
  exact B.sphereCapBall_isSmoothEmbedding B.exists_sphereCapQuotientAtlas.choose_spec.2 i

end MixedBoundaryCertificate

end GC.GraphManifold
