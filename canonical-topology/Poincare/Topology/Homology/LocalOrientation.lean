import Poincare.Topology.Homology.LocalDerivativeComparison
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Set Bundle
open scoped Manifold Topology

universe u v w

namespace Poincare.Topology

private theorem orientation_map_linearEquiv_trans
    {E : Type u} {F : Type v} {G : Type w}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    {ι : Type*} (A : E ≃ₗ[ℝ] F) (B : F ≃ₗ[ℝ] G) (o : Orientation ℝ E ι) :
    Orientation.map ι (A.trans B) o =
      Orientation.map ι B (Orientation.map ι A o) := by
  induction o using Module.Ray.ind with
  | h f hf => rfl

private theorem det_pos_of_orientations_agree
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (A B : F ≃ₗ[ℝ] E) (o : Orientation ℝ F (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (hA : Orientation.map _ A o = ω)
    (hB : Orientation.map _ B o = ω) :
    0 < LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E) := by
  have hinv : Orientation.map _ A.symm ω = o := by
    rw [← hA]
    exact (Orientation.map _ A).symm_apply_apply o
  apply (Orientation.map_eq_iff_det_pos ω (A.symm.trans B) (by simp)).mp
  rw [orientation_map_linearEquiv_trans, hinv, hB]

private theorem tangent_trivialization_transition_eq_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (x y p : M) (hx : p ∈ (chartAt E x).source) (hy : p ∈ (chartAt E y).source) :
    (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm.trans
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)) : E →L[ℝ] E) =
      fderiv ℝ ((chartAt E y) ∘ (chartAt E x).symm) (chartAt E x p) := by
  have hcomp :
      (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm.trans
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)) : E →L[ℝ] E) =
        tangentCoordChange 𝓘(ℝ, E) x y p := by
    change ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy) :
        TangentSpace 𝓘(ℝ, E) p →L[ℝ] E).comp
        (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm :
          E →L[ℝ] TangentSpace 𝓘(ℝ, E) p) = _
    rw [Trivialization.coe_continuousLinearEquivAt_eq', Trivialization.symm_continuousLinearEquivAt_eq',
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy,
      TangentBundle.symmL_trivializationAt_eq_core hx]
    apply ContinuousLinearMap.ext
    intro z
    exact tangentCoordChange_comp (I := 𝓘(ℝ, E)) (w := x) (x := p) (y := y) (z := p)
      ⟨⟨by simpa only [extChartAt_source] using hx, mem_extChartAt_source p⟩,
        by simpa only [extChartAt_source] using hy⟩
  simpa only [tangentCoordChange_def, mfld_simps, fderivWithin_univ] using hcomp

private theorem oriented_chart_transition_local_homology
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (x y p : M) (hx : p ∈ (chartAt E x).source) (hy : p ∈ (chartAt E y).source)
    (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) p) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (hxori : Orientation.map _
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o = ω)
    (hyori : Orientation.map _
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv o = ω) :
    let e := (chartAt E x).symm.trans (chartAt E y)
    ∃ he : chartAt E x p ∈ e.source,
      e (chartAt E x p) = chartAt E y p ∧
      (integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (e (chartAt E x p))))
          (show MapsTo (Homeomorph.subRight (e (chartAt E x p)))
            ({e (chartAt E x p)}ᶜ : Set E) ({0}ᶜ : Set E)
            from fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            e (chartAt E x p) he).hom.hom =
        integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E x p)))
          (show MapsTo (Homeomorph.subRight (chartAt E x p))
            ({chartAt E x p}ᶜ : Set E) ({0}ᶜ : Set E)
            from fun _ hz => sub_ne_zero.mpr hz) := by
  let e := (chartAt E x).symm.trans (chartAt E y)
  have he : chartAt E x p ∈ e.source := by
    change chartAt E x p ∈ (chartAt E x).target ∧
      (chartAt E x).symm (chartAt E x p) ∈ (chartAt E y).source
    exact ⟨(chartAt E x).map_source hx, by rwa [(chartAt E x).left_inv hx]⟩
  have hep : e (chartAt E x p) = chartAt E y p := by
    change chartAt E y ((chartAt E x).symm (chartAt E x p)) = chartAt E y p
    rw [(chartAt E x).left_inv hx]
  have hf : HasFDerivAt e (tangentCoordChange 𝓘(ℝ, E) x y p) (chartAt E x p) := by
    change HasFDerivAt ((chartAt E y) ∘ (chartAt E x).symm)
      (tangentCoordChange 𝓘(ℝ, E) x y p) (chartAt E x p)
    simpa only [mfld_simps, hasFDerivWithinAt_univ] using
      (hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, E)) (x := x) (y := y) (z := p)
        ⟨by simpa only [extChartAt_source] using hx,
          by simpa only [extChartAt_source] using hy⟩)
  have hf' : HasFDerivAt e.symm (tangentCoordChange 𝓘(ℝ, E) y x p) (e (chartAt E x p)) := by
    rw [hep]
    change HasFDerivAt ((chartAt E x) ∘ (chartAt E y).symm)
      (tangentCoordChange 𝓘(ℝ, E) y x p) (chartAt E y p)
    simpa only [mfld_simps, hasFDerivWithinAt_univ] using
      (hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, E)) (x := y) (y := x) (z := p)
        ⟨by simpa only [extChartAt_source] using hy,
          by simpa only [extChartAt_source] using hx⟩)
  have hdet : 0 < LinearMap.det (fderiv ℝ e (chartAt E x p)).toLinearMap := by
    have h := det_pos_of_orientations_agree
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv
      o ω hxori hyori
    have hd := tangent_trivialization_transition_eq_fderiv x y p hx hy
    change _ = fderiv ℝ e (chartAt E x p) at hd
    rw [← hd]
    exact h
  refine ⟨he, hep, ?_⟩
  have hsign := integralLocalHomologyOpenPartialHomeomorphIso_translation_eq_det_sign
    e (chartAt E x p) he hf.differentiableAt hf'.differentiableAt
  rw [sign_pos hdet, SignType.coe_one, one_smul] at hsign
  exact hsign

theorem oriented_local_homology_chart_maps_eq
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (x y p : M) (hx : p ∈ (chartAt E x).source) (hy : p ∈ (chartAt E y).source)
    (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) p) (Fin (Module.finrank ℝ E)))
    (hori : Orientation.map _
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o =
      Orientation.map _
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv o) :
    (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E x p)))
        (show MapsTo (Homeomorph.subRight (chartAt E x p))
          ({chartAt E x p}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E x) p hx).hom.hom =
      (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E y p)))
        (show MapsTo (Homeomorph.subRight (chartAt E y p))
          ({chartAt E y p}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E y) p hy).hom.hom := by
  let n := Module.finrank ℝ E
  let e := chartAt E x
  let f := chartAt E y
  let g := e.symm.trans f
  let ω := Orientation.map _
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o
  obtain ⟨hga, _, hsign⟩ := oriented_chart_transition_local_homology x y p hx hy o ω rfl hori.symm
  let U := e.source ∩ f.source
  have hU : IsOpen U := e.open_source.inter f.open_source
  have hpU : p ∈ U := ⟨hx, hy⟩
  have hUe : U ⊆ e.source := fun _ hz => hz.1
  have hUf : U ⊆ f.source := fun _ hz => hz.2
  let J := integralLocalHomologyNeighborhoodIso n p U hU hpU
  let Jg := integralLocalHomologyNeighborhoodIso n (e p) g.source g.open_source hga
  let Ie := integralLocalHomologyOpenPartialHomeomorphIso n e p hx
  let If := integralLocalHomologyOpenPartialHomeomorphIso n f p hy
  let Ig := integralLocalHomologyOpenPartialHomeomorphIso n g (e p) hga
  have hUeg : MapsTo e U g.source := by
    intro z hz
    change e z ∈ e.target ∧ e.symm (e z) ∈ f.source
    refine ⟨e.map_source hz.1, ?_⟩
    rw [e.left_inv hz.1]
    exact hz.2
  let q : C(U, g.source) :=
    ⟨fun z => ⟨e z, hUeg z.property⟩,
      ((e.continuousOn.mono hUe).domRestrict).subtype_mk _⟩
  have hq : MapsTo q ({(⟨p, hpU⟩ : U)}ᶜ : Set U)
      ({(⟨e p, hga⟩ : g.source)}ᶜ : Set g.source) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    apply e.injOn z.property.1 hx
    exact congrArg (fun w : g.source => (w : E)) heq
  let F : C(U, E) := ⟨fun z => f z, (f.continuousOn.mono hUf).domRestrict⟩
  have hF : MapsTo F ({(⟨p, hpU⟩ : U)}ᶜ : Set U) ({f p}ᶜ : Set E) :=
    fun z hz heq => hz (Subtype.ext (f.injOn z.property.2 hy heq))
  let G : C(g.source, E) := ⟨fun z => g z, g.continuousOn.domRestrict⟩
  have hG : MapsTo G ({(⟨e p, hga⟩ : g.source)}ᶜ : Set g.source)
      ({g (e p)}ᶜ : Set E) :=
    fun z hz heq => hz (Subtype.ext (g.injOn z.property hga heq))
  let Te := toContinuousMap (Homeomorph.subRight (e p))
  let Tf := toContinuousMap (Homeomorph.subRight (f p))
  let Tg := toContinuousMap (Homeomorph.subRight (g (e p)))
  have hTe : MapsTo Te ({e p}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hz => sub_ne_zero.mpr hz
  have hTf : MapsTo Tf ({f p}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hz => sub_ne_zero.mpr hz
  have hTg : MapsTo Tg ({g (e p)}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hz => sub_ne_zero.mpr hz
  change (integralRelativeHomologyMap n Tg hTg).comp Ig.hom.hom =
    integralRelativeHomologyMap n Te hTe at hsign
  have heJ : Ie.hom.hom.comp J.hom.hom =
      Jg.hom.hom.comp (integralRelativeHomologyMap n q hq) := by
    rw [integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood n e p U hU hpU hUe]
    change integralRelativeHomologyMap n _ _ =
      (integralRelativeHomologyMap n _ _).comp (integralRelativeHomologyMap n _ _)
    rw [← integralRelativeHomologyMap_comp]
    rfl
  have hfJ : If.hom.hom.comp J.hom.hom = integralRelativeHomologyMap n F hF :=
    integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood n f p U hU hpU hUf
  have hgJ : Ig.hom.hom.comp Jg.hom.hom = integralRelativeHomologyMap n G hG :=
    integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
      n g (e p) g.source g.open_source hga Subset.rfl
  have hmiddle : Ig.hom.hom.comp (Jg.hom.hom.comp (integralRelativeHomologyMap n q hq)) =
      (integralRelativeHomologyMap n G hG).comp (integralRelativeHomologyMap n q hq) := by
    rw [← LinearMap.comp_assoc, hgJ]
  have hmaps : Tg.comp (G.comp q) = Tf.comp F := by
    ext z
    change f (e.symm (e z)) - f (e.symm (e p)) = f z - f p
    rw [e.left_inv z.property.1, e.left_inv hx]
  let L := (integralRelativeHomologyMap n Te hTe).comp Ie.hom.hom
  let R := (integralRelativeHomologyMap n Tf hTf).comp If.hom.hom
  have hcomp : L.comp J.hom.hom = R.comp J.hom.hom := by
    calc
      L.comp J.hom.hom = (integralRelativeHomologyMap n Te hTe).comp
          (Ie.hom.hom.comp J.hom.hom) := LinearMap.comp_assoc _ _ _
      _ = ((integralRelativeHomologyMap n Tg hTg).comp Ig.hom.hom).comp
          (Ie.hom.hom.comp J.hom.hom) := by rw [hsign]
      _ = (integralRelativeHomologyMap n Tg hTg).comp
          (Ig.hom.hom.comp (Jg.hom.hom.comp (integralRelativeHomologyMap n q hq))) := by
        rw [heJ, LinearMap.comp_assoc]
      _ = (integralRelativeHomologyMap n Tg hTg).comp
          ((integralRelativeHomologyMap n G hG).comp (integralRelativeHomologyMap n q hq)) := by
        rw [hmiddle]
      _ = (integralRelativeHomologyMap n Tf hTf).comp (integralRelativeHomologyMap n F hF) := by
        rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp,
          ← integralRelativeHomologyMap_comp]
        simp only [hmaps]
      _ = (integralRelativeHomologyMap n Tf hTf).comp (If.hom.hom.comp J.hom.hom) := by rw [hfJ]
      _ = R.comp J.hom.hom := (LinearMap.comp_assoc _ _ _).symm
  change L = R
  apply LinearMap.ext
  intro z
  have hz : J.hom.hom (J.inv.hom z) = z := congrArg (fun k => k.hom z) J.inv_hom_id
  have h := LinearMap.congr_fun hcomp (J.inv.hom z)
  change L (J.hom.hom (J.inv.hom z)) = R (J.hom.hom (J.inv.hom z)) at h
  rw [hz] at h
  exact h

end Poincare.Topology
