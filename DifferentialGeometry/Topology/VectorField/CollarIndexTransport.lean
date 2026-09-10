import DifferentialGeometry.Topology.VectorField.CollarIndexCoordinates
import DifferentialGeometry.Topology.VectorField.CollarIndexZeros
import DifferentialGeometry.Topology.VectorField.InteriorIndexTransport
import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField
open Poincare.LocalDegree
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]

private theorem collar_coordinate_data
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ} (hx : x ∈ f.source)
    (hT : HasContinuousIsolatedZero I T (f x)) (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b (f x))
    (hz : collarExtension T b collarTransition (f x, t) = 0) :
    isolatedZero (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f T) x ∧
      ContDiffAt ℝ 1 (b ∘ f) x ∧
      collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))))
        (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f T)
        (b ∘ f) collarTransition (x, t) = 0 := by
  refine ⟨hT.model_pullback I f le_rfl hx, ?_, ?_⟩
  · exact contMDiffAt_iff_contDiffAt.mp
      (hb.comp x (f.contMDiffOn.contMDiffAt (f.open_source.mem_nhds hx)))
  · apply Prod.ext
    · exact (mpullback_partialDiffeomorph_eq_zero_iff f one_ne_zero T hx).mpr (congrArg Prod.fst hz)
    · have hnormal : (1 - collarTransition t) * b (f x) + collarTransition t = 0 :=
        congrArg Prod.snd hz
      exact hnormal

omit [IsManifold I 1 M] in
theorem mpullback_collarExtension_collarParametrization_germ
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    (T : ∀ x : M, TangentSpace I x) (b : M → ℝ) (ρ : ℝ → ℝ)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ f.source) (t : ℝ) :
    _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
        (I.prod 𝓘(ℝ, ℝ)) (collarParametrization I f) (collarExtension T b ρ) =ᶠ[𝓝 (euclideanProductPoint d x t)]
      euclideanCollarExtension (_root_.VectorField.mpullback
        𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f T) (b ∘ f) ρ := by
  have hp : euclideanProductPoint d x t ∈ (collarParametrization I f).source := by
    apply (collarParametrization_mem_source I f _).mpr
    change ((euclideanProductChart d) ((euclideanProductChart d).symm (x, t))).1 ∈ f.source
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx
  filter_upwards [(collarParametrization I f).open_source.mem_nhds hp] with z hz
  exact mpullback_collarExtension_collarParametrization I f T b ρ hz

theorem isolatedZero_mpullback_collarParametrization
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ} (hx : x ∈ f.source)
    (hT : HasContinuousIsolatedZero I T (f x)) (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b (f x))
    (hb0 : b (f x) ≠ 0) (hz : collarExtension T b collarTransition (f x, t) = 0) :
    isolatedZero (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      (I.prod 𝓘(ℝ, ℝ)) (collarParametrization I f) (collarExtension T b collarTransition))
      (euclideanProductPoint d x t) := by
  obtain ⟨hi, hb', hz'⟩ := collar_coordinate_data I f hx hT hb hz
  have hP := isolatedZero_euclideanCollarExtension hi hb' hb0 hz'
  exact (isolatedZero_congr (mpullback_collarExtension_collarParametrization_germ I f T b
    collarTransition hx t)).mpr hP

theorem localDegree_mpullback_collarParametrization
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ} (hx : x ∈ f.source)
    (hT : HasContinuousIsolatedZero I T (f x)) (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b (f x))
    (hb0 : b (f x) ≠ 0) (hz : collarExtension T b collarTransition (f x, t) = 0) :
    euclideanLocalDegree (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
        (I.prod 𝓘(ℝ, ℝ)) (collarParametrization I f) (collarExtension T b collarTransition))
        (euclideanProductPoint d x t) (isolatedZero_mpullback_collarParametrization I f hx hT hb hb0 hz) =
      interiorIndex I T (f x) hT
        (Poincare.Manifold.isInteriorPoint_of_model_partialDiffeomorph I 1 f one_ne_zero hx) := by
  obtain ⟨hi, hb', hz'⟩ := collar_coordinate_data I f hx hT hb hz
  have hP := isolatedZero_euclideanCollarExtension hi hb' hb0 hz'
  have he := euclideanLocalDegree_congr
    (isolatedZero_mpullback_collarParametrization I f hx hT hb hb0 hz) hP
    (mpullback_collarExtension_collarParametrization_germ I f T b collarTransition hx t)
  exact he.trans ((euclideanLocalDegree_collarExtension hi hb' hb0 hz').trans
    (interiorIndex_eq_localDegree I f hx hT).symm)


theorem isolatedZero_mpullback_collarInteriorChart
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {x : M} {t : ℝ}
    (hT : HasContinuousIsolatedZero I T x) (hx : I.IsInteriorPoint x)
    (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension T b collarTransition (x, t) = 0) :
    isolatedZero (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      (I.prod 𝓘(ℝ, ℝ)) (collarParametrization I (Poincare.Manifold.interiorChart I 1 x).symm)
      (collarExtension T b collarTransition))
      (euclideanProductPoint d (Poincare.Manifold.interiorChart I 1 x x) t) := by
  let c := Poincare.Manifold.interiorChart I 1 x
  have hcx : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx
  have he : c.symm (c x) = x := c.left_inv hcx
  have hT' : HasContinuousIsolatedZero I T (c.symm (c x)) := he.symm ▸ hT
  have hb' : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b (c.symm (c x)) := he.symm ▸ hb
  have hb0' : b (c.symm (c x)) ≠ 0 := by simpa only [he] using hb0
  have hz' : collarExtension T b collarTransition (c.symm (c x), t) = 0 := he.symm ▸ hz
  exact isolatedZero_mpullback_collarParametrization I c.symm (c.map_source hcx) hT' hb' hb0' hz'

theorem localDegree_mpullback_collarInteriorChart
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {x : M} {t : ℝ}
    (hT : HasContinuousIsolatedZero I T x) (hx : I.IsInteriorPoint x)
    (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension T b collarTransition (x, t) = 0) :
    euclideanLocalDegree (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
        (I.prod 𝓘(ℝ, ℝ)) (collarParametrization I (Poincare.Manifold.interiorChart I 1 x).symm)
        (collarExtension T b collarTransition))
        (euclideanProductPoint d (Poincare.Manifold.interiorChart I 1 x x) t)
        (isolatedZero_mpullback_collarInteriorChart I hT hx hb hb0 hz) =
      interiorIndex I T x hT hx := by
  let c := Poincare.Manifold.interiorChart I 1 x
  have hcx : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx
  have he : c.symm (c x) = x := c.left_inv hcx
  have hT' : HasContinuousIsolatedZero I T (c.symm (c x)) := he.symm ▸ hT
  have hb' : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b (c.symm (c x)) := he.symm ▸ hb
  have hb0' : b (c.symm (c x)) ≠ 0 := by simpa only [he] using hb0
  have hz' : collarExtension T b collarTransition (c.symm (c x), t) = 0 := he.symm ▸ hz
  have hd := localDegree_mpullback_collarParametrization I c.symm (c.map_source hcx) hT' hb' hb0' hz'
  simpa only [he] using hd

section Ambient
variable {G N : Type*} [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 2))) G) [IsManifold J 1 N]

omit [IsManifold I 1 M] [IsManifold J 1 N] in
theorem isInteriorPoint_collar_image
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (M × ℝ) N 1)
    {x : M} {t : ℝ} (hΦ : (x, t) ∈ Φ.source) (hx : I.IsInteriorPoint x) :
    J.IsInteriorPoint (Φ (x, t)) := by
  have hp : (I.prod 𝓘(ℝ, ℝ)).IsInteriorPoint (x, t) := by
    change (x, t) ∈ (I.prod 𝓘(ℝ, ℝ)).interior (M × ℝ)
    rw [ModelWithCorners.interior_prod]
    exact ⟨hx, BoundarylessManifold.isInteriorPoint⟩
  have hloc : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, ℝ)) J 1 Φ (x, t) :=
    ⟨Φ, hΦ, fun _ _ => rfl⟩
  exact (hloc.isInteriorPoint_iff one_ne_zero).mp hp

theorem HasContinuousIsolatedZero.collarPushforward
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (M × ℝ) N 1)
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {x : M} {t : ℝ}
    (hΦ : (x, t) ∈ Φ.source) (hT : HasContinuousIsolatedZero I T x)
    (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b x) (hb0 : b x ≠ 0)
    (hz : Poincare.VectorField.collarExtension T b collarTransition (x, t) = 0) :
    HasContinuousIsolatedZero J (_root_.VectorField.mpullback J (I.prod 𝓘(ℝ, ℝ)) Φ.symm
      (Poincare.VectorField.collarExtension T b collarTransition)) (Φ (x, t)) := by
  have hW := hT.collarExtension_of_contMDiffAt I hb hb0 hz
  have hW' : HasContinuousIsolatedZero (I.prod 𝓘(ℝ, ℝ))
      (Poincare.VectorField.collarExtension T b collarTransition) (Φ.symm (Φ (x, t))) :=
    (Φ.left_inv hΦ).symm ▸ hW
  exact hW'.mpullback J (I.prod 𝓘(ℝ, ℝ)) Φ.symm le_rfl (Φ.map_source hΦ)

theorem interiorIndex_collarPushforward
    (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (M × ℝ) N 1)
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {x : M} {t : ℝ}
    (hΦ : (x, t) ∈ Φ.source) (hT : HasContinuousIsolatedZero I T x)
    (hx : I.IsInteriorPoint x) (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension T b collarTransition (x, t) = 0) :
    interiorIndex J (_root_.VectorField.mpullback J (I.prod 𝓘(ℝ, ℝ)) Φ.symm
        (collarExtension T b collarTransition)) (Φ (x, t))
        (hT.collarPushforward I J Φ hΦ hb hb0 hz) (isInteriorPoint_collar_image I J Φ hΦ hx) =
      interiorIndex I T x hT hx := by
  let c := Poincare.Manifold.interiorChart I 1 x
  have hcx : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I 1 x).mpr hx
  let P := collarParametrization I c.symm
  let a := euclideanProductPoint d (c x) t
  have ha : a ∈ P.source := by
    apply (collarParametrization_mem_source I c.symm a).mpr
    change ((euclideanProductChart d) ((euclideanProductChart d).symm (c x, t))).1 ∈ c.target
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using c.map_source hcx
  have hPa : P a = (x, t) := by
    change collarParametrization I c.symm (euclideanProductPoint d (c x) t) = _
    rw [collarParametrization_point]
    exact Prod.ext (c.left_inv hcx) rfl
  let Γ := P.trans Φ
  have hΓa : a ∈ Γ.source := by
    refine ⟨ha, ?_⟩
    change P a ∈ Φ.source
    exact hPa.symm ▸ hΦ
  have hcenter : Γ a = Φ (x, t) := congrArg Φ hPa
  let W := collarExtension T b collarTransition
  let V := _root_.VectorField.mpullback J (I.prod 𝓘(ℝ, ℝ)) Φ.symm W
  have hV := hT.collarPushforward I J Φ hΦ hb hb0 hz
  have hV' : HasContinuousIsolatedZero J V (Γ a) := hcenter.symm ▸ hV
  have hP := isolatedZero_mpullback_collarInteriorChart I hT hx hb hb0 hz
  have hΓ := hV'.model_pullback J Γ le_rfl hΓa
  have heq : _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2))) J Γ V =ᶠ[𝓝 a]
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
        (I.prod 𝓘(ℝ, ℝ)) P W := by
    filter_upwards [Γ.open_source.mem_nhds hΓa] with z hz
    exact mpullback_trans_symm_partialDiffeomorph P Φ one_ne_zero W hz.1 hz.2
  have hd := (interiorIndex_eq_localDegree J Γ hΓa hV').trans
    ((euclideanLocalDegree_congr hΓ hP heq).trans
      (localDegree_mpullback_collarInteriorChart I hT hx hb hb0 hz))
  simpa only [hcenter] using hd

end Ambient
end Poincare.VectorField
