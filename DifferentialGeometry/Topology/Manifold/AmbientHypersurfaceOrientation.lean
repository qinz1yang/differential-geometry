import Mathlib.Geometry.Manifold.Instances.Real
import DifferentialGeometry.Topology.Manifold.BoundaryOrientationVariation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
# Orientation of a surface mapped into an oriented 3-manifold with a transverse field

Let `f : M → N` be a `C¹` map from a smooth surface to a smooth oriented 3-manifold and let `ν`
be a continuous vector field along `f` such that `(t, v) ↦ t ν x + df_x v` is bijective at every
point. Then `M` carries the smooth orientation for which `(ν, positive basis of T_x M)` is
positive in `N` (`ambientHypersurfaceSmoothOrientation`). This is the manifold-target version of
`hypersurfaceSmoothOrientation` (whose target is `ℝ³`), with only `C¹` regularity of `f`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Module Manifold TopologicalSpace Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The standard basis of the surface model. -/
def ambientSurfaceBasis : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

/-- Reindexing of the surface orientations. -/
def ambientSurfaceIndex : Fin 2 ≃ Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) :=
  finCongr (by simp)

/-- Reindexing of the ambient orientations. -/
def ambientSpaceIndex : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ≃ Fin 3 :=
  finCongr (by simp)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E2 M] [IsManifold (𝓡 2) ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]

/-- The frame `(t, v) ↦ t ν x + df_x v`. -/
def ambientNormalFrame (f : M → N) (ν : ∀ x, TangentSpace (𝓡 3) (f x)) (x : M) :
    (ℝ × E2) →L[ℝ] E3 :=
  (ContinuousLinearMap.fst ℝ ℝ E2).smulRight (ν x : E3) +
    (mfderiv (𝓡 2) (𝓡 3) f x : E2 →L[ℝ] E3).comp (ContinuousLinearMap.snd ℝ ℝ E2)

omit [IsManifold (𝓡 2) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem ambientNormalFrame_apply (f : M → N) (ν : ∀ x, TangentSpace (𝓡 3) (f x)) (x : M)
    (v : ℝ × E2) :
    ambientNormalFrame f ν x v = v.1 • (ν x : E3) + mfderiv (𝓡 2) (𝓡 3) f x v.2 := rfl

/-- The frame as a linear equivalence. -/
def ambientNormalFrameEquiv (f : M → N) (ν : ∀ x, TangentSpace (𝓡 3) (f x))
    (h : ∀ x, Bijective (ambientNormalFrame f ν x)) (x : M) : (ℝ × E2) ≃L[ℝ] E3 :=
  (LinearEquiv.ofBijective (ambientNormalFrame f ν x).toLinearMap (h x)).toContinuousLinearEquiv

/-- The orientation field: `normalFirstOrientation` of the frame against the orientation of `N`
at `f x`. -/
def ambientHypersurfaceOrientationField (f : M → N) (ν : ∀ x, TangentSpace (𝓡 3) (f x))
    (h : ∀ x, Bijective (ambientNormalFrame f ν x)) (o : SmoothOrientation (𝓡 3) N) (x : M) :
    Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) :=
  Orientation.reindex ℝ E2 ambientSurfaceIndex
    (normalFirstOrientation (ambientNormalFrameEquiv f ν h x).toLinearEquiv ambientSurfaceBasis
      (Orientation.reindex ℝ E3 ambientSpaceIndex (o.val (f x))))

/-- The chart domain at `p`: the chart of `M` at `p`, intersected with the preimage of the chart
of `N` at `f p`. -/
def ambientChartDomain (f : M → N) (hf : Continuous f) (p : M) : Opens M :=
  ⟨(chartAt E2 p).source ∩ f ⁻¹' (chartAt E3 (f p)).source,
    (chartAt E2 p).open_source.inter ((chartAt E3 (f p)).open_source.preimage hf)⟩

omit [IsManifold (𝓡 2) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem ambientChartDomain_mem_left (f : M → N) (hf : Continuous f) (p : M)
    (x : ambientChartDomain f hf p) : x.val ∈ (chartAt E2 p).source := x.property.1

omit [IsManifold (𝓡 2) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem ambientChartDomain_mem_right (f : M → N) (hf : Continuous f) (p : M)
    (x : ambientChartDomain f hf p) : f x.val ∈ (chartAt E3 (f p)).source := x.property.2

/-- The frame in the charts at `p` and `f p`. -/
def ambientFrameInCharts (f : M → N) (hf : Continuous f) (ν : ∀ x, TangentSpace (𝓡 3) (f x))
    (h : ∀ x, Bijective (ambientNormalFrame f ν x)) (p : M) (x : ambientChartDomain f hf p) :
    (ℝ × E2) ≃L[ℝ] E3 :=
  (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (preferredChartTangentEquiv (𝓡 2) p x.val (ambientChartDomain_mem_left f hf p x)).symm).trans
      (ambientNormalFrameEquiv f ν h x.val)).trans
    (preferredChartTangentEquiv (𝓡 3) (f p) (f x.val) (ambientChartDomain_mem_right f hf p x))

omit [IsManifold (𝓡 3) ∞ N] in
private theorem orientation_map_reindex_two (A : E2 ≃ₗ[ℝ] E2) (q : Orientation ℝ E2 (Fin 2)) :
    Orientation.map (Fin (Module.finrank ℝ E2)) A (Orientation.reindex ℝ E2 ambientSurfaceIndex q) =
      Orientation.reindex ℝ E2 ambientSurfaceIndex (Orientation.map (Fin 2) A q) := by
  induction q using Module.Ray.ind
  rfl

private theorem orientation_map_reindex_three (A : E3 ≃ₗ[ℝ] E3)
    (q : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    Orientation.map (Fin 3) A (Orientation.reindex ℝ E3 ambientSpaceIndex q) =
      Orientation.reindex ℝ E3 ambientSpaceIndex (Orientation.map _ A q) := by
  induction q using Module.Ray.ind
  rfl

/-- The chart representation of the orientation field. -/
theorem ambient_chart_representation (f : M → N) (hf : Continuous f)
    (ν : ∀ x, TangentSpace (𝓡 3) (f x)) (h : ∀ x, Bijective (ambientNormalFrame f ν x))
    (o : SmoothOrientation (𝓡 3) N) (p : M) (x : ambientChartDomain f hf p) :
    Orientation.map _ (preferredChartTangentEquiv (𝓡 2) p x.val (ambientChartDomain_mem_left f hf p x)).toLinearEquiv
      (ambientHypersurfaceOrientationField f ν h o x.val) =
      Orientation.reindex ℝ E2 ambientSurfaceIndex
        (normalFirstOrientation (ambientFrameInCharts f hf ν h p x).toLinearEquiv
          ambientSurfaceBasis
          (Orientation.reindex ℝ E3 ambientSpaceIndex (Orientation.map _
            (preferredChartTangentEquiv (𝓡 3) (f p) (f x.val) (ambientChartDomain_mem_right f hf p x)).toLinearEquiv
            (o.val (f x.val))))) := by
  rw [ambientHypersurfaceOrientationField, orientation_map_reindex_two]
  congr 1
  rw [← orientation_map_reindex_three]
  have hchange := normalFirstOrientation_change_boundary
    (ambientNormalFrameEquiv f ν h x.val).toLinearEquiv
    (preferredChartTangentEquiv (𝓡 2) p x.val (ambientChartDomain_mem_left f hf p x)).symm.toLinearEquiv
    ambientSurfaceBasis ambientSurfaceBasis
    (Orientation.reindex ℝ E3 ambientSpaceIndex (o.val (f x.val)))
  have hmap := normalFirstOrientation_map
    (((LinearEquiv.refl ℝ ℝ).prodCongr
      (preferredChartTangentEquiv (𝓡 2) p x.val (ambientChartDomain_mem_left f hf p x)).symm.toLinearEquiv).trans
      (ambientNormalFrameEquiv f ν h x.val).toLinearEquiv)
    (preferredChartTangentEquiv (𝓡 3) (f p) (f x.val) (ambientChartDomain_mem_right f hf p x)).toLinearEquiv
    ambientSurfaceBasis (Orientation.reindex ℝ E3 ambientSpaceIndex (o.val (f x.val)))
  exact hchange.symm.trans hmap.symm

omit [IsManifold (𝓡 2) ∞ M] in
private theorem preferred_three_apply_eq_trivialization (q y : N)
    (hy : y ∈ (chartAt E3 q).source) (w : E3) :
    (preferredChartTangentEquiv (𝓡 3) q y hy w : E3) =
      ((trivializationAt E3 (TangentSpace (𝓡 3)) q) ⟨y, w⟩).2 := by
  have hb : y ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  have h1 := congrArg (fun L : E3 →L[ℝ] E3 => L w)
    (trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv (𝓡 3) q y hy)
  refine h1.symm.trans ?_
  change (trivializationAt E3 (TangentSpace (𝓡 3)) q).continuousLinearMapAt ℝ y w = _
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_def_of_mem _ hb]
  rfl

/-- The derivative of `f` in the charts at `p` and `f p`, evaluated. -/
private theorem ambient_derivative_in_chart_apply (f : M → N) (hf : Continuous f) (p : M)
    (x : ambientChartDomain f hf p) (v : E2) :
    inTangentCoordinates (𝓡 2) (𝓡 3) id f (mfderiv (𝓡 2) (𝓡 3) f) p x.val v =
      preferredChartTangentEquiv (𝓡 3) (f p) (f x.val) (ambientChartDomain_mem_right f hf p x)
        (mfderiv (𝓡 2) (𝓡 3) f x.val
          ((preferredChartTangentEquiv (𝓡 2) p x.val (ambientChartDomain_mem_left f hf p x)).symm v)) := by
  have h := inTangentCoordinates_eq_mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (f := id) (g := f)
    (ϕ := mfderiv (𝓡 2) (𝓡 3) f) (ambientChartDomain_mem_left f hf p x) (ambientChartDomain_mem_right f hf p x)
  have hv := congrArg (fun A : E2 →L[ℝ] E3 => A v) h
  change inTangentCoordinates (𝓡 2) (𝓡 3) id f (mfderiv (𝓡 2) (𝓡 3) f) p x.val v =
    (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (f p)) (f x.val) : E3 →L[ℝ] E3)
      ((mfderiv (𝓡 2) (𝓡 3) f x.val : E2 →L[ℝ] E3)
        (mfderivWithin (𝓡 2) (𝓡 2) (extChartAt (𝓡 2) p).symm (range (𝓡 2))
          (extChartAt (𝓡 2) p x.val) v)) at hv
  refine hv.trans ?_
  rw [preferredChartTangentEquiv_symm_apply]
  rfl

theorem ambientFrameInCharts_apply (f : M → N) (hf : Continuous f)
    (ν : ∀ x, TangentSpace (𝓡 3) (f x)) (h : ∀ x, Bijective (ambientNormalFrame f ν x))
    (p : M) (x : ambientChartDomain f hf p) (v : ℝ × E2) :
    ambientFrameInCharts f hf ν h p x v =
      preferredChartTangentEquiv (𝓡 3) (f p) (f x.val) (ambientChartDomain_mem_right f hf p x)
        (v.1 • (ν x.val : E3) + mfderiv (𝓡 2) (𝓡 3) f x.val
          ((preferredChartTangentEquiv (𝓡 2) p x.val (ambientChartDomain_mem_left f hf p x)).symm v.2)) := rfl

/-- **Continuity of the frame in charts.** -/
theorem ambientFrameInCharts_continuousAt (f : M → N) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    (ν : ∀ x, TangentSpace (𝓡 3) (f x))
    (hν : Continuous (fun x => (⟨f x, ν x⟩ : TangentBundle (𝓡 3) N)))
    (h : ∀ x, Bijective (ambientNormalFrame f ν x)) (p : M) :
    ContinuousAt (fun x : ambientChartDomain f hf.continuous p =>
      (ambientFrameInCharts f hf.continuous ν h p x : (ℝ × E2) →L[ℝ] E3))
      ⟨p, mem_chart_source E2 p, mem_chart_source E3 (f p)⟩ := by
  let U := ambientChartDomain f hf.continuous p
  let pU : U := ⟨p, mem_chart_source E2 p, mem_chart_source E3 (f p)⟩
  let T := trivializationAt E3 (TangentSpace (𝓡 3)) (f p)
  have hD0 : ContinuousAt (inTangentCoordinates (𝓡 2) (𝓡 3) id f
      (mfderiv (𝓡 2) (𝓡 3) f) p) p :=
    (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have hD : ContinuousAt (fun x : U => inTangentCoordinates (𝓡 2) (𝓡 3) id f
      (mfderiv (𝓡 2) (𝓡 3) f) p x.val) pU :=
    hD0.comp_of_eq continuous_subtype_val.continuousAt rfl
  have hsrc : ∀ x : U, (⟨f x.val, ν x.val⟩ : TangentBundle (𝓡 3) N) ∈ T.source := by
    intro x
    rw [T.mem_source, TangentBundle.trivializationAt_baseSet]
    exact ambientChartDomain_mem_right f hf.continuous p x
  have hN : ContinuousAt (fun x : U => (T ⟨f x.val, ν x.val⟩).2) pU := by
    have h1 : ContinuousAt (fun z : TangentBundle (𝓡 3) N => T z) ⟨f p, ν p⟩ :=
      T.continuousOn.continuousAt (T.open_source.mem_nhds (hsrc pU))
    have hc : ContinuousAt (fun x : U => T ⟨f x.val, ν x.val⟩) pU :=
      h1.comp_of_eq (hν.comp continuous_subtype_val).continuousAt rfl
    exact continuous_snd.continuousAt.comp hc
  have hR : ContinuousAt (fun x : U =>
      (ContinuousLinearMap.fst ℝ ℝ E2).smulRight (T ⟨f x.val, ν x.val⟩).2 +
        (inTangentCoordinates (𝓡 2) (𝓡 3) id f (mfderiv (𝓡 2) (𝓡 3) f) p x.val).comp
          (ContinuousLinearMap.snd ℝ ℝ E2)) pU :=
    (((ContinuousLinearMap.smulRightL ℝ (ℝ × E2) E3
      (ContinuousLinearMap.fst ℝ ℝ E2)).continuous.continuousAt).comp hN).add
      (hD.clm_comp continuousAt_const)
  refine hR.congr (Eventually.of_forall fun x => ?_)
  apply ContinuousLinearMap.ext
  intro v
  change ((ContinuousLinearMap.fst ℝ ℝ E2).smulRight (T ⟨f x.val, ν x.val⟩).2 +
      (inTangentCoordinates (𝓡 2) (𝓡 3) id f (mfderiv (𝓡 2) (𝓡 3) f) p x.val).comp
        (ContinuousLinearMap.snd ℝ ℝ E2)) v = ambientFrameInCharts f hf.continuous ν h p x v
  have key : ∀ (D : E3 ≃L[ℝ] E3) (a : ℝ) (u w : E3), D (a • u + w) = a • D u + D w :=
    fun D a u w => by rw [map_add, map_smul]
  rw [ambientFrameInCharts_apply]
  refine Eq.trans ?_ (key _ _ _ _).symm
  refine congrArg₂ (fun a b : E3 => a + b) ?_ ?_
  · change v.1 • (T ⟨f x.val, ν x.val⟩).2 = _
    exact congrArg (v.1 • ·) (preferred_three_apply_eq_trivialization (f p) (f x.val)
      (ambientChartDomain_mem_right f hf.continuous p x) (ν x.val)).symm
  · exact ambient_derivative_in_chart_apply f hf.continuous p x v.2

/-- **The orientation of a surface in an oriented 3-manifold with a transverse field.** -/
def ambientHypersurfaceSmoothOrientation (f : M → N) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    (ν : ∀ x, TangentSpace (𝓡 3) (f x))
    (hν : Continuous (fun x => (⟨f x, ν x⟩ : TangentBundle (𝓡 3) N)))
    (h : ∀ x, Bijective (ambientNormalFrame f ν x)) (o : SmoothOrientation (𝓡 3) N) :
    SmoothOrientation (𝓡 2) M := by
  apply smoothOrientationOfLocalRepresentations (𝓡 2)
    (ambientHypersurfaceOrientationField f ν h o)
  intro p
  let S := ambientChartDomain f hf.continuous p
  let pS : S := ⟨p, mem_chart_source E2 p, mem_chart_source E3 (f p)⟩
  let g : S → Orientation ℝ E2 (Fin (Module.finrank ℝ E2)) := fun x =>
    Orientation.map _ (preferredChartTangentEquiv (𝓡 2) p x.val
      (ambientChartDomain_mem_left f hf.continuous p x)).toLinearEquiv
      (ambientHypersurfaceOrientationField f ν h o x.val)
  let rep : (chartAt E3 (f p)).source → Orientation ℝ E3 (Fin (Module.finrank ℝ E3)) := fun y =>
    Orientation.map _ (preferredChartTangentEquiv (𝓡 3) (f p) y.val y.property).toLinearEquiv
      (o.val y.val)
  let tgt : S → (chartAt E3 (f p)).source := fun x =>
    ⟨f x.val, ambientChartDomain_mem_right f hf.continuous p x⟩
  have htgt : Continuous tgt := (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hloc : IsLocallyConstant (rep ∘ tgt) := (o.property (f p)).comp_continuous htgt
  have hg : ∀ᶠ x in 𝓝 pS, g x = g pS := by
    have hev1 := hloc.eventually_eq pS
    have hev2 := normalFirstOrientation_eventually_eq
      (fun x => ambientFrameInCharts f hf.continuous ν h p x) ambientSurfaceBasis pS
      (ambientFrameInCharts_continuousAt f hf ν hν h p)
      (Orientation.reindex ℝ E3 ambientSpaceIndex (rep (tgt pS)))
    filter_upwards [hev1, hev2] with x h1 h2
    have hx := ambient_chart_representation f hf.continuous ν h o p x
    have hp := ambient_chart_representation f hf.continuous ν h o p pS
    change g x = _ at hx
    change g pS = _ at hp
    rw [hx, hp]
    change Orientation.reindex ℝ E2 ambientSurfaceIndex
        (normalFirstOrientation (ambientFrameInCharts f hf.continuous ν h p x).toLinearEquiv
          ambientSurfaceBasis (Orientation.reindex ℝ E3 ambientSpaceIndex ((rep ∘ tgt) x))) =
      Orientation.reindex ℝ E2 ambientSurfaceIndex
        (normalFirstOrientation (ambientFrameInCharts f hf.continuous ν h p pS).toLinearEquiv
          ambientSurfaceBasis (Orientation.reindex ℝ E3 ambientSpaceIndex ((rep ∘ tgt) pS)))
    rw [h1]
    exact congrArg (Orientation.reindex ℝ E2 ambientSurfaceIndex) h2
  obtain ⟨U, hU, hp, hloc'⟩ := locallyConstant_neighborhood_of_eventually_eq S pS g hg
  exact ⟨U, fun y hy => (hU hy).1, hp, hloc'⟩

theorem ambientHypersurfaceSmoothOrientation_apply (f : M → N)
    (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f) (ν : ∀ x, TangentSpace (𝓡 3) (f x))
    (hν : Continuous (fun x => (⟨f x, ν x⟩ : TangentBundle (𝓡 3) N)))
    (h : ∀ x, Bijective (ambientNormalFrame f ν x)) (o : SmoothOrientation (𝓡 3) N) (x : M) :
    (ambientHypersurfaceSmoothOrientation f hf ν hν h o).val x =
      ambientHypersurfaceOrientationField f ν h o x := rfl

end DifferentialGeometry.Topology.Manifold
