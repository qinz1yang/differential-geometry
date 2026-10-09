import DifferentialGeometry.Topology.Manifold.SplitInducedOrientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationLocal
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.SmoothMapDifferentialCoordinates

/-!
# Orientation of a manifold mapped into an oriented manifold with a complementary frame

Let `f : S → M` be a `C¹` map between smooth manifolds (any models), `M` oriented, and let
`ν x : F →L T_{f x} M` be a frame along `f` (continuous columns) such that
`(u, v) ↦ ν x u + df_x v` is bijective at every point. Given an ordered basis `bF` of `F`, `S`
carries the smooth orientation for which `(ν x (bF a))_a` followed by `df_x` of a positive basis
of `T_x S` is positive in `M` (`ambientSplitSmoothOrientation`, characterised by
`ambientSplitSmoothOrientation_eq_iff`).

This is the general-rank version of `ambientHypersurfaceSmoothOrientation` (rank one, `𝓡 2 → 𝓡 3`),
built on `splitInducedOrientation` instead of `normalFirstOrientation`; only `C¹` regularity of
`f` is used.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Module Manifold TopologicalSpace Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold I' ∞ S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ιF : Type*}

/-- The frame `(u, v) ↦ ν x u + df_x v`. -/
def ambientSplitFrame (f : S → M) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (x : S) :
    (F × E') →L[ℝ] E :=
  (ν x : F →L[ℝ] E).comp (ContinuousLinearMap.fst ℝ F E') +
    (mfderiv I' I f x : E' →L[ℝ] E).comp (ContinuousLinearMap.snd ℝ F E')

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold I' ∞ S]
  [FiniteDimensional ℝ F] in
theorem ambientSplitFrame_apply (f : S → M) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (x : S)
    (v : F × E') : ambientSplitFrame I I' f ν x v = (ν x v.1 : E) + mfderiv I' I f x v.2 := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold I' ∞ S]
  [FiniteDimensional ℝ F] in
theorem ambientSplitFrame_inl (f : S → M) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (x : S)
    (u : F) : ambientSplitFrame I I' f ν x (u, 0) = ν x u := by
  rw [ambientSplitFrame_apply]
  exact (congrArg (fun y => ν x u + y) (map_zero (mfderiv I' I f x))).trans (add_zero _)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold I' ∞ S]
  [FiniteDimensional ℝ F] in
theorem ambientSplitFrame_inr (f : S → M) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (x : S)
    (v : TangentSpace I' x) : ambientSplitFrame I I' f ν x (0, v) = mfderiv I' I f x v := by
  rw [ambientSplitFrame_apply]
  exact (congrArg (fun y => y + mfderiv I' I f x v) (map_zero (ν x))).trans (zero_add _)

/-- The frame as a linear equivalence. -/
def ambientSplitFrameEquiv (f : S → M) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x))
    (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)) (x : S) : (F × E') ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (ambientSplitFrame I I' f ν x).toLinearMap (h x)).toContinuousLinearEquiv

omit [IsManifold I ∞ M] [IsManifold I' ∞ S] [FiniteDimensional ℝ E] in
theorem ambientSplitFrameEquiv_apply (f : S → M) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x))
    (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)) (x : S) (v : F × E') :
    ambientSplitFrameEquiv I I' f ν h x v = (ν x v.1 : E) + mfderiv I' I f x v.2 := rfl

/-- The orientation field: the orientation of `T_x S` induced by `o (f x)` and the ordered frame
`ν x ∘ bF`. -/
def ambientSplitOrientationField (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ E') ≃ Fin (finrank ℝ E)) (f : S → M)
    (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x))
    (o : SmoothOrientation I M) (x : S) : Orientation ℝ E' (Fin (finrank ℝ E')) :=
  splitInducedOrientation bF (Module.finBasis ℝ E') σ (ambientSplitFrameEquiv I I' f ν h x).toLinearEquiv
    (o.val (f x))

/-- The chart domain at `p`. -/
def ambientSplitChartDomain (f : S → M) (hf : Continuous f) (p : S) : Opens S :=
  ⟨(extChartAt I' p).source ∩ f ⁻¹' (extChartAt I (f p)).source,
    (isOpen_extChartAt_source p).inter ((isOpen_extChartAt_source (f p)).preimage hf)⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold I' ∞ S] in
theorem ambientSplitChartDomain_mem_left (f : S → M) (hf : Continuous f) (p : S)
    (x : ambientSplitChartDomain I I' f hf p) : x.val ∈ (chartAt H' p).source := by
  simpa only [extChartAt_source] using x.property.1

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold I' ∞ S] in
theorem ambientSplitChartDomain_mem_right (f : S → M) (hf : Continuous f) (p : S)
    (x : ambientSplitChartDomain I I' f hf p) : f x.val ∈ (chartAt H (f p)).source := by
  have hx := x.property.2
  rw [mem_preimage, extChartAt_source] at hx
  exact hx

/-- The frame in the charts at `p` and `f p`. -/
def ambientSplitFrameInCharts (f : S → M) (hf : Continuous f)
    (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)) (p : S)
    (x : ambientSplitChartDomain I I' f hf p) : (F × E') ≃L[ℝ] E :=
  (((ContinuousLinearEquiv.refl ℝ F).prodCongr
    (preferredChartTangentEquiv I' p x.val (ambientSplitChartDomain_mem_left I I' f hf p x)).symm).trans
      (ambientSplitFrameEquiv I I' f ν h x.val)).trans
    (preferredChartTangentEquiv I (f p) (f x.val) (ambientSplitChartDomain_mem_right I I' f hf p x))

/-- The chart representation of the orientation field. -/
theorem ambientSplit_chart_representation (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ E') ≃ Fin (finrank ℝ E)) (f : S → M) (hf : Continuous f)
    (ν : ∀ x, F →L[ℝ] TangentSpace I (f x)) (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x))
    (o : SmoothOrientation I M) (p : S) (x : ambientSplitChartDomain I I' f hf p) :
    Orientation.map _
        (preferredChartTangentEquiv I' p x.val (ambientSplitChartDomain_mem_left I I' f hf p x)).toLinearEquiv
        (ambientSplitOrientationField I I' bF σ f ν h o x.val) =
      splitInducedOrientation bF (Module.finBasis ℝ E') σ
        (ambientSplitFrameInCharts I I' f hf ν h p x).toLinearEquiv
        (Orientation.map _ (preferredChartTangentEquiv I (f p) (f x.val)
          (ambientSplitChartDomain_mem_right I I' f hf p x)).toLinearEquiv (o.val (f x.val))) := by
  rw [ambientSplitOrientationField, ← splitInducedOrientation_change,
    ← splitInducedOrientation_map bF (Module.finBasis ℝ E') σ _
      (preferredChartTangentEquiv I (f p) (f x.val)
        (ambientSplitChartDomain_mem_right I I' f hf p x)).toLinearEquiv]
  rfl

omit [IsManifold I' ∞ S] [FiniteDimensional ℝ E'] in
theorem preferredChartTangentEquiv_apply_eq_trivialization_snd (q y : M)
    (hy : y ∈ (chartAt H q).source) (w : E) :
    (preferredChartTangentEquiv I q y hy w : E) =
      ((trivializationAt E (TangentSpace I) q) ⟨y, w⟩).2 := by
  have hb : y ∈ (trivializationAt E (TangentSpace I) q).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  have h1 := congrArg (fun L : E →L[ℝ] E => L w)
    (trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv I q y hy)
  refine h1.symm.trans ?_
  change (trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ y w = _
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_def_of_mem _ hb]
  rfl

/-- The derivative of `f` in the charts at `p` and `f p`, evaluated. -/
theorem ambientSplit_derivative_in_chart_apply (f : S → M) (hf : Continuous f) (p : S)
    (x : ambientSplitChartDomain I I' f hf p) (v : E') :
    inTangentCoordinates I' I id f (mfderiv I' I f) p x.val v =
      preferredChartTangentEquiv I (f p) (f x.val) (ambientSplitChartDomain_mem_right I I' f hf p x)
        (mfderiv I' I f x.val
          ((preferredChartTangentEquiv I' p x.val
            (ambientSplitChartDomain_mem_left I I' f hf p x)).symm v)) := by
  have h := inTangentCoordinates_eq_mfderiv_comp (I := I') (I' := I) (f := id) (g := f)
    (ϕ := mfderiv I' I f) (ambientSplitChartDomain_mem_left I I' f hf p x)
    (ambientSplitChartDomain_mem_right I I' f hf p x)
  have hv := congrArg (fun A : E' →L[ℝ] E => A v) h
  change inTangentCoordinates I' I id f (mfderiv I' I f) p x.val v =
    (mfderiv I 𝓘(ℝ, E) (extChartAt I (f p)) (f x.val) : E →L[ℝ] E)
      ((mfderiv I' I f x.val : E' →L[ℝ] E)
        (mfderivWithin 𝓘(ℝ, E') I' (extChartAt I' p).symm (range I')
          (extChartAt I' p x.val) v)) at hv
  refine hv.trans ?_
  rw [preferredChartTangentEquiv_symm_apply]
  rfl

/-- **Continuity of the frame in charts.** -/
theorem ambientSplitFrameInCharts_continuousAt (f : S → M)
    (hf : ContMDiff I' I 1 f) (ν : ∀ x, F →L[ℝ] TangentSpace I (f x))
    (hν : ∀ a : F, Continuous (fun x => (⟨f x, ν x a⟩ : TangentBundle I M)))
    (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)) (p : S) :
    ContinuousAt (fun x : ambientSplitChartDomain I I' f hf.continuous p =>
      (ambientSplitFrameInCharts I I' f hf.continuous ν h p x : (F × E') →L[ℝ] E))
      ⟨p, mem_extChartAt_source (I := I') p, mem_extChartAt_source (I := I) (f p)⟩ := by
  let U := ambientSplitChartDomain I I' f hf.continuous p
  let pU : U := ⟨p, mem_extChartAt_source (I := I') p, mem_extChartAt_source (I := I) (f p)⟩
  let T := trivializationAt E (TangentSpace I) (f p)
  have hD0 : ContinuousAt (inTangentCoordinates I' I id f (mfderiv I' I f) p) p :=
    (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have hD : ContinuousAt (fun x : U => inTangentCoordinates I' I id f
      (mfderiv I' I f) p x.val) pU :=
    hD0.comp_of_eq continuous_subtype_val.continuousAt rfl
  let Nc : U → F →L[ℝ] E := fun x =>
    (preferredChartTangentEquiv I (f p) (f x.val)
      (ambientSplitChartDomain_mem_right I I' f hf.continuous p x) : E →L[ℝ] E).comp
        (ν x.val : F →L[ℝ] E)
  have hN : ContinuousAt Nc pU := by
    refine continuousAt_clm_apply.mpr fun a => ?_
    have hsrc : ∀ x : U, (⟨f x.val, ν x.val a⟩ : TangentBundle I M) ∈ T.source := by
      intro x
      rw [T.mem_source, TangentBundle.trivializationAt_baseSet]
      exact ambientSplitChartDomain_mem_right I I' f hf.continuous p x
    have h1 : ContinuousAt (fun z : TangentBundle I M => T z) ⟨f p, ν p a⟩ :=
      T.continuousOn.continuousAt (T.open_source.mem_nhds (hsrc pU))
    have hc : ContinuousAt (fun x : U => T ⟨f x.val, ν x.val a⟩) pU :=
      h1.comp_of_eq ((hν a).comp continuous_subtype_val).continuousAt rfl
    refine (continuous_snd.continuousAt.comp hc).congr (Eventually.of_forall fun x => ?_)
    exact (preferredChartTangentEquiv_apply_eq_trivialization_snd I (f p) (f x.val)
      (ambientSplitChartDomain_mem_right I I' f hf.continuous p x) (ν x.val a)).symm
  have hR : ContinuousAt (fun x : U =>
      (Nc x).comp (ContinuousLinearMap.fst ℝ F E') +
        (inTangentCoordinates I' I id f (mfderiv I' I f) p x.val).comp
          (ContinuousLinearMap.snd ℝ F E')) pU :=
    (hN.clm_comp continuousAt_const).add (hD.clm_comp continuousAt_const)
  refine hR.congr (Eventually.of_forall fun x => ?_)
  apply ContinuousLinearMap.ext
  intro v
  change Nc x v.1 + inTangentCoordinates I' I id f (mfderiv I' I f) p x.val v.2 =
    ambientSplitFrameInCharts I I' f hf.continuous ν h p x v
  rw [ambientSplit_derivative_in_chart_apply I I' f hf.continuous p x v.2]
  change _ = preferredChartTangentEquiv I (f p) (f x.val)
      (ambientSplitChartDomain_mem_right I I' f hf.continuous p x)
    ((ν x.val v.1 : E) + mfderiv I' I f x.val
      ((preferredChartTangentEquiv I' p x.val
        (ambientSplitChartDomain_mem_left I I' f hf.continuous p x)).symm v.2))
  exact (map_add (preferredChartTangentEquiv I (f p) (f x.val)
    (ambientSplitChartDomain_mem_right I I' f hf.continuous p x)) (ν x.val v.1 : E) _).symm

/-- **The orientation of `S` induced by an oriented `M` and a complementary frame.** -/
def ambientSplitSmoothOrientation (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ E') ≃ Fin (finrank ℝ E)) (f : S → M) (hf : ContMDiff I' I 1 f)
    (ν : ∀ x, F →L[ℝ] TangentSpace I (f x))
    (hν : ∀ a : F, Continuous (fun x => (⟨f x, ν x a⟩ : TangentBundle I M)))
    (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)) (o : SmoothOrientation I M) :
    SmoothOrientation I' S := by
  apply smoothOrientationOfLocalRepresentations I' (ambientSplitOrientationField I I' bF σ f ν h o)
  intro p
  let U := ambientSplitChartDomain I I' f hf.continuous p
  let pU : U := ⟨p, mem_extChartAt_source (I := I') p, mem_extChartAt_source (I := I) (f p)⟩
  let g : U → Orientation ℝ E' (Fin (finrank ℝ E')) := fun x =>
    Orientation.map _ (preferredChartTangentEquiv I' p x.val
      (ambientSplitChartDomain_mem_left I I' f hf.continuous p x)).toLinearEquiv
      (ambientSplitOrientationField I I' bF σ f ν h o x.val)
  let rep : (chartAt H (f p)).source → Orientation ℝ E (Fin (finrank ℝ E)) := fun y =>
    Orientation.map _ (preferredChartTangentEquiv I (f p) y.val y.property).toLinearEquiv
      (o.val y.val)
  let tgt : U → (chartAt H (f p)).source := fun x =>
    ⟨f x.val, ambientSplitChartDomain_mem_right I I' f hf.continuous p x⟩
  have htgt : Continuous tgt := (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hloc : IsLocallyConstant (rep ∘ tgt) := (o.property (f p)).comp_continuous htgt
  have hg : ∀ᶠ x in 𝓝 pU, g x = g pU := by
    have hev1 := hloc.eventually_eq pU
    have hev2 := splitInducedOrientation_eventually_eq bF (Module.finBasis ℝ E') σ
      (fun x => ambientSplitFrameInCharts I I' f hf.continuous ν h p x) pU
      (ambientSplitFrameInCharts_continuousAt I I' f hf ν hν h p) (rep (tgt pU))
    filter_upwards [hev1, hev2] with x h1 h2
    have hx := ambientSplit_chart_representation I I' bF σ f hf.continuous ν h o p x
    have hp := ambientSplit_chart_representation I I' bF σ f hf.continuous ν h o p pU
    change g x = _ at hx
    change g pU = _ at hp
    rw [hx, hp]
    change splitInducedOrientation bF (Module.finBasis ℝ E') σ
        (ambientSplitFrameInCharts I I' f hf.continuous ν h p x).toLinearEquiv ((rep ∘ tgt) x) =
      splitInducedOrientation bF (Module.finBasis ℝ E') σ
        (ambientSplitFrameInCharts I I' f hf.continuous ν h p pU).toLinearEquiv ((rep ∘ tgt) pU)
    rw [h1]
    exact h2
  obtain ⟨V, hV, hp, hloc'⟩ := locallyConstant_neighborhood_of_eventually_eq U pU g hg
  exact ⟨V, fun y hy => by simpa only [extChartAt_source] using (hV hy).1, hp, hloc'⟩

theorem ambientSplitSmoothOrientation_apply (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ E') ≃ Fin (finrank ℝ E)) (f : S → M) (hf : ContMDiff I' I 1 f)
    (ν : ∀ x, F →L[ℝ] TangentSpace I (f x))
    (hν : ∀ a : F, Continuous (fun x => (⟨f x, ν x a⟩ : TangentBundle I M)))
    (h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)) (o : SmoothOrientation I M) (x : S) :
    (ambientSplitSmoothOrientation I I' bF σ f hf ν hν h o).val x =
      ambientSplitOrientationField I I' bF σ f ν h o x := rfl

variable {I I'} in
/-- **Characterisation (compatibility with the product orientation).** A basis `b` of `T_x S` is
positive iff the ordered frame `(ν x (bF a))_a, (df_x (b i))_i` is positive in `M`. -/
theorem ambientSplitSmoothOrientation_eq_iff {bF : Basis ιF ℝ F}
    {σ : ιF ⊕ Fin (finrank ℝ E') ≃ Fin (finrank ℝ E)} {f : S → M} (hf : ContMDiff I' I 1 f)
    {ν : ∀ x, F →L[ℝ] TangentSpace I (f x)}
    (hν : ∀ a : F, Continuous (fun x => (⟨f x, ν x a⟩ : TangentBundle I M)))
    {h : ∀ x, Bijective (ambientSplitFrame I I' f ν x)} {o : SmoothOrientation I M} {x : S}
    {b : Basis (Fin (finrank ℝ E')) ℝ E'} :
    b.orientation = (ambientSplitSmoothOrientation I I' bF σ f hf ν hν h o).val x ↔
      (splitFrameBasis bF b σ (ambientSplitFrameEquiv I I' f ν h x).toLinearEquiv).orientation =
        o.val (f x) :=
  splitInducedOrientation_eq_iff (Module.finBasis ℝ E')

end DifferentialGeometry.Topology.Manifold
