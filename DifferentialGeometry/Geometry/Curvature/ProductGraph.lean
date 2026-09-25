import DifferentialGeometry.Topology.GraphBand
import DifferentialGeometry.Topology.Manifold.TransverseGraph
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected
import DifferentialGeometry.Geometry.Curvature.RoundCylinderSectionalCurvature
import Mathlib.LinearAlgebra.Dimension.RankNullity

set_option autoImplicit false
noncomputable section
open Set Bundle
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem vertical_not_mem_range_of_positive_tangent_sectional_curvature
    (g : SmoothRiemannianMetric J N) (e : M → N × ℝ)
    (hdim : 1 < Module.finrank ℝ E)
    (hsec : ∀ p (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
      0 < metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p)
        (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
        (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p v)) :
    ∀ p, (0, 1) ∉ range (mfderiv I (J.prod 𝓘(ℝ)) e p) := by
  intro p hp
  obtain ⟨w, hw⟩ := hp
  have hw0 : w ≠ 0 := by
    intro hz
    have hh := congrArg Prod.snd hw
    simp only [hz, map_zero] at hh
    exact zero_ne_one hh
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := ℝ) (M := E) hdim
    (show (w : E) ≠ 0 from hw0)
  let vT : TangentSpace I p := v
  have hvw : LinearIndependent ℝ ![vT, w] := LinearIndependent.pair_symm_iff.mp hv
  have hpos := hsec p vT w hvw
  rw [hw] at hpos
  have hz := metricRm04StandardAt_prodEuclidean_axis g (e p)
    (mfderiv I (J.prod 𝓘(ℝ)) e p vT)
  exact (ne_of_gt hpos) hz

theorem exists_diffeomorph_graph_of_positive_tangent_sectional_curvature
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N]
    (g : SmoothRiemannianMetric J N) (e : M → N × ℝ)
    (he : ContMDiff I (J.prod 𝓘(ℝ)) ∞ e) (hinj : Function.Injective e)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hdim2 : 1 < Module.finrank ℝ E)
    (hsec : ∀ p (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
      0 < metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p)
        (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
        (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p v)) :
    ∃ (η : N ≃ₘ⟮J, I⟯ M) (h : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ h ∧
      ∀ p, e (η p) = (p, h p) := by
  let _ : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  have himm (p : M) : Function.Injective (mfderiv I (J.prod 𝓘(ℝ)) e p) := by
    intro v w hvw
    by_contra hne
    let z : TangentSpace I p := v - w
    have hz : z ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨u, hu⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := ℝ) (M := E)
      hdim2 (show (z : E) ≠ 0 from hz)
    let uT : TangentSpace I p := u
    have hp := hsec p z uT hu
    have hAz : mfderiv I (J.prod 𝓘(ℝ)) e p z = 0 := by
      dsimp only [z]
      rw [map_sub, hvw, sub_self]
    rw [hAz] at hp
    let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
    have hzero := Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent
      (g.prod (euclideanMetric (E := ℝ))) (e p) 0
      (mfderiv I (J.prod 𝓘(ℝ)) e p uT) (by
        intro hl
        have hn := hl.ne_zero (0 : Fin 2)
        simp only [Matrix.cons_val_zero] at hn
        exact hn rfl)
    exact (ne_of_gt hp) hzero
  exact DifferentialGeometry.Topology.Manifold.exists_diffeomorph_graph_of_transverse_embedding
    e he hinj himm hdim
    (vertical_not_mem_range_of_positive_tangent_sectional_curvature g e hdim2 hsec)


theorem exists_diffeomorph_graph_of_nonzero_tangent_sectional_curvature
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N]
    (g : SmoothRiemannianMetric J N) (e : M → N × ℝ)
    (he : ContMDiff I (J.prod 𝓘(ℝ)) ∞ e) (hinj : Function.Injective e)
    (hdimE : Module.finrank ℝ E = 2) (hdimF : Module.finrank ℝ F = 2)
    (hsec : ∀ p, ∃ v w : TangentSpace I p,
      metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p)
        (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
        (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p v) ≠ 0) :
    ∃ (η : N ≃ₘ⟮J, I⟯ M) (h : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ h ∧
      ∀ p, e (η p) = (p, h p) := by
  let _ : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hproj (p : M) : Function.Injective
      ((ContinuousLinearMap.fst ℝ F ℝ).comp (mfderiv I (J.prod 𝓘(ℝ)) e p)) := by
    let A : E →L[ℝ] F × ℝ := mfderiv I (J.prod 𝓘(ℝ)) e p
    let P : E →ₗ[ℝ] F := ((ContinuousLinearMap.fst ℝ F ℝ).comp A).toLinearMap
    obtain ⟨v, w, hnonzero⟩ := hsec p
    let vE : E := v
    let wE : E := w
    have hformula : metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p)
        (A vE) (A wE) (A wE) (A vE) = metricRm04StandardAt g (e p).1
          ((A vE).1) ((A wE).1) ((A wE).1) ((A vE).1) := by
      let V : TangentSpace (J.prod 𝓘(ℝ)) (e p) := A vE
      let W : TangentSpace (J.prod 𝓘(ℝ)) (e p) := A wE
      have hp : metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p) V W W V =
          metricRm04StandardAt g (e p).1 V.1 W.1 W.1 V.1 +
          metricRm04StandardAt (euclideanMetric (E := ℝ)) (e p).2 V.2 W.2 W.2 V.2 :=
        metricRm04At_productMetric_apply g (euclideanMetric (E := ℝ)) (e p)
          (vec4 (I := J.prod 𝓘(ℝ)) V W W V)
      have hz : metricRm04StandardAt (euclideanMetric (E := ℝ)) (e p).2 V.2 W.2 W.2 V.2 = 0 :=
        congrArg (fun T => T (vec4 (I := 𝓘(ℝ)) V.2 W.2 W.2 V.2))
          (metricRm04At_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp) (e p).2)
      exact hp.trans ((congrArg (fun z => metricRm04StandardAt g (e p).1 V.1 W.1 W.1 V.1 + z)
        hz).trans (add_zero _))
    have hli : LinearIndependent ℝ ![P v, P w] := by
      by_contra hdep
      apply hnonzero
      change metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p)
        (A vE) (A wE) (A wE) (A vE) = 0
      rw [hformula]
      exact Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent g (e p).1
        (P v) (P w) hdep
    have hspan : Submodule.span ℝ (range (![P v, P w] : Fin 2 → F)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simpa using hdimF.symm)
    have hsurj : Function.Surjective P := by
      rw [← LinearMap.range_eq_top]
      apply top_unique
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      fin_cases j
      · exact ⟨v, rfl⟩
      · exact ⟨w, rfl⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdimE.trans hdimF.symm)).mpr hsurj
  have himm (p : M) : Function.Injective (mfderiv I (J.prod 𝓘(ℝ)) e p) := by
    intro v w hvw
    apply hproj p
    change (mfderiv I (J.prod 𝓘(ℝ)) e p v).1 = (mfderiv I (J.prod 𝓘(ℝ)) e p w).1
    exact congrArg Prod.fst hvw
  have htrans (p : M) : (0, 1) ∉ range (mfderiv I (J.prod 𝓘(ℝ)) e p) := by
    rintro ⟨v, hv⟩
    have hv0 : v = 0 := by
      apply hproj p
      change (mfderiv I (J.prod 𝓘(ℝ)) e p v).1 = _
      rw [hv, map_zero]
    have hh := congrArg Prod.snd hv
    simp only [hv0, map_zero] at hh
    exact zero_ne_one hh
  exact DifferentialGeometry.Topology.Manifold.exists_diffeomorph_graph_of_transverse_embedding
    e he hinj himm (hdimE.trans hdimF.symm) htrans

theorem interior_eq_empty_of_frontier_eq_nonzero_tangent_sectional_curvature
    [CompactSpace M] [ConnectedSpace M] [ConnectedSpace N]
    (g : SmoothRiemannianMetric J N) (e : M → N × ℝ)
    (he : ContMDiff I (J.prod 𝓘(ℝ)) ∞ e) (hinj : Function.Injective e)
    (hdimE : Module.finrank ℝ E = 2) (hdimF : Module.finrank ℝ F = 2)
    (hsec : ∀ p, ∃ v w : TangentSpace I p,
      metricRm04StandardAt (g.prod (euclideanMetric (E := ℝ))) (e p)
        (mfderiv I (J.prod 𝓘(ℝ)) e p v) (mfderiv I (J.prod 𝓘(ℝ)) e p w)
        (mfderiv I (J.prod 𝓘(ℝ)) e p w) (mfderiv I (J.prod 𝓘(ℝ)) e p v) ≠ 0)
    {K : Set (N × ℝ)} (hK : IsCompact K) (hfront : frontier K = range e) :
    interior K = ∅ := by
  obtain ⟨η, h, _, hgraph⟩ := exists_diffeomorph_graph_of_nonzero_tangent_sectional_curvature
    g e he hinj hdimE hdimF hsec
  apply DifferentialGeometry.Topology.interior_eq_empty_of_frontier_subset_graph hK h
  rw [hfront]
  rintro _ ⟨x, rfl⟩
  exact ⟨η.symm x, by simpa only [η.apply_symm_apply] using (hgraph (η.symm x)).symm⟩

end DifferentialGeometry.Geometry.Curvature
