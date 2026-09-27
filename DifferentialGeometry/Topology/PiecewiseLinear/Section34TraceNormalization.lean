/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicExcessCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCircleModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceMeetsMeridians
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceNonseparating
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceAssembly

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem section34Trace_of_noOperation (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ s, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd s)
    (hnb : ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd s) :
    Section34Trace 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd := by
  let _ := hU
  let _ := hh
  apply section34_trace_of_intrinsic_operation_dichotomies
    (fun s => exists_positive_finite_section34Trace_circles hcut hgraph hinv s) ?_ ?_ hnc hnb
  · intro s J hJ hJT e he
    obtain ⟨P, C, u, hP, hu, hUP, hfront, hC, hCfr, hUC⟩ :=
      exists_section34Trace_circle_intrinsic_model hcut hgraph hinv s hJ hJT
    have hCF : C ⊆ u ⁻¹' fblBd s :=
      fun x hx => (hJT (hUC.subset ⟨x, hx, rfl⟩)).1
    have hcarry := hinv.model_trace_circle_carriesFirstHomologyOnto_of_no_operation
      hcut hgraph hnc hnb s hP hu hUP hfront hC hCfr hCF
    apply Or.inl
    rw [← hUC]
    exact intrinsic_trace_circle_inter_splitDiskBoundary_nonempty hcut hgraph.2.2.1
      s hP hu hUP hC hCfr hcarry e he
  · intro s J hJ hJT e he hmore
    obtain ⟨P, C, u, hP, hu, hUP, hfront, hC, hCfr, hUC⟩ :=
      exists_section34Trace_circle_intrinsic_model hcut hgraph hinv s hJ hJT
    have hCF : C ⊆ u ⁻¹' fblBd s :=
      fun x hx => (hJT (hUC.subset ⟨x, hx, rfl⟩)).1
    have hcarry := hinv.model_trace_circle_carriesFirstHomologyOnto_of_no_operation
      hcut hgraph hnc hnb s hP hu hUP hfront hC hCfr hCF
    obtain ⟨t, ht⟩ := exists_section34BigonSlide_of_excess_meridian_crossings hinv hcut hgraph
      hnc s hP hu hUP hC hCfr (by rwa [hUC]) (by rwa [hUC]) hcarry
        ⟨e, he, by rwa [hUC]⟩
    exact ⟨t, Or.inr ht⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
