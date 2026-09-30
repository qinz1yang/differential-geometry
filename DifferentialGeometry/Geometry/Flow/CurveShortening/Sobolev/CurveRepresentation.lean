import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

open private
  ambientCoordinate
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientCoordinate
  ambientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientSobolev
  tensorHsCongrL_ccTensorToHs
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.tensorHsCongrL_ccTensorToHs from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private
  fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev
  continuous_fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.continuous_fixedAmbientSobolev
  fixedAmbientSobolev_pullbackMetric_eq
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev_pullbackMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

section
noncomputable section

open Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarH1PiToContinuous_fixedAmbientSobolev
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (d : SmoothImmersion (I := I) (M := M)) (z : AddCircle (1 : ℝ)) :
    scalarH1PiToContinuous g₀
      ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)))
        (fixedAmbientSobolev e g₀ d)) z = fun i => e.map (d.map z) i := by
  funext i
  change scalarH1ToContinuous g₀
    (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
      (tensorHsCongrL g₀ 0 0 (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)
        (ccTensorToHs g₀ 0 3 (scalarCc g₀ (ambientCoordinate d e.map e.smooth i))))) z = _
  rw [tensorHsCongrL_ccTensorToHs, tensorHsInclusion_ccTensorToHs,
    scalarH1ToContinuous_apply_ccTensorToHs, scalar0_scalarCc]
  rfl

private theorem continuous_fixedAmbientSobolev_slice
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a < b) {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hi : c.ImmersedOn (I := I) (Icc a b)) :
    Continuous (fun t : Icc a b =>
      fixedAmbientSobolev e g₀ (slice c hc hi t.val t.property)) := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a b)
  have hconst : @Continuous Unit (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a b)) (fun _ => c) := continuous_const
  have hpair : Continuous (fun q : Unit × Icc a b =>
      slice c hc hi q.2.val q.2.property) :=
    continuous_iff_continuousAt.mpr fun q =>
      continuousAt_slice_smoothImmersion e hab hconst (fun _ => hc) (fun _ => hi) q
  have hslice : Continuous (fun t : Icc a b => slice c hc hi t.val t.property) :=
    hpair.comp ((continuous_const : Continuous (fun _ : Icc a b => ())).prodMk continuous_id)
  exact (continuous_fixedAmbientSobolev e g₀).comp hslice

private theorem exists_continuousOn_fixedAmbientSobolev_curve
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a < b) {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hi : c.ImmersedOn (I := I) (Icc a b)) :
    ∃ W : ℝ → PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)),
      ContinuousOn W (Icc a b) ∧
        (∀ t (ht : t ∈ Icc a b), W t = fixedAmbientSobolev e g₀ (slice c hc hi t ht)) ∧
        (∀ t ∈ Icc a b, ∀ z : AddCircle (1 : ℝ),
          scalarH1PiToContinuous g₀
            ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
              tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))) (W t)) z =
            fun i => e.map (c z t) i) := by
  classical
  let W : ℝ → PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) :=
    fun t => if ht : t ∈ Icc a b then fixedAmbientSobolev e g₀ (slice c hc hi t ht)
      else fixedAmbientSobolev e g₀ (slice c hc hi a ⟨le_rfl, hab.le⟩)
  have hW (t : ℝ) (ht : t ∈ Icc a b) :
      W t = fixedAmbientSobolev e g₀ (slice c hc hi t ht) := dite_eq_left ht
  refine ⟨W, ?_, hW, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_fixedAmbientSobolev_slice e g₀ hab hc hi).congr
      (fun t => (hW t.val t.property).symm)
  · intro t ht z
    rw [hW t ht]
    exact scalarH1PiToContinuous_fixedAmbientSobolev e g₀ (slice c hc hi t ht) z

variable [IsManifold I ∞ M]

private theorem exists_continuousOn_fixedAmbientSobolev_curve_with_initial
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : SmoothRiemannianMetric I M) (c₀ : SmoothImmersion (I := I) (M := M))
    {a b : ℝ} (hab : a < b) {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hi : c.ImmersedOn (I := I) (Icc a b))
    (hinit : ∀ z, c z a = c₀.map z) :
    ∃ W : ℝ → PiLp 2 (fun _ : Fin N =>
        TensorHs (c₀.pullbackMetric g) 0 0 (((1 : ℕ) : ℝ) + 2)),
      ContinuousOn W (Icc a b) ∧
        W a = ambientSobolev c₀ g e.map e.smooth (((1 : ℕ) : ℝ) + 2) ∧
        (∀ t (ht : t ∈ Icc a b),
          W t = fixedAmbientSobolev e (c₀.pullbackMetric g) (slice c hc hi t ht)) ∧
        (∀ t ∈ Icc a b, ∀ z : AddCircle (1 : ℝ),
          scalarH1PiToContinuous (c₀.pullbackMetric g)
            ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
              tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))) (W t)) z =
            fun i => e.map (c z t) i) := by
  obtain ⟨W, hWcont, hW, heval⟩ := exists_continuousOn_fixedAmbientSobolev_curve
    e (c₀.pullbackMetric g) hab hc hi
  refine ⟨W, hWcont, ?_, hW, heval⟩
  rw [hW a ⟨le_rfl, hab.le⟩]
  have hs : slice c hc hi a ⟨le_rfl, hab.le⟩ = c₀ := by
    cases c₀ with
    | mk f hf hif =>
      have hm : (fun z => c z a) = f := funext hinit
      cases hm
      rfl
  rw [hs, fixedAmbientSobolev_pullbackMetric_eq]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end
