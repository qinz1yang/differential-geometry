import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

open private
  CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

noncomputable section

open Set
open scoped ContDiff Manifold
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear (CircleHsPi circleHsPiInclusion)

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_sobolev_spatial_jets
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {P : Type*} [TopologicalSpace P] {S : Set P} {N : ℕ} {T : ℝ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : P → SmoothImmersion (I := I) (M := M))
    (u : P → timeH1 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T) :
    let f := fun p => fixedAmbientSobolev e g₀ (initial p)
    let B := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : P → CurveMap (EuclideanSpace ℝ (Fin N)) := fun p z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B (f p) + L ((u p).toFun t)) z)
    (∀ k : ℕ,
      ∃ W : (P × ℝ) → CircleHsPi g₀ (Fin N) ((k : ℝ) + 2),
        ContinuousOn W (S ×ˢ Icc 0 T) ∧
          ∀ p ∈ S, ∀ t ∈ Icc 0 T,
            circleHsPiInclusion g₀ (Fin N)
              (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [hk] :
                (1 : ℝ) ≤ (k : ℝ) + 2) (W (p, t)) =
              B (f p) + L ((u p).toFun t)) →
    (∀ p ∈ S, ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun x => (d p).lift x t)) ∧
      ∀ j : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedDeriv j (fun x => (d q.1).lift x q.2.1) q.2.2)
        (S ×ˢ Icc 0 T ×ˢ univ) := by
  intro f B L d htower
  let v : (P × ℝ) → ℝ → (Fin N → ℝ) := fun q x =>
    scalarH1PiToContinuous g₀ (B (f q.1) + L ((u q.1).toFun q.2))
      (x : AddCircle (1 : ℝ))
  have hjet (j : ℕ) :
      (∀ q ∈ S ×ˢ Icc 0 T, ContDiff ℝ j (v q)) ∧
        ContinuousOn (fun q : (P × ℝ) × ℝ => iteratedDeriv j (v q.1) q.2)
          ((S ×ˢ Icc 0 T) ×ˢ univ) := by
    obtain ⟨W, hW, hWu⟩ := htower j
    have hj : (j : ℝ) + 1 ≤ (j : ℝ) + 2 := by linarith
    let K := circleHsPiInclusion g₀ (Fin N) hj
    exact AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
      g₀ j (fun q : P × ℝ => B (f q.1) + L ((u q.1).toFun q.2))
      (fun q => K (W q)) (K.continuous.comp_continuousOn hW) (fun q hq => by
        refine Eq.trans ?_ (hWu q.1 hq.1 q.2 hq.2)
        apply PiLp.ext
        intro i
        exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ (j : ℝ) + 1) hj ((W q) i)).symm)
  let A := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm
  have hder (j : ℕ) (p : P) (t x : ℝ) :
      iteratedDeriv j (fun y => (d p).lift y t) x = A (iteratedDeriv j (v (p, t)) x) := by
    change iteratedDeriv j (A ∘ v (p, t)) x = _
    rw [iteratedDeriv_eq_iteratedFDeriv, A.iteratedFDeriv_comp_left]
    rfl
  constructor
  · intro p hp t ht
    rw [contDiff_infty]
    intro j
    exact A.contDiff.comp ((hjet j).1 (p, t) ⟨hp, ht⟩)
  · intro j
    have hc := A.continuous.comp_continuousOn (hjet j).2
    have hassoc : Continuous (fun q : P × ℝ × ℝ => ((q.1, q.2.1), q.2.2)) :=
      (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
    have hcont := hc.comp hassoc.continuousOn
      (show MapsTo (fun q : P × ℝ × ℝ => ((q.1, q.2.1), q.2.2))
        (S ×ˢ Icc 0 T ×ˢ univ) ((S ×ˢ Icc 0 T) ×ˢ univ) from
          fun _ hq => ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩)
    apply hcont.congr
    intro q _
    exact hder j q.1 q.2.1 q.2.2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open Set Filter
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

omit [FiniteDimensional ℝ E] in
private theorem reference_chart_spatial_jets
    {P : Type*} [TopologicalSpace P] {S : Set P} {V : Set ℝ} {N : ℕ} {T : ℝ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : P → SmoothImmersion (I := I) (M := M))
    (u : P → timeH1 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    {r : EuclideanSpace ℝ (Fin N) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U) (β : M) :
    let f := fun p => fixedAmbientSobolev e g₀ (initial p)
    let B := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : P → CurveMap (EuclideanSpace ℝ (Fin N)) := fun p z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (B (f p) + L ((u p).toFun t)) z)
    let c : P → CurveMap M := fun p z t => r (d p z t)
    (∀ p ∈ S, ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun x => (d p).lift x t)) →
    (∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (fun x => (d q.1).lift x q.2.1) q.2.2)
      (S ×ˢ Icc 0 T ×ˢ V)) →
    (∀ p ∈ S, ∀ t ∈ Icc 0 T, ∀ x ∈ V, (d p).lift x t ∈ U) →
    (∀ p ∈ S, ∀ t ∈ Icc 0 T, ∀ x ∈ V,
      (c p).lift x t ∈ (extChartAt I β).source) →
    ∀ j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j
        (fun x => extChartAt I β ((c q.1).lift x q.2.1)) q.2.2)
      (S ×ˢ Icc 0 T ×ˢ V) := by
  intro f B L d c hspace hjets hU hchart n
  let A : Set (EuclideanSpace ℝ (Fin N)) := U ∩ r ⁻¹' (extChartAt I β).source
  let ψ : EuclideanSpace ℝ (Fin N) → E := fun z => extChartAt I β (r z)
  have hA : IsOpen A := hr.continuousOn.isOpen_inter_preimage U.isOpen
    (isOpen_extChartAt_source (I := I) β)
  have hψ : ContDiffOn ℝ ∞ ψ A := by
    apply contMDiffOn_iff_contDiffOn.mp
    apply (contMDiffOn_extChartAt (I := I) (x := β)).comp (hr.mono inter_subset_left)
    intro z hz
    simpa only [extChartAt_source] using hz.2
  let first : (ℝ × ℝ × (Fin 1 → EuclideanSpace ℝ (Fin N))) →
      EuclideanSpace ℝ (Fin N) := fun q => q.2.2 0
  let Ω := first ⁻¹' A
  let Φ : (ℝ × ℝ × (Fin 1 → EuclideanSpace ℝ (Fin N))) → E := ψ ∘ first
  have hfirst : ContDiff ℝ ∞ first := by fun_prop
  have hΩ : IsOpen Ω := hA.preimage hfirst.continuous
  have hΦ : ContDiffOn ℝ ∞ Φ Ω := hψ.comp hfirst.contDiffOn (fun _ h => h)
  let G (p : P) (t x : ℝ) : EuclideanSpace ℝ (Fin N) := (d p).lift x t
  let W (p : P) (t : ℝ) := G p t ⁻¹' A
  have hW (p : P) (hp : p ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T) : IsOpen (W p t) :=
    hA.preimage (hspace p hp t ht).continuous
  have hmem (p : P) (hp : p ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) (hx : x ∈ V) :
      x ∈ W p t := ⟨hU p hp t ht x hx, hchart p hp t ht x hx⟩
  let Q (q : P × ℝ × ℝ) : ℝ × ℝ × (Fin (1 + n) → EuclideanSpace ℝ (Fin N)) :=
    (0, q.2.2, fun i => iteratedDeriv i.val (G q.1 q.2.1) q.2.2)
  have hQ : ContinuousOn Q (S ×ˢ Icc 0 T ×ˢ V) := by
    apply ContinuousOn.prodMk continuousOn_const
    apply ContinuousOn.prodMk continuous_snd.snd.continuousOn
    exact continuousOn_pi.mpr fun i => hjets i.val
  have hmap : MapsTo Q (S ×ˢ Icc 0 T ×ˢ V)
      (Analysis.scalarJetProjection (F := EuclideanSpace ℝ (Fin N))
        (Nat.le_add_right 1 n) ⁻¹' Ω) := by
    intro q hq
    change iteratedDeriv 0 (G q.1 q.2.1) q.2.2 ∈ A
    rw [iteratedDeriv_zero]
    exact hmem q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2
  have hcont := (Analysis.contDiffOn_scalarJetProlongation hΩ hΦ n).continuousOn.comp hQ hmap
  apply hcont.congr
  intro q hq
  have hlocal : ∀ x ∈ W q.1 q.2.1,
      (0, x, fun i : Fin 1 => iteratedDeriv i.val (G q.1 q.2.1) x) ∈ Ω := by
    intro x hx
    change iteratedDeriv 0 (G q.1 q.2.1) x ∈ A
    rwa [iteratedDeriv_zero]
  have heq := Analysis.iteratedDeriv_eq_scalarJetProlongation_of_contDiffOn hΩ hΦ
    (hW q.1 hq.1 q.2.1 hq.2.1) (hspace q.1 hq.1 q.2.1 hq.2.1).contDiffOn
    0 hlocal n (hmem q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2)
  simpa only [Φ, first, ψ, Q, G, c, CurveMap.lift, Function.comp_apply, Fin.val_zero,
    iteratedDeriv_zero] using heq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
