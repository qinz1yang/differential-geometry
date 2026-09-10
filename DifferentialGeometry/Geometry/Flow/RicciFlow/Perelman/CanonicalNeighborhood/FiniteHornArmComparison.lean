import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornCompactCompletion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompleteMetricSegment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalComparisonAngle

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem comparison_of_complete_metric_segments
    {W : Type u} [TopologicalSpace W] [T2Space W] [ChartedSpace ThreeSpace W]
    [IsManifold I3 ∞ W] [SigmaCompactSpace W] [ConnectedSpace W]
    (g : SmoothRiemannianMetric I3 W) (hcomplete : RiemannianMetricComplete g)
    (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ) (hL : ∀ k, 0 < L k)
    (hstart : arm 0 0 = arm 1 0)
    (hmetric : ∀ k s, s ∈ Icc 0 (L k) → ∀ t ∈ Icc 0 (L k),
      riemannianEDistOf g (arm k s) (arm k t) = ENNReal.ofReal |s - t|)
    (hsec : ∀ s ∈ Icc 0 (L 0), ∀ t ∈ Icc 0 (L 1), ∀ y : W,
      riemannianEDistOf g (arm 0 s) y + riemannianEDistOf g y (arm 1 t) =
        riemannianEDistOf g (arm 0 s) (arm 1 t) →
      metricRm04At (I := I3) g y ∈ tensor04SectionalNonnegativeCone (I := I3) (M := W))
    (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (haL : a2 ≤ L 0)
    (hb1 : 0 < b1) (hb12 : b1 ≤ b2) (hbL : b2 ≤ L 1) :
    comparisonAngle a2 b2 (riemannianEDistOf g (arm 0 a2) (arm 1 b2)).toReal ≤
      comparisonAngle a1 b1 (riemannianEDistOf g (arm 0 a1) (arm 1 b1)).toReal := by
  let : IsManifold I3 1 W := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace I3 W
  let : T3Space W := inferInstance
  let : RiemannianBundle (fun x : W => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : W => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace W := EMetricSpace.ofRiemannianMetric I3 W
  let : CompleteSpace W := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I3) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hdistOf (x y : W) : riemannianEDistOf g x y = riemannianEDist I3 x y :=
    riemannianEDistOf_eq_riemannianEDist g hEnorm x y
  have hnmetric (k : Fin 2) (s t : Icc (0 : ℝ) (L k)) :
      riemannianEDist I3 (arm k s) (arm k t) = ENNReal.ofReal |(s : ℝ) - t| := by
    rw [← hdistOf]
    exact hmetric k s s.property t t.property
  obtain ⟨u, hu, huall⟩ := exists_intrinsicGeodesic_eq_metric_segment g hEnorm (hL 0)
    (fun s : Icc (0 : ℝ) (L 0) => arm 0 s) (hnmetric 0)
  obtain ⟨v, hv, hvall⟩ := exists_intrinsicGeodesic_eq_metric_segment g hEnorm (hL 1)
    (fun s : Icc (0 : ℝ) (L 1) => arm 1 s) (hnmetric 1)
  let o : W := arm 0 0
  let v₀ : TangentSpace I3 o := (v : ThreeSpace)
  have hv₀ : g.inner o v₀ v₀ = 1 :=
    (congrArg (fun p => g.inner p (v : ThreeSpace) (v : ThreeSpace)) hstart).trans hv
  have hgeo₀ (s : ℝ) (hs : s ∈ Icc 0 (L 0)) :
      arm 0 s = intrinsicGeodesic g hEnorm o u s := huall ⟨s, hs⟩
  have hgeo₁ (t : ℝ) (ht : t ∈ Icc 0 (L 1)) :
      arm 1 t = intrinsicGeodesic g hEnorm o v₀ t :=
    (hvall ⟨t, ht⟩).trans
      (congrArg (fun p => intrinsicGeodesic g hEnorm p (v : ThreeSpace) t) hstart.symm)
  have ha2 : 0 < a2 := ha1.trans_le ha12
  have hb2 : 0 < b2 := hb1.trans_le hb12
  have hminA : (riemannianEDist I3 o (intrinsicGeodesic g hEnorm o u a2)).toReal = a2 := by
    rw [← hgeo₀ a2 ⟨ha2.le, haL⟩]
    have h := congrArg ENNReal.toReal (hnmetric 0 ⟨0, ⟨le_rfl, (hL 0).le⟩⟩
      ⟨a2, ⟨ha2.le, haL⟩⟩)
    simpa only [zero_sub, abs_neg, abs_of_pos ha2, ENNReal.toReal_ofReal ha2.le] using h
  have hminB : (riemannianEDist I3 o (intrinsicGeodesic g hEnorm o v₀ b2)).toReal = b2 := by
    rw [← hgeo₁ b2 ⟨hb2.le, hbL⟩]
    have h := congrArg ENNReal.toReal (hnmetric 1 ⟨0, ⟨le_rfl, (hL 1).le⟩⟩
      ⟨b2, ⟨hb2.le, hbL⟩⟩)
    rw [← hstart] at h
    simpa only [zero_sub, abs_neg, abs_of_pos hb2, ENNReal.toReal_ofReal hb2.le] using h
  have h := comparisonAngle_shortening_of_sectional_nonnegative_on_minimizing_lenses
    g hEnorm o u v₀ a1 a2 b1 b2 ha1 ha12 hb1 hb12 hu hv₀ hminA hminB (by
      intro s hs t ht y hy
      have hsL : s ∈ Icc 0 (L 0) := ⟨hs.1, hs.2.trans haL⟩
      have htL : t ∈ Icc 0 (L 1) := ⟨ht.1, ht.2.trans hbL⟩
      rw [← hgeo₀ s hsL, ← hgeo₁ t htL] at hy
      simp only [← hdistOf] at hy
      exact hsec s hsL t htL y hy)
  simpa only [← hgeo₀ a1 ⟨ha1.le, ha12.trans haL⟩, ← hgeo₀ a2 ⟨ha2.le, haL⟩,
    ← hgeo₁ b1 ⟨hb1.le, hb12.trans hbL⟩, ← hgeo₁ b2 ⟨hb2.le, hbL⟩,
    ← hdistOf] using h

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem exists_finiteHorn_arm_comparison_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ inner : ℕ,
        ∀ (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ), (∀ k, 0 < L k) →
          (∀ k, ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ (arm k) (Icc 0 (L k))) →
          (∀ k s, s ∈ Icc 0 (L k) → arm k s ∈ H.subend inner) →
          arm 0 0 = arm 1 0 →
          (∀ k s, s ∈ Icc 0 (L k) → ∀ t ∈ Icc 0 (L k),
            dist (arm k s) (arm k t) = |s - t|) →
          ∀ a1 a2 b1 b2 : ℝ, 0 < a1 → a1 ≤ a2 → a2 ≤ L 0 →
            0 < b1 → b1 ≤ b2 → b2 ≤ L 1 →
            comparisonAngle a2 b2 (dist (arm 0 a2) (arm 1 b2)) ≤
              comparisonAngle a1 b1 (dist (arm 0 a1) (arm 1 b1)) := by
  obtain ⟨H₀, hH₀, hcomplete⟩ := exists_finiteHorn_compact_complete_metric_depth (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth
  obtain ⟨inner, _hbuffer, hfamily⟩ := hcomplete g H hdepth 0
  refine ⟨inner, ?_⟩
  intro arm L hL hsmooth hmem hstart hmetric a1 a2 b1 b2 ha1 ha12 haL hb1 hb12 hbL
  let S : Set W := arm 0 '' Icc 0 (L 0) ∪ arm 1 '' Icc 0 (L 1)
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn (hsmooth 0).continuousOn).union
      (isCompact_Icc.image_of_continuousOn (hsmooth 1).continuousOn)
  have hSin : S ⊆ H.subend inner := by
    intro x hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
    · exact hmem 0 s hs
    · exact hmem 1 t ht
  have hSarm (k : Fin 2) (s : ℝ) (hs : s ∈ Icc 0 (L k)) : arm k s ∈ S := by
    fin_cases k
    · exact Or.inl ⟨s, hs, rfl⟩
    · exact Or.inr ⟨s, hs, rfl⟩
  obtain ⟨g', U, K, eta, hcomplete', hU, _hK, heta, hKU, _hSU, heq, hle, hdata⟩ :=
    hfamily S S hS hS hSin hSin
  let : ConnectedSpace W := connectedSpace_iff_univ.mpr H.tube.isConnected_univ
  have hmetric' (k : Fin 2) (s : ℝ) (hs : s ∈ Icc 0 (L k)) (t : ℝ) (ht : t ∈ Icc 0 (L k)) :
      riemannianEDistOf g' (arm k s) (arm k t) = ENNReal.ofReal |s - t| := by
    simpa only [hmetric k s hs t ht] using
      (hdata (arm k s) (hSarm k s hs) (arm k t) (hSarm k t ht)).1
  have hsec (s : ℝ) (hs : s ∈ Icc 0 (L 0)) (t : ℝ) (ht : t ∈ Icc 0 (L 1))
      (y : W) (hy : riemannianEDistOf g' (arm 0 s) y + riemannianEDistOf g' y (arm 1 t) =
        riemannianEDistOf g' (arm 0 s) (arm 1 t)) :
      metricRm04At (I := I3) g' y ∈ tensor04SectionalNonnegativeCone (I := I3) (M := W) := by
    have hpair := hdata (arm 0 s) (hSarm 0 s hs) (arm 1 t) (hSarm 1 t ht)
    exact auxiliary_sectional_nonnegative_of_distance_add g H g' hU heq hle
      hpair.1 heta.le (fun z hz => hKU ((hpair.2.1 z hz).2)) hy
  have h := comparison_of_complete_metric_segments g' hcomplete' arm L hL hstart hmetric' hsec
    a1 a2 b1 b2 ha1 ha12 haL hb1 hb12 hbL
  have hd₁ := (hdata (arm 0 a1) (hSarm 0 a1 ⟨ha1.le, ha12.trans haL⟩)
    (arm 1 b1) (hSarm 1 b1 ⟨hb1.le, hb12.trans hbL⟩)).1
  have hd₂ := (hdata (arm 0 a2) (hSarm 0 a2 ⟨(ha1.trans_le ha12).le, haL⟩)
    (arm 1 b2) (hSarm 1 b2 ⟨(hb1.trans_le hb12).le, hbL⟩)).1
  simpa only [hd₁, hd₂, ENNReal.toReal_ofReal dist_nonneg] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
