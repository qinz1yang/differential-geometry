import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Geodesic.Local.Existence
import DifferentialGeometry.Geometry.Geodesic.Flow.Uniqueness
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def IsGeodesicOnWithInitial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorField (I := I) g) s

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.isGeodesicAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (ht : s ∈ 𝓝 t) :
    IsGeodesicAt (I := I) g γ t := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  have hsrc : (f t).proj ∈ (chartAt H (γ t)).source := by
    rw [hproj t]
    exact mem_chart_source H (γ t)
  exact ⟨γ t, f, hproj, hsrc,
    (isMIntegralCurveAt_geodesicVectorFieldChart_iff g (γ t) hsrc).mpr
      (hf.isMIntegralCurveAt ht)⟩

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.start_eq
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) :
    γ 0 = p := by
  obtain ⟨f, hproj, hf0, _⟩ := hγ
  have h := hproj 0
  simp [hf0] at h
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.mono
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s s' : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (hs : s' ⊆ s) :
    IsGeodesicOnWithInitial (I := I) g γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩

def HasGeodesicAt
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v

def maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Set ℝ :=
  {t : ℝ | HasGeodesicAt (I := I) g p v t}

omit [NeZero (Module.finrank ℝ E)] in
lemma mem_maximalGeodesicInterval_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} :
    t ∈ maximalGeodesicInterval (I := I) g p v ↔
      HasGeodesicAt (I := I) g p v t :=
  Iff.rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicInterval_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsOpen (maximalGeodesicInterval (I := I) g p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩ := ht
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) ?_
  intro t' ht'
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

section LocalExistence

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma hasGeodesicAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    HasGeodesicAt (I := I) g p v 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorField (I := I) g)
      (t₀ := (0 : ℝ)) (x₀ := (⟨p, v⟩ : TangentBundle I M))
      ((contMDiff_geodesicVectorField g).contMDiffAt.of_le (by norm_num))
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, ?_, Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  · exact (convex_ball (0 : ℝ) ε).isPreconnected
  exact ⟨f, fun _ => rfl, hf0, hf_on⟩

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem zero_mem_maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (0 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v :=
  hasGeodesicAt_zero (I := I) g p v

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesicInterval_nonempty
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (maximalGeodesicInterval (I := I) g p v).Nonempty :=
  ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩

end LocalExistence

section MaximalGeodesicDefinition

variable [I.Boundaryless] [CompleteSpace E]

def maximalGeodesicChosenCurve
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : HasGeodesicAt (I := I) g p v t) :
    ℝ → M :=
  Classical.choose h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesicChosenCurve_spec
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : HasGeodesicAt (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g
        (maximalGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h

def maximalGeodesic
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : M :=
  letI : Decidable (HasGeodesicAt (I := I) g p v t) := Classical.dec _
  if h : HasGeodesicAt (I := I) g p v t then
    maximalGeodesicChosenCurve (I := I) g p v h t
  else p

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesic_of_not_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (ht : t ∉ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t = p := by
  unfold maximalGeodesic
  let : Decidable (HasGeodesicAt (I := I) g p v t) := Classical.dec _
  exact dif_neg ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesic_of_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t =
      maximalGeodesicChosenCurve (I := I) g p v h t := by
  unfold maximalGeodesic
  let : Decidable (HasGeodesicAt (I := I) g p v t) := Classical.dec _
  exact dif_pos h

end MaximalGeodesicDefinition

section MaximalGeodesicValue

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesic_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v 0 = p := by
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) h0]
  obtain ⟨_J, _hJ, _hJ_conn, _h0J, _h0J', hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  exact hγ.start_eq

end MaximalGeodesicValue

section MaximalGeodesicAtTime

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem exists_isGeodesicAt_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, _hJ_conn, h0, ht, hγ⟩ := h
  refine ⟨γ, J, hJ, h0, ht, hγ, ?_⟩
  exact hγ.isGeodesicAt (hJ.mem_nhds ht)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsGeodesicAt (I := I) g γ 0 ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, h0, ht, hγ_initial, hγ_at⟩ :=
    exists_isGeodesicAt_of_mem_maximalGeodesicInterval (I := I) h
  refine ⟨γ, hγ_initial.start_eq, ?_, hγ_at⟩
  exact hγ_initial.isGeodesicAt (hJ.mem_nhds h0)

end MaximalGeodesicAtTime

section MaximalGeodesicMain

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesic_properties
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    let I_max := maximalGeodesicInterval (I := I) g p v
    let γ_max := maximalGeodesic (I := I) g p v
    IsOpen I_max ∧ (0 : ℝ) ∈ I_max ∧ γ_max 0 = p ∧
      (∀ t ∉ I_max, γ_max t = p) ∧
      (∀ t ∈ I_max, ∃ γ : ℝ → M, γ 0 = p ∧
        IsGeodesicAt (I := I) g γ 0 ∧ IsGeodesicAt (I := I) g γ t) := by
  refine ⟨maximalGeodesicInterval_isOpen (I := I) g p v,
    zero_mem_maximalGeodesicInterval (I := I) g p v,
    maximalGeodesic_zero (I := I) g p v, ?_, ?_⟩
  · intro t ht
    exact maximalGeodesic_of_not_mem (I := I) ht
  · intro t ht
    exact exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval (I := I) ht

end MaximalGeodesicMain

section BridgeLemmas

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma isGeodesic_iff_isGeodesicOn_univ
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} :
    IsGeodesic (I := I) g γ ↔ IsGeodesicOn (I := I) g γ (Set.univ : Set ℝ) := by
  constructor
  · intro hγ
    exact hγ.isGeodesicOn _
  · intro hγ t
    exact hγ t (Set.mem_univ t)

end BridgeLemmas


end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
