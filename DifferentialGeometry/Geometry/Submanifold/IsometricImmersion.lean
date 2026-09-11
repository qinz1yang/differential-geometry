import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Comparison.HopfRinow.LocalGeodesicSeed
import DifferentialGeometry.Geometry.Geodesic.Chart.Regularity
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

section ImmersionInterface

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure IsRiemannianIsometricImmersion
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) : Prop where
  isImmersion : IsImmersion IN I ∞ iota
  inner_map : ∀ (x : N) (u v : TangentSpace IN x),
    gM.inner (iota x) (mfderiv IN I iota x u) (mfderiv IN I iota x v) =
      gN.inner x u v

namespace IsRiemannianIsometricImmersion

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem contMDiff
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    ContMDiff IN I ∞ iota :=
  h.isImmersion.contMDiff

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem continuous
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    Continuous iota :=
  h.contMDiff.continuous

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem speed_sq_comp
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota)
    {gamma : ℝ → N} {t : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) IN gamma t) :
    gM.inner (iota (gamma t))
        (mfderiv 𝓘(ℝ, ℝ) I (iota ∘ gamma) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (iota ∘ gamma) t (1 : ℝ)) =
      gN.inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) IN gamma t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) IN gamma t (1 : ℝ)) := by
  let one : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)
  have hchain := mfderiv_comp_apply
    (I := 𝓘(ℝ, ℝ)) (I' := IN) (I'' := I) t
    (h.contMDiff.mdifferentiableAt (by simp)) hgamma one
  change mfderiv 𝓘(ℝ, ℝ) I (iota ∘ gamma) t (1 : ℝ) =
      mfderiv IN I iota (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) IN gamma t (1 : ℝ)) at hchain
  rw [hchain]
  exact h.inner_map (gamma t) _ _

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem of_is_smooth_embedding
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (hemb : IsSmoothEmbedding IN I ∞ iota)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (iota x) (mfderiv IN I iota x u) (mfderiv IN I iota x v) =
        gN.inner x u v) :
    IsRiemannianIsometricImmersion gN gM iota :=
  ⟨hemb.isImmersion, hmetric⟩

end IsRiemannianIsometricImmersion

def preservesGeodesics
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) : Prop :=
  ∀ (gamma : ℝ → N) (t : ℝ),
    IsGeodesicAt (I := IN) gN gamma t →
      IsGeodesicAt (I := I) gM (iota ∘ gamma) t

namespace preservesGeodesics

theorem is_geodesic_on
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : preservesGeodesics gN gM iota) [I.Boundaryless]
    {gamma : ℝ → N} {U : Set ℝ}
    (hgamma : ∀ t ∈ U, IsGeodesicAt (I := IN) gN gamma t) :
    IsGeodesicOn (I := I) gM (iota ∘ gamma) U := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro t ht
  exact (h gamma t (hgamma t ht)).hasGeodesicEquationAt gM

end preservesGeodesics

end ImmersionInterface

section GeodesicGerm

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def isUnitSpeedGeodesicGermIn
    (g : SmoothRiemannianMetric I M) (C : Set M)
    (alpha : ℝ → M) : Prop :=
  ∃ epsilon : ℝ,
    0 < epsilon ∧
    IsGeodesicAt (I := I) g alpha 0 ∧
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ alpha (Set.Ioo (-epsilon) epsilon) ∧
    IsGeodesicOn (I := I) g alpha (Set.Ioo (-epsilon) epsilon) ∧
    (∀ s ∈ Set.Ioo (-epsilon) epsilon,
      g.inner (alpha s)
        (mfderiv 𝓘(ℝ, ℝ) I alpha s (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I alpha s (1 : ℝ)) = 1) ∧
    Set.MapsTo alpha (Set.Ioo (-epsilon) epsilon) C

end GeodesicGerm

section LocalUnitGeodesic

variable {EN HN N : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]

omit [IN.Boundaryless] in
theorem exists_unit_tangent_of_finrank_pos
    (gN : SmoothRiemannianMetric IN N)
    (hdim : 0 < Module.finrank ℝ EN) (y : N) :
    ∃ w : TangentSpace IN y, gN.inner y w w = 1 := by
  let _ : Nontrivial EN := Module.finrank_pos_iff.mp hdim
  let _ : Nontrivial (TangentSpace IN y) := inferInstanceAs (Nontrivial EN)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace IN y)
  let a : ℝ := Real.sqrt (gN.inner y v v)
  have hinner : 0 < gN.inner y v v := gN.pos y v hv
  have ha : 0 < a := Real.sqrt_pos.2 hinner
  have ha_sq : a ^ 2 = gN.inner y v v := Real.sq_sqrt hinner.le
  refine ⟨a⁻¹ • v, ?_⟩
  have hscale : gN.inner y (a⁻¹ • v) (a⁻¹ • v) =
      (a⁻¹) ^ 2 * gN.inner y v v := by
    rw [(gN.inner y).map_smul, smul_apply, (gN.inner y v).map_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hscale, ← ha_sq]
  field_simp

theorem exists_isGeodesicAt_on_ioo_at_velocity
    (gN : SmoothRiemannianMetric IN N) (y : N) (w : TangentSpace IN y) :
    ∃ (eta : ℝ → N) (delta : ℝ),
      0 < delta ∧ eta 0 = y ∧
      (mfderiv 𝓘(ℝ, ℝ) IN eta 0 (1 : ℝ) : EN) = (w : EN) ∧
      (∀ t ∈ Set.Ioo (-delta) delta,
        MDifferentiableAt 𝓘(ℝ, ℝ) IN eta t) ∧
      (∀ t ∈ Set.Ioo (-delta) delta,
        IsGeodesicAt (I := IN) gN eta t) := by
  let _ : CompleteSpace EN := FiniteDimensional.complete ℝ EN
  obtain ⟨eta, f, hf0, hetaProject, heta0, hfIntegral, _hgeodesic0⟩ :=
    exists_geodesic_with_initial_velocity_at (I := IN) gN y w
  subst hetaProject
  have hetaProject (t : ℝ) : projectCurve (I := IN) f t = (f t).proj := rfl
  have hf0Project : (f 0).proj = y := by rw [hf0]
  have hetaContinuous : ContinuousAt (projectCurve (I := IN) f) 0 := by
    have hproject : Continuous (fun p : TangentBundle IN N ↦ p.proj) :=
      FiberBundle.continuous_proj EN (TangentSpace IN)
    exact hproject.continuousAt.comp hfIntegral.continuousAt
  obtain ⟨epsilon, hepsilon, hfOn⟩ := isMIntegralCurveAt_iff'.mp hfIntegral
  have hsourceNhds :
      {t : ℝ | (f t).proj ∈ (chartAt HN y).source} ∈ 𝓝 (0 : ℝ) := by
    exact hetaContinuous.preimage_mem_nhds
      ((chartAt HN y).open_source.mem_nhds (by
        rw [heta0]
        exact mem_chart_source HN y))
  have hballNhds : Metric.ball (0 : ℝ) epsilon ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ hepsilon
  obtain ⟨delta, hdelta, hdeltaSubset⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hballNhds hsourceNhds)
  have hf0Source : (f 0).proj ∈ (chartAt HN y).source := by
    rw [hf0Project]
    exact mem_chart_source HN y
  have hmfderiv :
      mfderiv 𝓘(ℝ, ℝ) IN (fun t ↦ (f t).proj) 0 (1 : ℝ) = (f 0).snd :=
    IsMIntegralCurveAt.mfderiv_proj_one
      (I := IN) (g := gN) (α := y) (t₀ := 0) hfIntegral hf0Source
  have hf0Velocity : ((f 0).snd : EN) = (w : EN) := by rw [hf0]
  have hfAt (t : ℝ) (ht : t ∈ Set.Ioo (-delta) delta) :
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := IN) gN y) t ∧
        (f t).proj ∈ (chartAt HN y).source := by
    have htBall : t ∈ Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨ht.1, ht.2⟩
    have htBoth := hdeltaSubset htBall
    exact ⟨hfOn.isMIntegralCurveAt
        (Metric.isOpen_ball.mem_nhds htBoth.1), htBoth.2⟩
  refine ⟨projectCurve (I := IN) f, delta, hdelta, heta0, ?_, ?_, ?_⟩
  · rw [show (projectCurve (I := IN) f) = (fun t ↦ (f t).proj) from rfl,
      hmfderiv, hf0Velocity]
  · intro t ht
    have hfDifferentiable : MDifferentiableAt 𝓘(ℝ, ℝ) IN.tangent f t :=
      (hfAt t ht).1.hasMFDerivAt.mdifferentiableAt
    have hprojectDifferentiable : MDifferentiableAt IN.tangent IN
        (Bundle.TotalSpace.proj : TangentBundle IN N → N) (f t) :=
      (Bundle.contMDiffAt_proj
        (E := (TangentSpace IN : N → Type _)) (n := 1)).mdifferentiableAt
          (by norm_num)
    exact hprojectDifferentiable.comp t hfDifferentiable
  · intro t ht
    exact ⟨y, f, hetaProject, (hfAt t ht).2, (hfAt t ht).1⟩

private theorem exists_unit_speed_geodesic_data_at
    (gN : SmoothRiemannianMetric IN N)
    (hdim : 0 < Module.finrank ℝ EN) (y : N) :
    ∃ (eta : ℝ → N) (delta : ℝ),
      0 < delta ∧ eta 0 = y ∧
      ContMDiffOn 𝓘(ℝ, ℝ) IN ∞ eta (Set.Ioo (-delta) delta) ∧
      (∀ t ∈ Set.Ioo (-delta) delta,
        IsGeodesicAt (I := IN) gN eta t) ∧
      IsGeodesicOn (I := IN) gN eta (Set.Ioo (-delta) delta) ∧
      (∀ t ∈ Set.Ioo (-delta) delta,
        gN.inner (eta t)
          (mfderiv 𝓘(ℝ, ℝ) IN eta t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) IN eta t (1 : ℝ)) = 1) := by
  obtain ⟨w, hw⟩ := exists_unit_tangent_of_finrank_pos gN hdim y
  obtain ⟨eta, delta, hdelta, heta0, hvelocity, hmdiff, hgeodesicAt⟩ :=
    exists_isGeodesicAt_on_ioo_at_velocity gN y w
  let _ : CompleteSpace EN := FiniteDimensional.complete ℝ EN
  have hgeodesic : IsGeodesicOn (I := IN) gN eta
      (Set.Ioo (-delta) delta) := by
    intro t ht
    exact (hgeodesicAt t ht).hasGeodesicEquationAt gN
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) IN ∞ eta
      (Set.Ioo (-delta) delta) := by
    apply isGeodesicOn_contMDiffOn_infty
      (I := IN) gN isOpen_Ioo hgeodesic
    intro t ht
    exact (hmdiff t ht).continuousAt.continuousWithinAt
  refine ⟨eta, delta, hdelta, heta0, hsmooth, hgeodesicAt,
    hgeodesic, ?_⟩
  intro t ht
  have hIcc : Set.Icc (min 0 t) (max 0 t) ⊆ Set.Ioo (-delta) delta := by
    intro r hr
    exact ⟨(lt_min (neg_lt_zero.mpr hdelta) ht.1).trans_le hr.1,
      hr.2.trans_lt (max_lt hdelta ht.2)⟩
  have hspeed := HopfRinow.isGeodesicOn_speedSq_const
    (I := IN) gN (t₀ := 0) (t₁ := t) isOpen_Ioo hgeodesic
    (hsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) hIcc
  have hspeed0 :
      gN.inner (eta 0)
        (mfderiv 𝓘(ℝ, ℝ) IN eta 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) IN eta 0 (1 : ℝ)) = 1 := by
    rw [heta0]
    exact (congrArg₂ (fun u v : EN ↦ gN.inner y u v)
      hvelocity hvelocity).trans hw
  exact hspeed.symm.trans hspeed0

theorem exists_unit_speed_geodesic_germ_at
    (gN : SmoothRiemannianMetric IN N)
    (hdim : 0 < Module.finrank ℝ EN) (y : N) :
    ∃ eta : ℝ → N,
      eta 0 = y ∧ isUnitSpeedGeodesicGermIn gN Set.univ eta := by
  obtain ⟨eta, delta, hdelta, heta0, hsmooth, hgeodesicAt,
      hgeodesic, hunit⟩ := exists_unit_speed_geodesic_data_at gN hdim y
  have hzero : (0 : ℝ) ∈ Set.Ioo (-delta) delta :=
    ⟨neg_lt_zero.mpr hdelta, hdelta⟩
  exact ⟨eta, heta0, delta, hdelta, hgeodesicAt 0 hzero,
    hsmooth, hgeodesic, hunit, fun t _ht ↦ Set.mem_univ (eta t)⟩

end LocalUnitGeodesic

section GermInRange

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_unit_speed_geodesic_germ_in_range
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hgeodesic : preservesGeodesics gN gM iota)
    (hdim : 0 < Module.finrank ℝ EN) (y : N) :
    ∃ alpha : ℝ → M,
      alpha 0 = iota y ∧
        isUnitSpeedGeodesicGermIn gM (Set.range iota) alpha := by
  obtain ⟨eta, epsilon, hepsilon, heta0, hsmooth, hetaGeodesicAt,
      _hetaGeodesic, hunit⟩ := exists_unit_speed_geodesic_data_at gN hdim y
  have hzero : (0 : ℝ) ∈ Set.Ioo (-epsilon) epsilon :=
    ⟨neg_lt_zero.mpr hepsilon, hepsilon⟩
  refine ⟨iota ∘ eta, by simp [heta0], epsilon, hepsilon,
    hgeodesic eta 0 (hetaGeodesicAt 0 hzero),
    hisom.contMDiff.comp_contMDiffOn hsmooth,
    hgeodesic.is_geodesic_on hetaGeodesicAt, ?_, ?_⟩
  · intro t ht
    have hetaDifferentiable : MDifferentiableAt 𝓘(ℝ, ℝ) IN eta t :=
      (hsmooth t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)
        |>.mdifferentiableAt (by simp)
    exact (hisom.speed_sq_comp hetaDifferentiable).trans (hunit t ht)
  · intro t _ht
    exact ⟨eta t, rfl⟩

end GermInRange

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

@[reducible] alias PreservesGeodesics := DifferentialGeometry.Geometry.preservesGeodesics
end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry.PreservesGeodesics

alias is_geodesic_on := DifferentialGeometry.Geometry.preservesGeodesics.is_geodesic_on
end DifferentialGeometry.Geometry.PreservesGeodesics

namespace DifferentialGeometry.Geometry

@[reducible] alias IsUnitSpeedGeodesicGermIn := DifferentialGeometry.Geometry.isUnitSpeedGeodesicGermIn
end DifferentialGeometry.Geometry
