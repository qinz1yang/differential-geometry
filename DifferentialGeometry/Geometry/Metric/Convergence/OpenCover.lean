import DifferentialGeometry.Geometry.Metric.Convergence.EventualPullback
import DifferentialGeometry.Geometry.Metric.Pullback.CoefficientConvergence
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E Q : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q]
  [IsManifold 𝓘(ℝ, E) ∞ Q]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H}
  {N : ℕ → Type*} [∀ k, TopologicalSpace (N k)] [∀ k, ChartedSpace H (N k)]
  [∀ k, IsManifold J ∞ (N k)]

theorem exists_metricCInfConvergenceOnCompacts_restrict_open_of_local_coefficients
    {ι : Type*} (U : ι → TopologicalSpace.Opens E)
    (j : ∀ i, U i → Q) (hj : ∀ i, IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (j i))
    (hinj : ∀ i, Function.Injective (j i))
    (jbar : ι → E → Q) (hjbar : ∀ i (z : U i), jbar i z = j i z)
    (V : TopologicalSpace.Opens Q) [T2Space V]
    (hcover : ∀ x : V, ∃ i z, j i z = (x : Q))
    (g : ∀ k, SmoothRiemannianMetric J (N k)) (f : ∀ k, Q → N k)
    (gQ : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hpartial : ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) J Q (N k) ∞,
      (V : Set Q) ⊆ Φ.source ∧ Set.EqOn (Φ : Q → N k) (f k) Φ.source)
    (hconv : ∀ i, MapCInfConvergenceOnCompacts
      (Subtype.val '' ((j i) ⁻¹' (V : Set Q)))
      (fun k => Geometry.pullbackMetricCoefficients (g k) (f k ∘ jbar i))
      (Geometry.pullbackMetricCoefficients gQ (jbar i))) :
    ∃ G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) V,
      (∀ᶠ k in atTop, ContMDiff 𝓘(ℝ, E) J ∞ (fun x : V => f k x) ∧
        ∀ (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
          (G k).inner x v w = (g k).inner (f k x)
            (mfderiv 𝓘(ℝ, E) J (f k) (x : Q) v)
            (mfderiv 𝓘(ℝ, E) J (f k) (x : Q) w)) ∧
      MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  classical
  by_cases hV : Nonempty V
  · let p₀ : V := Classical.choice hV
    let A : ι → TopologicalSpace.Opens E := fun i =>
      ⟨Subtype.val '' ((j i) ⁻¹' (V : Set Q)),
        (U i).isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage (hj i).contMDiff.continuous)⟩
    have hAU (i : ι) : A i ≤ U i := by
      rintro z ⟨x, _, rfl⟩
      exact x.property
    let incl : ∀ i, A i → U i := fun i => TopologicalSpace.Opens.inclusion (hAU i)
    have hincl (i : ι) : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (incl i) := by
      intro z
      exact isLocalDiffeomorphAt_subtypeCodRestrict (fun y : A i => hAU i y.property)
        (isLocalDiffeomorph_subtype_val (A i) z)
    have hmem (i : ι) (z : A i) : j i (incl i z) ∈ V := by
      obtain ⟨x, hx, hzx⟩ := z.property
      have heq : incl i z = x := Subtype.ext hzx.symm
      rw [heq]
      exact hx
    let jV : ∀ i, A i → V := fun i z => ⟨j i (incl i z), hmem i z⟩
    have hjV (i : ι) : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (jV i) := by
      intro z
      exact isLocalDiffeomorphAt_subtypeCodRestrict (hmem i)
        (isLocalDiffeomorph_comp (hj i) (hincl i) z)
    have hinjV (i : ι) : Function.Injective (jV i) := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : U i => (z : E)) (hinj i (congrArg Subtype.val hxy))
    have hcoverV : ∀ x : V, ∃ i z, jV i z = x := by
      intro x
      obtain ⟨i, z, hz⟩ := hcover x
      have hzV : j i z ∈ V := hz ▸ x.property
      refine ⟨i, ⟨z, ⟨z, hzV, rfl⟩⟩, ?_⟩
      exact Subtype.ext hz
    let jVbar : ι → E → V := fun i z => if hz : z ∈ A i then jV i ⟨z, hz⟩ else p₀
    have hjVbar (i : ι) (z : A i) : jVbar i z = jV i z := dif_pos z.property
    have hbar (i : ι) : EqOn (fun z => (jVbar i z : Q)) (jbar i) (A i) := by
      intro z hz
      exact (congrArg Subtype.val (hjVbar i ⟨z, hz⟩)).trans
        (hjbar i (incl i ⟨z, hz⟩)).symm
    apply exists_metricCInfConvergenceOnCompacts_of_eventual_partial_pullback_coefficients
      V A jV hjV hinjV hcoverV jVbar hjVbar g f (gQ.restrictOpen V) hpartial
    intro i
    apply (hconv i).congr (A i).isOpen
    · intro k z hz
      apply Geometry.pullbackMetricCoefficients_eq_of_eventuallyEq
      exact Filter.eventuallyEq_of_mem ((A i).isOpen.mem_nhds hz)
        (fun y hy => congrArg (f k) (hbar i hy))
    · intro z hz
      calc
        Geometry.pullbackMetricCoefficients (gQ.restrictOpen V) (jVbar i) z =
            Geometry.pullbackMetricCoefficients gQ (fun y => (jVbar i y : Q)) z := by
          ext v w
          rw [Geometry.pullbackMetricCoefficients_apply, Geometry.pullbackMetricCoefficients_apply,
            SmoothRiemannianMetric.restrictOpen_inner, DifferentialGeometry.mfderiv_subtypeVal_comp]
          rfl
        _ = Geometry.pullbackMetricCoefficients gQ (jbar i) z :=
          Geometry.pullbackMetricCoefficients_eq_of_eventuallyEq gQ
            (Filter.eventuallyEq_of_mem ((A i).isOpen.mem_nhds hz) (hbar i))
  · obtain ⟨G, hG⟩ :=
      exists_eventually_pullback_metric_restrict_open V (gQ.restrictOpen V) g f hpartial
    refine ⟨G, hG, ?_⟩
    intro K hK p ε hε
    refine ⟨0, fun k hk => ?_⟩
    have hKempty : K = (∅ : Set V) := by
      ext x
      exact (hV ⟨x⟩).elim
    subst K
    simpa [metricDerivNormSupOn] using hε

end DifferentialGeometry.CheegerGromovCompactness
