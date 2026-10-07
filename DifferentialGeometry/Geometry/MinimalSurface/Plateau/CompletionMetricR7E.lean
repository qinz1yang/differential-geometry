import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarTopologyR7E
import DifferentialGeometry.Geometry.Metric.Conformal.PositiveDomain
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ProfileConfinement
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Operator.HessianAlgebra

/-!
# O-MY-R7E G2：`K°` 上的 completion metric `Ĝ`（complete + homogeneously regular + germ 相等 + barrier）

`Ĝ := canonicalPositiveDomainMetric G δ_K K°`，`δ_K = 1_K · cutoff(δ, ρ + b + δ)`
（`CollarTopologyR7E` 证光滑、
`{δ_K > 0} = K°`），即 `Ĝ = δ_K⁻² G` 在 `K°` 上；同一个度量就是树里 `profileMetric (G|K°) δ (ρ + b + δ)`。

`exists_completion_metric_R7E` 的四个结论：
1. `RiemannianMetricComplete Ĝ`、2. `HomogeneouslyRegularMetric Ĝ`（树里 [V]
   `canonicalPositiveDomainMetric_complete_homogeneous`，`dim = 3`）；
3. **germ**（R-MY3 (3) jets）：`ρ < −b − δ/2` 处 `Ĝ.inner = (G|K°).inner` 在邻域上（`cutoff = 1`）；
4. **barrier confinement**（R-MY3 (2) 选 barrier 方案）：`Ĝ`-Morrey 盘、光滑嵌入 `Γ`、`ρ ∘ Γ ≤ −b − δ` ⇒
   `ρ ∘ u ≤ −b − δ` 且 `Ĝ = G|K°` 在每个 `u z` 的邻域上（树里 [V] `IsMorreyDisk.profile_confinement`，
   其 `hbase`/`hcontact` 由 collar 严格凸给出）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- 平移后的 `ρ'` 在 `K°` 上对 `G|K°` 的 Hessian = `ρ` 对 `G` 的 Hessian。 -/
theorem hessFun_restrictOpen_shift_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) (c₀ : ℝ) (Ko : TopologicalSpace.Opens N)
    (x : Ko) (v : TangentSpace 𝓘(ℝ, E) x) :
    hessFun (G.restrictOpen Ko) (fun y : Ko => ρ y - c₀) x v v = hessFun G ρ x v v := by
  have h := hessFun_restrictOpen_of_contMDiff G Ko (fun y => ρ y - c₀)
    (hρ.sub contMDiff_const) x v v
  rw [mfderiv_subtype_val_apply] at h
  rw [h]
  let f : C^∞⟮𝓘(ℝ, E), N; ℝ⟯ := ⟨ρ, hρ⟩
  have hfun : (fun y => ρ y - c₀) = fun y => f y + -c₀ := by
    funext y
    rw [sub_eq_add_neg]
    rfl
  rw [hfun, hessFun_add_const G f (-c₀) (x : N) v v]
  rfl

/-- **G2**（R-MY3 定稿）：`K°` 上的 completion metric，见文件头。 -/
theorem exists_completion_metric_R7E [T3Space N] [SecondCountableTopology N]
    (hdim : Module.finrank ℝ E = 3) (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {b δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hcpt : IsCompact {x | ρ x ≤ -b + η})
    (hcoll : ∀ x, -b - δ ≤ ρ x → ρ x ≤ -b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x ≠ 0 ∧
      ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < hessFun G ρ x v v)
    {K : Set N} (hKcl : IsClosed K) (hKρ : K ⊆ {x | ρ x ≤ -b})
    (hfr : frontier K ⊆ {x | ρ x = -b}) (Ko : TopologicalSpace.Opens N)
    (hKo : (Ko : Set N) = interior K) :
    ∃ Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) Ko,
      RiemannianMetricComplete Ghat ∧ HomogeneouslyRegularMetric Ghat ∧
      (∀ x : Ko, ρ x < -b - δ / 2 →
        ∀ᶠ y in 𝓝 x, Ghat.inner y = (G.restrictOpen Ko).inner y) ∧
      ∀ (Γ : freeLoop Ko) (u : C(closedDisk, Ko)), IsMorreyDisk Ghat Γ u →
        IsSmoothEmbeddedLoop (E := E) Γ → (∀ θ, ρ (Γ θ : N) ≤ -b - δ) →
        (∀ z, ρ (u z : N) ≤ -b - δ) ∧
          ∀ z, ∀ᶠ y in 𝓝 (u z), Ghat.inner y = (G.restrictOpen Ko).inner y := by
  obtain ⟨X, hXc, β, ε, hε, hdρ, hβ0, hβ1, hβeq, -, -⟩ :=
    exists_collar_levelField_R7E G hρ (lo := -b - δ) (hi := -b) (by linarith) hη hcpt hcoll
  have hahi : -b - δ - ε < -b := by linarith
  have hhib : -b < -b + ε := by linarith
  have hc₀ : -b - δ < -b := by linarith
  have hA : -b - (-b - δ) = δ := by ring
  set δK : N → ℝ := K.indicator fun x => cutoff δ (ρ x - (-b - δ)) with hδK
  have hδKs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δK := by
    have h := contMDiff_collarDefining_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hKcl hahi hhib hKρ hfr hc₀
    rw [hA] at h
    exact h
  have hU : ∀ x : N, x ∈ Ko ↔ 0 < δK x := by
    intro x
    have h := collarDefining_pos_iff_R7E X hXc hρ hdρ hβeq hKcl hahi hhib hKρ hfr hc₀ (x := x)
    rw [hA] at h
    rw [← h, ← hKo]
    rfl
  have hKc : IsCompact K := hcpt.of_isClosed_subset hKcl fun x hx => by
    have h : ρ x ≤ -b := hKρ hx
    change ρ x ≤ -b + η
    linarith
  have hclos : IsCompact (closure (Ko : Set N)) :=
    hKc.of_isClosed_subset isClosed_closure (by
      rw [hKo]
      exact closure_minimal interior_subset hKcl)
  set Ghat := canonicalPositiveDomainMetric G hδKs Ko hU with hGhat
  have hCH := canonicalPositiveDomainMetric_complete_homogeneous G hδKs Ko hU hclos hdim
  have hKoρ : ∀ x : Ko, ρ x < -b := fun x =>
    rho_lt_of_mem_interior_R7E X hXc hρ hdρ hβeq hahi.le hhib.le hKρ (by rw [← hKo]; exact x.2)
  have hδKx : ∀ x : Ko, δK x = cutoff δ (ρ x - (-b - δ)) := fun x =>
    indicator_of_mem (interior_subset (by rw [← hKo]; exact x.2)) _
  -- `Ĝ` 就是 profile metric
  let ρ' : Ko → ℝ := fun y => ρ y - (-b - δ)
  have hρ' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ' :=
    (hρ.comp contMDiff_subtype_val).sub contMDiff_const
  have hρ'a : ∀ x, ρ' x < δ := fun x => by
    change ρ x - (-b - δ) < δ
    linarith [hKoρ x]
  have hprof : Ghat = profileMetric (G.restrictOpen Ko) δ hδ ρ' hρ' hρ'a := by
    ext x v w
    rw [hGhat, canonicalPositiveDomainMetric_inner, profileMetric_inner, hδKx x]
  refine ⟨Ghat, hCH.1, hCH.2, fun x hx => ?_, fun Γ u hu hΓ hΓρ => ?_⟩
  · let O : TopologicalSpace.Opens N :=
      ⟨interior K ∩ {y | ρ y < -b - δ / 2},
        isOpen_interior.inter (isOpen_lt hρ.continuous continuous_const)⟩
    have hO : ∀ y ∈ O, δK y = 1 := by
      rintro y ⟨hyK, hyρ⟩
      rw [hδK, indicator_of_mem (interior_subset hyK)]
      apply cutoff_eq_one hδ
      have : ρ y < -b - δ / 2 := hyρ
      linarith
    exact canonicalPositiveDomainMetric_inner_eventuallyEq G hδKs Ko hU O hO x
      ⟨by rw [← hKo]; exact x.2, hx⟩
  · have hbase : ∀ x : Ko, 0 < ρ' x → ∀ v : TangentSpace 𝓘(ℝ, E) x,
        0 ≤ hessFun (G.restrictOpen Ko) ρ' x v v := by
      intro x hx v
      rw [hessFun_restrictOpen_shift_R7E G hρ (-b - δ) Ko x v]
      have h1 : -b - δ ≤ ρ x := by
        have : 0 < ρ x - (-b - δ) := hx
        linarith
      by_cases hv : v = 0
      · subst hv
        have h0 : hessFun G ρ (x : N) (0 : TangentSpace 𝓘(ℝ, E) (x : N)) 0 = 0 := by simp
        exact h0.symm.le
      · exact ((hcoll x h1 (hKoρ x).le).2 v hv).le
    have hcontact : ∀ x : Ko, ρ' x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 →
        0 < hessFun (G.restrictOpen Ko) ρ' x v v := by
      intro x hx v hv
      rw [hessFun_restrictOpen_shift_R7E G hρ (-b - δ) Ko x v]
      have h1 : ρ x = -b - δ := by
        have : ρ x - (-b - δ) = 0 := hx
        linarith
      exact (hcoll x h1.ge (hKoρ x).le).2 v hv
    have hu' : IsMorreyDisk (profileMetric (G.restrictOpen Ko) δ hδ ρ' hρ' hρ'a) Γ u := by
      rw [← hprof]
      exact hu
    obtain ⟨hconf, -, hgerm⟩ := hu'.profile_confinement (G.restrictOpen Ko) δ hδ ρ' hρ' hρ'a
      hbase hcontact hΓ (fun θ => by
        change ρ (Γ θ : N) - (-b - δ) ≤ 0
        linarith [hΓρ θ])
    refine ⟨fun z => ?_, fun z => ?_⟩
    · have h := hconf z
      change ρ (u z : N) - (-b - δ) ≤ 0 at h
      linarith
    · filter_upwards [hgerm z] with y hy
      rw [hprof]
      exact hy.1

end DifferentialGeometry.Geometry
