import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamFrame
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# A global normal frame of a slice along its base map (lane CMS3-CARRIER, group G2, part 2)

For a `C^r` slice `S` (`r ≥ 2`) of dimension `d` and a `C^{r−1}` map `b : B → M` of a compact smooth
manifold onto `S`, `exists_normalFrame_along` produces finitely many vectors
`σ_α s = ρ_α s • n_α (b s)` (`α : Fin K`, `K = N (dim − d)`), where
* `n_α` are slice-chart normal frame vectors (`sliceNormalFrame_spec`), `C^{r−1}` vector fields on
  open sets `O_α ⊆ M`,
* `ρ_α = ψ_j / √(Σ ψ_i²)` for a smooth partition of unity `ψ` on `B` subordinate to the chart
  domains (so `Σ_j ρ_j² = 1`), with `tsupport ρ_α ⊆ b⁻¹ O_α`,

such that every `σ_α s` is normal to `S` at `b s` and every normal vector `v` at `b s` satisfies
the frame identity `v = Σ_α g(v, σ_α s) σ_α s`. This is the "finitely many frames, `Σ ρ_j² = 1`"
isometric embedding of the D-CMS3 design (§3, §10).

Also: `contMDiffAt_inner_along` (the metric on two `C^m` vector fields along a map) and
`normalSubFinite` (the normal space as a submodule) with `finrank_normalSubFinite` (`= dim − d`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section InnerAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {X : Type*} [TopologicalSpace X] [ChartedSpace G X]

/-- The metric evaluated on two `C^m` vector fields along a `C^m` map is `C^m` (`m ≤ n`). -/
theorem contMDiffAt_inner_along {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hmn : m ≤ n)
    {β : X → M} {v w : ∀ x, TangentSpace I (β x)} {x₀ : X}
    (hv : ContMDiffAt J I.tangent m (fun x => (⟨β x, v x⟩ : TangentBundle I M)) x₀)
    (hw : ContMDiffAt J I.tangent m (fun x => (⟨β x, w x⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt J 𝓘(ℝ, ℝ) m (fun x => g.inner (β x) (v x) (w x)) x₀ := by
  have hb : ContMDiffAt J I m β x₀ :=
    (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp x₀ hv
  have hG : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] Bundle.Trivial M ℝ y)
        (β x) (g.inner (β x))) x₀ :=
    (g.contMDiff.of_le hmn).contMDiffAt.comp x₀ hb
  have h := ContMDiffAt.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M ℝ) (b := β) (ψ := fun x => g.inner (β x)) (v := v) (w := w) hG hv hw
  exact (contMDiffAt_totalSpace.mp h).2

end InnerAlong

section NormalSub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `g`-normal space of `S` at `y`, as a submodule of the tangent space. -/
def normalSubFinite {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (S : Set M) (y : M) : Submodule ℝ (TangentSpace I y) where
  carrier := {v | ∀ w ∈ sliceTangent I S y, g.inner y v w = 0}
  add_mem' := by
    intro v v' hv hv' w hw
    change g.inner y (v + v') w = 0
    rw [map_add, add_apply, hv w hw, hv' w hw, add_zero]
  zero_mem' := by
    intro w _
    change g.inner y 0 w = 0
    rw [map_zero, zero_apply]
  smul_mem' := by
    intro a v hv w hw
    change g.inner y (a • v) w = 0
    rw [map_smul, smul_apply, hv w hw, smul_zero]

theorem mem_normalSubFinite {n : ℕ∞ω}
    {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)} {S : Set M} {y : M}
    {v : TangentSpace I y} :
    v ∈ normalSubFinite g S y ↔ ∀ w ∈ sliceTangent I S y, g.inner y v w = 0 :=
  Iff.rfl

/-- A `g`-orthonormal family of normal vectors spanning the normal space computes its dimension. -/
theorem finrank_normalSubFinite_of_frame {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {S : Set M} {y : M}
    {m : ℕ} (f : Fin m → TangentSpace I y)
    (hon : ∀ k l, g.inner y (f k) (f l) = if k = l then 1 else 0)
    (hnor : ∀ k, f k ∈ normalSubFinite g S y)
    (hspan : ∀ v ∈ normalSubFinite g S y, v = ∑ k, g.inner y v (f k) • f k) :
    Module.finrank ℝ (normalSubFinite g S y) = m := by
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc l
    have h := congrArg (fun v => g.inner y v (f l)) hc
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, hon, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero,
      zero_apply] at h
    exact h
  have hspan_eq : Submodule.span ℝ (Set.range f) = normalSubFinite g S y := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hnor k
    · intro v hv
      rw [hspan v hv]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  rw [← hspan_eq, finrank_span_eq_card hli, Fintype.card_fin]

end NormalSub

section Global

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
  [T2Space B]

variable {r : ℕ∞}

/-- **A global normal frame along the base map.** -/
theorem exists_normalFrame_along
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (b : B → M) (hb : Continuous b) (hbS : range b = S) :
    ∃ (K : ℕ) (ρ : Fin K → B → ℝ) (nf : Fin K → (y : M) → TangentSpace I y)
      (O : Fin K → Set M),
      (∀ α, IsOpen (O α)) ∧ (∀ α, ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ (ρ α)) ∧
      (∀ α, tsupport (ρ α) ⊆ b ⁻¹' O α) ∧
      (∀ α y, y ∈ O α → ContMDiffAt I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω)
        (fun y => (⟨y, nf α y⟩ : TangentBundle I M)) y) ∧
      (∀ α s, ρ α s • nf α (b s) ∈ normalSubFinite g S (b s)) ∧
      (∀ s, ∀ v ∈ normalSubFinite g S (b s),
        v = ∑ α, g.inner (b s) v (ρ α s • nf α (b s)) • (ρ α s • nf α (b s))) ∧
      ∀ s, Module.finrank ℝ (normalSubFinite g S (b s)) = Module.finrank ℝ E - d := by
  classical
  set m : ℕ := Module.finrank ℝ E - d with hm
  have hk0 : (r : ℕ∞ω) ≠ 0 := by
    have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr
    exact (zero_lt_one.trans_le h').ne'
  have hbS' : ∀ s, b s ∈ S := fun s => hbS ▸ mem_range_self s
  -- a slice chart and a normal frame at every parameter
  have hchart : ∀ s : B, ∃ (c : PartialDiffeomorph I 𝓘(ℝ, E) M E (r : ℕ∞ω))
      (A : AffineSubspace ℝ E) (_ : FiniteDimensional ℝ A.direction) (ν : Fin m → E → E),
      b s ∈ c.source ∧ c.toPartialEquiv.IsImage S (A : Set E) ∧
      (∀ k, ContDiffOn ℝ ((r - 1 : ℕ∞) : ℕ∞ω) (ν k) c.target) ∧
      (∀ x ∈ c.target, ∀ k l,
        sliceCoeffFinite g c x (ν k x) (ν l x) = if k = l then 1 else 0) ∧
      (∀ x ∈ c.target, ∀ k, ∀ u ∈ A.direction, sliceCoeffFinite g c x (ν k x) u = 0) ∧
      (∀ x ∈ c.target, ∀ v : E, (∀ u ∈ A.direction, sliceCoeffFinite g c x v u = 0) →
        v = ∑ k, sliceCoeffFinite g c x v (ν k x) • ν k x) := by
    intro s
    obtain ⟨c, A, hA, hsc, hdim, himage⟩ := hS (b s) (hbS' s)
    obtain ⟨ν, hν, hon, hnor, hspan⟩ := exists_sliceNormalFrame hr g c A hdim
    exact ⟨c, A, hA, ν, hsc, himage, hν, hon, hnor, hspan⟩
  choose c A hA ν hsc himage hν hon hnor hspan using hchart
  -- finite subcover of `B` by chart domains
  set U : B → Set B := fun s => b ⁻¹' (c s).source with hU
  have hUo : ∀ s, IsOpen (U s) := fun s => (c s).open_source.preimage hb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun s _ => mem_iUnion.mpr ⟨s, hsc s⟩)
  set N : ℕ := t.card with hN
  set pt : Fin N → B := fun j => (t.equivFin.symm j : B) with hpt
  have hcover : (univ : Set B) ⊆ ⋃ j, U (pt j) := by
    intro s _
    obtain ⟨s', hs't, hs⟩ := mem_iUnion₂.mp (ht (mem_univ s))
    refine mem_iUnion.mpr ⟨t.equivFin ⟨s', hs't⟩, ?_⟩
    simpa [hpt] using hs
  -- a smooth partition of unity, normalised to `Σ ρ_j² = 1`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, EB) isClosed_univ
    (fun j : Fin N => U (pt j)) (fun j => hUo _) hcover
  have hψsum : ∀ s, ∑ j, ψ j s = 1 := fun s => by
    rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_eq_one (mem_univ s)
  set Q : B → ℝ := fun s => ∑ j, (ψ j s) ^ 2 with hQ
  have hQpos : ∀ s, 0 < Q s := by
    intro s
    obtain ⟨j, hj⟩ : ∃ j, 0 < ψ j s := by
      by_contra hcon
      have hcon' : ∀ j, ψ j s ≤ 0 := fun j => not_lt.mp fun h => hcon ⟨j, h⟩
      have h0 : ∑ j, ψ j s ≤ 0 := Finset.sum_nonpos fun j _ => hcon' j
      rw [hψsum s] at h0
      norm_num at h0
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos hj 2⟩
  set ρj : Fin N → B → ℝ := fun j s => ψ j s * (Real.sqrt (Q s))⁻¹ with hρj
  have hQs : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ Q := by
    intro s
    exact contMDiffAt_finsetSum fun j _ => ((ψ j).contMDiff s).pow 2
  have hρjs : ∀ j, ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ (ρj j) := by
    intro j s
    have hsq : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ (fun s => Real.sqrt (Q s)) s :=
      (Real.contDiffAt_sqrt (hQpos s).ne').contMDiffAt.comp s (hQs s)
    exact ((ψ j).contMDiff s).mul (hsq.inv₀ (Real.sqrt_pos.mpr (hQpos s)).ne')
  have hρjsq : ∀ s, ∑ j, (ρj j s) ^ 2 = 1 := by
    intro s
    have hsq : Real.sqrt (Q s) ^ 2 = Q s := Real.sq_sqrt (hQpos s).le
    simp only [hρj, mul_pow, inv_pow, hsq, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (hQpos s).ne'
  have hρjsupp : ∀ j, tsupport (ρj j) ⊆ U (pt j) := fun j =>
    (tsupport_mul_subset_left).trans (hψ j)
  -- the indexed family
  set jk : Fin (N * m) → Fin N × Fin m := fun α => finProdFinEquiv.symm α with hjk
  set nfr : Fin N → Fin m → (y : M) → TangentSpace I y := fun j k y =>
    mfderiv 𝓘(ℝ, E) I (c (pt j)).symm (c (pt j) y) (ν (pt j) k (c (pt j) y)) with hnfr
  have hspec : ∀ j s, b s ∈ (c (pt j)).source →
      (∀ k l, g.inner (b s) (nfr j k (b s)) (nfr j l (b s)) = if k = l then 1 else 0) ∧
      (∀ k, ∀ w ∈ sliceTangent I S (b s), g.inner (b s) (nfr j k (b s)) w = 0) ∧
      ∀ v : TangentSpace I (b s), (∀ w ∈ sliceTangent I S (b s), g.inner (b s) v w = 0) →
        v = ∑ k, g.inner (b s) v (nfr j k (b s)) • nfr j k (b s) := fun j s hs =>
    sliceNormalFrame_spec hr g (hA (pt j)) (himage (pt j)) (hon (pt j)) (hnor (pt j))
      (hspan (pt j)) (hbS' s) hs
  refine ⟨N * m, fun α => ρj (jk α).1, fun α => nfr (jk α).1 (jk α).2,
    fun α => (c (pt (jk α).1)).source, fun α => (c _).open_source, fun α => hρjs _,
    fun α => hρjsupp _, ?_, ?_, ?_, ?_⟩
  · intro α y hy
    exact contMDiffAt_sliceFrame_along hr (hν _ _) contMDiffAt_id hy
  · intro α s
    change ρj (jk α).1 s • nfr (jk α).1 (jk α).2 (b s) ∈ normalSubFinite g S (b s)
    by_cases h0 : ρj (jk α).1 s = 0
    · rw [h0, zero_smul]; exact (normalSubFinite g S (b s)).zero_mem
    · have hs : b s ∈ (c (pt (jk α).1)).source := hρjsupp _ (subset_tsupport _ h0)
      exact (normalSubFinite g S (b s)).smul_mem _ ((hspec _ s hs).2.1 _)
  · intro s v hv
    have hterm : ∀ j k, g.inner (b s) v (ρj j s • nfr j k (b s)) • (ρj j s • nfr j k (b s)) =
        (ρj j s) ^ 2 • (g.inner (b s) v (nfr j k (b s)) • nfr j k (b s)) := by
      intro j k
      rw [map_smul, smul_eq_mul, smul_smul, smul_smul]
      congr 1
      ring
    have hj : ∀ j, ∑ k, g.inner (b s) v (ρj j s • nfr j k (b s)) • (ρj j s • nfr j k (b s)) =
        (ρj j s) ^ 2 • v := by
      intro j
      simp_rw [hterm]
      rw [← Finset.smul_sum]
      by_cases h0 : ρj j s = 0
      · rw [h0]; simp
      · have hs : b s ∈ (c (pt j)).source := hρjsupp _ (subset_tsupport _ h0)
        rw [← (hspec j s hs).2.2 v hv]
    have hsum2' : ∀ (F : Fin N → Fin m → TangentSpace I (b s)),
        ∑ α : Fin (N * m), F (jk α).1 (jk α).2 = ∑ j, ∑ k, F j k := by
      intro F
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
    have h2 := hsum2' (fun j k => g.inner (b s) v (ρj j s • nfr j k (b s)) •
      (ρj j s • nfr j k (b s)))
    refine Eq.trans ?_ h2.symm
    simp only [hj]
    rw [← Finset.sum_smul, hρjsq s, one_smul]
  · intro s
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (mem_univ s))
    have hs : b s ∈ (c (pt j)).source := hj
    obtain ⟨hon', hnor', hspan'⟩ := hspec j s hs
    exact finrank_normalSubFinite_of_frame g (fun k => nfr j k (b s)) hon'
      (fun k => hnor' k) (fun v hv => hspan' v hv)

end Global

end DifferentialGeometry.Geometry.FiniteSoul
