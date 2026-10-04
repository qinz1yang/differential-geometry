import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.InteriorRetraction
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.FiniteSupported
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Relative smooth approximation of normed-space-valued maps on a manifold with boundary

`exists_smooth_seq_rel_chart_tendsto_normedSpace`: let `A` be a compact Hausdorff manifold whose
model may have boundary, `u : A → F` a `C^k` map into a finite-dimensional normed space which is
already smooth on an open `O`, and `O'` an open neighbourhood of `∂A` with `closure O' ⊆ O`.
Then there are smooth maps `us j` with `us j = u` on `O'` (exactly, for every `j`), `us j → u`
uniformly, and in every extended chart the coordinate expressions converge in `C^k` on every
compact subset of the chart target that lies in the interior of the model range.

Route: a smooth cutoff splits `u = u₀ + u₁` with `u₀` smooth and `u₁` of class `C^k` supported in
a compact subset `C₁` of `int A` away from `O'`; a Whitney embedding `e` of `A` (boundary allowed),
a smooth retraction near `e '' C₁` (`exists_smooth_retraction_near_interior_compact`) and a
cutoff extend `u₁` to a compactly supported `C^k` map `G` on `ℝ^N` with `u₁ = G ∘ e`; one
mollification supported away from `e '' closure O'` gives `g j → G`, and `us j = u₀ + g j ∘ e`.
Hence `us j - u = (g j - G) ∘ e` everywhere.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

/-- `C^p` convergence on `K` only depends on the differences `Φ j - Φinf`. -/
theorem mapCPConvergenceOn_of_sub_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {p : ℕ}
    {Φ Ψ : ℕ → E → F} {Φinf Ψinf : E → F} (h : MapCPConvergenceOn K p Ψ Ψinf)
    (heq : ∀ j y, Φ j y - Φinf y = Ψ j y - Ψinf y) : MapCPConvergenceOn K p Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hfun : (fun y => Φ k y - Φinf y) = fun y => Ψ k y - Ψinf y := funext (heq k)
  have h1 := hk0 k hk r hr x hx
  unfold mapDerivNorm at h1 ⊢
  rw [hfun]
  exact h1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ A] in
/-- The part of an extended chart target lying in the interior of the model range is open. -/
theorem isOpen_extChartAt_target_inter_interior (p : A) :
    IsOpen ((extChartAt I p).target ∩ interior (range I)) := by
  have hset : (extChartAt I p).target ∩ interior (range I) =
      I.symm ⁻¹' (chartAt H p).target ∩ interior (range I) := by
    rw [extChartAt_target]
    ext z
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, interior_subset h3⟩, h3⟩
  rw [hset]
  exact (I.continuous_symm.isOpen_preimage _ (chartAt H p).open_target).inter isOpen_interior

variable [T2Space A] [CompactSpace A]

/-- **Relative smooth approximation (normed-space values, boundary allowed).** A `C^k` map
`u : A → F` that is smooth on an open `O ⊇ closure O'`, `O' ⊇ ∂A` open, is the uniform limit of
smooth maps equal to `u` on `O'`, whose coordinate expressions converge in `C^k` on compact subsets
of chart targets inside the interior of the model range. -/
theorem exists_smooth_seq_rel_chart_tendsto_normedSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) {u : A → F} (hu : ContMDiff I 𝓘(ℝ, F) k u)
    {O O' : Set A} (hO : IsOpen O) (hbO' : I.boundary A ⊆ O') (hO'O : closure O' ⊆ O)
    (hsm : ContMDiffOn I 𝓘(ℝ, F) ∞ u O) :
    ∃ us : ℕ → A → F, (∀ j, ContMDiff I 𝓘(ℝ, F) ∞ (us j)) ∧ (∀ j, EqOn (us j) u O') ∧
      TendstoUniformly us u atTop ∧
      ∀ (p : A) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        K ⊆ interior (range I) →
        MapCPConvergenceOn K k (fun j y => us j ((extChartAt I p).symm y))
          (fun y => u ((extChartAt I p).symm y)) := by
  classical
  obtain ⟨O₂, hO₂, hO'O₂, hO₂cl⟩ := normal_exists_closure_subset isClosed_closure hO hO'O
  obtain ⟨O₃, hO₃, hO₂O₃, hO₃cl⟩ := normal_exists_closure_subset isClosed_closure hO hO₂cl
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞)) I
    (isClosed_closure : IsClosed (closure O₂)) hO₃.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hO₂O₃)
  have hχs : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ := χ.contMDiff
  set u₀ : A → F := fun x => (1 - χ x) • u x with hu₀def
  set u₁ : A → F := fun x => χ x • u x with hu₁def
  have hsum : ∀ x, u₀ x + u₁ x = u x := by
    intro x
    simp only [hu₀def, hu₁def]
    rw [← add_smul, sub_add_cancel, one_smul]
  have hu₀supp : tsupport u₀ ⊆ O := by
    refine (closure_mono ?_).trans hO₃cl
    intro x hx
    by_contra hxO
    apply hx
    simp only [hu₀def, hχ1 hxO, Pi.one_apply, sub_self, zero_smul]
  have hu₀ : ContMDiff I 𝓘(ℝ, F) ∞ u₀ :=
    contMDiff_of_tsupport fun x hx =>
      ((contMDiffAt_const.sub (hχs x)).smul (hsm.contMDiffAt (hO.mem_nhds (hu₀supp hx))))
  have hu₁ : ContMDiff I 𝓘(ℝ, F) k u₁ := (hχs.of_le (by exact_mod_cast le_top)).smul hu
  have hu₁O₂ : ∀ x ∈ O₂, u₁ x = 0 := by
    intro x hx
    simp only [hu₁def, hχ0 (subset_closure hx), Pi.zero_apply, zero_smul]
  have hC₁O₂ : ∀ x ∈ O₂, x ∉ tsupport u₁ := by
    intro x hx
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hO₂.mem_nhds hx] with y hy
    exact hu₁O₂ y hy
  have hO'O₂' : O' ⊆ O₂ := subset_closure.trans hO'O₂
  have hC₁ : IsCompact (tsupport u₁) := (isClosed_tsupport u₁).isCompact
  have hC₁i : tsupport u₁ ⊆ I.interior A := by
    intro x hx
    change I.IsInteriorPoint x
    rw [I.isInteriorPoint_iff_not_isBoundaryPoint]
    exact fun hb => hC₁O₂ x (hO'O₂' (hbO' hb)) hx
  rcases (tsupport u₁).eq_empty_or_nonempty with hempty | hne
  · -- `u₁ = 0`, so `u = u₀` is already smooth
    have hu₁0 : ∀ x, u₁ x = 0 := fun x =>
      image_eq_zero_of_notMem_tsupport (by rw [hempty]; exact notMem_empty x)
    have huu₀ : u = u₀ := funext fun x => by rw [← hsum x, hu₁0 x, add_zero]
    refine ⟨fun _ => u, fun _ => huu₀ ▸ hu₀, fun _ => eqOn_refl _ _, ?_, ?_⟩
    · rw [Metric.tendstoUniformly_iff]
      exact fun ε hε => Eventually.of_forall fun _ x => by simpa using hε
    · intro p K _ _ _
      exact MapCPConvergenceOn.const_seq _
  obtain ⟨N, e, he, hemb, hi⟩ := exists_embedding_euclidean_of_compact (I := I) (M := A)
  obtain ⟨r, U, hU, hCU, hr, -, hleft⟩ :=
    exists_smooth_retraction_near_interior_compact he hemb.isEmbedding (fun x _ => hi x)
      hC₁ hC₁i hne
  obtain ⟨ψ, hψ, hψc, hψone, hψU, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact (hC₁.image he.continuous) hU hCU
  have hfr : ContDiffOn ℝ k (fun z => u₁ (r z)) U :=
    contMDiffOn_iff_contDiffOn.mp (hu₁.comp_contMDiffOn (hr.of_le (by exact_mod_cast le_top)))
  set G : EuclideanSpace ℝ (Fin N) → F := fun z => ψ z • u₁ (r z) with hGdef
  have hG : ContDiff ℝ k G := by
    apply contDiffOn_univ.mp
    exact DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hU
      (hψ.of_le (by exact_mod_cast le_top)) hψU (by simpa only [univ_inter] using hfr)
  have hGc : HasCompactSupport G := hψc.smul_right
  have hGe : ∀ x, G (e x) = u₁ x := by
    intro x
    by_cases hx : x ∈ tsupport u₁
    · have h1 : ψ (e x) = 1 :=
        (hψone.filter_mono (nhds_le_nhdsSet ⟨x, hx, rfl⟩)).self_of_nhds
      simp only [hGdef, h1, one_smul, hleft x (hCU ⟨x, hx, rfl⟩)]
    · have h0 : u₁ x = 0 := image_eq_zero_of_notMem_tsupport hx
      by_cases hxU : e x ∈ U
      · simp only [hGdef, hleft x hxU, h0, smul_zero]
      · have hψ0 : ψ (e x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hxU (hψU h)
        simp only [hGdef, hψ0, zero_smul, h0]
  set V : Set (EuclideanSpace ℝ (Fin N)) := (e '' closure O')ᶜ with hVdef
  have hV : IsOpen V :=
    (isClosed_closure.isCompact.image he.continuous).isClosed.isOpen_compl
  have hGV : tsupport G ⊆ V := by
    rintro z hz ⟨x, hx, rfl⟩
    refine (notMem_tsupport_iff_eventuallyEq.mpr ?_) hz
    have hxO₂ : x ∈ O₂ := hO'O₂ hx
    by_cases hxU : e x ∈ U
    · have hnhds : r ⁻¹' O₂ ∈ 𝓝 (e x) :=
        (hr.continuousOn.continuousAt (hU.mem_nhds hxU)).preimage_mem_nhds
          (hO₂.mem_nhds (by rw [hleft x hxU]; exact hxO₂))
      filter_upwards [hnhds] with w hw
      simp only [hGdef, hu₁O₂ _ hw, smul_zero, Pi.zero_apply]
    · have hψ0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hxU (hψU h)
      filter_upwards [hψ0] with w hw
      simp only [hGdef, hw, Pi.zero_apply, zero_smul]
  obtain ⟨K', -, hK'V, -, g, hg, hgsupp, hconv⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_approx_supported_in_open_of_contDiff k hG hGc
      hV hGV
  have hgk : ∀ n, ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (g n) := fun n =>
    (hg n).of_le (by exact_mod_cast le_top)
  have hgG : MapCPConvergenceOn univ k g G :=
    mapCPConvergenceOn_of_tendstoUniformly hgk hG fun j hj => (hconv j hj).tendstoUniformlyOn
  have hunif : TendstoUniformly g G atTop :=
    tendstoUniformlyOn_univ.mp
      (tendstoUniformlyOn_of_cPConvergence (hgG.mono_order (Nat.zero_le k)))
  refine ⟨fun j x => u₀ x + g j (e x), fun j => hu₀.add ((hg j).contMDiff.comp he), ?_, ?_, ?_⟩
  · intro j x hx
    have hg0 : g j (e x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h => ?_
      exact hK'V (hgsupp j h) ⟨x, subset_closure hx, rfl⟩
    change u₀ x + g j (e x) = u x
    rw [hg0, ← hsum x, hu₁O₂ x (hO'O₂' hx)]
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif ε hε] with j hj x
    rw [← hsum x, ← hGe x, dist_add_left]
    exact hj (e x)
  · intro p K hK hKt hKi
    have hKU' : K ⊆ (extChartAt I p).target ∩ interior (range I) := fun y hy => ⟨hKt hy, hKi hy⟩
    have hT : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun y => e ((extChartAt I p).symm y))
        ((extChartAt I p).target ∩ interior (range I)) :=
      ((contMDiffOn_iff_contDiffOn.mp
        (he.comp_contMDiffOn (contMDiffOn_extChartAt_symm p))).of_le
          (by exact_mod_cast le_top)).mono inter_subset_left
    have h := MapCPConvergenceOn.comp_contDiffOn_right
      (isOpen_extChartAt_target_inter_interior p) isOpen_univ hK hKU' hT (mapsTo_univ _ _)
      (hgG.mono_set (subset_univ _)) (fun n => (hgk n).contDiffOn) hG.contDiffOn
    refine mapCPConvergenceOn_of_sub_eq h fun j y => ?_
    change u₀ _ + g j _ - u _ = g j _ - G _
    rw [← hsum ((extChartAt I p).symm y), ← hGe ((extChartAt I p).symm y)]
    abel

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
