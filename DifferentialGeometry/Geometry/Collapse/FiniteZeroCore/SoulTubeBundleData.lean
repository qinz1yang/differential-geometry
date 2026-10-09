import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulTube
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamBundle
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierBase
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicSlice

/-!
# LFR49 (c): the soul data of a noncompact finite three-model, every soul dimension

Frozen blueprint master207A, LFR49 (A:29096): "If it is noncompact, apply LFR45–LFR47". The restated
LFR46 (`exists_finite_normalFlowMap_tube`, lane CMS3-FLOW2) needs, for the SAME soul `S`: LFR45's
tube `(ε, ψ)` and strict outward directions, a compact smooth base `B` with a smooth Riemannian
vector bundle `V`, the base map `b : B → M` with its inverse contract, and the normal
parametrization `ι : V → T M`. This file supplies all of them for a complete connected noncompact
finite-order three-manifold with `sec ≥ 0`, in every soul dimension:

* dimension 0 (BASE-0, new here): a connected `0`-slice is one point
  (`eq_singleton_of_isEmbeddedSliceOfOrder_zero`); the base is `Fin 0 → ℝ`
  (`soulBase_point_finite`);
* dimension 1: BASE-1a `exists_closedGeodesic_of_slice_dim_one` and BASE-1b
  `soulBase_closedGeodesic` (base `AddCircle 1`);
* dimension 2: BASE-2 `soulBase_surface_carrier` (W-SUB's carrier `Ŝ`);
* in every case `Ê` (`exists_soulNormalBundle`).

`exists_finite_soul_tube_bundle_data_dim_three` is item (c) of the LFR49 assembly
(build-logs/scratch/LFR49/Assembly.lean, `lfr49C_soul_tube_bundle_data`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Point

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A connected slice of dimension zero is one point.** -/
theorem eq_singleton_of_isEmbeddedSliceOfOrder_zero [T1Space M] {k : WithTop ℕ∞} {S : Set M}
    (hS : IsEmbeddedSliceOfOrder I k 0 S) (hconn : IsPreconnected S) {x : M} (hx : x ∈ S) :
    S = {x} := by
  obtain ⟨c, A, hfd, hxc, hdim0, himg⟩ := hS x hx
  have hA : ∀ a ∈ (A : Set E), ∀ b ∈ (A : Set E), a = b := by
    intro a ha b hb
    have hdir : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hdim0
    have hv := AffineSubspace.vsub_mem_direction hb ha
    rw [hdir, Submodule.mem_bot] at hv
    exact (vsub_eq_zero_iff_eq.mp hv).symm
  have hloc : S ∩ c.source ⊆ {x} := by
    rintro y ⟨hyS, hys⟩
    have hy : c.toPartialEquiv y ∈ (A : Set E) := (himg hys).mpr hyS
    have hxA : c.toPartialEquiv x ∈ (A : Set E) := (himg hxc).mpr hx
    exact c.toPartialEquiv.injOn hys hxc (hA _ hy _ hxA)
  have hsub : S ⊆ c.source := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hconn c.source {x}ᶜ c.open_source
        isOpen_compl_singleton (fun y _ => by
          by_cases hyx : y = x
          · exact Or.inl (hyx ▸ hxc)
          · exact Or.inr hyx)
        (by
          ext y
          constructor
          · rintro ⟨hyS, hys, hyx⟩
            exact hyx (hloc ⟨hyS, hys⟩)
          · intro h
            exact h.elim) with h | h
    · exact h
    · exact absurd (h hx) (by simp)
  exact Subset.antisymm (fun y hy => hloc ⟨hy, hsub hy⟩) (singleton_subset_iff.mpr hx)

/-- **BASE-0.** The base of a point soul: `Fin 0 → ℝ`, the constant map, its constant inverse. -/
theorem soulBase_point_finite (x : M) (n : WithTop ℕ∞) :
    ∃ b : (Fin 0 → ℝ) → M, ContMDiff 𝓘(ℝ, Fin 0 → ℝ) I n b ∧ Injective b ∧ range b = {x} ∧
      ∃ R : M → (Fin 0 → ℝ), (∀ s, R (b s) = s) ∧
        ∀ y ∈ ({x} : Set M), ContMDiffAt I 𝓘(ℝ, Fin 0 → ℝ) n R y :=
  ⟨fun _ => x, contMDiff_const, fun a b _ => Subsingleton.elim a b, range_const,
    fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ _ => contMDiffAt_const⟩

end Point

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

omit [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] in
/-- **The bundle data over a given base.** For a `d`-dimensional `C^r` slice `S` (`2 ≤ r`) and a
compact smooth base `B` of dimension `d` with a base map `b` satisfying the base contract, `Ê`
supplies a smooth Riemannian bundle `V` of rank `dim E - d` and the normal parametrization `ι`. -/
theorem exists_soul_bundle_data_of_base {r : ℕ∞} (hr : 2 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) (hdE : d ≤ Module.finrank ℝ E)
    {EB : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    (hEB : Module.finrank ℝ EB = d)
    {B : Type} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
    [T2Space B]
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F) (_ : FiniteDimensional ℝ F)
      (V : B → Type) (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V) (_ : VectorBundle ℝ F V)
      (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)) (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V)
      (ι : TotalSpace F V → TangentBundle I M),
      Module.finrank ℝ EB + Module.finrank ℝ F = Module.finrank ℝ E ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
      (∀ z, (ι z).proj = b z.proj) ∧
      (∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w)) ∧
      (∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2) ∧
      (∀ z, ι z ∈ normalSetFinite g S) ∧
      (∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) := by
  obtain ⟨V, i1, i2, i3, i4, i5, i6, i7, ι, hι, hιb, hιlin, hιnorm, hιν, hιonto, -⟩ :=
    exists_soulNormalBundle g hr hS b hb hbS hbinv
  refine ⟨EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d)), inferInstance, inferInstance,
    inferInstance, V, i1, i2, i3, i4, i5, i6, i7, ι, ?_, hι, hιb, hιlin, hιnorm, hιν, hιonto⟩
  rw [hEB, finrank_euclideanSpace_fin]
  omega

/-- **LFR49 (c).** For a complete connected noncompact finite-order (`C^{r+1}`, `3 ≤ r`)
three-manifold with `sec ≥ 0`: the soul `S`, LFR45's tube `(ε, ψ)` and strict outward directions,
a compact smooth base `B` with a smooth Riemannian vector bundle `V`, `dim B + rank V = 3`, the base
map `b` with its inverse contract and the normal parametrization `ι` — the hypotheses of the
restated LFR46 (`exists_finite_normalFlowMap_tube`), in every soul dimension. -/
theorem exists_finite_soul_tube_bundle_data_dim_three [NoncompactSpace M] [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3) {r : ℕ∞} (hr : 3 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∃ (S : Set M) (ε : ℝ) (ψ : M → TangentBundle I M)
      (EB : Type) (_ : NormedAddCommGroup EB) (_ : NormedSpace ℝ EB) (_ : FiniteDimensional ℝ EB)
      (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace EB B) (_ : IsManifold 𝓘(ℝ, EB) ∞ B)
      (_ : CompactSpace B)
      (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F) (_ : FiniteDimensional ℝ F)
      (V : B → Type) (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V) (_ : VectorBundle ℝ F V)
      (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)) (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V)
      (b : B → M) (ι : TotalSpace F V → TangentBundle I M),
      Module.finrank ℝ EB + Module.finrank ℝ F = 3 ∧
      IsCompact S ∧ S.Nonempty ∧
      (∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) ∧
      0 < ε ∧
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
      (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
        Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
      (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
        ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
        {x | 0 < infDist x S ∧ infDist x S < ε} ∧
      Injective b ∧ range b = S ∧
      (∃ R : M → B, (∀ s, R (b s) = s) ∧
        ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
      (∀ z, (ι z).proj = b z.proj) ∧
      (∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w)) ∧
      (∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2) ∧
      (∀ z, ι z ∈ normalSetFinite g S) ∧
      (∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) := by
  have instNZ_LFR49 : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  obtain ⟨S, hSne, hSc, hSconn, -, hslice, -, hd3, htg, hout, ε, hε, ψ, hψs, hψ, hψexp, -, hdS,
      -, -⟩ := exists_finite_soul_strict_outward_tube_data g hr hnorm hsec
  -- the common finishing step over a base of dimension `d`
  have finish : ∀ {d : ℕ} (_ : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) (_ : d ≤ 3)
      {EB : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
      (_ : Module.finrank ℝ EB = d)
      {B : Type} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
      [CompactSpace B] [T2Space B]
      (b : B → M) (_ : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (_ : Injective b)
      (_ : range b = S)
      (_ : ∃ R : M → B, (∀ s, R (b s) = s) ∧
        ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x),
      ∃ (S : Set M) (ε : ℝ) (ψ : M → TangentBundle I M)
        (EB : Type) (_ : NormedAddCommGroup EB) (_ : NormedSpace ℝ EB)
        (_ : FiniteDimensional ℝ EB)
        (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace EB B)
        (_ : IsManifold 𝓘(ℝ, EB) ∞ B) (_ : CompactSpace B)
        (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
        (_ : FiniteDimensional ℝ F)
        (V : B → Type) (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
        (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V) (_ : VectorBundle ℝ F V)
        (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB))
        (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V)
        (b : B → M) (ι : TotalSpace F V → TangentBundle I M),
        Module.finrank ℝ EB + Module.finrank ℝ F = 3 ∧
        IsCompact S ∧ S.Nonempty ∧
        (∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
          ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) ∧
        0 < ε ∧
        ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
        (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
          Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
        (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
          ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
          {x | 0 < infDist x S ∧ infDist x S < ε} ∧
        Injective b ∧ range b = S ∧
        (∃ R : M → B, (∀ s, R (b s) = s) ∧
          ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) ∧
        ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
        (∀ z, (ι z).proj = b z.proj) ∧
        (∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w)) ∧
        (∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2) ∧
        (∀ z, ι z ∈ normalSetFinite g S) ∧
        (∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) := by
    intro d hS hd3' EB _ _ _ hEB B _ _ _ _ _ b hb hbinj hbS hbinv
    obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, ι, hdimEF, hι, hιb, hιlin, hιnorm, hιν,
        hιonto⟩ := exists_soul_bundle_data_of_base hr2 g hS (by rw [hdim]; exact hd3') hEB b hb
          hbS hbinv
    exact ⟨S, ε, ψ, EB, inferInstance, inferInstance, inferInstance, B, inferInstance,
      inferInstance, inferInstance, inferInstance, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7,
      b, ι, hdimEF.trans hdim, hSc, hSne, hout, hε, hψs, hψ, hψexp, hdS, hbinj, hbS, hbinv, hι,
      hιb, hιlin, hιnorm, hιν, hιonto⟩
  -- the case split on the soul dimension
  set d := maxSliceDimOfOrder I (r : ℕ∞ω) S with hddef
  have hd : d < 3 := hdim ▸ hd3
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with h0 | h1 | h2
  · -- point soul
    rw [h0] at hslice
    obtain ⟨x, hx⟩ := hSne
    have hSx : S = {x} := eq_singleton_of_isEmbeddedSliceOfOrder_zero hslice
      hSconn.isPreconnected hx
    obtain ⟨b, hb, hbinj, hbS, R, hRb, hR⟩ := soulBase_point_finite (I := I) x
      ((r - 1 : ℕ∞) : ℕ∞ω)
    exact finish hslice (by norm_num) (EB := Fin 0 → ℝ) (Module.finrank_fin_fun ℝ) b hb hbinj
      (hbS.trans hSx.symm) ⟨R, hRb, hSx ▸ hR⟩
  · -- closed geodesic soul
    rw [h1] at hslice
    obtain ⟨p, ℓ, hℓ, hunit, hper, hinj, hSrange⟩ :=
      exists_closedGeodesic_of_slice_dim_one g hr2 hnorm hSc hSconn hslice htg
    obtain ⟨b, -, hb, hbinj, hbS, R, hRb, hR⟩ :=
      soulBase_closedGeodesic g hr2 hnorm p hℓ hunit hper hinj
    exact finish hslice (by norm_num) (EB := ℝ) (Module.finrank_self ℝ) b hb hbinj
      (hbS.trans hSrange.symm) ⟨R, hRb, fun x hx => hR x (hSrange ▸ hx)⟩
  · -- surface soul
    rw [h2] at hslice
    obtain ⟨Shat, hShat, hrest⟩ := soulBase_surface_carrier g hr2 hnorm hdim hSc ⟨hSne.some,
      hSne.some_mem⟩ hslice
    let _ := DifferentialGeometry.Geometry.Topology.embeddedSliceChartedSpace hShat
    obtain ⟨hc, ht, hm, b, hb, hbinj, hbS, R, hRb, hR⟩ := hrest
    have instC_LFR49 : CompactSpace Shat := hc
    have instT_LFR49 : T2Space Shat := ht
    have instM_LFR49 : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ Shat := hm
    exact finish hslice (by norm_num) (EB := Fin 2 → ℝ) (Module.finrank_fin_fun ℝ) b hb hbinj hbS
      ⟨R, hRb, hR⟩

end DifferentialGeometry.Geometry.Collapse
