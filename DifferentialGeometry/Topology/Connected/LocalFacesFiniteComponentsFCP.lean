import DifferentialGeometry.Topology.Connected.CompactFiniteComponentsFCP
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# The local face model of `C₁` gives a finite list of components (FDC04 "all the lists are
finite", FC39 `JunctionRimFacts74.local_faces`)

Lane S-FINCOMP, group G2 (suffix `_FCP`). FC39's `JunctionRimFacts74.local_faces` states, at every
frontier point `c` of the compact circle base `C₁` (a surface), an open `U ∋ c`, one or two smooth
face functions `φ f` with surjective joint derivative and `C₁ ∩ U = {c' ∈ U | ∀ f ∈ L, φ f c' ≤ 0}`.
That is the local model of a manifold with corners; this module proves that it forces
local connectedness, hence (compactness) the finite list of components of `C₁`.

* `exists_preconnected_of_convex_chart_FCP`: pointwise form of the convex-chart lemma (charts to a
  normed space `E` that depends on the point).
* `exists_preconnected_nhds_of_faces_FCP`: the submersion chart `(φ, ker)` of the implicit function
  theorem straightens the faces: `C₁ ∩ U'` contains a preconnected neighbourhood of `c` within
  `C₁`, inside every neighbourhood `U'` of `c`.
* `finite_components_of_local_faces_FCP`: the finite list of components of a compact set `S` in a
  surface all of whose frontier points carry the `local_faces` data (interior points are
  automatic).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

/-- **Pointwise convex-chart lemma** (the chart target `E` may depend on the point): if `e` is an
open partial homeomorphism to a real normed space with `x ∈ e.source` and
`e '' (s ∩ e.source) = K ∩ e.target` for a convex `K`, then inside every neighbourhood `U` of `x`
there is a preconnected neighbourhood of `x` within `s`. -/
theorem exists_preconnected_of_convex_chart_FCP {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set X} {x : X} (e : OpenPartialHomeomorph X E) (hxs : x ∈ s)
    (hxe : x ∈ e.source) {K : Set E} (hK : Convex ℝ K)
    (hKe : e '' (s ∩ e.source) = K ∩ e.target) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, V ∈ 𝓝[s] x ∧ IsPreconnected V ∧ V ⊆ s ∩ U := by
  have hex : e x ∈ K ∩ e.target := hKe ▸ ⟨x, ⟨hxs, hxe⟩, rfl⟩
  have hU' : U ∩ e.source ∈ 𝓝 x := inter_mem hU (e.open_source.mem_nhds hxe)
  have hsymm : e.symm ⁻¹' (U ∩ e.source) ∈ 𝓝 (e x) := by
    have h1 : U ∩ e.source ∈ 𝓝 (e.symm (e x)) := by
      rw [e.left_inv hxe]
      exact hU'
    exact e.continuousAt_symm (e.map_source hxe) h1
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hsymm (e.open_target.mem_nhds hex.2))
  have hbt : Metric.ball (e x) r ⊆ e.target := fun z hz => (hball hz).2
  have hbU : ∀ z ∈ Metric.ball (e x) r, e.symm z ∈ U ∩ e.source := fun z hz => (hball hz).1
  have hO : IsOpen (e.symm '' Metric.ball (e x) r) :=
    OpenPartialHomeomorph.isOpen_image_of_subset_source e.symm Metric.isOpen_ball
      (e.symm_source ▸ hbt)
  have hxO : x ∈ e.symm '' Metric.ball (e x) r :=
    ⟨e x, Metric.mem_ball_self hr, e.left_inv hxe⟩
  have hVs : ∀ z ∈ K ∩ Metric.ball (e x) r, e.symm z ∈ s := by
    intro z hz
    have hzK : z ∈ K ∩ e.target := ⟨hz.1, hbt hz.2⟩
    rw [← hKe] at hzK
    obtain ⟨w, hw, hwz⟩ := hzK
    rw [← hwz, e.left_inv hw.2]
    exact hw.1
  refine ⟨e.symm '' (K ∩ Metric.ball (e x) r), ?_, ?_, ?_⟩
  · refine mem_nhdsWithin.mpr ⟨_, hO, hxO, ?_⟩
    rintro z ⟨⟨b, hb, rfl⟩, hzs⟩
    have hzsrc : e.symm b ∈ e.source := (hbU b hb).2
    have hbK : b ∈ K := by
      have : e (e.symm b) ∈ K ∩ e.target := hKe ▸ ⟨e.symm b, ⟨hzs, hzsrc⟩, rfl⟩
      rw [e.right_inv (hbt hb)] at this
      exact this.1
    exact ⟨b, ⟨hbK, hb⟩, rfl⟩
  · exact (hK.inter (convex_ball (e x) r)).isPreconnected.image _
      (e.continuousOn_symm.mono fun z hz => hbt hz.2)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨hVs z hz, (hbU z hz.2).1⟩

section Faces

variable {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
  [IsManifold (𝓡 2) ∞ B]

/-- **The face functions in the chart at `c`**: `G x = (φ f (ψ.symm x))_{f ∈ L}` is smooth at
`ψ c` (`ψ = extChartAt (𝓡 2) c`) and its Fréchet derivative there is onto as soon as the joint
manifold derivative of the `φ f` at `c` is. -/
theorem exists_chart_face_map_FCP {c : B} {U : Set B} (hU : IsOpen U) (hcU : c ∈ U)
    {ι : Type*} (L : Finset ι) (φ : ι → B → ℝ)
    (hφ : ∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U)
    (hsurj : Surjective fun w : TangentSpace (𝓡 2) c =>
      fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → (L → ℝ),
      ContDiffAt ℝ ∞ G (extChartAt (𝓡 2) c c) ∧
      (∀ x, ∀ f : L, G x f = φ f ((extChartAt (𝓡 2) c).symm x)) ∧
      Surjective (fderiv ℝ G (extChartAt (𝓡 2) c c)) := by
  classical
  let ψ := extChartAt (𝓡 2) c
  have hx0 : ψ.symm (ψ c) = c := ψ.left_inv (mem_extChartAt_source c)
  have hcm : ∀ f : L, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞
      (fun x => φ f (ψ.symm x)) (ψ c) := by
    intro f
    have h1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) (ψ.symm (ψ c)) := by
      rw [hx0]
      exact (hφ f f.2).contMDiffAt (hU.mem_nhds hcU)
    exact h1.comp (ψ c)
      ((contMDiffOn_extChartAt_symm c).contMDiffAt (extChartAt_target_mem_nhds c))
  refine ⟨fun x f => φ f (ψ.symm x), contDiffAt_pi.2 fun f => contMDiffAt_iff_contDiffAt.mp (hcm f),
    fun _ _ => rfl, ?_⟩
  have hdf : ∀ f : L, fderiv ℝ (fun x => φ f (ψ.symm x)) (ψ c) =
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c := by
    intro f
    have hmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c :=
      ((hφ f f.2).contMDiffAt (hU.mem_nhds hcU)).mdifferentiableAt (by simp)
    rw [hmd.mfderiv_abuse]
    simp [writtenInExtChartAt, ψ, fderivWithin_univ]
    rfl
  have hdiff : ∀ f : L, DifferentiableAt ℝ (fun x => φ f (ψ.symm x)) (ψ c) := fun f =>
    ((contMDiffAt_iff_contDiffAt.mp (hcm f)).differentiableAt (by simp))
  intro v
  obtain ⟨w, hw⟩ := hsurj v
  refine ⟨w, ?_⟩
  rw [fderiv_pi hdiff]
  ext f
  change fderiv ℝ (fun x => φ f (ψ.symm x)) (ψ c) w = v f
  rw [hdf f]
  exact congrFun hw f

/-- **The submersion chart straightens the faces**: with `S ∩ U = {c' ∈ U | ∀ f ∈ L, φ f c' ≤ 0}`
for smooth `φ f` with surjective joint derivative at `c ∈ S`, every neighbourhood `U'` of `c`
contains a preconnected neighbourhood of `c` within `S`. (Chart: the implicit-function chart
`(φ, ker)` of the face map composed with the chart at `c`, restricted to `U`; target a convex
set `{y | ∀ f, y.1 f ≤ 0}`.) -/
theorem exists_preconnected_nhds_of_faces_FCP {S : Set B} {c : B} {U : Set B} (hU : IsOpen U)
    (hcU : c ∈ U) (hcS : c ∈ S) {ι : Type*} (L : Finset ι) (φ : ι → B → ℝ)
    (hφ : ∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U)
    (hsurj : Surjective fun w : TangentSpace (𝓡 2) c =>
      fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w)
    (hS : S ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}) {U' : Set B} (hU' : U' ∈ 𝓝 c) :
    ∃ V : Set B, V ∈ 𝓝[S] c ∧ IsPreconnected V ∧ V ⊆ S ∩ U' := by
  classical
  obtain ⟨G, hGd, hGeq, hGs⟩ := exists_chart_face_map_FCP hU hcU L φ hφ hsurj
  let ψ := extChartAt (𝓡 2) c
  have hstrict : HasStrictFDerivAt G (fderiv ℝ G (ψ c)) (ψ c) :=
    ContDiffAt.hasStrictFDerivAt hGd (by simp)
  have hrange : (fderiv ℝ G (ψ c)).range = ⊤ := LinearMap.range_eq_top.mpr hGs
  have hker : (fderiv ℝ G (ψ c)).ker.ClosedComplemented :=
    ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _
  let Ψ := hstrict.implicitToOpenPartialHomeomorphOfComplemented G _ hrange hker
  have hΨs : ψ c ∈ Ψ.source :=
    hstrict.mem_implicitToOpenPartialHomeomorphOfComplemented_source hrange hker
  let χ := chartAt (EuclideanSpace ℝ (Fin 2)) c
  have hψχ : ∀ z, ψ z = χ z := fun z => by simp [ψ]; rfl
  have hψχ' : ∀ x, ψ.symm x = χ.symm x := fun x => by simp [ψ]; rfl
  let e : OpenPartialHomeomorph B ((L → ℝ) × (fderiv ℝ G (ψ c)).ker) := (χ.trans Ψ).restr U
  have he_src : e.source = (χ.source ∩ χ ⁻¹' Ψ.source) ∩ U :=
    OpenPartialHomeomorph.restr_source' _ _ hU
  have hce : c ∈ e.source := by
    rw [he_src]
    refine ⟨⟨mem_chart_source _ c, ?_⟩, hcU⟩
    rw [mem_preimage, ← hψχ]
    exact hΨs
  have hez : ∀ z ∈ e.source, ∀ f : L, (e z).1 f = φ f z := by
    intro z hz f
    rw [he_src] at hz
    change (Ψ (χ z)).1 f = φ f z
    have h1 : (Ψ (χ z)).1 = G (χ z) :=
      hstrict.implicitToOpenPartialHomeomorphOfComplemented_fst hrange hker (χ z)
    rw [h1, hGeq, hψχ', χ.left_inv hz.1.1]
  refine exists_preconnected_of_convex_chart_FCP e hcS hce
    (K := {y : (L → ℝ) × (fderiv ℝ G (ψ c)).ker | ∀ f : L, y.1 f ≤ 0}) ?_ ?_ hU'
  · intro y hy y' hy' a b ha hb hab f
    have h1 := hy f
    have h2 := hy' f
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · ext y
    constructor
    · rintro ⟨z, ⟨hzS, hze⟩, rfl⟩
      refine ⟨fun f => ?_, e.map_source hze⟩
      have hzU : z ∈ U := (he_src ▸ hze).2
      have hz := (Set.ext_iff.mp hS z).mp ⟨hzS, hzU⟩
      rw [hez z hze f]
      exact hz.2 f f.2
    · rintro ⟨hyK, hyt⟩
      have hze : e.symm y ∈ e.source := e.map_target hyt
      refine ⟨e.symm y, ⟨?_, hze⟩, e.right_inv hyt⟩
      have hzU : e.symm y ∈ U := (he_src ▸ hze).2
      refine ((Set.ext_iff.mp hS (e.symm y)).mpr ⟨hzU, fun f hf => ?_⟩).1
      have := hez (e.symm y) hze ⟨f, hf⟩
      rw [e.right_inv hyt] at this
      rw [← this]
      exact hyK ⟨f, hf⟩

/-- **The finite list of components of a compact set with the local face model** (the shape of
FC39's `JunctionRimFacts74.local_faces` at the frontier points of `C₁`; at the other points of `S`
the surface is locally connected). -/
theorem finite_components_of_local_faces_FCP {ι : Type*} {S : Set B} (hS : IsCompact S)
    (h : ∀ c ∈ frontier S, ∃ U : TopologicalSpace.Opens B, c ∈ U ∧
      ∃ (L : Finset ι) (φ : ι → B → ℝ),
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        S ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}) :
    ∃ (m : ℕ) (Bc : Fin m → Set B), (∀ i, IsCompact (Bc i)) ∧ (∀ i, IsConnected (Bc i)) ∧
      (∀ i, Bc i ⊆ S) ∧ (∀ i, IsClopen (Subtype.val ⁻¹' Bc i : Set S)) ∧
      (∀ i, ∀ x ∈ Bc i, connectedComponentIn S x = Bc i) ∧
      Pairwise (Disjoint on Bc) ∧ S = ⋃ i, Bc i := by
  have hlc : LocallyConnectedSpace B :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) B
  have : LocallyConnectedSpace S := by
    refine locallyConnectedSpace_of_forall_exists_preconnected_FCP fun x hx U hU => ?_
    by_cases hfr : x ∈ frontier S
    · obtain ⟨U0, hxU0, L, φ, hφ, hsurj, hS0⟩ := h x hfr
      exact exists_preconnected_nhds_of_faces_FCP U0.isOpen hxU0 hx L φ hφ hsurj hS0 hU
    · have hxi : x ∈ interior S := by
        by_contra hxi
        exact hfr ⟨subset_closure hx, hxi⟩
      obtain ⟨V, hV, hVc, hVU⟩ := locallyConnectedSpace_iff_connected_subsets.mp hlc x
        (U ∩ interior S) (inter_mem hU (isOpen_interior.mem_nhds hxi))
      exact ⟨V, nhdsWithin_le_nhds hV, hVc, fun z hz => ⟨interior_subset (hVU hz).2, (hVU hz).1⟩⟩
  exact exists_finite_components_of_isCompact_locallyConnected_FCP hS

end Faces

end DifferentialGeometry.Topology
