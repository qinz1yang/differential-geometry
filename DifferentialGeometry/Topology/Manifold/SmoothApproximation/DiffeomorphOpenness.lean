import DifferentialGeometry.Topology.Manifold.SmoothApproximation.ChartConvergence
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Openness of diffeomorphisms of compact manifolds (W2)

`eventually_exists_diffeomorph_of_chart_tendsto`: let `h : A ≃ₘ^n⟮I, J⟯ B` be a `C^n`
diffeomorphism (`1 ≤ n`) between manifolds with boundaryless models, `A` compact Hausdorff. If
`C^r` maps `hs j : A → B` (`1 ≤ r`) converge to `h` chart-wise in `C^m` (`1 ≤ m`) in the sense of
W1 (`exists_smooth_seq_chart_tendsto`), then eventually every `hs j` is a `C^r`
diffeomorphism. The hypothesis is literally W1's conclusion.

Proof: the local step (`exists_isOpen_eventually_injOn_isInvertible_mfderiv`) gives finitely
many open sets `N a` covering `A` on which eventually every `hs j` is injective with invertible
`mfderiv`; on the compact set `Z = A × A ∖ ⋃ N a × N a` the values of `h` are separated, hence
(LU + `T2`) eventually those of `hs j`; so eventually `hs j` is an injective local
diffeomorphism. Its range is open and compact, hence clopen; every connected component of `B`
(finitely many, all open) meets the range by LU, so the range is `B`. No connectedness, no
dimension count, no degree.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

private theorem eventually_forall_of_isCompact {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {P : ℕ → X → Prop}
    (hP : ∀ x ∈ S, ∃ N ∈ 𝓝 x, ∀ᶠ j in atTop, ∀ z ∈ N, P j z) :
    ∀ᶠ j in atTop, ∀ z ∈ S, P j z := by
  refine hS.induction_on (p := fun T => ∀ᶠ j in atTop, ∀ z ∈ T, P j z) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun _ _ hz => hz.elim
  · intro s t hst ht
    exact ht.mono fun j hj z hz => hj z (hst hz)
  · intro s t hs ht
    filter_upwards [hs, ht] with j hj1 hj2 z hz
    exact hz.elim (hj1 z) (hj2 z)
  · intro x hx
    obtain ⟨N, hN, hev⟩ := hP x hx
    exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, hev⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

omit [FiniteDimensional ℝ E'] in
/-- **W2 (openness of diffeomorphisms).** If `C^r` maps `hs j` (`1 ≤ r`) converge chart-wise in
`C^m` (`1 ≤ m`) to a `C^n` diffeomorphism `h` (`1 ≤ n`) of compact boundaryless manifolds, then
eventually every `hs j` is a `C^r` diffeomorphism. The convergence hypothesis is exactly the
conclusion of W1 (`exists_smooth_seq_chart_tendsto`). -/
theorem eventually_exists_diffeomorph_of_chart_tendsto
    {n : ℕ∞ω} (hn : 1 ≤ n) (h : A ≃ₘ^n⟮I, J⟯ B) {r : ℕ∞} (hr : 1 ≤ r) {m : ℕ} (hm : 1 ≤ m)
    {hs : ℕ → A → B} (hsm : ∀ j, ContMDiff I J r (hs j))
    (hconv : ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K m (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y)))) :
    ∀ᶠ j in atTop, ∃ Φ : A ≃ₘ^r⟮I, J⟯ B, ⇑Φ = hs j := by
  have hh1 : ContMDiff I J 1 h := h.contMDiff.of_le hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have hsm1 : ∀ j, ContMDiff I J 1 (hs j) := fun j => (hsm j).of_le (by exact_mod_cast hr)
  have hinv : ∀ a, (mfderiv I J h a).IsInvertible := fun a => h.isInvertible_mfderiv hn0
  have : T2Space B := h.toHomeomorph.symm.isEmbedding.t2Space
  have : CompactSpace B := h.toHomeomorph.compactSpace
  have : LocallyConnectedSpace H' := J.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace B := ChartedSpace.locallyConnectedSpace H' B
  -- local pieces
  choose N hNo haN hNev using fun a =>
    exists_isOpen_eventually_injOn_isInvertible_mfderiv hm hh1 hsm1 hconv (hinv a)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.2 ⟨x, haN x⟩)
  have hpieces : ∀ᶠ j in atTop, ∀ a ∈ t,
      InjOn (hs j) (N a) ∧ ∀ x ∈ N a, (mfderiv I J (hs j) x).IsInvertible :=
    (eventually_all_finset t).2 fun a _ => hNev a
  -- separation off the pieces
  set Z : Set (A × A) := univ \ ⋃ a ∈ t, N a ×ˢ N a with hZdef
  have hZ : IsCompact Z :=
    isCompact_univ.diff (isOpen_biUnion fun a _ => (hNo a).prod (hNo a))
  have hsep : ∀ᶠ j in atTop, ∀ z ∈ Z, hs j z.1 ≠ hs j z.2 := by
    apply eventually_forall_of_isCompact hZ
    rintro ⟨x, x'⟩ hz
    have hne : x ≠ x' := by
      rintro rfl
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact hz.2 (mem_iUnion₂.2 ⟨a, ha, ⟨hxa, hxa⟩⟩)
    obtain ⟨V₁, V₂, hV₁, hV₂, hx₁, hx₂, hdisj⟩ := t2_separation (h.injective.ne hne)
    obtain ⟨N₁, hN₁, hev₁⟩ := eventually_mapsTo_of_chart_tendsto h.continuous hconv x hV₁ hx₁
    obtain ⟨N₂, hN₂, hev₂⟩ := eventually_mapsTo_of_chart_tendsto h.continuous hconv x' hV₂ hx₂
    refine ⟨N₁ ×ˢ N₂, prod_mem_nhds hN₁ hN₂, ?_⟩
    filter_upwards [hev₁, hev₂] with j hj₁ hj₂ z hz'
    exact hdisj.ne_of_mem (hj₁ hz'.1) (hj₂ hz'.2)
  -- every connected component of `B` is eventually met
  obtain ⟨t', ht'⟩ := isCompact_univ.elim_finite_subcover (fun b : B => connectedComponent b)
    (fun _ => isOpen_connectedComponent) (fun b _ => mem_iUnion.2 ⟨b, mem_connectedComponent⟩)
  have hcomp : ∀ᶠ j in atTop, ∀ b ∈ t', hs j (h.symm b) ∈ connectedComponent b := by
    refine (eventually_all_finset t').2 fun b _ => ?_
    have hb : h (h.symm b) ∈ connectedComponent b := by
      rw [h.apply_symm_apply]
      exact mem_connectedComponent
    obtain ⟨N', hN', hev⟩ :=
      eventually_mapsTo_of_chart_tendsto h.continuous hconv (h.symm b) isOpen_connectedComponent hb
    exact hev.mono fun j hj => hj (mem_of_mem_nhds hN')
  filter_upwards [hpieces, hsep, hcomp] with j hpj hsj hcj
  have hloc : IsLocalDiffeomorph I J r (hs j) := by
    rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ]
    refine ((hsm j).contMDiffOn (s := univ)).isLocalDiffeomorphOn_of_isInvertible_mfderiv
      isOpen_univ (by exact_mod_cast hr) fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact (hpj a ha).2 x hxa
  have hinj : Injective (hs j) := by
    intro x x' heq
    by_contra hne
    by_cases hz : (x, x') ∈ Z
    · exact hsj _ hz heq
    · have hmem : (x, x') ∈ ⋃ a ∈ t, N a ×ˢ N a := by
        by_contra hc
        exact hz ⟨mem_univ _, hc⟩
      obtain ⟨a, ha, hxa, hxa'⟩ := mem_iUnion₂.1 hmem
      exact hne ((hpj a ha).1 hxa hxa' heq)
  have hsurj : Surjective (hs j) := by
    have hclopen : IsClopen (range (hs j)) :=
      ⟨(isCompact_range (hsm j).continuous).isClosed, hloc.isOpenMap.isOpen_range⟩
    intro y
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 (ht' (mem_univ y))
    exact isPreconnected_connectedComponent.subset_isClopen hclopen
      ⟨_, hcj b hb, mem_range_self _⟩ hyb
  exact ⟨hloc.diffeomorphOfBijective ⟨hinj, hsurj⟩, rfl⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
