import DifferentialGeometry.Topology.Manifold.TransversePerturbation
import DifferentialGeometry.Topology.Manifold.Coincidences
import DifferentialGeometry.Topology.Compactness.Perturbation
import DifferentialGeometry.Topology.LoopSpace.FamilyDerivatives
import DifferentialGeometry.Topology.Manifold.AddCircle

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold
namespace DifferentialGeometry.Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_local_loop_family_perturbation_transverse
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    {γ : ℝ × AddCircle (1 : ℝ) → M} {S : Set (ℝ × AddCircle (1 : ℝ))}
    (hγ : ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ)) I ∞ γ S) (hS : IsOpen S)
    (t₀ : ℝ) (z₀ w₀ : AddCircle (1 : ℝ)) (hzw : z₀ ≠ w₀)
    (hzS : (t₀, z₀) ∈ S) (hwS : (t₀, w₀) ∈ S)
    (hzchart : γ (t₀, z₀) ∈ e.source) (hwchart : γ (t₀, w₀) ∈ e.source) :
    ∃ (ρ : ℝ × AddCircle (1 : ℝ) → ℝ)
      (U : Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) (δ : ℝ),
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ tsupport ρ ⊆ S ∩ γ ⁻¹' e.source ∧
      IsOpen U ∧ (t₀, z₀, w₀) ∈ U ∧
      (∀ q ∈ U, ρ (q.1, q.2.1) = 1 ∧ ρ (q.1, q.2.2) = 0 ∧
        (q.1, q.2.1) ∈ S ∩ γ ⁻¹' e.source ∧ (q.1, q.2.2) ∈ S ∩ γ ⁻¹' e.source) ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, F).prod (𝓘(ℝ).prod 𝓘(ℝ))) I ∞
        (fun q : F × (ℝ × AddCircle (1 : ℝ)) =>
          e.patchMap γ (fun x => e (γ x) - ρ x • q.1) q.2)
        (ball 0 δ ×ˢ S) ∧
      ∀ ε > 0, ∃ (v : F) (β : ℝ × AddCircle (1 : ℝ) → M), ‖v‖ < ε ∧
        β = e.patchMap γ (fun p => e (γ p) - ρ p • v) ∧
        ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod I) ∞ (fun p => (p.1, β p)) S ∧
        (∀ p, p ∉ tsupport ρ → β p = γ p) ∧
        (∀ p ∈ S, γ p ∈ e.source →
          β p ∈ e.source ∧ e (β p) = e (γ p) - ρ p • v ∧
            ‖e (β p) - e (γ p)‖ < ε) ∧
        ∀ q ∈ U, β (q.1, q.2.1) = β (q.1, q.2.2) →
          Function.Surjective
            ((show (ℝ × ℝ × ℝ) →L[ℝ] E from
              mfderiv (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) I
                (fun z : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => β (z.1, z.2.1)) q) -
             (show (ℝ × ℝ × ℝ) →L[ℝ] E from
              mfderiv (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) I
                (fun z : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => β (z.1, z.2.2)) q)) := by
  let l : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → ℝ × AddCircle (1 : ℝ) :=
    fun q => (q.1, q.2.1)
  let r : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → ℝ × AddCircle (1 : ℝ) :=
    fun q => (q.1, q.2.2)
  have hl : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ l :=
    contMDiff_fst.prodMk contMDiff_snd.fst
  have hr : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ r :=
    contMDiff_fst.prodMk contMDiff_snd.snd
  obtain ⟨ρ, U, δ, hρ, hcompact, hbound, hsupp, hU, hqU, hpairs, hδ, hjoint, hperturb⟩ :=
    exists_local_chart_perturbation_transverse e hγ hS hl hr (t₀, z₀, w₀) hzS hwS
      (fun h => hzw (congrArg Prod.snd h)) hzchart hwchart
  refine ⟨ρ, U, δ, hρ, hcompact, hbound, hsupp, hU, hqU, hpairs, hδ, hjoint, ?_⟩
  intro ε hε
  obtain ⟨v, β, hv, hβdef, hβ, hfixed, hcoords, htrans⟩ := hperturb ε hε
  exact ⟨v, β, hv, hβdef, contMDiffOn_fst.prodMk hβ, hfixed, hcoords, htrans⟩

end DifferentialGeometry.Manifold

end

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

theorem exists_finite_loop_family_coincidence_cover
    {γ : ℝ × AddCircle (1 : ℝ) → M}
    (hγ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞ γ)
    {a b δ : ℝ} (hδ : 0 < δ) :
    let K : Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
      {q | q.1 ∈ Icc a b ∧ δ ≤ dist q.2.1 q.2.2}
    let Z : Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
      {q | q ∈ K ∧ γ (q.1, q.2.1) = γ (q.1, q.2.2)}
    ∃ (t : Finset Z)
      (e : Z → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
      (c : Z → PartialDiffeomorph (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ)))
        𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) (ℝ × ℝ × ℝ) ∞)
      (ρ : Z → (ℝ × AddCircle (1 : ℝ)) → ℝ)
      (U A : Z → Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))
      (B : Z → Set (ℝ × AddCircle (1 : ℝ))),
      IsCompact K ∧
      (∀ i : Z,
        ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (ρ i) ∧ HasCompactSupport (ρ i) ∧
        (∀ x, ρ i x ∈ Icc (0 : ℝ) 1) ∧
        IsOpen (U i) ∧ (i : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ∈ U i ∧
        IsCompact (closure (U i)) ∧ IsCompact (A i) ∧ A i ⊆ U i ∧
        closure (U i) ⊆ (c i).source ∧ IsCompact (B i) ∧ tsupport (ρ i) ⊆ B i ∧
        MapsTo (fun q => (q.1, q.2.1)) (closure (U i)) (B i) ∧
        MapsTo (fun q => (q.1, q.2.2)) (closure (U i)) (B i) ∧
        B i ⊆ γ ⁻¹' (e i).source ∧
        ∀ q ∈ closure (U i), ρ i (q.1, q.2.1) = 1 ∧ ρ i (q.1, q.2.2) = 0) ∧
      Z ⊆ ⋃ i ∈ t, interior (A i) := by
  let K : Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
    {q | q.1 ∈ Icc a b ∧ δ ≤ dist q.2.1 q.2.2}
  have hK : IsCompact K := by
    have heq : K = (Icc a b ×ˢ univ) ∩
        {q : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | δ ≤ dist q.2.1 q.2.2} := by
      ext q
      simp only [K, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true]
    rw [heq]
    exact (isCompact_Icc.prod isCompact_univ).inter_right
      (isClosed_le continuous_const (continuous_snd.fst.dist continuous_snd.snd))
  let l : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → ℝ × AddCircle (1 : ℝ) :=
    fun q => (q.1, q.2.1)
  let r : ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → ℝ × AddCircle (1 : ℝ) :=
    fun q => (q.1, q.2.2)
  have hl : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ l :=
    contMDiff_fst.prodMk contMDiff_snd.fst
  have hr : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ r :=
    contMDiff_fst.prodMk contMDiff_snd.snd
  have hneq : ∀ q ∈ K, l q ≠ r q := by
    intro q hq heq
    have heq' : q.2.1 = q.2.2 := congrArg Prod.snd heq
    have hbound := hq.2
    rw [heq', dist_self] at hbound
    exact hδ.not_ge hbound
  obtain ⟨t, e, c, ρ, U, A, B, hlocal, hcover⟩ :=
    exists_finite_compact_coincidence_cover hγ hl hr hK hneq
  exact ⟨t, e, c, ρ, U, A, B, hK, hlocal, hcover⟩

end DifferentialGeometry.Manifold

end

noncomputable section

open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Manifold

private theorem exists_finite_approximation_of_local_perturbations
    {A ι : Type*} (C : A → A → ℝ → Prop) (P : A → Prop) (T : ι → A → Prop)
    (c : A) (hc : P c) {R : ℝ} (hR : 0 < R)
    (hrefl : ∀ ε, 0 < ε → C c c ε)
    (htriangle : ∀ {f g h ε δ}, C g f ε → C f h δ → C g h (ε + δ))
    (hmono : ∀ {f g ε δ}, ε ≤ δ → C f g ε → C f g δ)
    (hstep : ∀ f, P f → C f c R → ∀ t : Finset ι, (∀ i ∈ t, T i f) →
      ∀ i, ∀ δ, 0 < δ → ∃ g, P g ∧ C g f δ ∧ T i g ∧ ∀ j ∈ t, T j g)
    (s : Finset ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ g, P g ∧ C g c ε ∧ ∀ i ∈ s, T i g := by
  classical
  have hbounded : ∀ s : Finset ι, ∀ ε, 0 < ε → ε ≤ R →
      ∃ g, P g ∧ C g c ε ∧ ∀ i ∈ s, T i g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ε hε _
      exact ⟨c, hc, hrefl ε hε, by simp⟩
    | @insert i s _ ih =>
      intro ε hε hεR
      have hhalf : 0 < ε / 2 := by positivity
      have hhalfR : ε / 2 ≤ R := by linarith
      obtain ⟨f, hf, hfC, hfT⟩ := ih (ε / 2) hhalf hhalfR
      obtain ⟨g, hg, hgC, hgi, hgT⟩ := hstep f hf (hmono hhalfR hfC) s hfT i
        (ε / 2) hhalf
      exact ⟨g, hg, by simpa using htriangle hgC hfC, by
        intro j hj
        simp only [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact hgi
        · exact hgT j hj⟩
  obtain ⟨g, hg, hgC, hgT⟩ := hbounded s (min ε R) (lt_min hε hR) (min_le_right _ _)
  exact ⟨g, hg, hmono (min_le_left _ _) hgC, hgT⟩

private theorem exists_approximation_of_local_perturbations
    {A ι : Type*} [Finite ι] (C : A → A → ℝ → Prop) (P : A → Prop) (T : ι → A → Prop)
    (c : A) (hc : P c) {R : ℝ} (hR : 0 < R)
    (hrefl : ∀ ε, 0 < ε → C c c ε)
    (htriangle : ∀ {f g h ε δ}, C g f ε → C f h δ → C g h (ε + δ))
    (hmono : ∀ {f g ε δ}, ε ≤ δ → C f g ε → C f g δ)
    (hstep : ∀ f, P f → C f c R → ∀ t : Finset ι, (∀ i ∈ t, T i f) →
      ∀ i, ∀ δ, 0 < δ → ∃ g, P g ∧ C g f δ ∧ T i g ∧ ∀ j ∈ t, T j g)
    {ε : ℝ} (hε : 0 < ε) : ∃ g, P g ∧ C g c ε ∧ ∀ i, T i g := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨g, hg, hgC, hgT⟩ := exists_finite_approximation_of_local_perturbations
    C P T c hc hR hrefl htriangle hmono hstep Finset.univ hε
  exact ⟨g, hg, hgC, fun i => hgT i (Finset.mem_univ i)⟩


local notation "Circle" => AddCircle (1 : ℝ)
local notation "Loop" => ℝ × Circle
local notation "Pairs" => ℝ × Circle × Circle
local notation "IL" => ModelWithCorners.prod 𝓘(ℝ) 𝓘(ℝ)
local notation "IQ" => ModelWithCorners.prod 𝓘(ℝ) (ModelWithCorners.prod 𝓘(ℝ) 𝓘(ℝ))

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [T2Space M] in
private theorem eventually_uniform_embedding_dist
    (j : M → F) (hj : Continuous j)
    {f : E → Loop → M} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn (Function.uncurry f) (ball 0 δ ×ˢ univ))
    {B : Set Loop} (hB : IsCompact B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 (0 : E), ∀ p ∈ B, dist (j (f v p)) (j (f 0 p)) < ε := by
  obtain ⟨W, hW, hclose⟩ := hB.mem_uniformity_of_prod
    (f := fun v p => j (f v p)) (q := (0 : E))
    ((hj.comp_continuousOn hf).mono (prod_mono subset_rfl (subset_univ B)))
    (by simpa only [mem_ball, dist_self] using hδ) (Metric.dist_mem_uniformity hε)
  rw [isOpen_ball.nhdsWithin_eq (by simpa only [mem_ball, dist_self] using hδ)] at hW
  filter_upwards [hW] with v hv p hp
  exact hclose v hv p hp

private theorem eventually_patchMap_preserves_transverse
    (hdim : Module.finrank ℝ E = 3)
    (e : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {c : Loop → M} {ρ : Loop → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hjoint : ContMDiffOn (𝓘(ℝ, E).prod IL) I ∞
      (fun q : E × Loop => e.patchMap c (fun p => e (c p) - ρ p • q.1) q.2)
      (ball 0 δ ×ˢ univ))
    {L : Set Pairs} (hL : IsCompact L)
    (htrans : ∀ q ∈ L, c (q.1, q.2.1) = c (q.1, q.2.2) →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => c (z.1, z.2.1)) q) -
         (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => c (z.1, z.2.2)) q))) :
    ∀ᶠ v in 𝓝 (0 : E), ∀ q ∈ L,
      e.patchMap c (fun p => e (c p) - ρ p • v) (q.1, q.2.1) =
      e.patchMap c (fun p => e (c p) - ρ p • v) (q.1, q.2.2) →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => e.patchMap c (fun p => e (c p) - ρ p • v) (z.1, z.2.1)) q) -
         (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => e.patchMap c (fun p => e (c p) - ρ p • v) (z.1, z.2.2)) q)) := by
  let f : E → Pairs → M := fun v q =>
    e.patchMap c (fun p => e (c p) - ρ p • v) (q.1, q.2.1)
  let g : E → Pairs → M := fun v q =>
    e.patchMap c (fun p => e (c p) - ρ p • v) (q.1, q.2.2)
  have hzero (p : Loop) : e.patchMap c (fun y => e (c y) - ρ y • (0 : E)) p = c p := by
    apply e.patchMap_eq_self
    rw [smul_zero, sub_zero]
  have hf (q : Pairs) : ContMDiffAt (𝓘(ℝ, E).prod IQ) I 1
      (Function.uncurry f) (0, q) := by
    have h := hjoint.contMDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      (show ((0 : E), (q.1, q.2.1)) ∈ ball 0 δ ×ˢ univ from
        ⟨by simpa only [mem_ball, dist_self] using hδ, mem_univ _⟩))
    have hmap : ContMDiffAt (𝓘(ℝ, E).prod IQ) (𝓘(ℝ, E).prod IL) ∞
        (fun z : E × Pairs => (z.1, z.2.1, z.2.2.1)) (0, q) :=
      contMDiffAt_fst.prodMk (contMDiffAt_snd.fst.prodMk contMDiffAt_snd.snd.fst)
    exact (h.comp (0, q) hmap).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hg (q : Pairs) : ContMDiffAt (𝓘(ℝ, E).prod IQ) I 1
      (Function.uncurry g) (0, q) := by
    have h := hjoint.contMDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      (show ((0 : E), (q.1, q.2.2)) ∈ ball 0 δ ×ˢ univ from
        ⟨by simpa only [mem_ball, dist_self] using hδ, mem_univ _⟩))
    have hmap : ContMDiffAt (𝓘(ℝ, E).prod IQ) (𝓘(ℝ, E).prod IL) ∞
        (fun z : E × Pairs => (z.1, z.2.1, z.2.2.2)) (0, q) :=
      contMDiffAt_fst.prodMk (contMDiffAt_snd.fst.prodMk contMDiffAt_snd.snd.snd)
    exact (h.comp (0, q) hmap).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hfzero : f 0 = fun q => c (q.1, q.2.1) := funext fun q => hzero _
  have hgzero : g 0 = fun q => c (q.1, q.2.2) := funext fun q => hzero _
  apply DifferentialGeometry.Topology.eventually_surjective_mfderiv_sub_at_coincidences_on_isCompact
    (show Module.finrank ℝ (ℝ × ℝ × ℝ) = Module.finrank ℝ E by simp [hdim])
    hL (fun q _ => hf q) (fun q _ => hg q)
  intro q hq heq
  change f 0 q = g 0 q at heq
  rw [hfzero, hgzero] at heq
  change Function.Surjective ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I (f 0) q) -
    (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I (g 0) q))
  rw [hfzero, hgzero]
  exact htrans q hq heq

theorem exists_small_loop_family_chart_perturbation_preserving_transverse
    (hdim : Module.finrank ℝ E = 3)
    (j : M → F) (hj : ContMDiff I 𝓘(ℝ, F) ∞ j)
    (e : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (a : PartialDiffeomorph IQ 𝓘(ℝ, ℝ × ℝ × ℝ) Pairs (ℝ × ℝ × ℝ) ∞)
    {c : Loop → M} (hc : ContMDiff IL I ∞ c)
    {ρ : Loop → ℝ} (hρ : ContMDiff IL 𝓘(ℝ) ∞ ρ)
    (hcompact : HasCompactSupport ρ) (hsupport : tsupport ρ ⊆ c ⁻¹' e.source)
    (hbound : ∀ p, ‖ρ p‖ ≤ 1)
    {U : Set Pairs} (hU : IsOpen U)
    (hpairs : ∀ q ∈ U, c (q.1, q.2.1) ∈ e.source ∧ c (q.1, q.2.2) ∈ e.source)
    (hleft : ∀ q ∈ U, ρ (q.1, q.2.1) = 1)
    (hright : ∀ q ∈ U, ρ (q.1, q.2.2) = 0)
    {B : Set Loop} (hB : IsCompact B)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : UniqueDiffOn ℝ J)
    {L : Set Pairs} (hL : IsCompact L)
    (htrans : ∀ q ∈ L, c (q.1, q.2.1) = c (q.1, q.2.2) →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => c (z.1, z.2.1)) q) -
         (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => c (z.1, z.2.2)) q)))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : E) (β : Loop → M), ‖v‖ < ε ∧
      β = e.patchMap c (fun p => e (c p) - ρ p • v) ∧
      ContMDiff IL I ∞ β ∧
      (∀ p, p ∉ tsupport ρ → β p = c p) ∧
      (∀ p ∈ B, dist (j (β p)) (j (c p)) < ε) ∧
      (∀ m : ℕ, m ≤ n → ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
        ‖iteratedFDerivWithin ℝ m
            (fun r : ℝ × ℝ => j (β (r.2, (r.1 : Circle)))) (univ ×ˢ J) q -
          iteratedFDerivWithin ℝ m
            (fun r : ℝ × ℝ => j (c (r.2, (r.1 : Circle)))) (univ ×ˢ J) q‖ < ε) ∧
      ∀ q ∈ L ∪ (U ∩ a.source), β (q.1, q.2.1) = β (q.1, q.2.2) →
        Function.Surjective
          ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
            (fun z : Pairs => β (z.1, z.2.1)) q) -
           (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
            (fun z : Pairs => β (z.1, z.2.2)) q)) := by
  have hsupp : univ ∩ tsupport ρ ⊆ c ⁻¹' e.source := fun _ h => hsupport h.2
  obtain ⟨δ, hδ, hjoint, _, _, hzero, _⟩ :=
    e.exists_pos_contMDiffOn_patchMap_bump hc.contMDiffOn hρ.contMDiffOn
      (by simpa only [univ_inter] using hcompact.isCompact) hsupp hbound
  let b : E → Loop → M := fun v => e.patchMap c (fun p => e (c p) - ρ p • v)
  have hbzero : b 0 = c := funext hzero
  have hC0 : ∀ᶠ v in 𝓝 (0 : E), ∀ p ∈ B, dist (j (b v p)) (j (c p)) < ε := by
    simpa only [hbzero] using eventually_uniform_embedding_dist j hj.continuous (f := b) hδ
      hjoint.continuousOn hB hε
  have hjets : ∀ᶠ v in 𝓝 (0 : E), ∀ m : ℕ, m ≤ n → ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => j (b v (r.2, (r.1 : Circle)))) (univ ×ˢ J) q -
        iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => j (c (r.2, (r.1 : Circle)))) (univ ×ˢ J) q‖ < ε := by
    have hbjoint : ContMDiffOn (𝓘(ℝ, E).prod IL) I ∞
        (Function.uncurry b) (ball (0 : E) δ ×ˢ J ×ˢ univ) :=
      hjoint.mono (prod_mono subset_rfl (subset_univ (J ×ˢ univ)))
    have h := DifferentialGeometry.Topology.eventually_uniform_loop_family_lift_derivatives
      j hj (f := b) (a := (0 : E)) isOpen_ball hJD hJ hbjoint
      (by simpa only [mem_ball, dist_self] using hδ) n hε
    rw [hbzero] at h
    exact h
  have hpreserve := eventually_patchMap_preserves_transverse hdim e hδ hjoint hL htrans
  obtain ⟨η, hη, hηall⟩ := Metric.eventually_nhds_iff.mp (hC0.and (hjets.and hpreserve))
  let l : Pairs → Loop := fun q => (q.1, q.2.1)
  let r : Pairs → Loop := fun q => (q.1, q.2.2)
  have hl : ContMDiff IQ IL ∞ l := contMDiff_fst.prodMk contMDiff_snd.fst
  have hr : ContMDiff IQ IL ∞ r := contMDiff_fst.prodMk contMDiff_snd.snd
  obtain ⟨v, β, hv, hβdef, hβ, hfixed, _, hnew⟩ :=
    exists_small_chart_perturbation_transverse_on_pair_region e a hc.contMDiffOn
      hρ.contMDiffOn (by simpa only [univ_inter] using hcompact.isCompact) hsupp hbound hU
      hl.contMDiffOn hr.contMDiffOn
      (fun q hq => ⟨mem_univ _, (hpairs q hq).1⟩)
      (fun q hq => ⟨mem_univ _, (hpairs q hq).2⟩) hleft hright (lt_min hε hη)
  have hvε : ‖v‖ < ε := hv.trans_le (min_le_left _ _)
  have hvη : dist v 0 < η := by
    simpa only [dist_zero_right] using hv.trans_le (min_le_right _ _)
  obtain ⟨hvC0, hvjets, hvold⟩ := hηall hvη
  refine ⟨v, β, hvε, hβdef, contMDiffOn_univ.mp hβ, hfixed, ?_, ?_, ?_⟩
  · simpa only [hβdef] using hvC0
  · simpa only [hβdef] using hvjets
  · intro q hq heq
    rcases hq with hq | hq
    · rw [hβdef] at heq ⊢
      exact hvold q hq heq
    · exact hnew q hq heq

theorem exists_loop_family_perturbation_transverse_on_finite_union
    (hdim : Module.finrank ℝ E = 3)
    (j : M → F) (hj : ContMDiff I 𝓘(ℝ, F) ∞ j) (hjind : Topology.IsInducing j)
    {ι : Type*} [Finite ι]
    (e : ι → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (a : ι → PartialDiffeomorph IQ 𝓘(ℝ, ℝ × ℝ × ℝ) Pairs (ℝ × ℝ × ℝ) ∞)
    (ρ : ι → Loop → ℝ) (U A : ι → Set Pairs) (K : ι → Set Loop)
    (hρ : ∀ i, ContMDiff IL 𝓘(ℝ) ∞ (ρ i))
    (hcompact : ∀ i, HasCompactSupport (ρ i)) (hbound : ∀ i p, ‖ρ i p‖ ≤ 1)
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, IsCompact (A i))
    (hAU : ∀ i, A i ⊆ U i ∩ (a i).source)
    (hK : ∀ i, IsCompact (K i)) (hsupp : ∀ i, tsupport (ρ i) ⊆ K i)
    (hpairs : ∀ i q, q ∈ U i → (q.1, q.2.1) ∈ K i ∧ (q.1, q.2.2) ∈ K i)
    (hleft : ∀ i q, q ∈ U i → ρ i (q.1, q.2.1) = 1)
    (hright : ∀ i q, q ∈ U i → ρ i (q.1, q.2.2) = 0)
    {c : Loop → M} (hc : ContMDiff IL I ∞ c)
    (hcK : ∀ i, MapsTo c (K i) (e i).source)
    {B : Set Loop} (hB : IsCompact B)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : UniqueDiffOn ℝ J)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : Loop → M, ContMDiff IL I ∞ β ∧
      (∀ p, p ∉ ⋃ i, tsupport (ρ i) → β p = c p) ∧
      (∀ p ∈ B, dist (j (β p)) (j (c p)) < ε) ∧
      (∀ m : ℕ, m ≤ n → ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
        ‖iteratedFDerivWithin ℝ m
            (fun r : ℝ × ℝ => j (β (r.2, (r.1 : Circle)))) (univ ×ˢ J) q -
          iteratedFDerivWithin ℝ m
            (fun r : ℝ × ℝ => j (c (r.2, (r.1 : Circle)))) (univ ×ˢ J) q‖ < ε) ∧
      ∀ i q, q ∈ A i → β (q.1, q.2.1) = β (q.1, q.2.2) →
        Function.Surjective
          ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
            (fun z : Pairs => β (z.1, z.2.1)) q) -
           (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
            (fun z : Pairs => β (z.1, z.2.2)) q)) := by
  classical
  let B' : Set Loop := B ∪ ⋃ i, K i
  have hB' : IsCompact B' := hB.union (isCompact_iUnion hK)
  obtain ⟨R, hR, hRmem⟩ := hjind.exists_uniform_dist_mem_finite_of_continuousOn
    hK (fun _ => hc.continuous.continuousOn) (fun i => (e i).open_source) hcK
  let C : (Loop → M) → (Loop → M) → ℝ → Prop := fun f g η =>
    (∀ p ∈ B', dist (j (f p)) (j (g p)) < η) ∧
    (∀ m : ℕ, m ≤ n → ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => j (f (r.2, (r.1 : Circle)))) (univ ×ˢ J) q -
        iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => j (g (r.2, (r.1 : Circle)))) (univ ×ˢ J) q‖ < η)
  let P : (Loop → M) → Prop := fun f => ContMDiff IL I ∞ f ∧
    ∀ p, p ∉ ⋃ i, tsupport (ρ i) → f p = c p
  let T : ι → (Loop → M) → Prop := fun i f => ∀ q ∈ A i,
    f (q.1, q.2.1) = f (q.1, q.2.2) →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => f (z.1, z.2.1)) q) -
         (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
          (fun z : Pairs => f (z.1, z.2.2)) q))
  have hrefl (η : ℝ) (hη : 0 < η) : C c c η := by
    constructor
    · intro p hp
      simpa only [dist_self] using hη
    · intro m hm q hq
      simpa only [sub_self, norm_zero] using hη
  have htriangle {f g h : Loop → M} {η κ : ℝ} (hgf : C g f η) (hfh : C f h κ) :
      C g h (η + κ) := by
    constructor
    · intro p hp
      exact (dist_triangle _ (j (f p)) _).trans_lt (add_lt_add (hgf.1 p hp) (hfh.1 p hp))
    · intro m hm q hq
      exact (norm_sub_le_norm_sub_add_norm_sub _
        (iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => j (f (r.2, (r.1 : Circle)))) (univ ×ˢ J) q) _).trans_lt
          (add_lt_add (hgf.2 m hm q hq) (hfh.2 m hm q hq))
  have hmono {f g : Loop → M} {η κ : ℝ} (hηκ : η ≤ κ) (hfg : C f g η) : C f g κ :=
    ⟨fun p hp => (hfg.1 p hp).trans_le hηκ,
      fun m hm q hq => (hfg.2 m hm q hq).trans_le hηκ⟩
  have hstep (f : Loop → M) (hf : P f) (hfC : C f c R)
      (t : Finset ι) (hft : ∀ i ∈ t, T i f) (i : ι) (η : ℝ) (hη : 0 < η) :
      ∃ g, P g ∧ C g f η ∧ T i g ∧ ∀ k ∈ t, T k g := by
    have hfmaps (k : ι) : MapsTo f (K k) (e k).source := by
      intro p hp
      exact hRmem k p hp (f p) (hfC.1 p (Or.inr (mem_iUnion.mpr ⟨k, hp⟩)))
    have hL : IsCompact (⋃ k ∈ t, A k) :=
      t.finite_toSet.isCompact_biUnion (fun k _ => hA k)
    have htrans : ∀ q ∈ ⋃ k ∈ t, A k, f (q.1, q.2.1) = f (q.1, q.2.2) →
        Function.Surjective
          ((show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
            (fun z : Pairs => f (z.1, z.2.1)) q) -
           (show (ℝ × ℝ × ℝ) →L[ℝ] E from mfderiv IQ I
            (fun z : Pairs => f (z.1, z.2.2)) q)) := by
      intro q hq
      obtain ⟨k, hkt, hqk⟩ := mem_iUnion₂.mp hq
      exact hft k hkt q hqk
    obtain ⟨v, g, _, _, hg, hfixed, hC0, hjets, htrans'⟩ :=
      exists_small_loop_family_chart_perturbation_preserving_transverse hdim j hj (e i) (a i)
        hf.1 (hρ i) (hcompact i) (fun p hp => hfmaps i (hsupp i hp)) (hbound i)
        (hU i) (fun q hq => ⟨hfmaps i (hpairs i q hq).1, hfmaps i (hpairs i q hq).2⟩)
        (hleft i) (hright i) hB' hJ hJD hL htrans n hη
    refine ⟨g, ⟨hg, ?_⟩, ⟨hC0, hjets⟩, ?_, ?_⟩
    · intro p hp
      exact (hfixed p (fun h => hp (mem_iUnion.mpr ⟨i, h⟩))).trans (hf.2 p hp)
    · intro q hq heq
      exact htrans' q (Or.inr (hAU i hq)) heq
    · intro k hk q hq heq
      exact htrans' q (Or.inl (mem_iUnion₂.mpr ⟨k, hk, hq⟩)) heq
  obtain ⟨β, hβ, hβC, hβT⟩ := exists_approximation_of_local_perturbations
    C P T c ⟨hc, fun _ _ => rfl⟩ hR hrefl htriangle hmono hstep hε
  exact ⟨β, hβ.1, hβ.2, fun p hp => hβC.1 p (Or.inl hp), hβC.2, hβT⟩

end DifferentialGeometry.Manifold

end
