import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Morse.CriticalPoints

open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

section

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ F H} {n : ℕ∞ω}

theorem criticalPoints_comp_eq_of_graph
    {e : M → E × ℝ} (he : ContMDiff I 𝓘(ℝ, E × ℝ) n e)
    (hinj : Function.Injective e)
    (χ : PartialDiffeomorph 𝓘(ℝ, E) I E M n) (hn : n ≠ 0)
    {U : Set E} (hU : IsOpen U) (hUχ : U ⊆ χ.source)
    {q g : E → ℝ} (hgraph : ∀ y ∈ U, e (χ y) = (y, q y))
    (D : E × ℝ → E × ℝ) (hDdiff : ContDiff ℝ n D)
    (hD : ∀ y ∈ U, D (y, q y) = (y, g y))
    {K : Set (E × ℝ)} (hK : IsClosed K)
    (hset : K ∩ range e = K ∩ ((fun y => (y, q y)) '' U))
    (hfix : EqOn D id Kᶜ) :
    criticalPoints I (fun y => (D (e y)).2) =
      (criticalPoints I (fun y => (e y).2) \ χ '' U) ∪
        χ '' (U ∩ criticalPoints 𝓘(ℝ, E) g) ∧
    ∀ x ∉ χ '' U, (D ∘ e) =ᶠ[𝓝 x] e := by
  have hout (x : M) (hx : x ∉ χ '' U) : (D ∘ e) =ᶠ[𝓝 x] e := by
    have hxK : e x ∉ K := by
      intro hxK
      obtain ⟨y, hy, hyx⟩ := (hset.subset ⟨hxK, mem_range_self x⟩).2
      exact hx ⟨y, hy, hinj ((hgraph y hy).trans hyx)⟩
    filter_upwards [he.continuous.continuousAt.eventually
      (hK.isOpen_compl.mem_nhds hxK)] with y hy
    exact hfix hy
  have hnew : ContMDiff I 𝓘(ℝ, ℝ) n (fun y => (D (e y)).2) :=
    contDiff_snd.contMDiff.comp (hDdiff.contMDiff.comp he)
  have hchart {y : E} (hy : y ∈ U) :
      IsCriticalPointAt I (fun x => (D (e x)).2) (χ y) ↔
        IsCriticalPointAt 𝓘(ℝ, E) g y := by
    have hlocal := χ.isLocalDiffeomorphAt _ _ _ (hUχ hy)
    have hcomp := isCriticalPointAt_comp_iff (χ.mdifferentiableAt hn (hUχ hy))
      (hnew.mdifferentiableAt hn) (hlocal.mfderivToContinuousLinearEquiv hn).surjective
    have heq : (fun x => (D (e x)).2) ∘ χ =ᶠ[𝓝 y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      change (D (e (χ z))).2 = g z
      rw [hgraph z hz, hD z hz]
    apply hcomp.symm.trans
    unfold IsCriticalPointAt
    rw [heq.mfderiv_eq]
    rfl
  refine ⟨?_, hout⟩
  ext x
  change IsCriticalPointAt I (fun y => (D (e y)).2) x ↔
    (IsCriticalPointAt I (fun y => (e y).2) x ∧ x ∉ χ '' U) ∨
      x ∈ χ '' (U ∩ criticalPoints 𝓘(ℝ, E) g)
  by_cases hx : x ∈ χ '' U
  · obtain ⟨y, hy, rfl⟩ := hx
    constructor
    · intro hc
      exact Or.inr ⟨y, ⟨hy, (hchart hy).mp hc⟩, rfl⟩
    · rintro (hc | ⟨z, ⟨hz, hzc⟩, hzy⟩)
      · exact False.elim (hc.2 ⟨y, hy, rfl⟩)
      · have hzy' : z = y := χ.injOn (hUχ hz) (hUχ hy) hzy
        exact (hchart hy).mpr (hzy' ▸ hzc)
  · have hc : IsCriticalPointAt I (fun y => (D (e y)).2) x ↔
        IsCriticalPointAt I (fun y => (e y).2) x := by
      unfold IsCriticalPointAt
      exact Iff.of_eq (congrArg (fun L => L = 0)
        (((hout x hx).fun_comp Prod.snd).mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))))
    constructor
    · intro h
      exact Or.inl ⟨hc.mp h, hx⟩
    · rintro (h | ⟨y, hy, hyx⟩)
      · exact hc.mpr h.1
      · exact False.elim (hx ⟨y, hy.1, hyx⟩)

end

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

theorem isCriticalPointAt_snd_iff_of_eventually_graph {e : M → E × ℝ} {x : M}
    (he : IsImmersionAt I 𝓘(ℝ, E × ℝ) ∞ e x)
    {g : E → ℝ} (hg : ContDiffAt ℝ ∞ g (e x).1)
    (hgraph : ∀ᶠ y in 𝓝 x, (e y).2 = g (e y).1) :
    IsCriticalPointAt I (fun y => (e y).2) x ↔ fderiv ℝ g (e x).1 = 0 := by
  let p : M → E := fun y => (e y).1
  have hp : MDifferentiableAt I 𝓘(ℝ, E) p x :=
    ((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : E × ℝ → E)).differentiable
      (by simp) (e x)).mdifferentiableAt.comp x
        (he.contMDiffAt.mdifferentiableAt (by simp))
  have heq : e =ᶠ[𝓝 x] ((fun z => (z, g z)) ∘ p) := by
    filter_upwards [hgraph] with y hy
    exact Prod.ext rfl hy
  have hd : mfderiv I 𝓘(ℝ, E × ℝ) e x =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × ℝ) (fun z => (z, g z)) (p x)).comp
        (mfderiv I 𝓘(ℝ, E) p x) := by
    exact heq.mfderiv_eq.trans
      (mfderiv_comp x ((contDiffAt_id.prodMk hg).differentiableAt (by simp)).mdifferentiableAt hp)
  have hinj : Function.Injective (mfderiv I 𝓘(ℝ, E) p x) := by
    intro u v huv
    apply he.injective_mfderiv (by simp)
    have hh := congrArg (fun f : E →L[ℝ] E × ℝ => f u - f v) hd
    have hz : (mfderiv I 𝓘(ℝ, E × ℝ) e x) u - (mfderiv I 𝓘(ℝ, E × ℝ) e x) v = 0 := by
      calc
        _ = _ := hh
        _ = 0 := by
          change
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × ℝ) (fun z => (z, g z)) (p x))
              (mfderiv I 𝓘(ℝ, E) p x u) -
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × ℝ) (fun z => (z, g z)) (p x))
                  (mfderiv I 𝓘(ℝ, E) p x v) = 0; rw [huv, sub_self]
    exact sub_eq_zero.mp hz
  let D : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) p x
  have hs : Function.Surjective (mfderiv I 𝓘(ℝ, E) p x) :=
    LinearMap.surjective_of_injective (f := D.toLinearMap) hinj
  have hc := isCriticalPointAt_comp_iff hp (hg.differentiableAt (by simp)).mdifferentiableAt hs
  have heq' : (fun y => (e y).2) =ᶠ[𝓝 x] g ∘ p := hgraph
  have hi : IsCriticalPointAt I (fun y => (e y).2) x ↔ IsCriticalPointAt I (g ∘ p) x :=
    Iff.of_eq (congrArg (fun D : E →L[ℝ] ℝ => D = 0) heq'.mfderiv_eq)
  exact hi.trans (hc.trans (by
    unfold IsCriticalPointAt
    rw [mfderiv_eq_fderiv]
    rfl))

theorem eventuallyEq_of_isCriticalPointAt_regular_graph_replacement
    {e : M → E × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ e)
    {W : Set (E × ℝ)} (hW : IsOpen W) {Y : Set E} {g k : E → ℝ}
    (hgraph : ∀ x, e x ∈ W → (e x).2 = g (e x).1)
    (hk : ContDiff ℝ ∞ k) (hkd : ∀ y, fderiv ℝ k y ≠ 0)
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ))
    (hAfst : ∀ p, (A p).1 = p.1)
    (hAgraph : ∀ y ∈ Y, A (y, g y) = (y, k y))
    (hfix : ∀ p ∈ range e, p ∉ W ∩ {q | q.1 ∈ interior Y} →
      (A : (E × ℝ) → E × ℝ) =ᶠ[𝓝 p] id)
    {x : M} (hx : IsCriticalPointAt I (fun y => (A (e y)).2) x) :
    e x ∉ W ∩ {q | q.1 ∈ interior Y} ∧ (A ∘ e) =ᶠ[𝓝 x] e := by
  have hn : e x ∉ W ∩ {q | q.1 ∈ interior Y} := by
    intro hxW
    have hopen : IsOpen (e ⁻¹' (W ∩ {q | q.1 ∈ interior Y})) :=
      (hW.inter (isOpen_interior.preimage continuous_fst)).preimage he.contMDiff.continuous
    have hgerm : ∀ᶠ y in 𝓝 x, (A (e y)).2 = k (A (e y)).1 := by
      filter_upwards [hopen.mem_nhds hxW] with y hy
      have heq : e y = ((e y).1, g (e y).1) := Prod.ext rfl (hgraph y hy.1)
      rw [hAfst, heq, hAgraph _ (interior_subset hy.2)]
    have hc := (isCriticalPointAt_snd_iff_of_eventually_graph
      ((he.diffeomorph_comp A).isImmersion.isImmersionAt x) hk.contDiffAt hgerm).mp hx
    exact hkd _ hc
  exact ⟨hn, (hfix (e x) (mem_range_self x) hn).comp_tendsto he.contMDiff.continuous.continuousAt⟩

end DifferentialGeometry.Topology.Morse
