import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {f : ℝ → ∀ x, V x} {m n : WithTop ℕ∞}

theorem ContMDiffAt.fiberwise_time_deriv {p₀ : ℝ × M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : TotalSpace F V)) p₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, deriv (fun t => f t p.2) p.1⟩ : TotalSpace F V)) p₀ := by
  rw [contMDiffAt_totalSpace] at hf ⊢
  refine ⟨contMDiffAt_snd, ?_⟩
  let e := trivializationAt F V p₀.2
  have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun p : ℝ × M => (e ⟨p.2, f p.1 p.2⟩).2) p₀ := hf.2
  have hd := DifferentialGeometry.timeDeriv_smoothAt hcoord hmn
  apply hd.congr_of_eventuallyEq
  have hbase : ∀ᶠ p : ℝ × M in 𝓝 p₀, p.2 ∈ e.baseSet :=
    continuous_snd.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V p₀.2))
  filter_upwards [hbase] with p hp
  let L := e.continuousLinearEquivAt ℝ p.2 hp
  have hL : ∀ v : V p.2, L v = (e ⟨p.2, v⟩).2 := by
    intro v
    rw [show (L : V p.2 → F) = e.continuousLinearMapAt ℝ p.2 from
      e.coe_continuousLinearEquivAt_eq hp]
    exact e.continuousLinearMapAt_apply_of_mem ℝ hp v
  have heq : (fun t => (e ⟨p.2, f t p.2⟩).2) = L ∘ (fun t => f t p.2) := by
    funext t
    exact (hL _).symm
  change (e ⟨p.2, deriv (fun t => f t p.2) p.1⟩).2 =
    deriv (fun t => (e ⟨p.2, f t p.2⟩).2) p.1
  rw [heq, ← hL]
  change L (fderiv ℝ (fun t => f t p.2) p.1 1) =
    fderiv ℝ (L ∘ (fun t => f t p.2)) p.1 1
  rw [L.comp_fderiv]
  rfl

theorem ContMDiffOn.fiberwise_time_deriv {s : Set (ℝ × M)}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : TotalSpace F V)) s)
    (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, deriv (fun t => f t p.2) p.1⟩ : TotalSpace F V)) s := by
  intro p hp
  exact ((hf.contMDiffAt (hs.mem_nhds hp)).fiberwise_time_deriv hmn).contMDiffWithinAt

theorem ContMDiff.fiberwise_time_deriv
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : TotalSpace F V)))
    (hmn : m + 1 ≤ n) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, deriv (fun t => f t p.2) p.1⟩ : TotalSpace F V)) := by
  intro p
  exact hf.contMDiffAt.fiberwise_time_deriv hmn

theorem ContMDiffOn.fiberwise_time_derivWithin {s : Set ℝ} {u : Set M}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : TotalSpace F V)) (s ×ˢ u))
    (hs : UniqueDiffOn ℝ s) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) m
      (fun p : ℝ × M => (⟨p.2, derivWithin (fun t => f t p.2) s p.1⟩ : TotalSpace F V))
      (s ×ˢ u) := by
  intro p₀ hp₀
  have hf₀ := hf p₀ hp₀
  rw [contMDiffWithinAt_totalSpace] at hf₀ ⊢
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let e := trivializationAt F V p₀.2
  let C : ℝ × M → F := fun p => (e ⟨p.2, f p.1 p.2⟩).2
  have hcoord : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n C (s ×ˢ u) p₀ := hf₀.2
  have harg : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) n (fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      ((s ×ˢ u) ×ˢ s) (p₀, p₀.1) :=
    contMDiffWithinAt_snd.prodMk contMDiffWithinAt_fst.snd
  have hC : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, F) n (fun q : (ℝ × M) × ℝ => C (q.2, q.1.2))
      ((s ×ˢ u) ×ˢ s) (p₀, p₀.1) :=
    hcoord.comp (f := fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      (g := C) (p₀, p₀.1) harg (fun q hq => ⟨hq.2, hq.1.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F))
    (f := fun (p : ℝ × M) (t : ℝ) => C (t, p.2))
    (g := fun p : ℝ × M => p.1) (g₁ := fun p : ℝ × M => p)
    (g₂ := fun _ : ℝ × M => (1 : ℝ)) (x₀ := p₀)
    hC contMDiffWithinAt_fst contMDiffWithinAt_id contMDiffWithinAt_const hmn
    (mapsTo_id _) hp₀ (fun _ hp => hp.1) hs.uniqueMDiffOn
  have hd' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) m
      (fun p : ℝ × M => derivWithin (fun t => C (t, p.2)) s p.1) (s ×ˢ u) p₀ := by
    simpa only [inTangentCoordinates_model_space, mfderivWithin_eq_fderivWithin,
      derivWithin] using hd
  have heq (p : ℝ × M) (hp : p ∈ s ×ˢ u) (hb : p.2 ∈ e.baseSet) :
      (e ⟨p.2, derivWithin (fun t => f t p.2) s p.1⟩).2 =
        derivWithin (fun t => C (t, p.2)) s p.1 := by
    let L := e.continuousLinearEquivAt ℝ p.2 hb
    have hL : ∀ v : V p.2, L v = (e ⟨p.2, v⟩).2 := by
      intro v
      rw [show (L : V p.2 → F) = e.continuousLinearMapAt ℝ p.2 from
        e.coe_continuousLinearEquivAt_eq hb]
      exact e.continuousLinearMapAt_apply_of_mem ℝ hb v
    have hcomp : (fun t => C (t, p.2)) = L ∘ (fun t => f t p.2) := by
      funext t
      exact (hL _).symm
    rw [hcomp, ← hL]
    change L (fderivWithin ℝ (fun t => f t p.2) s p.1 1) =
      fderivWithin ℝ (L ∘ (fun t => f t p.2)) s p.1 1
    rw [L.comp_fderivWithin (hs p.1 hp.1)]
    rfl
  apply hd'.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p : ℝ × M in 𝓝[s ×ˢ u] p₀, p.2 ∈ e.baseSet :=
      continuousWithinAt_snd (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V p₀.2))
    filter_upwards [self_mem_nhdsWithin, hbase] with p hp hb
    exact heq p hp hb
  · exact heq p₀ hp₀ (mem_baseSet_trivializationAt F V p₀.2)

omit [IsManifold I 1 M] in
theorem ContMDiffWithinAt.fiberwise_time_contDiffWithinAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    {f : ℝ → ∀ x, V x} {t : ℝ} {x : M} {n : WithTop ℕ∞}
    {s : Set ℝ} {u : Set M}
    (hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × M => (⟨p.2, f p.1 p.2⟩ : TotalSpace F V)) (s ×ˢ u) (t, x)) (hxU : x ∈ u) :
    ContDiffWithinAt ℝ n (fun r => f r x) s t := by
  rw [contMDiffWithinAt_totalSpace] at hf
  let e := trivializationAt F V x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hcoord : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun p : ℝ × M => (e ⟨p.2, f p.1 p.2⟩).2) (s ×ˢ u) (t, x) := hf.2
  have hmaps : MapsTo (fun r : ℝ => (r, x)) s (s ×ˢ u) := fun r hr => ⟨hr, hxU⟩
  have hfixed := hcoord.comp (f := fun r : ℝ => (r, x)) t
    (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const) hmaps
  have hback := (e.symmL ℝ x).contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt t hfixed
  rw [← contMDiffWithinAt_iff_contDiffWithinAt]
  have heq (r : ℝ) : f r x = e.symmL ℝ x (e ⟨x, f r x⟩).2 := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hx]
    exact (e.symmL_continuousLinearMapAt hx _).symm
  exact hback.congr (fun r _ => heq r) (heq t)
