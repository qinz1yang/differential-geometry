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
