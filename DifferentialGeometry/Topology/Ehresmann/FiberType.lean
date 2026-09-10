import DifferentialGeometry.Topology.Ehresmann.LocalTriviality
import Mathlib.Topology.Connected.Clopen

noncomputable section
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
  (f : M → N) (hf : ContMDiff I J ∞ f)
  (hreg : ∀ x, Function.Surjective (mfderiv I J f x))

private def fiberDiffeomorphOfTrivialization (y : N)
    (Q : TopologicalSpace.Opens N) (z : Q) :
    let _ (w : N) := regularFiberChartedSpace f w hf (fun x _ ↦ hreg x)
    ∀ (Θ : Diffeomorph
      (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ).prod J) I
      ({x : M // f x = y} × Q)
      (⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩ : TopologicalSpace.Opens M) ∞),
    (∀ p, f (Θ p).1 = p.2.1) →
    {x : M // f x = y} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)⟯ {x : M // f x = z.1} := by
  dsimp only
  let _ (w : N) := regularFiberChartedSpace f w hf (fun x _ ↦ hreg x)
  intro Θ hover
  let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
  let K := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let inc : {x : M // f x = z.1} → U := fun x ↦ ⟨x.1, by
    change f x.1 ∈ Q
    rw [x.2]
    exact z.2⟩
  have hinc : ContMDiff 𝓘(ℝ, K) I ∞ inc := by
    apply (ContMDiff.subtypeVal_comp_iff U inc).mp
    exact contMDiff_regularFiberInclusion f z.1 hf (fun x _ ↦ hreg x)
  have hsnd : ∀ x : {x : M // f x = z.1}, (Θ.symm (inc x)).2 = z := by
    intro x
    apply Subtype.ext
    have h := hover (Θ.symm (inc x))
    rw [Θ.apply_symm_apply] at h
    exact h.symm.trans x.2
  refine
    { toEquiv :=
        { toFun := fun x ↦ ⟨(Θ (x, z)).1, hover (x, z)⟩
          invFun := fun x ↦ (Θ.symm (inc x)).1
          left_inv := ?_
          right_inv := ?_ }
      contMDiff_toFun := ?_
      contMDiff_invFun := contMDiff_fst.comp (Θ.symm.contMDiff.comp hinc) }
  · intro x
    have he : inc ⟨(Θ (x, z)).1, hover (x, z)⟩ = Θ (x, z) := Subtype.ext rfl
    change (Θ.symm (inc ⟨(Θ (x, z)).1, hover (x, z)⟩)).1 = x
    rw [he, Θ.symm_apply_apply]
  · intro x
    apply Subtype.ext
    have hp : ((Θ.symm (inc x)).1, z) = Θ.symm (inc x) := Prod.ext rfl (hsnd x).symm
    change (Θ ((Θ.symm (inc x)).1, z)).1 = x.1
    rw [hp, Θ.apply_symm_apply]
  · apply (contMDiff_regularFiber_iff f z.1 hf (fun x _ ↦ hreg x) _).mpr
    exact contMDiff_subtype_val.comp (Θ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const))

theorem eventually_nonempty_diffeomorph_regularFiber
    [T2Space M] [SigmaCompactSpace M] [T2Space N]
    (hproper : IsProperMap f) (y : N) :
    let _ (w : N) := regularFiberChartedSpace f w hf (fun x _ ↦ hreg x)
    ∀ᶠ z in 𝓝 y, Nonempty
      ({x : M // f x = y} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ),
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)⟯ {x : M // f x = z}) := by
  dsimp only
  let _ (w : N) := regularFiberChartedSpace f w hf (fun x _ ↦ hreg x)
  obtain ⟨Q, hy, Θ, hover, -⟩ := ehresmann_local_triviality f hf hproper hreg y
  filter_upwards [Q.isOpen.mem_nhds hy] with z hz
  exact ⟨fiberDiffeomorphOfTrivialization f hf hreg y Q ⟨z, hz⟩ Θ hover⟩

theorem nonempty_diffeomorph_regularFiber_of_mem_connectedComponent
    [T2Space M] [SigmaCompactSpace M] [T2Space N]
    (hproper : IsProperMap f) (y z : N) (hz : z ∈ connectedComponent y) :
    let _ (w : N) := regularFiberChartedSpace f w hf (fun x _ ↦ hreg x)
    Nonempty
      ({x : M // f x = y} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ),
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)⟯ {x : M // f x = z}) := by
  dsimp only
  let _ (w : N) := regularFiberChartedSpace f w hf (fun x _ ↦ hreg x)
  let K := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let R : N → N → Prop := fun a b ↦ Nonempty
    ({x : M // f x = a} ≃ₘ⟮𝓘(ℝ, K), 𝓘(ℝ, K)⟯ {x : M // f x = b})
  have hlocal : ∀ a, ∀ᶠ b in 𝓝 a, R a b :=
    eventually_nonempty_diffeomorph_regularFiber f hf hreg hproper
  have hopen : IsOpen {a | R y a} := by
    rw [isOpen_iff_mem_nhds]
    intro a ha
    filter_upwards [hlocal a] with b hb
    exact ⟨ha.some.trans hb.some⟩
  have hclosed : IsClosed {a | R y a} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro a ha
    filter_upwards [hlocal a] with b hb
    intro hya
    exact ha ⟨hya.some.trans hb.some.symm⟩
  exact (IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩
    (show R y y from ⟨Diffeomorph.refl 𝓘(ℝ, K) _ ∞⟩)) hz

end DifferentialGeometry.Topology.Ehresmann
