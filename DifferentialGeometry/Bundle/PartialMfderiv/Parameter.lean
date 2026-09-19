import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import DifferentialGeometry.Bundle.TangentMap

noncomputable section
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 E G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {m n : ℕ∞ω}

theorem ContMDiffAt.partial_mfderiv_apply {Φ : P → N → M}
    {w : (p : P × N) → TangentSpace J p.2} {p₀ : P × N}
    (hΦ : ContMDiffAt (IP.prod J) I n (Function.uncurry Φ) p₀)
    (hw : ContMDiffAt (IP.prod J) J.tangent m
      (fun p => (⟨p.2, w p⟩ : TangentBundle J N)) p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt (IP.prod J) I.tangent m
      (fun p : P × N => (⟨Φ p.1 p.2, mfderiv J I (Φ p.1) p.2 (w p)⟩ : TangentBundle I M))
      p₀ := by
  have harg : ContMDiffAt ((IP.prod J).prod J)
      (IP.prod J) n (fun q : (P × N) × N => (q.1.1, q.2)) (p₀, p₀.2) :=
    contMDiffAt_fst.fst.prodMk contMDiffAt_snd
  have hΦ' : ContMDiffAt ((IP.prod J).prod J) I n
      (fun q : (P × N) × N => Φ q.1.1 q.2) (p₀, p₀.2) :=
    hΦ.comp (p₀, p₀.2) harg
  have hd := ContMDiffAt.mfderiv (I := J) (I' := I) (J := IP.prod J) (hf := hΦ')
    (fun (p : P × N) (y : N) => Φ p.1 y) Prod.snd contMDiffAt_snd hmn
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := E) (E₁ := TangentSpace J (M := N))
    (F₂ := F) (E₂ := TangentSpace I (M := M))
    (b₁ := fun p : P × N => p.2) (b₂ := fun p : P × N => Φ p.1 p.2)
    (ϕ := fun p : P × N => mfderiv J I (Φ p.1) p.2)
    (v := w) hd hw
    (hΦ.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn))

end

section

noncomputable section

open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
theorem source_mfderivWithin_spatial {F : ℝ × A → M} {T : Set ℝ} {s : Set A}
    (hs : IsOpen s) {r : ℝ} (hr : r ∈ T) {q : A} (hq : q ∈ s)
    (hF : MDifferentiableWithinAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (T ×ˢ s) (r, q)) (v : A) :
    mfderivWithin 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (T ×ˢ s) (r, q) (0, v) =
      mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun y => F (r, y)) q v := by
  have he : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, ℝ × A) (fun y : A => (r, y)) q :=
    (differentiableAt_const r |>.prodMk differentiableAt_id).mdifferentiableAt
  have hc := mfderivWithin_comp q hF he.mdifferentiableWithinAt
    (show MapsTo (fun y : A => (r, y)) s (T ×ˢ s) from fun y hy => ⟨hr, hy⟩)
    (hs.uniqueDiffOn q hq).uniqueMDiffWithinAt
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hq)] at hc
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hq), mfderiv_eq_fderiv] at hc
  have hderiv := ((hasFDerivAt_const (𝕜 := ℝ) r q).prodMk (hasFDerivAt_id (𝕜 := ℝ) q)).fderiv
  simp only [id_eq] at hderiv
  rw [hderiv] at hc
  have hv := congrArg (fun L => L v) hc
  exact hv.symm

theorem contMDiffOn_source_spatialPartial {F : ℝ × A → M} {T : Set ℝ} {s : Set A}
    (hT : UniqueDiffOn ℝ T) (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) ∞ F (T ×ˢ s)) (v : A) :
    ContMDiffOn 𝓘(ℝ, ℝ × A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (F p)
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun q => F (p.1, q)) p.2 v)) (T ×ˢ s) := by
  apply (contMDiffOn_source_partialWithin (hT.prod hs.uniqueDiffOn) hF
    (m := ∞) (by simp) (0, v)).congr
  intro p hp
  rw [source_mfderivWithin_spatial hs hp.1 hp.2
    ((hF p hp).mdifferentiableWithinAt (by simp)) v]

end DifferentialGeometry.Geometry

end

end
