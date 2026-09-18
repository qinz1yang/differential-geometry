import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

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
