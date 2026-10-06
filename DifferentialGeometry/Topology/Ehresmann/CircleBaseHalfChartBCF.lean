import DifferentialGeometry.Topology.Ehresmann.CircleChartDifferentialBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.PlaneHalfChartBCF

/-!
# Half charts of the circle-base curve from the corner record (lane S-BCF03b; BCF03 G7 K-D1..D3)

Binding kernel (generic manifold, no chain objects) joining
`surjective_base_differential_BCF` (G25: independence through a circle chart) with
`exists_halfChart_of_plane_{corner,interior}_BCF` (G24): at a point `y` of a curve `Γ` of the
two-dimensional base `B₀`, let `σ : ℝ² → H` (smooth embedding with injective differential onto
`B₀ ∩ Oσ`) and `φ : ℝ² × S¹ → M` (smooth embedding into a `3`-manifold, `f ∘ φ = σ ∘ fst`) be a
circle chart at `y = σ 0`, and `ψ i` (`i ∈ ι`) the face functions of the corner record, smooth on an
open `O ∋ y`, vanishing at `y`, with `v ↦ (mvfderiv (ψ i ∘ f) p v)_i` onto at a point `p` of the
fibre.

* `exists_halfChart_of_circleCorner_BCF`: two labels `ℓ ≠ v` (`ι = {ℓ, v}`) and
  `Γ ∩ O = {ψ ℓ = 0, ψ v ≤ 0}` (on `O ∩ B₀`): a half chart of `Γ` at `y` with coordinate `0`;
* `exists_halfChart_of_circleInterior_BCF`: one label and `Γ ∩ O = {ψ ℓ = 0}`: a half chart at `y`
  with positive coordinate.
-/

set_option autoImplicit false

open Set Function Manifold Topology
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

section Corner

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} [Finite ι]

omit [Finite ι] in
/-- **The base differentials through a circle chart are onto (corner record form)**: from the
surjectivity of the family `v ↦ (mvfderiv (ψ i ∘ f) p v)_i` at `p = φ (0, z₀)`, the differentials
`d(ψ i ∘ σ)(0)` are onto `ℝ^ι`. -/
theorem circleChart_differentials_surjective_BCF {f : M → H} {σ : E2 → H} {φ : E2 × Circle → M}
    {y : H} {O : Set H} (hO : IsOpen O) (hyO : y ∈ O) (hσ0 : σ 0 = y) (hσ : ContDiff ℝ ∞ σ)
    (hφ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) I ∞ φ) (hdim : Module.finrank ℝ EM = 3)
    (hf : ∀ x z, f (φ (x, z)) = σ x) (ψ : ι → H → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) O)
    (z₀ : Circle)
    (hsurj : Surjective fun w : TangentSpace I (φ (0, z₀)) =>
      fun i : ι => mvfderiv I (fun q => ψ i (f q)) (φ (0, z₀)) w) :
    Surjective fun v : E2 => fun i : ι => fderiv ℝ (fun x => ψ i (σ x)) 0 v := by
  have hΨ : ∀ i, DifferentiableAt ℝ (fun x => ψ i (σ x)) 0 := by
    intro i
    have h1 : ContDiffAt ℝ ∞ (ψ i) (σ 0) := (hψ i).contDiffAt (hO.mem_nhds (hσ0 ▸ hyO))
    exact (h1.comp (0 : E2) hσ.contDiffAt).differentiableAt (by simp)
  exact surjective_base_differential_BCF (fun i q => ψ i (f q)) (fun i x => ψ i (σ x)) φ hφ hdim 0
    z₀ hΨ (fun i x z => by simp only [hf]) hsurj

/-- **A corner of the circle-base curve has a half chart** (coordinate `0`). -/
theorem exists_halfChart_of_circleCorner_BCF {f : M → H} {B₀ Γ : Set H} {y : H} {σ : E2 → H}
    {φ : E2 × Circle → M} {Oσ : Set H} (hσ0 : σ 0 = y) (hσ : ContDiff ℝ ∞ σ)
    (hσe : IsEmbedding σ) (hσd : ∀ x, Injective (fderiv ℝ σ x)) (hOσ : IsOpen Oσ)
    (hrange : range σ = B₀ ∩ Oσ) (hφ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) I ∞ φ)
    (hdim : Module.finrank ℝ EM = 3) (hf : ∀ x z, f (φ (x, z)) = σ x) (hΓB : Γ ⊆ B₀)
    {O : Set H} (hO : IsOpen O) (hyO : y ∈ O) (ψ : ι → H → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) O)
    (hψ0 : ∀ i, ψ i y = 0) (ℓ v : ι) (hne : ℓ ≠ v) (hι : ∀ i, i = ℓ ∨ i = v) (z₀ : Circle)
    (hsurj : Surjective fun w : TangentSpace I (φ (0, z₀)) =>
      fun i : ι => mvfderiv I (fun q => ψ i (f q)) (φ (0, z₀)) w)
    (hZ : ∀ y' ∈ O ∩ B₀, y' ∈ Γ ↔ ψ ℓ y' = 0 ∧ ψ v y' ≤ 0) :
    ∃ (B : Set H) (d : HalfChart_BCF B Γ), y ∈ d.O ∧ d.L y + d.κ = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hS := circleChart_differentials_surjective_BCF hO hyO hσ0 hσ hφ hdim hf ψ hψ z₀ hsurj
  have hcard : Module.finrank ℝ (ι → ℝ) = 2 := by
    have huniv : (Finset.univ : Finset ι) = {ℓ, v} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hι i
    rw [Module.finrank_fintype_fun_eq_card, ← Finset.card_univ, huniv, Finset.card_pair hne]
  let Lm : E2 →ₗ[ℝ] (ι → ℝ) :=
    LinearMap.pi fun i => (fderiv ℝ (fun x => ψ i (σ x)) 0 : E2 →L[ℝ] ℝ).toLinearMap
  have hLs : Surjective Lm := hS
  have hLi : Injective Lm := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hcard, finrank_euclideanSpace_fin])).mpr hLs
  have hind : Injective fun x : E2 => (fderiv ℝ (fun x => ψ ℓ (σ x)) 0 x,
      fderiv ℝ (fun x => ψ v (σ x)) 0 x) := by
    intro x x' h
    refine hLi (funext fun i => ?_)
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    rcases hι i with rfl | rfl
    · exact h1
    · exact h2
  have hP : IsOpen (σ ⁻¹' O) := hO.preimage hσ.continuous
  have h0 : (0 : E2) ∈ σ ⁻¹' O := by simpa [hσ0] using hyO
  have hu : ∀ i, ContDiffOn ℝ ∞ (fun x => ψ i (σ x)) (σ ⁻¹' O) := fun i =>
    (hψ i).comp hσ.contDiffOn fun x hx => hx
  have hz : ∀ i, ψ i (σ 0) = 0 := fun i => by rw [hσ0]; exact hψ0 i
  have hZ' : ∀ x ∈ σ ⁻¹' O, σ x ∈ Γ ↔ (ψ ℓ (σ x) = 0 ∧ ψ v (σ x) ≤ 0) := fun x hx =>
    hZ (σ x) ⟨hx, (hrange ▸ mem_range_self x : σ x ∈ B₀ ∩ Oσ).1⟩
  obtain ⟨B, d, hd1, hd2⟩ := exists_halfChart_of_plane_corner_BCF hσ hσe hσd hOσ hrange hΓB hP h0
    (hu ℓ) (hu v) (hz ℓ) (hz v) hind hZ'
  exact ⟨B, d, hσ0 ▸ hd1, hσ0 ▸ hd2⟩

end Corner

section Interior

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*}

/-- A nonzero linear functional of the plane and its quarter turn have independent kernels. -/
theorem injective_pair_rot_BCF (A : E2 →L[ℝ] ℝ) (x₁ : E2) (h1 : A x₁ = 1) :
    ∃ w : E2 →L[ℝ] ℝ, Injective fun x : E2 => (A x, w x) := by
  let e₀ : E2 := EuclideanSpace.single 0 1
  let e₁ : E2 := EuclideanSpace.single 1 1
  have hdec : ∀ x : E2, x = x 0 • e₀ + x 1 • e₁ := by
    intro x
    ext i
    fin_cases i <;> simp [e₀, e₁]
  have hA : ∀ x : E2, A x = x 0 * A e₀ + x 1 * A e₁ := by
    intro x
    conv_lhs => rw [hdec x]
    simp [map_add, map_smul]
  set a := A e₀ with ha
  set b := A e₁ with hb
  refine ⟨(-b) • EuclideanSpace.proj (0 : Fin 2) + a • EuclideanSpace.proj (1 : Fin 2), ?_⟩
  have hab : 0 < a ^ 2 + b ^ 2 := by
    by_contra hle
    have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have := hA x₁
    rw [h1, ha0, hb0] at this
    simp at this
  intro x x' h
  have h1' := congrArg Prod.fst h
  have h2' := congrArg Prod.snd h
  have hproj : ∀ (i : Fin 2) (x : E2), (EuclideanSpace.proj i : E2 →L[ℝ] ℝ) x = x i :=
    fun _ _ => rfl
  simp only [hA, add_apply, smul_apply, hproj, smul_eq_mul] at h1' h2'
  have e0 : x 0 = x' 0 := by
    have : (a ^ 2 + b ^ 2) * (x 0 - x' 0) = 0 := by linear_combination a * h1' - b * h2'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hab.ne'
    · linarith
  have e1 : x 1 = x' 1 := by
    have : (a ^ 2 + b ^ 2) * (x 1 - x' 1) = 0 := by linear_combination b * h1' + a * h2'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hab.ne'
    · linarith
  ext i
  fin_cases i
  · exact e0
  · exact e1

/-- **An interior point of the circle-base curve has a half chart** (positive coordinate). -/
theorem exists_halfChart_of_circleInterior_BCF {f : M → H} {B₀ Γ : Set H} {y : H} {σ : E2 → H}
    {φ : E2 × Circle → M} {Oσ : Set H} (hσ0 : σ 0 = y) (hσ : ContDiff ℝ ∞ σ)
    (hσe : IsEmbedding σ) (hσd : ∀ x, Injective (fderiv ℝ σ x)) (hOσ : IsOpen Oσ)
    (hrange : range σ = B₀ ∩ Oσ) (hφ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) I ∞ φ)
    (hdim : Module.finrank ℝ EM = 3) (hf : ∀ x z, f (φ (x, z)) = σ x) (hΓB : Γ ⊆ B₀)
    {O : Set H} (hO : IsOpen O) (hyO : y ∈ O) (ψ : ι → H → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) O)
    (hψ0 : ∀ i, ψ i y = 0) (ℓ : ι) (z₀ : Circle)
    (hsurj : Surjective fun w : TangentSpace I (φ (0, z₀)) =>
      fun i : ι => mvfderiv I (fun q => ψ i (f q)) (φ (0, z₀)) w)
    (hZ : ∀ y' ∈ O ∩ B₀, y' ∈ Γ ↔ ψ ℓ y' = 0) :
    ∃ (B : Set H) (d : HalfChart_BCF B Γ), y ∈ d.O ∧ 0 < d.L y + d.κ := by
  have hS := circleChart_differentials_surjective_BCF hO hyO hσ0 hσ hφ hdim hf ψ hψ z₀ hsurj
  obtain ⟨x₁, hx₁⟩ := hS (fun _ => 1)
  have hA1 : fderiv ℝ (fun x => ψ ℓ (σ x)) 0 x₁ = 1 := congrFun hx₁ ℓ
  obtain ⟨w, hw⟩ := injective_pair_rot_BCF (fderiv ℝ (fun x => ψ ℓ (σ x)) 0) x₁ hA1
  have hind : Injective fun x : E2 => (fderiv ℝ (fun x => ψ ℓ (σ x)) 0 x, fderiv ℝ w 0 x) := by
    rw [w.fderiv]
    exact hw
  have hP : IsOpen (σ ⁻¹' O) := hO.preimage hσ.continuous
  have h0 : (0 : E2) ∈ σ ⁻¹' O := by simpa [hσ0] using hyO
  have hu : ContDiffOn ℝ ∞ (fun x => ψ ℓ (σ x)) (σ ⁻¹' O) :=
    (hψ ℓ).comp hσ.contDiffOn fun x hx => hx
  have hz : ψ ℓ (σ 0) = 0 := by rw [hσ0]; exact hψ0 ℓ
  have hZ' : ∀ x ∈ σ ⁻¹' O, σ x ∈ Γ ↔ ψ ℓ (σ x) = 0 := fun x hx =>
    hZ (σ x) ⟨hx, (hrange ▸ mem_range_self x : σ x ∈ B₀ ∩ Oσ).1⟩
  obtain ⟨B, d, hd1, hd2⟩ := exists_halfChart_of_plane_interior_BCF hσ hσe hσd hOσ hrange hΓB hP h0
    hu w.contDiff.contDiffOn hz (map_zero w) hind hZ'
  exact ⟨B, d, hσ0 ▸ hd1, hσ0 ▸ hd2⟩

end Interior

end DifferentialGeometry.Topology
