import DifferentialGeometry.Geometry.Exponential.Flat.TranslationIsometry
import DifferentialGeometry.Geometry.Exponential.Flat.PlaneIsometry
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.Quotient

/-!
# SF4(c): a compact orientable flat surface is a torus

* `nonempty_diffeomorph_addCircle_prod_of_periodic_cover` (no metric): a surface with an onto
  local diffeomorphism from its model plane whose fibres are exactly the cosets of `ℤv₁ + ℤv₂`
  for a basis `(v₁, v₂)` is diffeomorphic to `ℝ/ℤ × ℝ/ℤ`. Both directions are descended through
  the two periodic local diffeomorphisms `E → M` and `E → (ℝ/ℤ)²`
  (`IsLocalDiffeomorph.contMDiff_of_comp_of_surjective`).
* `exists_periodic_cover_of_flat`: for a compact connected orientable smooth flat surface, `exp_p`
  is such a cover. The translation lattice `Λ` of SF4(b) is discrete; compactness of `M` makes it
  cocompact (review §4.2 step 4: "free + discrete" alone allows rank `0`, `1` or `2`), so it is
  spanned over `ℤ` by an `ℝ`-basis (`exists_basis_span_eq_of_discrete_of_cocompact`).
* `nonempty_diffeomorph_addCircle_prod_of_flat`: the smooth type is the torus.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FlatSurface

section Descent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
private theorem injective_mfderiv_coe_comp (L : E →L[ℝ] ℝ) (y : E) :
    ∀ u u', mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y u =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y u' → L u = L u' := by
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y) :=
    AddCircle.contMDiff_coe.mdifferentiable (by simp) (L y)
  have hl : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y :=
    (L.contDiff (n := 1)).contMDiff.mdifferentiable (by simp) y
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y) :=
    mfderiv_comp (f := fun z => L z) (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) y hc hl
  have hL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  intro u u' h
  rw [hcomp, hL] at h
  exact (AddCircle.bijective_mfderiv_coe (L y)).1 h

private theorem addCircle_coe_eq_coe_iff {a b : ℝ} :
    (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) ↔ ∃ m : ℤ, b - a = m := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [zsmul_eq_mul, mul_one] at hm
    exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [zsmul_eq_mul, mul_one]; linarith⟩

/-- **The standard torus from a periodic cover.** A manifold with an onto local diffeomorphism
from its model plane whose fibres are the cosets of `ℤv₁ + ℤv₂`, for a basis `(v₁, v₂)`, is
diffeomorphic to `ℝ/ℤ × ℝ/ℤ`. -/
theorem nonempty_diffeomorph_addCircle_prod_of_periodic_cover (hdim : Module.finrank ℝ E = 2)
    {cov : E → M} (hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov) (hsurj : Surjective cov)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂])
    (hfib : ∀ y z, cov y = cov z ↔ ∃ m n : ℤ, z - y = m • v₁ + n • v₂) :
    Nonempty (M ≃ₘ⟮I, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  let b : Module.Basis (Fin 2) ℝ E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = v₁ := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = v₂ := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  let c₁ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 0)
  let c₂ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 1)
  have hrepr : ∀ z, c₁ z • v₁ + c₂ z • v₂ = z := by
    intro z
    have h := b.sum_repr z
    rw [Fin.sum_univ_two, hb0, hb1] at h
    exact h
  have hc : ∀ s t : ℝ, c₁ (s • v₁ + t • v₂) = s ∧ c₂ (s • v₁ + t • v₂) = t := by
    intro s t
    have h1 : b.repr (s • v₁ + t • v₂) = Finsupp.single 0 s + Finsupp.single 1 t := by
      rw [← hb0, ← hb1, map_add, map_smul, map_smul, b.repr_self, b.repr_self,
        Finsupp.smul_single_one, Finsupp.smul_single_one]
    refine ⟨?_, ?_⟩
    · change b.repr (s • v₁ + t • v₂) 0 = s
      rw [h1]
      simp
    · change b.repr (s • v₁ + t • v₂) 1 = t
      rw [h1]
      simp
  let pair : E → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := fun z =>
    ((c₁ z : AddCircle (1 : ℝ)), (c₂ z : AddCircle (1 : ℝ)))
  have h₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (c₁ z : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp c₁.contDiff.contMDiff
  have h₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (c₂ z : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp c₂.contDiff.contMDiff
  have hpair_s : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ pair := h₁.prodMk h₂
  have hpair_inj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) pair y) := by
    intro y u u' h
    rw [mfderiv_prodMk (h₁.mdifferentiableAt (by simp)) (h₂.mdifferentiableAt (by simp))] at h
    have e1 := injective_mfderiv_coe_comp c₁ y u u' (congrArg Prod.fst h)
    have e2 := injective_mfderiv_coe_comp c₂ y u u' (congrArg Prod.snd h)
    rw [← hrepr u, ← hrepr u', e1, e2]
  have hpair : IsLocalDiffeomorph 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ pair :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv pair hpair_s
      hpair_inj (by simp [hdim])
  have hpsurj : Surjective pair := by
    rintro ⟨x₁, x₂⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x₁
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x₂
    refine ⟨s • v₁ + t • v₂, ?_⟩
    simp only [pair, (hc s t).1, (hc s t).2]
  have hpair_eq : ∀ y z, pair y = pair z ↔ ∃ m n : ℤ, z - y = m • v₁ + n • v₂ := by
    intro y z
    simp only [pair, Prod.mk.injEq, addCircle_coe_eq_coe_iff]
    constructor
    · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
      refine ⟨m, n, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, ← hm, ← hn, sub_smul, sub_smul]
      conv_lhs => rw [← hrepr z, ← hrepr y]
      abel
    · rintro ⟨m, n, hmn⟩
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at hmn
      have hz : z = y + ((m : ℝ) • v₁ + (n : ℝ) • v₂) := by rw [← hmn]; abel
      have hcz := hc (c₁ y + m) (c₂ y + n)
      have hz' : (c₁ y + m) • v₁ + (c₂ y + n) • v₂ = z := by
        rw [hz, add_smul, add_smul]
        conv_rhs => rw [← hrepr y]
        abel
      rw [hz'] at hcz
      exact ⟨⟨m, by rw [hcz.1]; ring⟩, ⟨n, by rw [hcz.2]; ring⟩⟩
  have hcompat : ∀ y z, cov y = cov z ↔ pair y = pair z := fun y z => by
    rw [hfib, hpair_eq]
  let φ : M → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := fun q => pair (surjInv hsurj q)
  let ψ : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → M := fun x => cov (surjInv hpsurj x)
  have hφcov : ∀ z, φ (cov z) = pair z := fun z => (hcompat _ _).mp (surjInv_eq hsurj (cov z))
  have hψp : ∀ z, ψ (pair z) = cov z := fun z => (hcompat _ _).mpr (surjInv_eq hpsurj (pair z))
  have hφs : ContMDiff I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ φ := by
    refine hcov.contMDiff_of_comp_of_surjective hsurj ?_
    have h : φ ∘ cov = pair := funext hφcov
    rw [h]
    exact hpair_s
  have hψs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ ψ := by
    refine hpair.contMDiff_of_comp_of_surjective hpsurj ?_
    have h : ψ ∘ pair = cov := funext hψp
    rw [h]
    exact hcov.contMDiff
  have hleft : LeftInverse ψ φ := by
    intro q
    obtain ⟨z, rfl⟩ := hsurj q
    rw [hφcov, hψp]
  have hright : RightInverse ψ φ := by
    intro x
    obtain ⟨z, rfl⟩ := hpsurj x
    rw [hψp, hφcov]
  exact ⟨{ toEquiv := ⟨φ, ψ, hleft, hright⟩, contMDiff_toFun := hφs, contMDiff_invFun := hψs }⟩

end Descent

end DifferentialGeometry.Geometry.FlatSurface

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **SF4(c), periodic cover.** A compact connected orientable smooth flat surface has a periodic
covering by its model plane: `exp_p` is an onto covering local diffeomorphism whose fibres are the
cosets of `ℤv₁ + ℤv₂` for a basis `(v₁, v₂)`. -/
theorem exists_periodic_cover_of_flat (hdim : Module.finrank ℝ E = 2) [CompactSpace M]
    [ConnectedSpace M] (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0) :
    ∃ (cov : E → M) (v₁ v₂ : E), IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov ∧ IsCoveringMap cov ∧
      Surjective cov ∧ LinearIndependent ℝ ![v₁, v₂] ∧
      ∀ y z : E, cov y = cov z ↔ ∃ m n : ℤ, z - y = m • v₁ + n • v₂ := by
  obtain ⟨p⟩ : Nonempty M := inferInstance
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  obtain ⟨hloc, -, hcovF, hsurj⟩ :=
    flat_expMapIntrinsic_isLocalIsometry_isCoveringMap (I := I) g hEnorm hR p
  obtain ⟨Λ, hdisc, hfibΛ⟩ := flat_exists_translationLattice (I := I) hdim o g hEnorm hR p
  -- compactness of `M` makes the lattice cocompact
  have hopen : ∀ n : ℕ, IsOpen (F '' Metric.ball (0 : E) n) := fun n =>
    hloc.isOpenMap _ Metric.isOpen_ball
  have hcover : (univ : Set M) ⊆ ⋃ n : ℕ, F '' Metric.ball (0 : E) n := by
    intro q _
    obtain ⟨y, rfl⟩ := hsurj q
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact mem_iUnion.mpr ⟨n, y, mem_ball_zero_iff.mpr hn, rfl⟩
  have hmono : Monotone fun n : ℕ => F '' Metric.ball (0 : E) n := fun a c hac =>
    image_mono (Metric.ball_subset_ball (by exact_mod_cast hac))
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover _ hopen hcover hmono.directed_le
  have hcocpt : ∀ y : E, ∃ l ∈ Λ.toIntSubmodule, ‖y - l‖ ≤ n := by
    intro y
    obtain ⟨z, hz, hFz⟩ := hn (mem_univ (F y))
    refine ⟨y - z, (hfibΛ z y).mp hFz, ?_⟩
    rw [sub_sub_cancel]
    exact (mem_ball_zero_iff.mp hz).le
  have : DiscreteTopology Λ.toIntSubmodule := hdisc
  obtain ⟨b, hb⟩ :=
    DifferentialGeometry.Geometry.FlatSurface.exists_basis_span_eq_of_discrete_of_cocompact
      Λ.toIntSubmodule hcocpt
  let b₂ := b.reindex (finCongr hdim)
  have hrange : Set.range b = {b₂ 0, b₂ 1} := by
    rw [← b.range_reindex (finCongr hdim)]
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  refine ⟨F, b₂ 0, b₂ 1, hloc, hcovF, hsurj, ?_, ?_⟩
  · have h := b₂.linearIndependent
    convert h using 1
    ext i
    fin_cases i <;> rfl
  · intro y z
    rw [hfibΛ y z]
    change z - y ∈ Λ.toIntSubmodule ↔ _
    rw [← hb, hrange, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, k, h⟩
      exact ⟨m, k, h.symm⟩
    · rintro ⟨m, k, h⟩
      exact ⟨m, k, h.symm⟩

/-- **SF4(c).** A compact connected orientable smooth flat surface is diffeomorphic to the torus
`ℝ/ℤ × ℝ/ℤ`. -/
theorem nonempty_diffeomorph_addCircle_prod_of_flat (hdim : Module.finrank ℝ E = 2)
    [CompactSpace M] [ConnectedSpace M] (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0) :
    Nonempty (M ≃ₘ⟮I, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  obtain ⟨cov, v₁, v₂, hloc, -, hsurj, hli, hfib⟩ :=
    exists_periodic_cover_of_flat hdim o g hEnorm hR
  exact DifferentialGeometry.Geometry.FlatSurface.nonempty_diffeomorph_addCircle_prod_of_periodic_cover
    hdim hloc hsurj hli hfib

end DifferentialGeometry.Geometry.Riemannian.Exponential
