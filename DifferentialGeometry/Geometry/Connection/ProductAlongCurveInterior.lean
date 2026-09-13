import DifferentialGeometry.Geometry.Connection.ProductAlongCurve
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Type*} [TopologicalSpace K] {I' : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold I' ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem mdifferentiableAt_tangentBundle_prod {γ : ℝ → M} {γ' : ℝ → N}
    {Z : ∀ t, TangentSpace I (γ t)} {Z' : ∀ t, TangentSpace I' (γ' t)} {x : ℝ}
    (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun u => (⟨γ u, Z u⟩ : TangentBundle I M)) x)
    (hZ' : MDifferentiableAt 𝓘(ℝ, ℝ) I'.tangent
      (fun u => (⟨γ' u, Z' u⟩ : TangentBundle I' N)) x) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod I').tangent
      (fun u => (⟨(γ u, γ' u), (Z u, Z' u)⟩ : TangentBundle (I.prod I') (M × N))) x := by
  have hpair : MDifferentiableAt 𝓘(ℝ, ℝ) (I.tangent.prod I'.tangent)
      (fun u => ((⟨γ u, Z u⟩ : TangentBundle I M),
        (⟨γ' u, Z' u⟩ : TangentBundle I' N))) x := hZ.prodMk hZ'
  have hsm : ∀ y : TangentBundle I M × TangentBundle I' N,
      MDifferentiableAt (I.tangent.prod I'.tangent) (I.prod I').tangent
        ⇑(equivTangentBundleProd I M I' N).symm y := fun y =>
    (contMDiff_equivTangentBundleProd_symm (I := I) (I' := I') (M := M) (M' := N)
      (n := ∞)).mdifferentiable (by simp) y
  exact (MDifferentiableAt.comp x (hsm _) hpair).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => rfl)

theorem covDerivAlong_prod_of_isInteriorPoint [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (g' : SmoothRiemannianMetric I' N)
    (γ : ℝ → M) (γ' : ℝ → N)
    (Z : ∀ t, TangentSpace I (γ t)) (Z' : ∀ t, TangentSpace I' (γ' t)) (x : ℝ)
    (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun u => (⟨γ u, Z u⟩ : TangentBundle I M)) x)
    (hZ' : MDifferentiableAt 𝓘(ℝ, ℝ) I'.tangent
      (fun u => (⟨γ' u, Z' u⟩ : TangentBundle I' N)) x)
    (hint : I.IsInteriorPoint (γ x)) (hint' : I'.IsInteriorPoint (γ' x)) :
    covDerivAlong (g.prod g') (fun u => (γ u, γ' u)) (fun u => (Z u, Z' u)) x =
      (covDerivAlong g γ Z x, covDerivAlong g' γ' Z' x) := by
  have hpair := mdifferentiableAt_tangentBundle_prod (I := I) (I' := I') hZ hZ'
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
    ((mdifferentiableAt_totalSpace I _).mp hZ).1
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) I' γ' x :=
    ((mdifferentiableAt_totalSpace I' _).mp hZ').1
  have h₁ := derivAlongWithin_leviCivita_eq_covDerivAlong g γ Z Filter.univ_mem hγ hint
  have h₂ := derivAlongWithin_leviCivita_eq_covDerivAlong g' γ' Z' Filter.univ_mem hγ' hint'
  have hpairBase : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) x :=
    ((mdifferentiableAt_totalSpace (I.prod I') _).mp hpair).1
  have hintProd : (I.prod I').IsInteriorPoint (γ x, γ' x) := by
    have h : (γ x, γ' x) ∈ (I.prod I').interior (M × N) := by
      rw [ModelWithCorners.interior_prod]
      exact ⟨hint, hint'⟩
    exact h
  have h₃ := derivAlongWithin_leviCivita_eq_covDerivAlong (g.prod g')
    (fun u => (γ u, γ' u)) (fun u => (Z u, Z' u)) Filter.univ_mem hpairBase hintProd
  have hsplit := derivAlongWithin_prod (s := Set.univ) g g' γ γ' Z Z'
    (hZ.mdifferentiableWithinAt (s := Set.univ))
    (hZ'.mdifferentiableWithinAt (s := Set.univ))
  rw [← h₃, hsplit, h₁, h₂]

end DifferentialGeometry.Geometry.Connection
