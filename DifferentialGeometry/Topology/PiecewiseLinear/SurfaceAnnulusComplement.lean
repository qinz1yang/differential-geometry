/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusComplement
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusEuler
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.Connected.BicollarComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_annulus_complement_of_isOrientable
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hU : U ∈ 𝓝ˢ[K.space] J) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsOrientable 2 R ∧
      eulerChar R = eulerChar K ∧
      ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧ W ⊆ K.space ∧ W ⊆ U ∧
        W ∈ 𝓝ˢ[K.space] J ∧ IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧
        (∀ x ∈ J, ρ (x, 0) = x) ∧ R.space = closure (K.space \ W) ∧
        R.space ⊆ K.space \ J ∧
        (boundaryComplex 2 R).space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) ∧
        W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) ∧ W ∪ R.space = K.space ∧
        IsPLSphere 1 (ρ '' (J ×ˢ {(-1 : ℝ)})) ∧ IsPLSphere 1 (ρ '' (J ×ˢ {(1 : ℝ)})) ∧
        Disjoint (ρ '' (J ×ˢ {(-1 : ℝ)})) (ρ '' (J ×ˢ {(1 : ℝ)})) ∧
        (IsPreconnected (K.space \ J) → IsConnected R.space) := by
  obtain ⟨W, ρ, hW, hWK, hWU, hWnhds, hρ, hzero⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ hJK hU
  obtain ⟨A, R, hAfin, hRfin, hA, hR, hAspace, hRspace, -, hRbd, hmeet, hcover⟩ :=
    hK.exists_annulus_complement K hJ (by norm_num : (-1 : ℝ) < 1) hρ hWK
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite R.faces := hRfin.to_subtype
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hRo : IsOrientable 2 R :=
    hor.of_space_subset K R hRK hK.isCombinatorialManifoldWithBoundary hR
  have hmeetW : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by rwa [hAspace] at hmeet
  have hcoverW : W ∪ R.space = K.space := by rwa [hAspace] at hcover
  have hRc (hnonsep : IsPreconnected (K.space \ J)) : IsConnected R.space :=
    Topology.isConnected_complement_of_bicollar
    hJ.isConnected hJ.isPolyhedron.isCompact (isPolyhedron_space R).isClosed
    (by rwa [union_comm]) (by rwa [inter_comm])
    hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hnonsep
  have hRχ : eulerChar R = eulerChar K :=
    eulerChar_eq_of_annulus_complement K A R hJ (by norm_num : (-1 : ℝ) < 1)
      (hAspace.symm ▸ hρ) hcover hmeet
  have hRJ : Disjoint R.space J := by
    apply disjoint_left.mpr
    intro x hxR hxJ
    obtain ⟨O, hO, hJO, hOW⟩ := mem_nhdsSetWithin.mp hWnhds
    rw [hRspace] at hxR
    obtain ⟨y, hyO, hyK, hyW⟩ := mem_closure_iff.mp hxR O hO (hJO hxJ)
    exact hyW (hOW ⟨hyO, hyK⟩)
  have hleft : J ×ˢ {(-1 : ℝ)} ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, by norm_num⟩⟩
  have hright : J ×ˢ {(1 : ℝ)} ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩
  have hJ₀ : IsPLSphere 1 (ρ '' (J ×ˢ {(-1 : ℝ)})) := hJ.of_isPLHomeomorphOn
    ((hJ.isPolyhedron.isPLHomeomorphOn_prod_const (-1 : ℝ)).trans
      (hρ.restrict (isPolyhedron_prod_singleton hJ.isPolyhedron (-1 : ℝ)) hleft))
  have hJ₁ : IsPLSphere 1 (ρ '' (J ×ˢ {(1 : ℝ)})) := hJ.of_isPLHomeomorphOn
    ((hJ.isPolyhedron.isPLHomeomorphOn_prod_const (1 : ℝ)).trans
      (hρ.restrict (isPolyhedron_prod_singleton hJ.isPolyhedron (1 : ℝ)) hright))
  have hdis : Disjoint (ρ '' (J ×ˢ {(-1 : ℝ)})) (ρ '' (J ×ˢ {(1 : ℝ)})) := by
    apply disjoint_left.mpr
    rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
    have heq := hρ.bijOn.injOn (hleft hu) (hright hv) (hux.trans hvx.symm)
    have ht := hu.2.symm.trans ((congrArg Prod.snd heq).trans hv.2)
    norm_num at ht
  exact ⟨R, hRfin, hR, hRo, hRχ, W, ρ, hW, hWK, hWU, hWnhds, hρ, hzero,
    hRspace, fun x hx => ⟨hRK hx, fun hxJ => disjoint_left.mp hRJ hx hxJ⟩,
    hRbd, hmeetW, hcoverW, hJ₀, hJ₁, hdis, hRc⟩

open Classical in
theorem IsCombinatorialManifold.exists_connected_annulus_complement
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hnonsep : IsPreconnected (K.space \ J)) (hU : U ∈ 𝓝ˢ[K.space] J) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsOrientable 2 R ∧ IsConnected R.space ∧
      eulerChar R = eulerChar K ∧
      ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧ W ⊆ K.space ∧ W ⊆ U ∧
        W ∈ 𝓝ˢ[K.space] J ∧ IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧
        (∀ x ∈ J, ρ (x, 0) = x) ∧ R.space = closure (K.space \ W) ∧
        R.space ⊆ K.space \ J ∧
        (boundaryComplex 2 R).space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) ∧
        W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) ∧ W ∪ R.space = K.space ∧
        IsPLSphere 1 (ρ '' (J ×ˢ {(-1 : ℝ)})) ∧ IsPLSphere 1 (ρ '' (J ×ˢ {(1 : ℝ)})) ∧
        Disjoint (ρ '' (J ×ˢ {(-1 : ℝ)})) (ρ '' (J ×ˢ {(1 : ℝ)})) := by
  obtain ⟨R, hRfin, hR, hRo, hRχ, W, ρ, hW, hWK, hWU, hWnhds, hρ, hzero,
      hRspace, hRK, hRbd, hmeet, hcover, hJ₀, hJ₁, hdis, hRc⟩ :=
    hK.exists_annulus_complement_of_isOrientable K hor hJ hJK hU
  exact ⟨R, hRfin, hR, hRo, hRc hnonsep, hRχ, W, ρ, hW, hWK, hWU, hWnhds, hρ, hzero,
    hRspace, hRK, hRbd, hmeet, hcover, hJ₀, hJ₁, hdis⟩

end DifferentialGeometry.Topology.PiecewiseLinear
