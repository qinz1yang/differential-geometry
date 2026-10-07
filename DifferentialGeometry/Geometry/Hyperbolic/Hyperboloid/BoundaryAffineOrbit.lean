import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryRegularity
import Mathlib.Topology.Algebra.ConstMulAction
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryZoomLimit
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryConjugation
import DifferentialGeometry.Geometry.Affine.HomothetyLimits
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Module

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

private theorem exists_compact_quotient_returns_of_conjugated_compact_returns
    {X G : Type*} [PseudoMetricSpace X] [Group G]
    (ρ : G →* (X ≃ᵢ X)) (B : X ≃ᵢ X) (x : ℕ → X) (γ : ℕ → G)
    (D : Set X) (hD : IsCompact D)
    (hreturn : ∀ n, ρ (γ n) (B (x n)) ∈ D) :
    let ρB := (MulAut.conj B.symm).toMonoidHom.comp ρ
    letI : MulAction G X := MulAction.compHom X ρB
    ∃ K : Set (MulAction.orbitRel.Quotient G X), IsCompact K ∧
      ∀ n, Quotient.mk (MulAction.orbitRel G X) (x n) ∈ K := by
  intro ρB
  let : MulAction G X := MulAction.compHom X ρB
  let π : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X)
  refine ⟨π '' (B.symm '' D), (hD.image B.symm.continuous).image continuous_quotient_mk', ?_⟩
  intro n
  refine ⟨B.symm (ρ (γ n) (B (x n))), ⟨ρ (γ n) (B (x n)), hreturn n, rfl⟩, ?_⟩
  apply Quotient.sound
  exact ⟨γ n, rfl⟩

private theorem lineDeriv_ne_zero_of_affine_direction
    (h : ℂ ≃ₜ ℂ) (v : ℂ) (hv : v ≠ 0)
    (hline : ∀ (x : ℂ) (t : ℝ),
      h (x + t • v) = h x + t • (h (x + v) - h x)) (x : ℂ) :
    lineDeriv ℝ h x v ≠ 0 := by
  have hder : HasLineDerivAt ℝ h (h (x + v) - h x) x v := by
    change HasDerivAt (fun t : ℝ => h (x + t • v)) (h (x + v) - h x) 0
    simp_rw [hline]
    simpa only [one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (h (x + v) - h x)).const_add (h x)
  rw [hder.lineDeriv]
  intro hz
  exact hv (add_eq_left.mp (h.injective (sub_eq_zero.mp hz)))

private theorem lineDeriv_ne_zero_on_affine_pencil
    (h : ℂ ≃ₜ ℂ) (p v : ℂ) (hv : v ≠ 0)
    (hpencil : ∀ (u : ℂ) (t : ℝ),
      h (p + t • u) = h p + t • (h (p + u) - h p)) (r : ℝ) :
    lineDeriv ℝ h (p + r • v) v ≠ 0 := by
  have hder : HasLineDerivAt ℝ h (h (p + v) - h p) (p + r • v) v := by
    change HasDerivAt (fun t : ℝ => h ((p + r • v) + t • v)) (h (p + v) - h p) 0
    have heq : (fun t : ℝ => h ((p + r • v) + t • v)) =
        fun t : ℝ => h (p + r • v) + t • (h (p + v) - h p) := by
      funext t
      have harg : (p + r • v) + t • v = p + (r + t) • v := by module
      rw [harg, hpencil, hpencil]
      module
    rw [heq]
    simpa only [one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (h (p + v) - h p)).const_add (h (p + r • v))
  rw [hder.lineDeriv]
  intro hz
  exact hv (add_eq_left.mp (h.injective (sub_eq_zero.mp hz)))

private theorem dense_rational_directions (h : ℂ → ℂ) (z : ℂ)
    (hd : ∀ p q : ℚ, LineDifferentiableAt ℝ h z
      (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)) :
    Dense {v : ℂ | LineDifferentiableAt ℝ h z v} := by
  have hrat : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hcomplex := Complex.equivRealProdCLM.symm.surjective.denseRange.comp hrat
    Complex.equivRealProdCLM.symm.continuous
  apply hcomplex.mono
  rintro _ ⟨⟨p, q⟩, rfl⟩
  change LineDifferentiableAt ℝ h z (Complex.equivRealProdCLM.symm ((p : ℝ), (q : ℝ)))
  simpa only [Complex.equivRealProdCLM_symm_apply] using! hd p q

private theorem exists_not_mem_countable_on_line
    (E : Set ℂ) (hE : E.Countable) (z v : ℂ) (hv : v ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ z + t • v ∉ E := by
  have hinj : Function.Injective (fun t : ℝ => z + t • v) := by
    intro s t hst
    exact smul_left_injective ℝ hv (add_left_cancel hst)
  have hcount : (insert (0 : ℝ) ((fun t : ℝ => z + t • v) ⁻¹' E)).Countable :=
    (hE.preimage hinj).insert 0
  have hne : insert (0 : ℝ) ((fun t : ℝ => z + t • v) ⁻¹' E) ≠ Set.univ := by
    intro heq
    exact Set.not_countable_univ (heq ▸ hcount)
  obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  exact ⟨t, fun ht0 => ht (Set.mem_insert_iff.mpr (Or.inl ht0)),
    fun htE => ht (Set.mem_insert_iff.mpr (Or.inr htE))⟩

local notation "H3" => Hyperboloid (EuclideanSpace ℝ (Fin 3))

private theorem exists_regular_outside_countable
    (f g : C(H3, H3))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
    (hgf : ∃ C : ℝ, ∀ x : H3, dist (g (f x)) x ≤ C)
    (hfg : ∃ C : ℝ, ∀ x : H3, dist (f (g x)) x ≤ C)
    (hnorth : boundaryMap f hf sphereNorthPole = sphereNorthPole)
    (E : Set ℂ) (hE : E.Countable) :
    let h := boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth
    ∃ z : ℂ, z ∉ E ∧ Dense {v : ℂ | LineDifferentiableAt ℝ h z v} ∧
      lineDeriv ℝ h z (1 : ℂ) ≠ 0 := by
  intro h
  obtain ⟨_, hpos⟩ :=
    volume_pos_rational_lineDifferentiableAt_and_lineDeriv_ne_zero_boundaryPlaneHomeomorph
      f g hf hg hgf hfg hnorth 0 1 0 1 zero_lt_one zero_lt_one
  have hnull : MeasureTheory.volume E = 0 := hE.measure_zero MeasureTheory.volume
  have hae := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull
  obtain ⟨z, hz, hzE⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (MeasureTheory.ae_restrict_of_ae hae)
  exact ⟨z, hzE, dense_rational_directions h z hz.2.2.1, hz.2.2.2⟩

private def homothetyZoom (h : ℂ ≃ₜ ℂ) (z : ℂ) (s : ℝ) : C(ℂ, ℂ) :=
  ⟨fun w => h z + s • (h (z + s⁻¹ • (w - z)) - h z), by fun_prop⟩

private theorem prepost_equivariant {G : Type*} [Group G]
    (ρ σ : G →* (H3 ≃ᵢ H3)) (f : C(H3, H3))
    (hequiv : ∀ γ x, f (ρ γ x) = σ γ (f x)) (A B : H3 ≃ᵢ H3) (γ : G) (x : H3) :
    ((A : C(H3, H3)).comp (f.comp (B : C(H3, H3))))
        (((MulAut.conj B.symm).toMonoidHom.comp ρ) γ x) =
      ((MulAut.conj A).toMonoidHom.comp σ) γ
        (((A : C(H3, H3)).comp (f.comp (B : C(H3, H3)))) x) := by
  change A (f (B (B.symm (ρ γ (B x))))) = A (σ γ (A.symm (A (f (B x)))))
  rw [B.apply_symm_apply, A.symm_apply_apply, hequiv]

theorem exists_affineEquiv_boundary_conjugate_of_compact_returns
    {G : Type*} [Group G] (ρ σ : G →* (H3 ≃ᵢ H3))
    (f g : C(H3, H3))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
    (hgf : ∃ C : ℝ, ∀ x : H3, dist (g (f x)) x ≤ C)
    (hfg : ∃ C : ℝ, ∀ x : H3, dist (f (g x)) x ≤ C)
    (hnorth : boundaryMap f hf sphereNorthPole = sphereNorthPole)
    (hequiv : ∀ γ x, f (ρ γ x) = σ γ (f x))
    (E : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (hE : E.Countable)
    (hreturns : ∀ (B : H3 ≃ᵢ H3) (z : ℂ),
      boundaryHomeomorph B (stereographicComplex.symm z).val ∉ E →
      ∃ (s : ℕ → ℝ) (hs : ∀ n, 0 < s n),
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∃ (γ : ℕ → G) (D : Set H3), IsCompact D ∧ ∀ n,
          ρ (γ n) (B
            ((((boundaryTranslation (-z)).trans
              (boundarySimilarity (((s n)⁻¹ : ℝ) : ℂ)
                (Complex.ofReal_ne_zero.mpr (inv_ne_zero (hs n).ne')))).trans
              (boundaryTranslation z)) origin)) ∈ D) :
    ∃ (A B : H3 ≃ᵢ H3) (e : ℂ ≃ᵃ[ℝ] ℂ),
      boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B sphereNorthPole)) = sphereNorthPole ∧
      ∀ z : ℂ, (stereographicComplex.symm (e z)).val =
        boundaryHomeomorph A
          (boundaryMap f hf (boundaryHomeomorph B (stereographicComplex.symm z).val)) := by
  classical
  let S : Set (ℂ ≃ₜ ℂ) := {H | ∃ A B : H3 ≃ᵢ H3,
    boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B sphereNorthPole)) = sphereNorthPole ∧
    ∀ z : ℂ, (stereographicComplex.symm (H z)).val =
      boundaryHomeomorph A
        (boundaryMap f hf (boundaryHomeomorph B (stereographicComplex.symm z).val))}
  have hproduce (H : ℂ ≃ₜ ℂ) (hH : H ∈ S) :
      ∃ T : Set ℂ, T.Countable ∧
        (∃ z : ℂ, z ∉ T ∧ Dense {v : ℂ | LineDifferentiableAt ℝ H z v} ∧
          lineDeriv ℝ H z (1 : ℂ) ≠ 0) ∧
        ∀ z : ℂ, z ∉ T → lineDeriv ℝ H z (1 : ℂ) ≠ 0 →
          ∃ (s : ℕ → ℝ) (H' : ℂ ≃ₜ ℂ),
            Filter.Tendsto s Filter.atTop Filter.atTop ∧ H' ∈ S ∧
            Filter.Tendsto (fun n => homothetyZoom H z (s n)) Filter.atTop (𝓝 (H' : C(ℂ, ℂ))) := by
    obtain ⟨A, B, hN, hchart⟩ := hH
    let F := (A : C(H3, H3)).comp (f.comp (B : C(H3, H3)))
    let J := (B.symm : C(H3, H3)).comp (g.comp (A.symm : C(H3, H3)))
    obtain ⟨hF, hJ, hJF, hFJ, hboundary⟩ :=
      exists_boundaryHomeomorphOfCoarseInverse_isometry_conjugate f g A B hf hg hgf hfg
    have hmap (ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        boundaryMap F hF ξ = boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B ξ)) :=
      congrArg (fun Q => Q ξ) hboundary
    have hNF : boundaryMap F hF sphereNorthPole = sphereNorthPole := (hmap _).trans hN
    have hplane : boundaryPlaneHomeomorph F J hF hJ hJF hFJ hNF = H := by
      apply Homeomorph.ext
      intro z
      apply stereographicComplex.symm.injective
      apply Subtype.ext
      rw [stereographicComplex_symm_boundaryPlaneHomeomorph, hmap, hchart]
    let T := (fun z : ℂ => boundaryHomeomorph B (stereographicComplex.symm z).val) ⁻¹' E
    have hT : T.Countable := hE.preimage
      ((boundaryHomeomorph B).injective.comp (Subtype.val_injective.comp stereographicComplex.symm.injective))
    obtain ⟨z, hzT, hzd, hzn⟩ := exists_regular_outside_countable F J hF hJ hJF hFJ hNF T hT
    rw [hplane] at hzd hzn
    refine ⟨T, hT, ⟨z, hzT, hzd, hzn⟩, ?_⟩
    intro w hw hne
    obtain ⟨s, hs, hstop, γ, D, hD, hDreturns⟩ := hreturns B w hw
    let b (n : ℕ) : H3 ≃ᵢ H3 :=
      ((boundaryTranslation (-w)).trans
        (boundarySimilarity (((s n)⁻¹ : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (inv_ne_zero (hs n).ne')))).trans (boundaryTranslation w)
    let ρB := (MulAut.conj B.symm).toMonoidHom.comp ρ
    let σA := (MulAut.conj A).toMonoidHom.comp σ
    let : MulAction G H3 := MulAction.compHom H3 ρB
    obtain ⟨K, hK, hKreturns⟩ :=
      exists_compact_quotient_returns_of_conjugated_compact_returns ρ B (fun n => b n origin)
        γ D hD hDreturns
    have hneF : lineDeriv ℝ (boundaryPlaneHomeomorph F J hF hJ hJF hFJ hNF) w (1 : ℂ) ≠ 0 := by
      rwa [hplane]
    obtain ⟨k, C, D, H', hk, _, hN', hchart', hlim⟩ :=
      exists_homothety_plane_homeomorph_limit_of_compact_quotient_returns
        ρB σA F J hF hJ hJF hFJ hNF (prepost_equivariant ρ σ f hequiv A B)
        w hneF s hs hstop K hK hKreturns
    refine ⟨fun n => s (k n), H', hstop.comp hk.tendsto_atTop, ?_, ?_⟩
    · refine ⟨A.trans C, D.trans B, ?_, ?_⟩
      · simpa only [boundaryHomeomorph_trans, Homeomorph.trans_apply, hmap] using hN'
      · intro x
        simpa only [boundaryHomeomorph_trans, Homeomorph.trans_apply, hmap] using hchart' x
    · simpa only [hplane, homothetyZoom] using hlim
  let h₀ := boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth
  have h₀S : h₀ ∈ S := by
    refine ⟨IsometryEquiv.refl H3, IsometryEquiv.refl H3, ?_, ?_⟩
    · simpa only [boundaryHomeomorph_refl, Homeomorph.refl_apply, id_eq] using hnorth
    · intro z
      simpa only [boundaryHomeomorph_refl, Homeomorph.refl_apply, id_eq] using
        stereographicComplex_symm_boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth z
  obtain ⟨T₀, _, ⟨z₁, hz₁, hd₁, hn₁⟩, hreturn₀⟩ := hproduce h₀ h₀S
  obtain ⟨s₁, h₁, hs₁, hh₁S, hlim₁⟩ := hreturn₀ z₁ hz₁ hn₁
  have hpoint₁ (x : ℂ) := hlim₁.eval_const x
  have hradial₁ := h₁.continuous.homothety_limit_eq_add_smul
    (h := (h₀ : ℂ → ℂ)) (z := z₁) s₁ hs₁ hd₁ hpoint₁
  have hcenter₁ : h₁ z₁ = h₀ z₁ := by
    simpa only [zero_smul, add_zero] using hradial₁ (0 : ℂ) 0
  have hpencil₁ (v : ℂ) (t : ℝ) :
      h₁ (z₁ + t • v) = h₁ z₁ + t • (h₁ (z₁ + v) - h₁ z₁) := by
    rw [hcenter₁]
    exact hradial₁ v t
  obtain ⟨T₁, hT₁, _, hreturn₁⟩ := hproduce h₁ hh₁S
  obtain ⟨t₁, ht₁, hw₁⟩ := exists_not_mem_countable_on_line T₁ hT₁ z₁ 1 one_ne_zero
  let w₁ := z₁ + t₁ • (1 : ℂ)
  have hn₂ : lineDeriv ℝ h₁ w₁ (1 : ℂ) ≠ 0 :=
    lineDeriv_ne_zero_on_affine_pencil h₁ z₁ 1 one_ne_zero hpencil₁ t₁
  obtain ⟨s₂, h₂, hs₂, hh₂S, hlim₂⟩ := hreturn₁ w₁ hw₁ hn₂
  have hparallel₂ := ContinuousMap.map_add_smul_eq_of_tendsto_homothety
    (h₁ : C(ℂ, ℂ)) z₁ w₁ s₂ hpencil₁ hs₂ (fun _ _ => rfl) hlim₂
  obtain ⟨T₂, _, ⟨z₂, hz₂, hd₃, hn₃⟩, hreturn₂⟩ := hproduce h₂ hh₂S
  obtain ⟨s₃, h₃, hs₃, hh₃S, hlim₃⟩ := hreturn₂ z₂ hz₂ hn₃
  have hparallel₃ := ContinuousMap.affine_direction_of_tendsto_homothety
    (h₂ : ℂ → ℂ) z₂ (w₁ - z₁) s₃ hparallel₂ (fun _ _ => rfl) hlim₃
  obtain ⟨T₃, hT₃, _, hreturn₃⟩ := hproduce h₃ hh₃S
  obtain ⟨t₂, ht₂, hw₂⟩ := exists_not_mem_countable_on_line T₃ hT₃ z₂ Complex.I Complex.I_ne_zero
  let w₂ := z₂ + t₂ • Complex.I
  have hdirection : w₁ - z₁ = t₁ • (1 : ℂ) := by dsimp [w₁]; abel
  have hv₁ : w₁ - z₁ ≠ 0 := by
    rw [hdirection]
    exact smul_ne_zero ht₁ one_ne_zero
  have hn₄ : lineDeriv ℝ h₃ w₂ (1 : ℂ) ≠ 0 := by
    have hnonzero := lineDeriv_ne_zero_of_affine_direction h₃ (w₁ - z₁) hv₁ hparallel₃ w₂
    rw [hdirection, lineDeriv_smul] at hnonzero
    intro hzero
    exact hnonzero (by rw [hzero, smul_zero])
  obtain ⟨s₄, h₄, hs₄, hh₄S, hlim₄⟩ := hreturn₃ w₂ hw₂ hn₄
  have hind : LinearIndependent ℝ ![w₁ - z₁, w₂ - z₂] := by
    have hi : LinearIndependent ℝ ![(1 : ℂ), Complex.I] := by
      simpa only [Complex.coe_basisOneI] using Complex.basisOneI.linearIndependent
    have hdiff₂ : w₂ - z₂ = t₂ • Complex.I := by dsimp [w₂]; abel
    rw [hdirection, hdiff₂]
    exact (LinearIndependent.pair_smul_smul_iff (Ne.isUnit ht₁) (Ne.isUnit ht₂)).mpr hi
  obtain ⟨e, he⟩ := DifferentialGeometry.Geometry.Affine.exists_affineEquiv_of_homothety_limits
    Complex.finrank_real_complex (h₀ : ℂ → ℂ)
    (h₁ : C(ℂ, ℂ)) (h₂ : C(ℂ, ℂ)) (h₃ : C(ℂ, ℂ)) (h₄ : C(ℂ, ℂ))
    z₁ w₁ z₂ w₂ s₁ s₂ s₃ s₄
    (fun n => homothetyZoom h₀ z₁ (s₁ n)) (fun n => homothetyZoom h₁ w₁ (s₂ n))
    (fun n => homothetyZoom h₂ z₂ (s₃ n)) (fun n => homothetyZoom h₃ w₂ (s₄ n))
    hs₁ hs₂ hs₃ hs₄ hd₁ hd₃ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) hlim₁ hlim₂ hlim₃ hlim₄ hind h₄.injective
  obtain ⟨A, B, hN, hchart⟩ := hh₄S
  refine ⟨A, B, e, hN, ?_⟩
  intro z
  rw [he]
  exact hchart z

end DifferentialGeometry.Hyperboloid
