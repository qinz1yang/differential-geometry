import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMap
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulTube
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamBundle
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseApplications

/-!
# Consumers of the restated LFR46 (lane CMS3-FLOW2, G2)

* `exists_finite_normalFlowMap_tube_radius`: for the SAME `X, φ, e`, the zero section goes onto `S`,
  and the fibre radius `u x = |e⁻¹ x|` is `d_S` on `{d_S ≤ ℓ}` and `ℓ − τ x` outside (the radius
  identity LFR49 consumes).
* `exists_finite_normalFlowMap_surface`: the same-witness chain in dimension three for a soul of
  relative dimension two: LFR45 (`exists_finite_soul_strict_outward_tube_data`) → BASE-2 carrier
  (`soulBase_surface_carrier`, with its inverse contract) → `Ê` (`exists_soulNormalBundle`) → LFR46
  restated; `M` is `C^(r−2)`-diffeomorphic to the total space of the smoothed normal line bundle over
  the smooth carrier, the zero section going onto the soul.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (embeddedSliceChartedSpace)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

section Radius

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
  [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]

/-- **The fibre radius of the actual normal-flow map.** For the SAME choice as LFR46: the zero
section is `b` (onto `S`), `|e⁻¹ x| = d_S x` on `{d_S ≤ ℓ}`, and `|e⁻¹ x| = ℓ − τ x ≥ ℓ` outside,
`τ` the hitting time of level `ℓ`. -/
theorem exists_finite_normalFlowMap_tube_radius [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0)
    {ε : ℝ} (hε : 0 < ε) (ψ : M → TangentBundle I M)
    (hψs : ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε})
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε})
    (b : B → M) (hbinj : Injective b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x)
    (ι : TotalSpace F V → TangentBundle I M)
    (hι : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι)
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2)
    (hιν : ∀ z, ι z ∈ normalSetFinite g S)
    (hιonto : ∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) (p : M) :
    ∃ (φ : ℝ → M → M) (ℓ : ℝ),
      0 < ℓ ∧ ∃ e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M,
        range (fun s : B => e ⟨s, 0⟩) = S ∧
        (∀ x, infDist x S ≤ ℓ → ‖(e.symm x).2‖ = infDist x S) ∧
        ∀ x, ℓ ≤ infDist x S →
          ‖(e.symm x).2‖ = ℓ - hittingTime φ (fun y => infDist y S) x ℓ ∧
            ℓ ≤ ‖(e.symm x).2‖ := by
  obtain ⟨-, φ, ℓ, -, δ, -, hℓ, -, hδ, -, hℓε, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e, he0,
    -, -, -, heinner, heouter, -⟩ := exists_finite_normalFlowMap_tube g hr hnorm hsec hSc hSne
      hout hε ψ hψs hψ hψexp hdS b hbinj hbS hbinv ι hι hιb hιlin hιnorm hιν hιonto p
  have hrad : ∀ x, infDist x S ≤ ℓ → ‖(e.symm x).2‖ = infDist x S := by
    intro x hx
    have hxε : infDist x S < ε := by linarith
    have h := hιnorm (e.symm x)
    rw [heinner x hx] at h
    rw [← (hψ x hxε).2.2, h, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨φ, ℓ, hℓ, e, ?_, hrad, fun x hx => ?_⟩
  · rw [← hbS]
    exact congrArg range (funext he0)
  · obtain ⟨hτ0, hl, hsymm⟩ := heouter x hx
    set τ := hittingTime φ (fun y => infDist y S) x ℓ with hτ
    have h4 : ‖(e.symm x).2‖ = ‖((ℓ - τ) / ℓ) • (e.symm (φ τ x)).2‖ := by rw [hsymm]
    have hpos : 0 ≤ (ℓ - τ) / ℓ := div_nonneg (by linarith) hℓ.le
    rw [h4, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hrad _ hl.le, hl,
      div_mul_cancel₀ _ hℓ.ne']
    exact ⟨rfl, by linarith⟩

end Radius

/-- **The same-witness chain in dimension three, surface soul.** LFR45 → BASE-2 carrier → `Ê` →
LFR46 restated: when the soul has relative dimension two, `M` is `C^(r−2)`-diffeomorphic to the
total space of the smoothed normal line bundle over W-SUB's smooth carrier `Ŝ`, the zero section
going onto the soul and the fibre radius being `d_S` near it. -/
theorem exists_finite_normalFlowMap_surface [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 3) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧
      (maxSliceDimOfOrder I (r : ℕ∞ω) S = 2 →
        ∃ (Shat : Set M) (hShat : IsEmbeddedSlice I 2 Shat),
          let _ := embeddedSliceChartedSpace hShat
          ∃ (V : Shat → Type) (_ : ∀ s, NormedAddCommGroup (V s))
            (_ : ∀ s, InnerProductSpace ℝ (V s))
            (_ : TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V))
            (_ : FiberBundle (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V)
            (e : TotalSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮
              𝓘(ℝ, Fin 2 → ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))), I⟯ M)
            (ℓ : ℝ), 0 < ℓ ∧ range (fun s : Shat => e ⟨s, 0⟩) = S ∧
            ∀ x, infDist x S ≤ ℓ → ‖(e.symm x).2‖ = infDist x S) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  obtain ⟨S, hSne, hSc, -, -, hslice, hrel, -, -, hout, ε, hε, ψ, hψs, hψ, hψexp, -, hdS, -, -⟩ :=
    exists_finite_soul_strict_outward_tube_data g hr hnorm hsec
  refine ⟨S, hSne, hSc, hrel, fun h2 => ?_⟩
  rw [h2] at hslice
  obtain ⟨Shat, hShat, hrest⟩ := soulBase_surface_carrier g hr2 hnorm hdim hSc hSne hslice
  refine ⟨Shat, hShat, ?_⟩
  intro _
  obtain ⟨hc, ht, hm, b, hb, hbinj, hbS, R, hRb, hR⟩ := hrest
  have instC : CompactSpace Shat := hc
  have instT : T2Space Shat := ht
  have instM : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ Shat := hm
  obtain ⟨V, i1, i2, i3, i4, i5, i6, i7, ιE, hι, hιb, hιlin, hιnorm, hιν, hιonto, -⟩ :=
    exists_soulNormalBundle (EB := Fin 2 → ℝ) g hr2 hslice b hb hbS ⟨R, hRb, hR⟩
  obtain ⟨φ, ℓ, hℓ, e, hrange, hradius, -⟩ := exists_finite_normalFlowMap_tube_radius g hr hnorm
    hsec hSc hSne hout hε ψ hψs hψ hψexp hdS b hbinj hbS ⟨R, hRb, hR⟩ ιE hι hιb hιlin hιnorm hιν
    hιonto p
  exact ⟨V, i1, i2, i3, i4, e, ℓ, hℓ, hrange, hradius⟩

end DifferentialGeometry.Geometry.FiniteSoul
