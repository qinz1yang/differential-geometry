import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyAmbient_S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyChart_S15

/-!
# CH12-S15, H1: the transfer isotopy (assembly)
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric
noncomputable section
namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

theorem scaledExp_eq_geodesic_S15 (X : ∀ y : M, TangentSpace I y) (μ : ℝ) (y : M) :
    scaledExp_S15 g hEnorm X μ y = intrinsicGeodesic g hEnorm y (X y) μ := by
  simp only [scaledExp_S15, expMapIntrinsic_def, intrinsicGeodesic_smul]

/-- **H1 for a given transfer field.**  For a fixed atlas `A` and compact `D ⊆ A.cover` there is
`ε > 0` such that for every smooth vector field `X` which is `C¹`-`ε`-small w.r.t. `A`, the
isotopy `E_t(p) = exp_p(t X p)`, `0 ≤ t ≤ 1`, extends over `D` to a compactly supported smooth
ambient isotopy `Ψ` of `M` through global diffeomorphisms (`Ψ 0 t`), with `Ψ 0 0 = id`,
`Ψ 0 t = E_t` on `D`, `E_t(D)` within distance `|X|` of `D`, and `|∂_t E_t| ≤ |X|`. -/
theorem transfer_isotopy_of_field_S15 (A : CkAtlas_S15 I M) {D : Set M} (hD : IsCompact D)
    (hDA : D ⊆ A.cover) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : (∀ y : M, TangentSpace I y),
      ContMDiff I I.tangent ∞ (secBundle_S15 X) → CkSmall_S15 g A X 1 ε →
      ∃ (Ψ : ℝ → ℝ → M → M) (C : Set M), IsCompact C ∧
        ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
          (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
        (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
        (∀ s t y, y ∉ C → Ψ s t y = y) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = expMapIntrinsic g hEnorm x (t • X x)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Manifold.riemannianEDist I x (Ψ 0 t x) ≤
          ENNReal.ofReal (tanLen_S15 g (secBundle_S15 X x))) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → ∀ x ∈ D,
          Manifold.riemannianEDist I (Ψ 0 s x) (Ψ 0 t x) ≤
            ENNReal.ofReal (tanLen_S15 g (secBundle_S15 X x) * (t - s))) := by
  obtain ⟨ε, hε, hgood⟩ := transfer_family_good_S15 g hEnorm A hD hDA
  refine ⟨ε, hε, fun X hX hsmall => ?_⟩
  set F : ℝ × M → M := fun q => scaledExp_S15 g hEnorm X q.1 q.2 with hF
  have hFs : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ F :=
    contMDiff_scaledExp_S15 (J := 𝓘(ℝ, ℝ).prod I) g hEnorm (fun q : ℝ × M => secBundle_S15 X q.2)
      (fun q : ℝ × M => q.1) (hX.comp contMDiff_snd) contMDiff_fst
  have hJ : IsOpen (Ioo (-2 : ℝ) 2) := isOpen_Ioo
  have hU : IsOpen A.cover := isOpen_iUnion fun i => A.isOpen_U i
  obtain ⟨Ψ, C, hC, hsm, hself, hcoc, hsupp, hΨF⟩ := transfer_ambient_isotopy_S15 (I := I)
    (F := F) (J := Ioo (-2 : ℝ) 2) (U := A.cover) hJ hU hD hDA (a := 0) (b := 1) zero_le_one
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) ⟨le_rfl, zero_le_one⟩
    hFs.contMDiffOn
    (fun t ht x hx => (hgood X hX hsmall t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)).1 x hx)
    (fun t ht => (hgood X hX hsmall t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)).2)
    (fun x _ => by
      simp only [hF, scaledExp_S15, zero_smul]
      exact expMapIntrinsic_zero g hEnorm x)
  refine ⟨Ψ, C, hC, hsm, hself, hcoc, hsupp, ?_, ?_, ?_⟩
  · intro t ht x hx
    rw [hΨF t ht x hx]
    simp only [hF, scaledExp_S15]
  · intro t ht x hx
    rw [hΨF t ht x hx]
    refine (edist_scaledExp_le_S15 g hEnorm X t x).trans (ENNReal.ofReal_le_ofReal ?_)
    have hn : 0 ≤ tanLen_S15 g (secBundle_S15 X x) := Real.sqrt_nonneg _
    rw [abs_of_nonneg ht.1]
    nlinarith [ht.2]
  · intro s t hs hst ht x hx
    rw [hΨF s ⟨hs, hst.trans ht⟩ x hx, hΨF t ⟨hs.trans hst, ht⟩ x hx]
    simp only [hF]
    rw [scaledExp_eq_geodesic_S15, scaledExp_eq_geodesic_S15]
    exact intrinsicGeodesic_riemannianEDist_le g hEnorm x (X x) hst |>.trans
      (le_of_eq rfl)


/-- the vector part of a tangent-bundle map, as a vector field. -/
def secOf_S15 (v : M → TangentBundle I M) : ∀ y : M, TangentSpace I y :=
  fun y => show TangentSpace I y from (v y).snd

theorem secBundle_secOf_S15 (v : M → TangentBundle I M) {y : M} (h : (v y).proj = y) :
    secBundle_S15 (secOf_S15 v) y = v y := by
  have key : ∀ u : TangentBundle I M, u.proj = y → (⟨y, u.snd⟩ : TangentBundle I M) = u := by
    rintro ⟨b, w⟩ hb
    simp only at hb
    subst hb
    rfl
  exact key (v y) h

/-- **Cutoff extension.**  Given compact `D1 ⊆ int D2`, there are `O ⊇ D2`, `ρ > 0` and a cutoff
`χ` (all independent of `Φ`) such that every smooth `Φ` on `O` moving points by `< ρ` is `exp ∘ X`
on `D1` for a *globally defined* smooth vector field `X = χ · v_Φ` supported in `O`,
with `|X| ≤ d(p, Φ p)`. -/
theorem exists_transfer_field_S15 {D1 D2 : Set M} (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hD12 : D1 ⊆ interior D2) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p ∈ D1, χ p = 1) ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧
      tsupport χ ⊆ O ∧
      ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
        (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
        ∃ X : (∀ y : M, TangentSpace I y), ContMDiff I I.tangent ∞ (secBundle_S15 X) ∧
          (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
          (∀ p, p ∉ O → X p = 0) ∧
          (∀ p ∈ O, tanLen_S15 g (secBundle_S15 X p) ≤ (Manifold.riemannianEDist I p (Φ p)).toReal) := by
  obtain ⟨O, hO, hD2O, ρ, hρ, hsec⟩ := exists_transfer_section_S15 g hEnorm hD2
  have hD1O : D1 ⊆ O := fun p hp => hD2O (interior_subset (hD12 hp))
  obtain ⟨W, hWo, hD1W, hWO, hWc⟩ := exists_open_between_and_isCompact_closure hD1 hO hD1O
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ := exists_contMDiff_support_eq_eq_one_iff I hWo
    hD1.isClosed hD1W
  have hts : tsupport χ ⊆ O := by
    rw [tsupport, hsupp]; exact hWO
  refine ⟨O, hO, hD2O, ρ, hρ, χ, hχ, fun p hp => (hone p).mp hp, fun p => hrange ⟨p, rfl⟩, hts, ?_⟩
  intro Φ hΦ hdist
  obtain ⟨v, hvs, hv⟩ := hsec Φ hΦ hdist
  set X : (∀ y : M, TangentSpace I y) := fun y => χ y • secOf_S15 v y with hX
  have hXO : ∀ p ∉ O, X p = 0 := by
    intro p hp
    have : χ p = 0 := by
      by_contra hne
      exact hp (hts (subset_tsupport _ hne))
    simp [hX, this]
  refine ⟨X, ?_, ?_, hXO, ?_⟩
  · intro p
    by_cases hp : p ∈ O
    · have hV : ContMDiffAt I I.tangent ∞ (secBundle_S15 (secOf_S15 v)) p := by
        refine ((hvs.contMDiffAt (hO.mem_nhds hp))).congr_of_eventuallyEq ?_
        filter_upwards [hO.mem_nhds hp] with y hy
        exact secBundle_secOf_S15 v (hv y hy).1
      exact contMDiffAt_smul_tangent_S15 (secBundle_S15 (secOf_S15 v)) χ hV (hχ p)
    · have hpt : p ∉ tsupport χ := fun h => hp (hts h)
      have hev : χ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hpt
      have hz : ContMDiffAt I I.tangent ∞ (fun y : M => (⟨y, (0 : E)⟩ : TangentBundle I M)) p :=
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))) p
      refine hz.congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp only [secBundle_S15, hX, hy, Pi.zero_apply, zero_smul]
      rfl
  · intro p hp
    have hχ1 : χ p = 1 := (hone p).mp hp
    obtain ⟨hproj, hexp, -⟩ := hv p (hD1O hp)
    simp only [hX, hχ1, one_smul]
    exact hexp
  · intro p hp
    obtain ⟨hproj, -, hlen⟩ := hv p hp
    have h1 := tanLen_smul_S15 g p (χ p) (secOf_S15 v p)
    have h2 : tanLen_S15 g (⟨p, secOf_S15 v p⟩ : TangentBundle I M) = tanLen_S15 g (v p) := by
      rw [← secBundle_secOf_S15 v hproj]; rfl
    have hχ0 := hrange ⟨p, rfl⟩
    show tanLen_S15 g (⟨p, χ p • secOf_S15 v p⟩ : TangentBundle I M) ≤ _
    rw [h1, abs_of_nonneg hχ0.1, h2, ← hlen]
    have : 0 ≤ tanLen_S15 g (v p) := Real.sqrt_nonneg _
    nlinarith [hχ0.2]


/-- **H1 (transfer map and small isotopy), static part.**  Fix a metric `g` (complete, with its
metric norm), a finite compact atlas `A`, and compact `D ⊆ D1 ⊆ int D2 ⊆ D2 ⊆ A.cover`
(quantifier order: `A, D, D1, D2` first, then `ε, O, ρ`, then `Φ`).  Then for every smooth `Φ`
on `O ⊇ D2` moving points by `< ρ` there is a global smooth vector field `X`, vanishing off `O`,
with `exp ∘ X = Φ` on `D1` and `|X| ≤ d(p, Φ p)`; and if `X` is `C¹`-`ε`-small w.r.t. `A`, the
isotopy `E_t = exp(t X)` extends over `D` to a compactly supported ambient isotopy `Ψ` of global
diffeomorphisms `Ψ 0 t`, with `Ψ 0 0 = id`, `Ψ 0 1 = Φ` on `D`, `E_t(D)` within `d(x, Φ x)` of
`x`, and `|∂_t E_t| ≤ d(x, Φ x)`. -/
theorem transfer_isotopy_S15 (A : CkAtlas_S15 I M) {D D1 D2 : Set M} (hD : IsCompact D)
    (hD1 : IsCompact D1) (hD2 : IsCompact D2) (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2)
    (hD2A : D2 ⊆ A.cover) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
        (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
        ∃ X : (∀ y : M, TangentSpace I y), ContMDiff I I.tangent ∞ (secBundle_S15 X) ∧
          (∀ p, p ∉ O → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
          (CkSmall_S15 g A X 1 ε →
            ∃ (Ψ : ℝ → ℝ → M → M) (C : Set M), IsCompact C ∧
              ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
                (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
              (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
              (∀ s t y, y ∉ C → Ψ s t y = y) ∧ (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
              (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Manifold.riemannianEDist I x (Ψ 0 t x) ≤
                ENNReal.ofReal (Manifold.riemannianEDist I x (Φ x)).toReal) ∧
              (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → ∀ x ∈ D,
                Manifold.riemannianEDist I (Ψ 0 s x) (Ψ 0 t x) ≤
                  ENNReal.ofReal ((Manifold.riemannianEDist I x (Φ x)).toReal * (t - s)))) := by
  obtain ⟨O, hO, hD2O, ρ, hρ, χ, -, -, -, -, hfield⟩ :=
    exists_transfer_field_S15 g hEnorm hD1 hD2 hD12
  have hD2cov : D ⊆ A.cover := hDD1.trans ((hD12.trans interior_subset).trans hD2A)
  obtain ⟨ε, hε, hiso⟩ := transfer_isotopy_of_field_S15 g hEnorm A hD hD2cov
  refine ⟨ε, hε, O, hO, hD2O, ρ, hρ, fun Φ hΦ hd => ?_⟩
  obtain ⟨X, hXs, hXexp, hX0, hXlen⟩ := hfield Φ hΦ hd
  refine ⟨X, hXs, hX0, hXexp, fun hsm => ?_⟩
  obtain ⟨Ψ, C, hC, hsm', hself, hcoc, hsupp, hΨ, hd1, hd2⟩ := hiso X hXs hsm
  have hDO : ∀ x ∈ D, x ∈ O := fun x hx =>
    hD2O (interior_subset (hD12 (hDD1 hx)))
  have hlen : ∀ x ∈ D, tanLen_S15 g (secBundle_S15 X x) ≤
      (Manifold.riemannianEDist I x (Φ x)).toReal := fun x hx => hXlen x (hDO x hx)
  refine ⟨Ψ, C, hC, hsm', hself, hcoc, hsupp, ?_, ?_, ?_⟩
  · intro x hx
    rw [hΨ 1 ⟨zero_le_one, le_rfl⟩ x hx, one_smul]
    exact hXexp x (hDD1 hx)
  · intro t ht x hx
    exact (hd1 t ht x hx).trans (ENNReal.ofReal_le_ofReal (hlen x hx))
  · intro s t hs hst ht x hx
    refine (hd2 s t hs hst ht x hx).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (hlen x hx) (by linarith)

end Complete
end GC.LongTime.Ch12
