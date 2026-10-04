import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamGlobal
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ProjectionSmoothing

/-!
# §10: the normal bundle over the smooth carrier, already smoothed (lane CMS3-CARRIER, group G2)

Frozen interface `exists_normalParametrization` (D-CMS3 §10, review §11: correct). For a `C^r` slice
`S` (`r ≥ 2`) of dimension `d` and a `C^{r−1}` map `b : B → M` of a compact smooth manifold onto
`S` (with the BASE inverse contract), there are a SMOOTH field `P̂` of orthogonal projections of
`ℝ^K` of rank `dim − d` and a `C^{r−1}` map `ι : B × ℝ^K → TM`, fibrewise linear, that is, on
`range P̂ s`, a linear isometry onto the normal space `ν_{b s} S`, and onto `ν_g S`.

Route (design §3 "§10"):
* the global normal frame `σ_α s` of `exists_normalFrame_along` (frame identity on `ν`) gives
  `J_s v = Σ_α g(v, σ_α s) e_α` (isometric on `ν`) and `J*_s a = Σ_α a_α σ_α s` (onto `ν`);
* `P s = J_s J*_s` is a `C^{r−1}` field of orthogonal projections (entries `g(σ_α, σ_β)`) of rank
  `dim − d`;
* S-BUNDLE (CMS-BUN, `exists_smooth_projection_and_orthogonal_intertwiner`, Nat order) gives the
  smooth `P̂` and the orthogonal `C^{r−1}` intertwiner `B_s` with `B P = P̂ B`; for `r = ∞` the
  identity branch `P̂ = P`, `B = 1` (disposition D11);
* `ι (s, w) = J*_s (B_s* w)`.

`exists_normalParametrization_data` keeps the SAME witness and adds (disposition D6, review §11):
the zero-section formula `ι (s, 0) = 0_{b s}` and the two-way regularity of `ι|_{range P̂}`: a map
`Λ : TM → B × ℝ^K`, `C^{r−1}` at every vector based on `S`, inverse to `ι` on `range P̂` and on
`ν_g S` (it uses the BASE inverse `R` of `b`).

Deviation (linter-forced): the frozen hypotheses `[NeZero (finrank ℝ E)]`, `hnorm`, `hSc`, `hbinj`
are not used by the construction and are dropped; the verbatim statement is an `example` in
`NormalParamApplications.lean`. `hbinv` is used (for `Λ`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section Intertwiner

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
  [T2Space B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **S-BUNDLE in every order `n : ℕ∞`** (disposition D11): for finite `n` this is CMS-BUN's
corrected interface; for `n = ∞` the projection field is already smooth and the identity branch
`P̂ = P`, `B = 1` applies. -/
theorem exists_smooth_projection_intertwiner_enat {n : ℕ∞} (P : B → F →L[ℝ] F)
    (hP : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, F →L[ℝ] F) (n : ℕ∞ω) P) (hidem : ∀ s, P s ∘L P s = P s)
    (hsymm : ∀ s, (P s).adjoint = P s) :
    ∃ (Phat : B → F →L[ℝ] F) (Bm : B → F →L[ℝ] F),
      ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, F →L[ℝ] F) ∞ Phat ∧
      ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, F →L[ℝ] F) (n : ℕ∞ω) Bm ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Bm s ∘L P s = Phat s ∘L Bm s) ∧
      (∀ s, (Bm s).adjoint ∘L Bm s = 1) ∧ (∀ s, Bm s ∘L (Bm s).adjoint = 1) ∧
      ∀ s, Module.finrank ℝ (LinearMap.range (Phat s : F →ₗ[ℝ] F)) =
        Module.finrank ℝ (LinearMap.range (P s : F →ₗ[ℝ] F)) := by
  induction n using ENat.recTopCoe with
  | top =>
    refine ⟨P, fun _ => 1, hP, contMDiff_const, hidem, hsymm, fun s => ?_, fun s => ?_,
      fun s => ?_, fun s => rfl⟩
    · ext1 a; rfl
    · rw [ContinuousLinearMap.adjoint_one]; ext1 a; rfl
    · rw [ContinuousLinearMap.adjoint_one]; ext1 a; rfl
  | coe k =>
    obtain ⟨Phat, Bm, hPhat, hB, -, hPi, hPs, hBP, hBB, hBB', -, hrank, -, -⟩ :=
      exists_smooth_projection_and_orthogonal_intertwiner (IB := 𝓘(ℝ, EB)) P hP hidem hsymm
        one_pos
    exact ⟨Phat, Bm, hPhat, hB, hPi, hPs, hBP, hBB, hBB', hrank⟩

end Intertwiner

section Param

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
  [T2Space B]

variable {r : ℕ∞}

/-- **§10 normal parametrization, data form** (same witness: frozen conclusions, zero section,
two-way regularity of `ι` on `range P̂`). -/
theorem exists_normalParametrization_data
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ (K : ℕ) (Phat : B → EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
      (ι : B × EuclideanSpace ℝ (Fin K) → TangentBundle I M)
      (Λ : TangentBundle I M → B × EuclideanSpace ℝ (Fin K)),
      ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) ∞ Phat ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : EuclideanSpace ℝ (Fin K) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin K))) = Module.finrank ℝ E - d) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
      (∀ s w, (ι (s, w)).proj = b s) ∧
      (∀ s, ∃ A : EuclideanSpace ℝ (Fin K) →L[ℝ] E, ∀ w, @Eq E (ι (s, w)).snd (A w)) ∧
      (∀ s w, ι (s, Phat s w) = ι (s, w)) ∧
      (∀ s w, Phat s w = w → ι (s, w) ∈ normalSetFinite g S ∧
        g.inner (ι (s, w)).proj (ι (s, w)).snd (ι (s, w)).snd = ‖w‖ ^ 2) ∧
      (∀ v ∈ normalSetFinite g S, ∃ s w, Phat s w = w ∧ ι (s, w) = v) ∧
      (∀ s, ι (s, 0) = (⟨b s, 0⟩ : TangentBundle I M)) ∧
      (∀ v : TangentBundle I M, v.proj ∈ S →
        ContMDiffAt I.tangent (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K)))
          ((r - 1 : ℕ∞) : ℕ∞ω) Λ v) ∧
      (∀ s w, Phat s w = w → Λ (ι (s, w)) = (s, w)) ∧
      ∀ v ∈ normalSetFinite g S, Phat (Λ v).1 (Λ v).2 = (Λ v).2 ∧ ι (Λ v) = v := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set mm : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hmm
  have hmm_le : mm ≤ (r : ℕ∞ω) + 1 := coe_sub_one_le_add_one_tube
  obtain ⟨R, hRb, hRs⟩ := hbinv
  have hbS' : ∀ s, b s ∈ S := fun s => hbS ▸ mem_range_self s
  obtain ⟨K, ρ, nf, O, hOo, hρs, hρsupp, hnf, hσnor, hframe, hrank⟩ :=
    exists_normalFrame_along (EB := EB) g hr1 hS b hb.continuous hbS
  set σ : Fin K → (s : B) → TangentSpace I (b s) := fun α s => ρ α s • nf α (b s) with hσdef
  -- regularity of the frame along `b`
  have hσreg : ∀ α, ContMDiff 𝓘(ℝ, EB) I.tangent mm
      (fun s => (⟨b s, σ α s⟩ : TangentBundle I M)) := by
    intro α s
    refine contMDiffAt_along_smul_of_tsupport (W := b ⁻¹' O α) (hρsupp α)
      ((hρs α s).of_le (WithTop.coe_le_coe.mpr le_top)) (hb s) fun hs => ?_
    exact (hnf α (b s) hs).comp s (hb s)
  -- the coordinate vectors
  set e : Fin K → EuclideanSpace ℝ (Fin K) := fun α => EuclideanSpace.single α (1 : ℝ) with he
  have he_coord : ∀ (c : Fin K → ℝ) β, (∑ α, c α • e α) β = c β := by
    intro c β
    simp [he, Pi.single_apply]
  set Jv : (s : B) → TangentSpace I (b s) → EuclideanSpace ℝ (Fin K) :=
    fun s v => ∑ α, g.inner (b s) v (σ α s) • e α with hJv
  set Js : (s : B) → EuclideanSpace ℝ (Fin K) → TangentSpace I (b s) :=
    fun s a => ∑ α, a α • σ α s with hJs
  have hJv_coord : ∀ s v β, (Jv s v) β = g.inner (b s) v (σ β s) := fun s v β =>
    he_coord _ β
  -- (F1) `J*` lands in the normal space
  have hJs_nor : ∀ s a, Js s a ∈ normalSubFinite g S (b s) := fun s a =>
    Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (hσnor α s)
  -- (F2) `J* J = id` on the normal space
  have hJsJv : ∀ s, ∀ v ∈ normalSubFinite g S (b s), Js s (Jv s v) = v := by
    intro s v hv
    refine Eq.trans ?_ (hframe s v hv).symm
    exact Finset.sum_congr rfl fun α _ => by rw [hJv_coord]
  -- (F3) adjointness
  have hJadj : ∀ s v a, ⟪Jv s v, a⟫_ℝ = g.inner (b s) v (Js s a) := by
    intro s v a
    simp only [hJv, hJs, sum_inner, inner_smul_left, he, EuclideanSpace.inner_single_left,
      map_sum, map_smul, smul_eq_mul, RCLike.conj_to_real, map_one, one_mul]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  -- the `C^{r−1}` projection field
  set G : B → Fin K → Fin K → ℝ := fun s α β => g.inner (b s) (σ α s) (σ β s) with hG
  set P : B → EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) := fun s =>
    ∑ α, ∑ β, G s α β • (EuclideanSpace.proj α : EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ).smulRight (e β)
    with hP
  have hP_apply : ∀ s a, P s a = Jv s (Js s a) := by
    intro s a
    simp only [hP, hJv, hJs, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hG,
      map_sum, map_smul, smul_eq_mul, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    congr 1
    change G s α β * a α = a α * G s α β
    ring
  have hPs : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
      mm P := by
    intro s
    refine contMDiffAt_finsetSum fun α _ => contMDiffAt_finsetSum fun β _ => ?_
    have hGs : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) mm (fun s => G s α β) s :=
      contMDiffAt_inner_along g hmm_le (hσreg α s) (hσreg β s)
    exact hGs.smul contMDiffAt_const
  have hPidem : ∀ s, P s ∘L P s = P s := by
    intro s
    ext1 a
    rw [ContinuousLinearMap.comp_apply, hP_apply, hP_apply, hJsJv s _ (hJs_nor s a)]
  have hPsymm : ∀ s, (P s).adjoint = P s := by
    intro s
    refine ((ContinuousLinearMap.eq_adjoint_iff (P s) (P s)).mpr fun a a' => ?_).symm
    rw [hP_apply, hP_apply, hJadj, real_inner_comm, hJadj, g.symm]
  have hPrank : ∀ s, Module.finrank ℝ (LinearMap.range (P s : EuclideanSpace ℝ (Fin K) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin K))) = Module.finrank ℝ E - d := by
    intro s
    let JL : TangentSpace I (b s) →ₗ[ℝ] EuclideanSpace ℝ (Fin K) :=
      { toFun := Jv s
        map_add' := fun v v' => by
          simp only [hJv, map_add, add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c v => by
          simp only [hJv, map_smul, smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
            RingHom.id_apply] }
    let L := JL ∘ₗ (normalSubFinite g S (b s)).subtype
    have hLinj : Injective L := by
      intro v v' hvv'
      have hsub : L (v - v') = 0 := by rw [map_sub, hvv', sub_self]
      set u : TangentSpace I (b s) := ((v - v' : normalSubFinite g S (b s)) :
        TangentSpace I (b s)) with hu
      have hLu : L (v - v') = Jv s u := rfl
      have hw : u = 0 := by
        have h1 : ⟪Jv s u, Jv s u⟫_ℝ = g.inner (b s) u u := by
          rw [hJadj, hJsJv s u (v - v').2]
        rw [← hLu, hsub, inner_zero_left] at h1
        by_contra hne
        exact (g.pos (b s) _ hne).ne' h1.symm
      exact sub_eq_zero.mp (Subtype.ext hw)
    have hrange : LinearMap.range (P s : EuclideanSpace ℝ (Fin K) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin K)) = LinearMap.range L := by
      apply le_antisymm
      · rintro _ ⟨a, rfl⟩
        exact ⟨⟨Js s a, hJs_nor s a⟩, (hP_apply s a).symm⟩
      · rintro _ ⟨v, rfl⟩
        refine ⟨Jv s v, ?_⟩
        change P s (Jv s v) = Jv s v
        rw [hP_apply, hJsJv s v v.2]
    rw [hrange, LinearMap.finrank_range_of_inj hLinj, hrank s]
  -- S-BUNDLE
  obtain ⟨Phat, Bm, hPhat, hBm, hPhi, hPhs, hBP, hBB, hBB', hPhrank⟩ :=
    exists_smooth_projection_intertwiner_enat (n := r - 1) P hPs hPidem hPsymm
  have hBB_apply : ∀ s a, (Bm s).adjoint (Bm s a) = a := fun s a =>
    congrArg (fun T => T a) (hBB s)
  have hBB'_apply : ∀ s w, Bm s ((Bm s).adjoint w) = w := fun s w =>
    congrArg (fun T => T w) (hBB' s)
  have hBP_apply : ∀ s a, Bm s (P s a) = Phat s (Bm s a) := fun s a =>
    congrArg (fun T => T a) (hBP s)
  have hBadj_apply : ∀ s w, (Bm s).adjoint (Phat s w) = P s ((Bm s).adjoint w) := by
    intro s w
    calc (Bm s).adjoint (Phat s w)
        = (Bm s).adjoint (Phat s (Bm s ((Bm s).adjoint w))) := by rw [hBB'_apply]
      _ = (Bm s).adjoint (Bm s (P s ((Bm s).adjoint w))) := by rw [hBP_apply]
      _ = P s ((Bm s).adjoint w) := by rw [hBB_apply]
  have hJsP : ∀ s a, Js s (P s a) = Js s a := fun s a => by
    rw [hP_apply, hJsJv s _ (hJs_nor s a)]
  -- the map `ι`
  set ι : B × EuclideanSpace ℝ (Fin K) → TangentBundle I M := fun p =>
    ⟨b p.1, Js p.1 ((Bm p.1).adjoint p.2)⟩ with hιdef
  have hcoef : ∀ s w α, ((Bm s).adjoint w) α = ⟪w, Bm s (e α)⟫_ℝ := by
    intro s w α
    rw [← ContinuousLinearMap.adjoint_inner_left, he, EuclideanSpace.inner_single_right]
    simp
  have hιreg : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) I.tangent mm ι := by
    intro p
    have hb1 : ContMDiffAt (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) I mm
        (fun p : B × EuclideanSpace ℝ (Fin K) => b p.1) p := (hb p.1).comp p contMDiffAt_fst
    refine contMDiffAt_along_sum Finset.univ hb1 fun α _ => contMDiffAt_along_smul ?_ ?_
    · have hBe : ContMDiffAt (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin K)) mm
          (fun p : B × EuclideanSpace ℝ (Fin K) => Bm p.1 (e α)) p :=
        ((hBm p.1).comp p contMDiffAt_fst).clm_apply contMDiffAt_const
      have hin : ContMDiffAt (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) 𝓘(ℝ, ℝ) mm
          (fun p : B × EuclideanSpace ℝ (Fin K) => innerSL ℝ (Bm p.1 (e α)) p.2) p :=
        (((innerSL ℝ : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ).contDiff
          (n := mm)).contMDiff.contMDiffAt.comp p hBe).clm_apply contMDiffAt_snd
      refine hin.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
      change ((Bm q.1).adjoint q.2) α = innerSL ℝ (Bm q.1 (e α)) q.2
      rw [hcoef q.1 q.2 α, innerSL_apply_apply, real_inner_comm]
    · exact (hσreg α p.1).comp p contMDiffAt_fst
  -- the inverse `Λ`
  set σt : Fin K → (y : M) → TangentSpace I y := fun α y => ρ α (R y) • nf α y with hσt
  set Λ : TangentBundle I M → B × EuclideanSpace ℝ (Fin K) := fun v =>
    (R v.proj, Bm (R v.proj) (∑ α, g.inner v.proj v.snd (σt α v.proj) • e α)) with hΛdef
  have hΛb : ∀ s (v : TangentSpace I (b s)),
      Λ ⟨b s, v⟩ = (s, Bm s (Jv s v)) := by
    intro s v
    change (R (b s), Bm (R (b s)) (∑ α, g.inner (b s) v (ρ α (R (b s)) • nf α (b s)) • e α)) = _
    rw [hRb s]
  -- onto and the normal-set facts
  have hnormal_iff : ∀ s (v : TangentSpace I (b s)),
      (⟨b s, v⟩ : TangentBundle I M) ∈ normalSetFinite g S ↔ v ∈ normalSubFinite g S (b s) :=
    fun s v => ⟨fun h => h.2, fun h => ⟨hbS' s, h⟩⟩
  have hσtreg : ∀ α, ∀ y ∈ S, ContMDiffAt I I.tangent mm
      (fun y => (⟨y, σt α y⟩ : TangentBundle I M)) y := by
    intro α y hy
    by_cases hyO : y ∈ O α
    · have hρR : ContMDiffAt I 𝓘(ℝ, ℝ) mm (fun y => ρ α (R y)) y :=
        ((hρs α (R y)).of_le (WithTop.coe_le_coe.mpr le_top)).comp y (hRs y hy)
      exact contMDiffAt_along_smul (b := id) hρR (hnf α y hyO)
    · obtain ⟨s₀, rfl⟩ : y ∈ range b := hbS ▸ hy
      have hs₀ : s₀ ∉ tsupport (ρ α) := fun h => hyO (hρsupp α h)
      have hev0 : ρ α =ᶠ[𝓝 s₀] 0 := notMem_tsupport_iff_eventuallyEq.mp hs₀
      have hRc : ContinuousAt R (b s₀) := (hRs (b s₀) hy).continuousAt
      have hev : (fun y => ρ α (R y)) =ᶠ[𝓝 (b s₀)] fun _ => 0 := by
        have h1 : Tendsto R (𝓝 (b s₀)) (𝓝 s₀) := by
          have := hRc.tendsto
          rwa [hRb s₀] at this
        filter_upwards [h1.eventually hev0] with y hy'
        exact hy'
      refine (contMDiffAt_along_zero (b := id) contMDiffAt_id).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy'
      change (⟨y, ρ α (R y) • nf α y⟩ : TangentBundle I M) = ⟨y, 0⟩
      rw [hy', zero_smul]
  have hΛreg : ∀ v : TangentBundle I M, v.proj ∈ S →
      ContMDiffAt I.tangent (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) mm Λ v := by
    intro v hv
    have hproj : ContMDiffAt I.tangent I mm (fun v : TangentBundle I M => v.proj) v :=
      (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt
    have hR1 : ContMDiffAt I.tangent 𝓘(ℝ, EB) mm (fun v : TangentBundle I M => R v.proj) v :=
      (hRs v.proj hv).comp v hproj
    have hcoefs : ∀ α, ContMDiffAt I.tangent 𝓘(ℝ, ℝ) mm
        (fun v : TangentBundle I M => g.inner v.proj v.snd (σt α v.proj)) v := by
      intro α
      have hid : ContMDiffAt I.tangent I.tangent mm
          (fun v : TangentBundle I M => (⟨v.proj, v.snd⟩ : TangentBundle I M)) v :=
        contMDiffAt_id
      exact contMDiffAt_inner_along g hmm_le hid ((hσtreg α v.proj hv).comp v hproj)
    have hvec : ContMDiffAt I.tangent 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) mm
        (fun v : TangentBundle I M => ∑ α, g.inner v.proj v.snd (σt α v.proj) • e α) v :=
      contMDiffAt_finsetSum fun α _ => (hcoefs α).smul contMDiffAt_const
    exact hR1.prodMk (((hBm (R v.proj)).comp v hR1).clm_apply hvec)
  refine ⟨K, Phat, ι, Λ, hPhat, hPhi, hPhs, fun s => (hPhrank s).trans (hPrank s), hιreg,
    fun s w => rfl, ?_, ?_, ?_, ?_, ?_, hΛreg, ?_, ?_⟩
  · intro s
    let JsL : EuclideanSpace ℝ (Fin K) →L[ℝ] E :=
      ∑ α, (EuclideanSpace.proj α : EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ).smulRight (σ α s : E)
    refine ⟨JsL ∘L (Bm s).adjoint, fun w => ?_⟩
    simp only [JsL, ContinuousLinearMap.comp_apply, sum_apply]
    rfl
  · intro s w
    change (⟨b s, Js s ((Bm s).adjoint (Phat s w))⟩ : TangentBundle I M) =
      ⟨b s, Js s ((Bm s).adjoint w)⟩
    rw [hBadj_apply, hJsP]
  · intro s w hw
    have hPa : P s ((Bm s).adjoint w) = (Bm s).adjoint w := by
      rw [← hBadj_apply, hw]
    refine ⟨(hnormal_iff s _).2 (hJs_nor s _), ?_⟩
    change g.inner (b s) (Js s ((Bm s).adjoint w)) (Js s ((Bm s).adjoint w)) = ‖w‖ ^ 2
    rw [← hJadj, ← hP_apply, hPa, ContinuousLinearMap.adjoint_inner_left, hBB'_apply,
      real_inner_self_eq_norm_sq]
  · rintro ⟨y, v⟩ hv
    obtain ⟨s, rfl⟩ : y ∈ range b := hbS ▸ hv.1
    have hvn : v ∈ normalSubFinite g S (b s) := hv.2
    refine ⟨s, Bm s (Jv s v), ?_, ?_⟩
    · rw [← hBP_apply, hP_apply, hJsJv s v hvn]
    · change (⟨b s, Js s ((Bm s).adjoint (Bm s (Jv s v)))⟩ : TangentBundle I M) = ⟨b s, v⟩
      rw [hBB_apply, hJsJv s v hvn]
  · intro s
    change (⟨b s, Js s ((Bm s).adjoint 0)⟩ : TangentBundle I M) = ⟨b s, 0⟩
    rw [map_zero]
    congr 1
    simp [hJs]
  · intro s w hw
    have hPa : P s ((Bm s).adjoint w) = (Bm s).adjoint w := by
      rw [← hBadj_apply, hw]
    change Λ ⟨b s, Js s ((Bm s).adjoint w)⟩ = (s, w)
    rw [hΛb, ← hP_apply, hPa, hBB'_apply]
  · rintro ⟨y, v⟩ hv
    obtain ⟨s, rfl⟩ : y ∈ range b := hbS ▸ hv.1
    have hvn : v ∈ normalSubFinite g S (b s) := hv.2
    rw [hΛb]
    refine ⟨?_, ?_⟩
    · change Phat s (Bm s (Jv s v)) = Bm s (Jv s v)
      rw [← hBP_apply, hP_apply, hJsJv s v hvn]
    · change (⟨b s, Js s ((Bm s).adjoint (Bm s (Jv s v)))⟩ : TangentBundle I M) = ⟨b s, v⟩
      rw [hBB_apply, hJsJv s v hvn]

/-- **§10 normal parametrization** (`2 ≤ r`): the frozen statement minus the unused
`[NeZero (finrank ℝ E)]`, `hnorm`, `hSc`, `hbinj` (verbatim form: `NormalParamApplications.lean`). -/
theorem exists_normalParametrization
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ (K : ℕ) (Phat : B → EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
      (ι : B × EuclideanSpace ℝ (Fin K) → TangentBundle I M),
      ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) ∞ Phat ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : EuclideanSpace ℝ (Fin K) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin K))) = Module.finrank ℝ E - d) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
      (∀ s w, (ι (s, w)).proj = b s) ∧
      (∀ s, ∃ A : EuclideanSpace ℝ (Fin K) →L[ℝ] E, ∀ w, @Eq E (ι (s, w)).snd (A w)) ∧
      (∀ s w, ι (s, Phat s w) = ι (s, w)) ∧
      (∀ s w, Phat s w = w → ι (s, w) ∈ normalSetFinite g S ∧
        g.inner (ι (s, w)).proj (ι (s, w)).snd (ι (s, w)).snd = ‖w‖ ^ 2) ∧
      (∀ v ∈ normalSetFinite g S, ∃ s w, Phat s w = w ∧ ι (s, w) = v) := by
  obtain ⟨K, Phat, ι, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ :=
    exists_normalParametrization_data g hr hS b hb hbS hbinv
  exact ⟨K, Phat, ι, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Param

end DifferentialGeometry.Geometry.FiniteSoul
