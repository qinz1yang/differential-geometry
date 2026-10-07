import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FinitePresentedStaticCapC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecordC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutoffRecordC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksC11X

/-!
# ExtContractG2ConsumerC11X（S-CH11-EXT1 G2 consumer：Contract 链 4 个 extension）

对每个 SIG（改名）项给 `example`，展示 `_C11X` 加强版 ⇒ 宿主旧版（`type_of%` 对齐到宿主声明本身）：

* `finitePresentedStaticCaps{,OfTerminal}_C11X`：类型与宿主旧 `def` 逐字相同（`rfl`）；
* `PreparedCutoffEventGeometry.exists_of_retainedEvent_heq_C11X` ⇒ 宿主私有旧定理（去掉最后一个合取项）；
* `finitePresentedStaticCapsOfStage_C11X` ⇒ 宿主私有旧 `def` 的类型（去掉 `HasRadialCoordinates` 合取项）；
* `…_of_fineCutNecks_with_radial_coordinates`（public，HornFine）⇒ `…_of_fineCutNecks`：donor 自己写的
  "forget the radial certificate" 机械投影（逐字）；
* Poincare 的两个 `…_with_radial_coordinates` ⇒ 宿主旧版：同上（donor 逐字投影）。
-/

open private PreparedCutoffEventGeometry.exists_of_retainedEvent_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
open private PreparedCutoffEventGeometry.exists_of_retainedEvent_heq_C11X from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecordC11X
open private finitePresentedStaticCapsOfStage from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
open private finitePresentedStaticCapsOfStage_C11X from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecordC11X
open private
  exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks
  from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks
open private
  exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks_with_radial_coordinates
  from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksC11X

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

example : type_of% @finitePresentedStaticCaps.{u} = type_of% @finitePresentedStaticCaps_C11X.{u} :=
  rfl

example :
    type_of% @finitePresentedStaticCapsOfTerminal.{u} =
      type_of% @finitePresentedStaticCapsOfTerminal_C11X.{u} := rfl

example : type_of% @PreparedCutoffEventGeometry.exists_of_retainedEvent_heq.{u} := by
  intro P Q P' Q' a s a' s' E p δ r k F E' hP hQ ha hs hE
  obtain ⟨F', e, hneck, eB, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
    PreparedCutoffEventGeometry.exists_of_retainedEvent_heq_C11X F E' hP hQ ha hs hE
  exact ⟨F', e, hneck, eB, h1, h2, h3, h4, h5, h6, h7, h8.1⟩

example : type_of% @finitePresentedStaticCapsOfStage.{u} := by
  intro P ι _ precision hδ hδ1 f hf hdisj hs R hnontrivial t₀ t₁ fixed D ε m hD Q Ret Disc Bidx
    oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  have x := finitePresentedStaticCapsOfStage_C11X P hδ hδ1 f hf hdisj hs R hnontrivial hD
    oQ oRet oDisc G L E A B a hboundary hB hDisc hCap htrace hG hL
    hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside w hOutput
  exact ⟨x.1, ⟨x.2.1, x.2.2.1, fun b =>
    ⟨(x.2.2.2 b).1, (x.2.2.2 b).2.1, (x.2.2.2 b).2.2.1, (x.2.2.2 b).2.2.2.2⟩⟩⟩

example :
    type_of% @exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks.{u} := by
  have radialProjectionSource :=
    exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks_with_radial_coordinates.{u}
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  obtain ⟨εcoarse, radialProjectionh4⟩ := radialProjectionh3
  refine ⟨εcoarse, ?_⟩
  obtain ⟨radialProjectionfield5, radialProjectionh6⟩ := radialProjectionh4
  refine ⟨radialProjectionfield5, ?_⟩
  intro Dcap radialProjectionx7 radialProjectionx8 m accuracy radialProjectionx9 η
    radialProjectionx10
  have radialProjectionh11 := @radialProjectionh6 Dcap radialProjectionx7 radialProjectionx8 m
    accuracy radialProjectionx9 η radialProjectionx10
  obtain ⟨δ, ε₀, radialProjectionh12⟩ := radialProjectionh11
  refine ⟨δ, ε₀, ?_⟩
  obtain ⟨radialProjectionfield13, radialProjectionfield14, radialProjectionfield15,
    radialProjectionfield16, radialProjectionh17⟩ := radialProjectionh12
  refine ⟨radialProjectionfield13, radialProjectionfield14, radialProjectionfield15,
    radialProjectionfield16, ?_⟩
  intro P₀ g₀ H initial radialProjectionx18 D radialProjectionx19 radialProjectionx20
    radialProjectionx21 ε Λ P radialProjectionx22 εc Qc radialProjectionx23 radialProjectionx24
    radialProjectionx25 radialProjectionx26 Q radialProjectionx27 radialProjectionx28
    radialProjectionx29
  have radialProjectionh30 := @radialProjectionh17 P₀ g₀ H initial radialProjectionx18 D
    radialProjectionx19 radialProjectionx20 radialProjectionx21 ε Λ P radialProjectionx22 εc Qc
    radialProjectionx23 radialProjectionx24 radialProjectionx25 radialProjectionx26 Q
    radialProjectionx27 radialProjectionx28 radialProjectionx29
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, radialProjectionh31⟩ :=
    radialProjectionh30
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, radialProjectionfield37,
    radialProjectionfield38, radialProjectionfield39, radialProjectionfield40,
    radialProjectionfield41, radialProjectionfield42, radialProjectionfield43,
    radialProjectionfield44, radialProjectionfield45, radialProjectionfield46,
    radialProjectionfield47, radialProjectionfield48, radialProjectionfield49,
    radialProjectionfield50, radialProjectionfield51, radialProjectionfield52,
    radialProjectionfield53, radialProjectionfield54, radialProjectionfield55,
    radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, radialProjectionh63⟩ := radialProjectionh31
  refine ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, radialProjectionfield37,
    radialProjectionfield38, radialProjectionfield39, radialProjectionfield40,
    radialProjectionfield41, radialProjectionfield42, radialProjectionfield43,
    radialProjectionfield44, radialProjectionfield45, radialProjectionfield46,
    radialProjectionfield47, radialProjectionfield48, radialProjectionfield49,
    radialProjectionfield50, radialProjectionfield51, radialProjectionfield52,
    radialProjectionfield53, radialProjectionfield54, radialProjectionfield55,
    radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, ?_⟩
  refine ⟨?_, radialProjectionh63.2⟩
  have radialProjectionh64 := radialProjectionh63.1
  intro radialProjectionx65
  have radialProjectionh66 := @radialProjectionh64 radialProjectionx65
  obtain ⟨G, radialProjectionh67⟩ := radialProjectionh66
  refine ⟨G, ?_⟩
  obtain ⟨radialProjectionfield68, radialProjectionfield69, radialProjectionfield70,
    radialProjectionfield71, radialProjectionh72⟩ := radialProjectionh67
  refine ⟨radialProjectionfield68, radialProjectionfield69, radialProjectionfield70,
    radialProjectionfield71, ?_⟩
  exact radialProjectionh72.1

example : type_of% @exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks.{u} := by
  intro P₀ g₀
  have radialProjectionSource :=
    exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks_with_radial_coordinates.{u}
    P₀ g₀
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  obtain ⟨εcoarse, radialProjectionh4⟩ := radialProjectionh3
  refine ⟨εcoarse, ?_⟩
  obtain ⟨radialProjectionfield5, radialProjectionh6⟩ := radialProjectionh4
  refine ⟨radialProjectionfield5, ?_⟩
  intro Dtrace Dbig r tol Ctime radialProjectionx7 radialProjectionx8 radialProjectionx9
    radialProjectionx10 radialProjectionx11
  have radialProjectionh12 := @radialProjectionh6 Dtrace Dbig r tol Ctime radialProjectionx7
    radialProjectionx8 radialProjectionx9 radialProjectionx10 radialProjectionx11
  obtain ⟨εold, δold, radialProjectionh13⟩ := radialProjectionh12
  refine ⟨εold, δold, ?_⟩
  obtain ⟨radialProjectionfield14, radialProjectionfield15, radialProjectionh16⟩ :=
    radialProjectionh13
  refine ⟨radialProjectionfield14, radialProjectionfield15, ?_⟩
  intro m accuracy radialProjectionx17 ηrecord radialProjectionx18
  have radialProjectionh19 := @radialProjectionh16 m accuracy radialProjectionx17 ηrecord
    radialProjectionx18
  obtain ⟨δ, ε₀, Λq, radialProjectionh20⟩ := radialProjectionh19
  refine ⟨δ, ε₀, Λq, ?_⟩
  obtain ⟨radialProjectionfield21, radialProjectionfield22, radialProjectionfield23,
    radialProjectionfield24, radialProjectionfield25, radialProjectionh26⟩ := radialProjectionh20
  refine ⟨radialProjectionfield21, radialProjectionfield22, radialProjectionfield23,
    radialProjectionfield24, radialProjectionfield25, ?_⟩
  intro q0 radialProjectionx27 Λmax coreFloor radialProjectionx28 radialProjectionx29 Qlower
  have radialProjectionh30 := @radialProjectionh26 q0 radialProjectionx27 Λmax coreFloor
    radialProjectionx28 radialProjectionx29 Qlower
  obtain ⟨Q, v, radialProjectionh31⟩ := radialProjectionh30
  refine ⟨Q, v, ?_⟩
  obtain ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, radialProjectionh37⟩ := radialProjectionh31
  refine ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, ?_⟩
  intro p₀ radialProjectionx38 radialProjectionx39 radialProjectionx40 H initial radialProjectionx41
    ρold radialProjectionx42 s G L hsing stepParameters radialProjectionx43
  have radialProjectionh44 := @radialProjectionh37 p₀ radialProjectionx38 radialProjectionx39
    radialProjectionx40 H initial radialProjectionx41 ρold radialProjectionx42 s G L hsing
    stepParameters radialProjectionx43
  dsimp only at radialProjectionh44 ⊢
  intro radialProjectionx45 radialProjectionx46 ε Λ P radialProjectionx47 εc radialProjectionx48
    radialProjectionx49 radialProjectionx50 radialProjectionx51 radialProjectionx52
    radialProjectionx53
  have radialProjectionh54 := @radialProjectionh44 radialProjectionx45 radialProjectionx46 ε Λ P
    radialProjectionx47 εc radialProjectionx48 radialProjectionx49 radialProjectionx50
    radialProjectionx51 radialProjectionx52 radialProjectionx53
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, radialProjectionh55⟩ :=
    radialProjectionh54
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, radialProjectionfield63, radialProjectionfield64,
    radialProjectionfield65, radialProjectionfield66, radialProjectionfield67,
    radialProjectionfield68, radialProjectionfield69, radialProjectionfield70,
    radialProjectionfield71, radialProjectionfield72, radialProjectionfield73,
    radialProjectionfield74, radialProjectionfield75, radialProjectionfield76,
    radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, radialProjectionh87⟩ := radialProjectionh55
  refine ⟨radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, radialProjectionfield63, radialProjectionfield64,
    radialProjectionfield65, radialProjectionfield66, radialProjectionfield67,
    radialProjectionfield68, radialProjectionfield69, radialProjectionfield70,
    radialProjectionfield71, radialProjectionfield72, radialProjectionfield73,
    radialProjectionfield74, radialProjectionfield75, radialProjectionfield76,
    radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, ?_⟩
  refine ⟨?_, radialProjectionh87.2⟩
  have radialProjectionh88 := radialProjectionh87.1
  obtain ⟨Record, radialProjectionh89⟩ := radialProjectionh88
  refine ⟨Record, ?_⟩
  obtain ⟨radialProjectionfield90, radialProjectionfield91, radialProjectionfield92,
    radialProjectionfield93, radialProjectionh94⟩ := radialProjectionh89
  refine ⟨radialProjectionfield90, radialProjectionfield91, radialProjectionfield92,
    radialProjectionfield93, ?_⟩
  exact radialProjectionh94.1

example :
    type_of%
      @exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks.{u} := by
  intro P₀ g₀
  have radialProjectionSource :=
    exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks_with_radial_coordinates.{u}
    P₀ g₀
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  obtain ⟨εP, εbar, radialProjectionh4⟩ := radialProjectionh3
  refine ⟨εP, εbar, ?_⟩
  obtain ⟨radialProjectionfield5, radialProjectionfield6, radialProjectionfield7,
    radialProjectionh8⟩ := radialProjectionh4
  refine ⟨radialProjectionfield5, radialProjectionfield6, radialProjectionfield7, ?_⟩
  intro Dtrace Dbig r tol Ctime radialProjectionx9 radialProjectionx10 radialProjectionx11
    radialProjectionx12 radialProjectionx13
  have radialProjectionh14 := @radialProjectionh8 Dtrace Dbig r tol Ctime radialProjectionx9
    radialProjectionx10 radialProjectionx11 radialProjectionx12 radialProjectionx13
  obtain ⟨εold, δold, radialProjectionh15⟩ := radialProjectionh14
  refine ⟨εold, δold, ?_⟩
  obtain ⟨radialProjectionfield16, radialProjectionfield17, radialProjectionh18⟩ :=
    radialProjectionh15
  refine ⟨radialProjectionfield16, radialProjectionfield17, ?_⟩
  intro m accuracy radialProjectionx19 ηrecord radialProjectionx20
  have radialProjectionh21 := @radialProjectionh18 m accuracy radialProjectionx19 ηrecord
    radialProjectionx20
  obtain ⟨δ, εcut, radialProjectionh22⟩ := radialProjectionh21
  refine ⟨δ, εcut, ?_⟩
  obtain ⟨radialProjectionfield23, radialProjectionfield24, radialProjectionfield25,
    radialProjectionfield26, radialProjectionfield27, radialProjectionh28⟩ := radialProjectionh22
  refine ⟨radialProjectionfield23, radialProjectionfield24, radialProjectionfield25,
    radialProjectionfield26, radialProjectionfield27, ?_⟩
  intro C1 C2 radialProjectionx29
  have radialProjectionh30 := @radialProjectionh28 C1 C2 radialProjectionx29
  obtain ⟨C, Λ, radialProjectionh31⟩ := radialProjectionh30
  refine ⟨C, Λ, ?_⟩
  obtain ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionh34⟩ :=
    radialProjectionh31
  refine ⟨radialProjectionfield32, radialProjectionfield33, ?_⟩
  intro qcan originalCoreFloor protectedFloor Kfine radialProjectionx35 radialProjectionx36
    radialProjectionx37 radialProjectionx38
  have radialProjectionh39 := @radialProjectionh34 qcan originalCoreFloor protectedFloor Kfine
    radialProjectionx35 radialProjectionx36 radialProjectionx37 radialProjectionx38
  obtain ⟨Q, v, radialProjectionh40⟩ := radialProjectionh39
  refine ⟨Q, v, ?_⟩
  obtain ⟨radialProjectionfield41, radialProjectionfield42, radialProjectionfield43,
    radialProjectionh44⟩ := radialProjectionh40
  refine ⟨radialProjectionfield41, radialProjectionfield42, radialProjectionfield43, ?_⟩
  intro p₀ radialProjectionx45 radialProjectionx46 radialProjectionx47 H initial radialProjectionx48
    ρold radialProjectionx49 s G L hsing stepParameters radialProjectionx50
  have radialProjectionh51 := @radialProjectionh44 p₀ radialProjectionx45 radialProjectionx46
    radialProjectionx47 H initial radialProjectionx48 ρold radialProjectionx49 s G L hsing
    stepParameters radialProjectionx50
  dsimp only at radialProjectionh51 ⊢
  intro radialProjectionx52 radialProjectionx53 radialProjectionx54 radialProjectionx55
    radialProjectionx56 radialProjectionx57
  have radialProjectionh58 := @radialProjectionh51 radialProjectionx52 radialProjectionx53
    radialProjectionx54 radialProjectionx55 radialProjectionx56 radialProjectionx57
  obtain ⟨ρ, hρ, radialProjectionh59⟩ := radialProjectionh58
  refine ⟨ρ, hρ, ?_⟩
  obtain ⟨radialProjectionfield60, radialProjectionfield61, radialProjectionfield62,
    radialProjectionfield63, radialProjectionfield64, radialProjectionh65⟩ := radialProjectionh59
  refine ⟨radialProjectionfield60, radialProjectionfield61, radialProjectionfield62,
    radialProjectionfield63, radialProjectionfield64, ?_⟩
  try dsimp only at radialProjectionh65 ⊢
  obtain ⟨P, radialProjectionh66⟩ := radialProjectionh65
  refine ⟨P, ?_⟩
  obtain ⟨radialProjectionfield67, radialProjectionfield68, radialProjectionfield69,
    radialProjectionfield70, radialProjectionfield71, radialProjectionh72⟩ := radialProjectionh66
  refine ⟨radialProjectionfield67, radialProjectionfield68, radialProjectionfield69,
    radialProjectionfield70, radialProjectionfield71, ?_⟩
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, radialProjectionh73⟩ :=
    radialProjectionh72
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨radialProjectionfield74, radialProjectionfield75, radialProjectionfield76,
    radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, radialProjectionfield87, radialProjectionfield88,
    radialProjectionfield89, radialProjectionfield90, radialProjectionfield91,
    radialProjectionfield92, radialProjectionfield93, radialProjectionfield94,
    radialProjectionfield95, radialProjectionfield96, radialProjectionfield97,
    radialProjectionfield98, radialProjectionfield99, radialProjectionfield100,
    radialProjectionfield101, radialProjectionfield102, radialProjectionfield103,
    radialProjectionfield104, radialProjectionh105⟩ := radialProjectionh73
  refine ⟨radialProjectionfield74, radialProjectionfield75, radialProjectionfield76,
    radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, radialProjectionfield87, radialProjectionfield88,
    radialProjectionfield89, radialProjectionfield90, radialProjectionfield91,
    radialProjectionfield92, radialProjectionfield93, radialProjectionfield94,
    radialProjectionfield95, radialProjectionfield96, radialProjectionfield97,
    radialProjectionfield98, radialProjectionfield99, radialProjectionfield100,
    radialProjectionfield101, radialProjectionfield102, radialProjectionfield103,
    radialProjectionfield104, ?_⟩
  refine ⟨?_, radialProjectionh105.2⟩
  have radialProjectionh106 := radialProjectionh105.1
  obtain ⟨Record, radialProjectionh107⟩ := radialProjectionh106
  refine ⟨Record, ?_⟩
  obtain ⟨radialProjectionfield108, radialProjectionfield109, radialProjectionfield110,
    radialProjectionfield111, radialProjectionfield112, radialProjectionh113⟩ :=
    radialProjectionh107
  refine ⟨radialProjectionfield108, radialProjectionfield109, radialProjectionfield110,
    radialProjectionfield111, radialProjectionfield112, ?_⟩
  exact radialProjectionh113.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
