import D2RelationGap.ArbFilling
import D2RelationGap.DeficiencyBound

/-!
Global deficiency zero for OpenAI's G: every surjection FreeGroup (Fin m) ->> G whose
kernel is the normal closure of k elements has m <= k, and the five-relator
presentation realizes equality. `DeficiencyBound` gives m <= k+1; here k = m-1 is
excluded: the Fox map of the relators is then injective, so the arbitrary-rank tagged
presentation target has injective defined d2 (`ArbFilling.comparison`), while a raw word
for a preimage of x1 gives a detecting square-null loop (`ArbMoves.d2_not_injective`).
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies G, the
character, the identities and the torsion obstruction.
-/
noncomputable section
namespace D2RelationGap.DeficiencyZero
open Targets GenericFox OrientedSimplices SimplicialTransport EdgePaths

/-- No presentation of G has deficiency one. -/
theorem no_deficiency_one (m k : ℕ) (q : FreeGroup (Fin m) →* G) (hq : Function.Surjective q)
    (v : Fin k → FreeGroup (Fin m)) (hv : Subgroup.normalClosure (Set.range v) = q.ker)
    (hmk : m = k + 1) : False := by
  have hvk : ∀ j, (ComplexCharacter.rho.comp q) (v j) = 1 := by
    intro j
    have hm : v j ∈ q.ker := hv ▸ Subgroup.subset_normalClosure ⟨j, rfl⟩
    simp [MonoidHom.mem_ker.mp hm]
  choose w hrep using fun j => ArbRose.exists_word (v j)
  have hk : ∀ j, value (ArbRose.transport
      (fun i => unitsChar (ComplexCharacter.rho.comp q) (FreeGroup.of i))) (ArbRose.wordPath (w j)) = 1 := by
    intro j
    apply Units.ext
    rw [ArbRose.word_value, hrep j, hvk j]
    rfl
  have hfox : Function.Injective (Fintype.linearCombination ℂ
      (fun j => D (ComplexCharacter.rho.comp q) (ArbRose.freeWord (w j)))) := by
    have he : (fun j => D (ComplexCharacter.rho.comp q) (ArbRose.freeWord (w j))) =
        (fun j => D (ComplexCharacter.rho.comp q) (v j)) := funext (fun j => by rw [hrep j])
    rw [he]
    apply LinearIndependent.fintypeLinearCombination_injective
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    have hspan : foxSpan (ComplexCharacter.rho.comp q) q.ker ≤
        Submodule.span ℂ (Set.range (fun j => D (ComplexCharacter.rho.comp q) (v j))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨n, hn, rfl⟩
      exact normalClosure_span _ v hvk n (hv ▸ hn)
    have hdim := Submodule.finrank_mono ((DeficiencyBound.kernel_le q hq).trans hspan)
    have hker := kernel_finrank (ComplexCharacter.rho.comp q) (DeficiencyBound.exists_nontrivial q hq)
    have hle : Module.finrank ℂ (Submodule.span ℂ
        (Set.range (fun j => D (ComplexCharacter.rho.comp q) (v j)))) ≤ k := by
      have h := finrank_range_le_card (R := ℂ) (fun j => D (ComplexCharacter.rho.comp q) (v j))
      rw [Fintype.card_fin] at h
      exact h
    rw [Fintype.card_fin] at hker ⊢
    change k = Module.finrank ℂ (Submodule.span ℂ _)
    omega
  obtain ⟨x, hx⟩ := hq (quotientMap (FreeGroup.of .x1))
  obtain ⟨u, hu⟩ := ArbRose.exists_word x
  have hsq : (ArbRose.freeWord u)^2 ∈ (ArbTransport.evalLoops w).ker := by
    apply ArbMoves.kernel_contains w v hrep
    rw [hv, MonoidHom.mem_ker, hu, map_pow, hx]
    exact Character.x1_square
  have hd : value (ArbTransport.transport w _ hk) (ArbTransport.wordPath w u) ≠ 1 := by
    intro h1
    have hv1 := ArbTransport.old_path_value w _ hk (ArbRose.wordPath u)
    change value _ (ArbTransport.wordPath w u) = _ at hv1
    rw [h1] at hv1
    have hval := ArbRose.word_value (ComplexCharacter.rho.comp q) u
    rw [← hv1, hu] at hval
    simp only [Units.val_one, MonoidHom.coe_comp, Function.comp_apply, hx] at hval
    exact ComplexCharacter.rho_x1_nontrivial hval.symm
  exact ArbMoves.d2_not_injective w _ hk u hsq hd
    (ArbFilling.comparison w (ComplexCharacter.rho.comp q) hk hfox)

/-- GLOBAL DEFICIENCY ZERO: G has a presentation with five generators and five relators,
and every finite presentation of G has at least as many relators as generators. -/
theorem deficiency_zero : DeficiencyZeroTarget := by
  refine ⟨hasNormalGenerators_five, ?_⟩
  rintro m k q hq ⟨v, hv⟩
  have h1 := DeficiencyBound.rank_le_succ m k q hq v hv
  by_contra h
  exact no_deficiency_one m k q hq v hv (by omega)

end D2RelationGap.DeficiencyZero
