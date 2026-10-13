import D2RelationGap.PresentationMoves
import D2RelationGap.Perfectness
import D2RelationGap.ComplexFox

/-!
CONDITIONAL assembly of the fixed-presentation integral relation gap.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
groups, perfectness, character, Fox data and torsion obstruction.

The ONLY unproved input is `FoxFillingComparison`, displayed in full below. It is a
statement about ARBITRARY raw relator words killed by the original character; it
mentions neither normal generation of N nor the number four, and its antecedent is
satisfiable (`comparison_antecedent_satisfiable`). It is NOT proved here; nothing in
this file is an unconditional relation-gap theorem.
-/
noncomputable section
namespace D2RelationGap.ConditionalRelationGap
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops Targets
open PresentationCells PresentationTransport

/-- OPEN HYPOTHESIS (L3.3 Fox filling comparison on the SAME tagged target and transport):
if the algebraic left complex Fox boundary of the raw words is injective, then the
DEFINED weighted d2 of their actual tagged presentation target is injective. -/
def FoxFillingComparison : Prop :=
  ∀ {k : ℕ} (w : Fin k → Word)
    (hk : ∀ j, value (PresentationRose.transport PresentationRose.generatorUnit)
      (PresentationRose.wordPath (w j)) = 1),
    Function.Injective (ComplexFox.boundaryTwo (fun j => freeWord (w j))) →
      Function.Injective (boundaryTwo (target w)
        (coeff (PresentationTransport.transport w PresentationRose.generatorUnit hk)))

/-- Every element of the actual free group has a raw (unreduced) word representative. -/
theorem exists_word (f : F) : ∃ w : Word, freeWord w = f := by
  induction f using FreeGroup.induction_on with
  | one => exact ⟨[], rfl⟩
  | of g => exact ⟨[pos g], by simp [freeWord, freeLetter, pos]⟩
  | inv_of g _ => exact ⟨[neg g], by simp [freeWord, freeLetter, neg]⟩
  | mul a b ha hb =>
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    exact ⟨u ++ v, by simp [freeWord, List.map_append, List.prod_append]⟩

/-- Under the displayed comparison, no four elements normally generate N. -/
theorem no_four_normal_generators (hc : FoxFillingComparison) : ¬ HasNormalGenerators 4 := by
  rintro ⟨v, hv⟩
  choose w hrep using fun j => exists_word (v j)
  have hk := tuple_kills w v hv hrep
  have hfox : Function.Injective (ComplexFox.boundaryTwo (fun j => freeWord (w j))) := by
    have he : (fun j => freeWord (w j)) = v := funext hrep
    rw [he]
    exact ComplexFox.boundaryTwo_injective v hv
  exact PresentationMoves.target_d2_not_injective w v hv hrep (hc w hk hfox)

theorem normal_rank_five (hc : FoxFillingComparison) : NormalRankFive := by
  refine ⟨hasNormalGenerators_five, fun k hk => ?_⟩
  have h4 := FoxSpan.normal_generators_at_least_four hk
  rcases Nat.lt_or_ge k 5 with h | h
  · have hk4 : k = 4 := by omega
    subst hk4
    exact (no_four_normal_generators hc hk).elim
  · exact h

/-- CONDITIONAL fixed-presentation integral relation gap: d_ZG(N_ab) = 4 < 5 = d_F(N),
with the canonical integral ZG action. The single hypothesis is displayed above. -/
theorem integral_relation_gap_of_comparison (hc : FoxFillingComparison) :
    IntegralRelationGapTarget :=
  ⟨RelationModule.canonicalAction, Perfectness.integral_module_rank_four.1,
    Perfectness.integral_module_rank_four.2, normal_rank_five hc⟩

/-! Non-vacuity guard: the comparison's antecedent holds for a genuine killed tuple. -/

theorem r1_killed : ∀ j : Fin 1, value (PresentationRose.transport PresentationRose.generatorUnit)
    (PresentationRose.wordPath ((fun _ : Fin 1 => r1) j)) = 1 := by
  intro j
  change value PresentationRose.originalTransport (PresentationRose.wordPath r1) = 1
  rw [PresentationRose.word_value]
  have hn := FoxSpan.sourceRelator_mem_kernel 0
  have he : quotientMap (freeWord r1) = 1 := MonoidHom.mem_ker.mp hn
  rw [he, map_one]

theorem r1_fox_a1_ne_zero : FoxSemantics.complexDerivative (freeWord r1) .a1 ≠ 0 := by
  rw [FoxSemantics.complex_foxRow_sound]
  have h : CycloPair.foxRow r1 .a1 = (⟨-2,0⟩ : CycloPair) := by decide
  rw [h]
  norm_num

theorem comparison_antecedent_satisfiable :
    Function.Injective (ComplexFox.boundaryTwo (fun _ : Fin 1 => freeWord r1)) := by
  intro a b hab
  funext j
  fin_cases j
  have h := congrFun hab .a1
  simp only [ComplexFox.boundaryTwo, Fintype.linearCombination_apply, Finset.univ_unique,
    Finset.sum_singleton, Pi.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ r1_fox_a1_ne_zero h

end D2RelationGap.ConditionalRelationGap
