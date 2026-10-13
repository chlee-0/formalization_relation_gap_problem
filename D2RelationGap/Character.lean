import D2RelationGap.Cyclotomic
import D2RelationGap.WordSemantics

/-! OpenAI's character descends to the actual original six-relator quotient G.
Credit: A Counterexample to Wall's D(2) Problem, October 6, 2026;
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
Coefficients are in the genuine field Q[X]/(X^2+X+1); no complex embedding is claimed here. -/
namespace D2RelationGap
namespace Character
open Targets Cyclotomic

noncomputable section

theorem rho_mul_conj (g : Gen) :
    CycloPair.mul (CycloPair.rho g) (CycloPair.conj (CycloPair.rho g)) = CycloPair.one := by
  have hm : g ∈ allGens := by cases g <;> decide
  exact beq_iff_eq.mp (List.all_eq_true.mp CycloPair.roots_are_units g hm)

def generatorUnit (g : Gen) : Eˣ where
  val := evalPair (CycloPair.rho g)
  inv := evalPair (CycloPair.conj (CycloPair.rho g))
  val_inv := by rw [← evalPair_mul, rho_mul_conj, evalPair_one]
  inv_val := by rw [mul_comm, ← evalPair_mul, rho_mul_conj, evalPair_one]

def freeCharacter : F →* Eˣ := FreeGroup.lift generatorUnit

def freeValue : F →* E := (Units.coeHom E).comp freeCharacter

theorem freeValue_letter (l : Letter) :
    freeValue (freeLetter l) = evalPair (CycloPair.letterValue l) := by
  rcases l with ⟨g, b⟩
  cases b <;> simp [freeValue, freeCharacter, freeLetter, CycloPair.letterValue, generatorUnit]

theorem word_fold_sound (w : Word) (p : CycloPair) :
    evalPair (w.foldl (fun acc l => CycloPair.mul acc (CycloPair.letterValue l)) p) =
      evalPair p * freeValue (freeWord w) := by
  induction w generalizing p with
  | nil => simp
  | cons l w ih =>
    rw [List.foldl_cons, ih, evalPair_mul, ← freeValue_letter]
    simp [freeWord_cons, map_mul, mul_assoc]

theorem wordValue_sound (w : Word) :
    freeValue (freeWord w) = evalPair (CycloPair.wordValue w) := by
  simpa [CycloPair.wordValue] using (word_fold_sound w CycloPair.one).symm

theorem word_character_trivial (w : Word) (hw : w ∈ allWords) :
    freeCharacter (freeWord w) = 1 := by
  have hm : CycloPair.wordValue w ∈ allWords.map CycloPair.wordValue :=
    List.mem_map_of_mem hw
  rw [CycloPair.relators_evaluate_to_one] at hm
  have hv : CycloPair.wordValue w = CycloPair.one := (List.mem_replicate.mp hm).2
  apply Units.ext
  change freeValue (freeWord w) = 1
  rw [wordValue_sound, hv, evalPair_one]

theorem original_relators_killed : ∀ r ∈ quotientRelations, freeCharacter r = 1 := by
  intro r hr
  simp only [quotientRelations, sourceRelations, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
  all_goals exact word_character_trivial _ (by simp [allWords, sourceWords])

def character : G →* Eˣ := PresentedGroup.toGroup original_relators_killed

def rho : G →* E := (Units.coeHom E).comp character

/-- The map factors through exactly the original quotient map, not a replacement quotient. -/
theorem character_quotient (f : F) : character (quotientMap f) = freeCharacter f := rfl

theorem rho_quotient (f : F) : rho (quotientMap f) = freeValue f := rfl

@[simp] theorem character_of (g : Gen) :
    character (quotientMap (FreeGroup.of g)) = generatorUnit g := by
  rw [character_quotient]
  exact FreeGroup.lift_apply_of

theorem rho_x1 : rho (quotientMap (FreeGroup.of .x1)) = -1 := by
  simp [rho, generatorUnit, evalPair, CycloPair.rho]

theorem rho_a1 : rho (quotientMap (FreeGroup.of .a1)) = zeta := by
  simp [rho, generatorUnit, CycloPair.rho]

theorem rho_x2 : rho (quotientMap (FreeGroup.of .x2)) = zeta ^ 2 := by
  simp [rho, generatorUnit, evalPair, CycloPair.rho, zeta_square]
  ring

theorem rho_a2 : rho (quotientMap (FreeGroup.of .a2)) = -1 := by
  simp [rho, generatorUnit, evalPair, CycloPair.rho]

theorem rho_s : rho (quotientMap (FreeGroup.of .s)) = 1 := by
  simp [rho, generatorUnit, CycloPair.rho]

theorem rho_x1_nontrivial : rho (quotientMap (FreeGroup.of .x1)) ≠ 1 := by
  rw [rho_x1]
  norm_num

theorem x1_square : (quotientMap (FreeGroup.of .x1)) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (show freeWord t1 ∈ quotientRelations by simp [quotientRelations])
  simpa [t1, freeWord, freeLetter, pos, pow_two] using h

theorem x1_ne_one : quotientMap (FreeGroup.of .x1) ≠ 1 := by
  intro h
  apply rho_x1_nontrivial
  rw [h, map_one]

theorem freeCharacter_trivial_on_kernel (n : N) : freeCharacter (n : F) = 1 := by
  rw [← character_quotient]
  rw [MonoidHom.mem_ker.mp n.property, map_one]

/-- A deliberately corrupted relator stays nontrivial in the genuine field interpretation. -/
theorem corrupted_relator_nontrivial :
    freeValue (freeWord ([pos .x1] ++ List.replicate 12 (neg .a2))) ≠ 1 := by
  rw [wordValue_sound, ← evalPair_one]
  exact fun h => CycloPair.corrupted_relator_rejected (evalPair_injective h)

/-- Incorrectly replacing the a1 character value by 1 is rejected. -/
theorem corrupted_a1_assignment_rejected : rho (quotientMap (FreeGroup.of .a1)) ≠ 1 := by
  rw [rho_a1]
  exact zeta_ne_one

end
end Character
end D2RelationGap
