import D2RelationGap.Character
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-! Connects the faithful cyclotomic interpretation to genuine complex coefficients.
Credit: OpenAI, A Counterexample to Wall's D(2) Problem, October 6, 2026;
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
The positive imaginary root is explicit; no topological obstruction is assumed. -/
namespace D2RelationGap
namespace ComplexCharacter
open Targets Cyclotomic

noncomputable section

def complexZeta : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem complexZeta_relation : complexZeta ^ 2 + complexZeta + 1 = 0 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [complexZeta, pow_two] <;> nlinarith [hs]

theorem complexZeta_im_positive : 0 < complexZeta.im :=
  div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)

theorem complexZeta_root :
    polynomial.eval₂ (algebraMap ℚ ℂ) complexZeta = 0 := by
  unfold polynomial
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_one]
  exact complexZeta_relation

def complexEmbedding : E →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℚ ℂ) complexZeta complexZeta_root

theorem complexEmbedding_injective : Function.Injective complexEmbedding :=
  complexEmbedding.injective

@[simp] theorem complexEmbedding_zeta : complexEmbedding zeta = complexZeta :=
  AdjoinRoot.lift_root complexZeta_root

theorem pair_complex_embedding (x : CycloPair) :
    complexEmbedding (evalPair x) = (x.a : ℂ) + (x.b : ℂ) * complexZeta := by
  simp [evalPair]

theorem pair_complex_embedding_injective :
    Function.Injective (fun x : CycloPair => complexEmbedding (evalPair x)) :=
  complexEmbedding_injective.comp evalPair_injective

def character : G →* ℂˣ :=
  (Units.map complexEmbedding.toMonoidHom).comp Character.character

def rho : G →* ℂ := complexEmbedding.toMonoidHom.comp Character.rho

theorem character_value (g : G) : (character g : ℂ) = rho g := rfl

theorem rho_quotient (f : F) :
    rho (quotientMap f) = complexEmbedding (Character.freeValue f) := by
  simp [rho, Character.rho_quotient]

theorem wordValue_sound (w : Word) :
    rho (quotientMap (freeWord w)) =
      ((CycloPair.wordValue w).a : ℂ) + ((CycloPair.wordValue w).b : ℂ) * complexZeta := by
  rw [rho_quotient, Character.wordValue_sound, pair_complex_embedding]

theorem rho_x1 : rho (quotientMap (FreeGroup.of .x1)) = -1 := by
  simp [rho, Character.rho_x1]

theorem rho_a1 : rho (quotientMap (FreeGroup.of .a1)) = complexZeta := by
  simp [rho, Character.rho_a1]

theorem rho_x2 : rho (quotientMap (FreeGroup.of .x2)) = complexZeta ^ 2 := by
  simp [rho, Character.rho_x2]

theorem rho_a2 : rho (quotientMap (FreeGroup.of .a2)) = -1 := by
  simp [rho, Character.rho_a2]

theorem rho_s : rho (quotientMap (FreeGroup.of .s)) = 1 := by
  simp [rho, Character.rho_s]

theorem rho_x1_nontrivial : rho (quotientMap (FreeGroup.of .x1)) ≠ 1 := by
  rw [rho_x1]
  norm_num

theorem complexZeta_cube : complexZeta ^ 3 = 1 := by
  rw [← complexEmbedding_zeta, ← map_pow, zeta_cube, map_one]

theorem complexZeta_ne_one : complexZeta ≠ 1 := by
  rw [← complexEmbedding_zeta, ← map_one complexEmbedding]
  exact fun h => zeta_ne_one (complexEmbedding_injective h)

/-- The scalar certificate is nonzero over C; the actual matrix determinant bridge is separate. -/
theorem complex_distinguished_minor_nonzero :
    complexEmbedding (evalPair (CycloPair.det 4
      (CycloPair.foxTable.map (CycloPair.eraseAt 3)))) ≠ 0 := by
  rw [← map_zero complexEmbedding]
  exact fun h => interpreted_distinguished_minor_nonzero (complexEmbedding_injective h)

theorem complex_distinguished_minor_value :
    complexEmbedding (evalPair (CycloPair.det 4
      (CycloPair.foxTable.map (CycloPair.eraseAt 3)))) = -4 * (1 - complexZeta ^ 2) := by
  rw [interpreted_distinguished_minor_value]
  have h4 : complexEmbedding (4 : E) = (4 : ℂ) := map_natCast complexEmbedding 4
  simp only [map_mul, map_neg, map_sub, map_one, map_pow, complexEmbedding_zeta]
  rw [h4]

theorem complex_corrupted_minor_rejected :
    complexEmbedding (evalPair (CycloPair.det 4
      (CycloPair.foxTable.map (CycloPair.eraseAt 3)))) ≠ complexEmbedding (evalPair ⟨8, 4⟩) :=
  fun h => interpreted_corrupted_minor_rejected (complexEmbedding_injective h)

theorem corrupted_relator_nontrivial :
    rho (quotientMap (freeWord ([pos .x1] ++ List.replicate 12 (neg .a2)))) ≠ 1 := by
  rw [rho_quotient, ← map_one complexEmbedding]
  exact fun h => Character.corrupted_relator_nontrivial (complexEmbedding_injective h)

theorem corrupted_a1_assignment_rejected : rho (quotientMap (FreeGroup.of .a1)) ≠ 1 := by
  rw [rho_a1]
  exact complexZeta_ne_one

end
end ComplexCharacter
end D2RelationGap
