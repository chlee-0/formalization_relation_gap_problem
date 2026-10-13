import D2RelationGap.ComplexCharacter

/-! Evaluated left Fox derivatives on the actual free group and its actual kernel.
The character and Fox data are from OpenAI, A Counterexample to Wall's D(2) Problem,
October 6, 2026; openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
An affine-group lift proves the cocycle laws independently of the executable scan. -/
namespace D2RelationGap.FoxSemantics
open Targets Cyclotomic Character
noncomputable section

abbrev Vector := Gen → E

@[ext] structure Affine where
  scalar : Eˣ
  vector : Vector

instance : One Affine := ⟨⟨1, 0⟩⟩
instance : Mul Affine := ⟨fun a b =>
  ⟨a.scalar * b.scalar, fun g => a.vector g + (a.scalar : E) * b.vector g⟩⟩
instance : Inv Affine := ⟨fun a =>
  ⟨a.scalar⁻¹, fun g => -(↑(a.scalar⁻¹) : E) * a.vector g⟩⟩

instance : Group Affine where
  mul_assoc a b c := by
    apply Affine.ext
    · exact mul_assoc _ _ _
    · funext g
      change (a.vector g + (a.scalar : E) * b.vector g) +
        ↑(a.scalar * b.scalar) * c.vector g =
        a.vector g + (a.scalar : E) * (b.vector g + (b.scalar : E) * c.vector g)
      simp [mul_add, mul_assoc, add_assoc]
  one_mul a := by
    apply Affine.ext
    · exact one_mul _
    · funext g; change 0 + (↑(1 : Eˣ) : E) * a.vector g = a.vector g; simp
  mul_one a := by
    apply Affine.ext
    · exact mul_one _
    · funext g; change a.vector g + (a.scalar : E) * 0 = a.vector g; simp
  inv_mul_cancel a := by
    apply Affine.ext
    · exact inv_mul_cancel _
    · funext g; change -(a.scalar⁻¹ : Eˣ) * a.vector g +
        (a.scalar⁻¹ : Eˣ) * a.vector g = 0; simp

def scalarHom : Affine →* Eˣ where
  toFun := Affine.scalar
  map_one' := rfl
  map_mul' _ _ := rfl

def basis (g : Gen) : Vector := fun h => if h = g then 1 else 0

def generatorAffine (g : Gen) : Affine := ⟨generatorUnit g, basis g⟩
def freeAffine : F →* Affine := FreeGroup.lift generatorAffine
def derivative (f : F) : Vector := (freeAffine f).vector

theorem freeAffine_scalar (f : F) : (freeAffine f).scalar = freeCharacter f := by
  have h : scalarHom.comp freeAffine = freeCharacter :=
    FreeGroup.ext_hom _ _ (fun g => by simp [freeAffine, freeCharacter, scalarHom, generatorAffine])
  exact DFunLike.congr_fun h f

@[simp] theorem derivative_one : derivative 1 = 0 := by
  change (freeAffine 1).vector = 0
  rw [map_one]; rfl

theorem derivative_mul (u v : F) :
    derivative (u * v) = derivative u + freeValue u • derivative v := by
  funext g
  simp only [derivative, map_mul]
  change (freeAffine u).vector g + ((freeAffine u).scalar : E) * (freeAffine v).vector g =
    (freeAffine u).vector g + freeValue u * (freeAffine v).vector g
  rw [freeAffine_scalar]; rfl

theorem derivative_inv (u : F) :
    derivative u⁻¹ = -(freeValue u⁻¹ • derivative u) := by
  funext g
  change (freeAffine u⁻¹).vector g = -(freeValue u⁻¹ * (freeAffine u).vector g)
  rw [map_inv]
  change -(↑((freeAffine u).scalar⁻¹) : E) * (freeAffine u).vector g =
    -(freeValue u⁻¹ * (freeAffine u).vector g)
  rw [freeAffine_scalar]
  simp [freeValue]

@[simp] theorem derivative_of (g : Gen) : derivative (FreeGroup.of g) = basis g := by
  simp [derivative, freeAffine, generatorAffine]

theorem freeValue_kernel (n : N) : freeValue (n : F) = 1 := by
  change (freeCharacter (n : F) : E) = 1
  rw [freeCharacter_trivial_on_kernel]; rfl

theorem derivative_conjugate (f : F) (n : N) :
    derivative (f * (n : F) * f⁻¹) = freeValue f • derivative (n : F) := by
  rw [derivative_mul, derivative_mul, map_mul, freeValue_kernel, mul_one, derivative_inv]
  have h : freeValue f * freeValue f⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [smul_neg, smul_smul, h, one_smul]
  abel

theorem derivative_letter (l : Letter) (g : Gen) :
    derivative (freeLetter l) g =
      if g = l.gen then (if l.positive then 1 else -freeValue (freeLetter l)) else 0 := by
  rcases l with ⟨h, b⟩
  cases b <;> by_cases hg : g = h <;> simp [freeLetter, derivative_inv, basis, hg]

theorem scanStep_scalar (st : CycloPair × CycloPair.Row) (l : Letter) :
    evalPair (CycloPair.scanStep st l).1 = evalPair st.1 * freeValue (freeLetter l) := by
  simp [CycloPair.scanStep, evalPair_mul, freeValue_letter]

theorem scanStep_vector (st : CycloPair × CycloPair.Row) (l : Letter) (g : Gen) :
    evalPair ((CycloPair.scanStep st l).2 g) =
      evalPair (st.2 g) + evalPair st.1 * derivative (freeLetter l) g := by
  rw [derivative_letter]
  rcases l with ⟨h, b⟩
  cases b <;> by_cases hg : g = h <;>
    simp [CycloPair.scanStep, hg, evalPair_add, evalPair_neg, evalPair_mul, freeValue_letter]

theorem scan_vector_sound (w : Word) (st : CycloPair × CycloPair.Row) (g : Gen) :
    evalPair ((w.foldl CycloPair.scanStep st).2 g) =
      evalPair (st.2 g) + evalPair st.1 * derivative (freeWord w) g := by
  induction w generalizing st with
  | nil => simp
  | cons l w ih =>
    rw [List.foldl_cons, ih, scanStep_vector, scanStep_scalar,
      freeWord_cons, derivative_mul]
    change evalPair (st.2 g) + evalPair st.1 * derivative (freeLetter l) g +
      (evalPair st.1 * freeValue (freeLetter l)) * derivative (freeWord w) g =
      evalPair (st.2 g) + evalPair st.1 *
        (derivative (freeLetter l) g + freeValue (freeLetter l) * derivative (freeWord w) g)
    ring

/-- The closed prefix scan computes the actual free-group cocycle, on every word. -/
theorem foxRow_sound (w : Word) (g : Gen) :
    derivative (freeWord w) g = evalPair (CycloPair.foxRow w g) := by
  simpa [CycloPair.foxRow] using (scan_vector_sound w (CycloPair.one, fun _ => CycloPair.zero) g).symm

/-- A corrupted Fox entry is rejected after interpreting the scan on actual F. -/
theorem corrupted_fox_entry_rejected :
    derivative (freeWord r1) .a1 ≠ evalPair (⟨-1,0⟩ : CycloPair) := by
  rw [foxRow_sound]
  exact fun h => CycloPair.corrupted_fox_entry_rejected (evalPair_injective h)

/-- Restriction to the actual kernel is additive, because the lifted character kills N. -/
def kernelHom : N →* Multiplicative Vector where
  toFun := fun n => Multiplicative.ofAdd (derivative (n : F))
  map_one' := by change derivative (1 : F) = 0; exact derivative_one
  map_mul' n m := by
    change derivative ((n : F) * (m : F)) = derivative (n : F) + derivative (m : F)
    rw [derivative_mul, freeValue_kernel, one_smul]

/-- This map has the actual N_ab as its domain. Integral ZG linearity is a later obligation. -/
def abelianizedDerivative : RelationCarrier →+ Vector :=
  (Abelianization.lift kernelHom).toAdditiveLeft

theorem abelianizedDerivative_of (n : N) :
    abelianizedDerivative (Additive.ofMul (Abelianization.of n)) = derivative (n : F) := rfl

theorem abelianizedDerivative_conjugate (f : F) (n n' : N)
    (h : (n' : F) = f * (n : F) * f⁻¹) :
    abelianizedDerivative (Additive.ofMul (Abelianization.of n')) =
      Character.rho (quotientMap f) •
        abelianizedDerivative (Additive.ofMul (Abelianization.of n)) := by
  rw [abelianizedDerivative_of, abelianizedDerivative_of, h, derivative_conjugate, rho_quotient]

theorem abelianizedDerivative_zlinear (k : ℤ) (v : RelationCarrier) :
    abelianizedDerivative (k • v) = k • abelianizedDerivative v := map_zsmul _ _ _

def complexDerivative (f : F) : Gen → ℂ :=
  fun g => ComplexCharacter.complexEmbedding (derivative f g)

theorem complexDerivative_mul (u v : F) :
    complexDerivative (u * v) = complexDerivative u +
      ComplexCharacter.rho (quotientMap u) • complexDerivative v := by
  funext g
  simp [complexDerivative, derivative_mul, ComplexCharacter.rho_quotient]

theorem complexDerivative_inv (u : F) :
    complexDerivative u⁻¹ =
      -(ComplexCharacter.rho (quotientMap u⁻¹) • complexDerivative u) := by
  funext g
  simp [complexDerivative, derivative_inv, ComplexCharacter.rho_quotient]

theorem complexDerivative_conjugate (f : F) (n : N) :
    complexDerivative (f * (n : F) * f⁻¹) =
      ComplexCharacter.rho (quotientMap f) • complexDerivative (n : F) := by
  funext g
  simp [complexDerivative, derivative_conjugate, ComplexCharacter.rho_quotient]

theorem complex_foxRow_sound (w : Word) (g : Gen) :
    complexDerivative (freeWord w) g =
      ((CycloPair.foxRow w g).a : ℂ) +
        ((CycloPair.foxRow w g).b : ℂ) * ComplexCharacter.complexZeta := by
  rw [complexDerivative, foxRow_sound]
  exact ComplexCharacter.pair_complex_embedding _

end
end D2RelationGap.FoxSemantics
